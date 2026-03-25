use std::collections::HashMap;

use miette::NamedSource;

use crate::atlas_c::{
    atlas_hir::{
        HirModule,
        arena::HirArena,
        error::{
            HirError, HirResult, TryingToAccessADeletedValueError, TypeIsNotTriviallyCopyableError,
        },
        expr::{HirDeleteExpr, HirExpr, HirIdentExpr, HirUnaryOp},
        signature::HirModuleSignature,
        stmt::{HirAssignStmt, HirBlock, HirExprStmt, HirStatement},
        ty::HirTy,
    },
    utils,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OwnershipState {
    Alive,
    Deleted(crate::atlas_c::utils::Span),
}

#[derive(Debug, Clone, Copy)]
struct LocalVar<'hir> {
    name: &'hir str,
    ty: &'hir HirTy<'hir>,
    is_compiler_temp: bool,
}

#[derive(Debug, Clone, Default)]
struct ScopeFrame<'hir> {
    locals: Vec<LocalVar<'hir>>,
    states: HashMap<&'hir str, OwnershipState>,
}

pub struct HirOwnershipPass<'hir> {
    _hir_arena: &'hir HirArena<'hir>,
    signature: HirModuleSignature<'hir>,
}

impl<'hir> HirOwnershipPass<'hir> {
    pub fn new(hir_arena: &'hir HirArena<'hir>, signature: &HirModuleSignature<'hir>) -> Self {
        Self {
            _hir_arena: hir_arena,
            signature: signature.clone(),
        }
    }

    pub fn run(
        &mut self,
        hir_module: &'hir mut HirModule<'hir>,
    ) -> HirResult<&'hir mut HirModule<'hir>> {
        for function in hir_module.body.functions.values_mut() {
            let mut scope_stack = vec![ScopeFrame::default()];
            for param in &function.signature.params {
                self.register_local(
                    &mut scope_stack,
                    LocalVar {
                        name: param.name,
                        ty: param.ty,
                        is_compiler_temp: self.is_compiler_temp_name(param.name),
                    },
                );
            }

            function.body = self.transform_block(function.body.clone(), &mut scope_stack)?;
        }

        Ok(hir_module)
    }

    fn transform_block(
        &self,
        block: HirBlock<'hir>,
        scope_stack: &mut Vec<ScopeFrame<'hir>>,
    ) -> HirResult<HirBlock<'hir>> {
        scope_stack.push(ScopeFrame::default());

        let mut statements = Vec::with_capacity(block.statements.len());
        for statement in block.statements {
            match statement {
                HirStatement::Block(inner) => {
                    let transformed = self.transform_block(inner, scope_stack)?;
                    statements.push(HirStatement::Block(transformed));
                }
                HirStatement::Return(ret) => {
                    self.validate_expr(&ret.value, scope_stack)?;
                    let excluded = self.returned_identifier_name(&ret.value);
                    statements.extend(self.collect_scope_drops(scope_stack, excluded));
                    statements.push(HirStatement::Return(ret));
                }
                HirStatement::Expr(expr_stmt) => {
                    self.validate_expr(&expr_stmt.expr, scope_stack)?;
                    if let Some((name, span)) = self.deleted_identifier(&expr_stmt.expr) {
                        self.mark_deleted(scope_stack, name, span);
                    }
                    statements.push(HirStatement::Expr(expr_stmt));
                }
                HirStatement::Let(let_stmt) => {
                    self.validate_expr(&let_stmt.value, scope_stack)?;
                    self.ensure_identifier_copy_allowed(
                        scope_stack,
                        &let_stmt.value,
                        Some(let_stmt.name),
                    )?;
                    let consumed_temp = self.consumed_compiler_temp_from_value(
                        scope_stack,
                        &let_stmt.value,
                        let_stmt.name,
                        let_stmt.ty,
                    );
                    self.register_local(
                        scope_stack,
                        LocalVar {
                            name: let_stmt.name,
                            ty: let_stmt.ty,
                            is_compiler_temp: self.is_compiler_temp_name(let_stmt.name),
                        },
                    );
                    if let Some((temp_name, temp_span)) = consumed_temp {
                        self.mark_deleted(scope_stack, temp_name, temp_span);
                    }
                    statements.push(HirStatement::Let(let_stmt));
                }
                HirStatement::Const(const_stmt) => {
                    self.validate_expr(&const_stmt.value, scope_stack)?;
                    self.ensure_identifier_copy_allowed(
                        scope_stack,
                        &const_stmt.value,
                        Some(const_stmt.name),
                    )?;
                    let consumed_temp = self.consumed_compiler_temp_from_value(
                        scope_stack,
                        &const_stmt.value,
                        const_stmt.name,
                        const_stmt.ty,
                    );
                    self.register_local(
                        scope_stack,
                        LocalVar {
                            name: const_stmt.name,
                            ty: const_stmt.ty,
                            is_compiler_temp: self.is_compiler_temp_name(const_stmt.name),
                        },
                    );
                    if let Some((temp_name, temp_span)) = consumed_temp {
                        self.mark_deleted(scope_stack, temp_name, temp_span);
                    }
                    statements.push(HirStatement::Const(const_stmt));
                }
                HirStatement::Assign(assign_stmt) => {
                    self.validate_expr(&assign_stmt.dst, scope_stack)?;
                    self.validate_expr(&assign_stmt.val, scope_stack)?;
                    let dst_name = match self.strip_noop_unary(&assign_stmt.dst) {
                        HirExpr::Ident(id) => Some(id.name),
                        _ => None,
                    };
                    self.ensure_identifier_copy_allowed(scope_stack, &assign_stmt.val, dst_name)?;
                    let consumed_temp =
                        self.consumed_compiler_temp_from_assign(scope_stack, &assign_stmt);
                    if let Some(delete_stmt) =
                        self.pre_delete_before_assign(scope_stack, &assign_stmt)
                    {
                        statements.push(delete_stmt);
                    }
                    self.mark_assigned_alive(scope_stack, &assign_stmt);
                    if let Some((temp_name, temp_span)) = consumed_temp {
                        self.mark_deleted(scope_stack, temp_name, temp_span);
                    }
                    statements.push(HirStatement::Assign(assign_stmt));
                }
                HirStatement::IfElse(mut if_else) => {
                    self.validate_expr(&if_else.condition, scope_stack)?;
                    if_else.then_branch = self.transform_block(if_else.then_branch, scope_stack)?;
                    if let Some(else_branch) = if_else.else_branch.take() {
                        if_else.else_branch = Some(self.transform_block(else_branch, scope_stack)?);
                    }
                    statements.push(HirStatement::IfElse(if_else));
                }
                HirStatement::While(mut while_stmt) => {
                    self.validate_expr(&while_stmt.condition, scope_stack)?;
                    while_stmt.body = self.transform_block(while_stmt.body, scope_stack)?;
                    statements.push(HirStatement::While(while_stmt));
                }
                HirStatement::Break(span) => statements.push(HirStatement::Break(span)),
                HirStatement::Continue(span) => statements.push(HirStatement::Continue(span)),
            }
        }

        // Block exit RAII: destroy surviving locals declared in this scope in reverse order.
        if let Some(frame) = scope_stack.last() {
            let mut tail_drops = Vec::new();
            for local in frame.locals.iter().rev() {
                if !matches!(frame.states.get(local.name), Some(OwnershipState::Alive)) {
                    continue;
                }
                if self.should_auto_delete_local(local) {
                    tail_drops.push(self.delete_stmt_for(block.span, local.name, local.ty));
                }
            }
            statements.extend(tail_drops);
        }

        scope_stack.pop();
        Ok(HirBlock {
            span: block.span,
            statements,
        })
    }

    fn should_auto_delete(&self, ty: &'hir HirTy<'hir>) -> bool {
        match ty {
            HirTy::PtrTy(_) => false,
            HirTy::Named(named) => self
                .signature
                .structs
                .get(named.name)
                .is_some_and(|sig| sig.destructor.is_some()),
            HirTy::Generic(generic) => self
                .signature
                .structs
                .get(generic.name)
                .is_some_and(|sig| sig.destructor.is_some()),
            HirTy::InlineArray(arr) => self.should_auto_delete(arr.inner),
            _ => false,
        }
    }

    fn should_auto_delete_local(&self, local: &LocalVar<'hir>) -> bool {
        self.should_auto_delete(local.ty)
    }

    fn is_implicitly_copyable(&self, ty: &'hir HirTy<'hir>) -> bool {
        match ty {
            HirTy::Integer(_)
            | HirTy::UnsignedInteger(_)
            | HirTy::Float(_)
            | HirTy::Boolean(_)
            | HirTy::Char(_)
            | HirTy::Unit(_)
            | HirTy::String(_)
            | HirTy::LiteralInteger(_)
            | HirTy::LiteralUnsignedInteger(_)
            | HirTy::LiteralFloat(_)
            | HirTy::PtrTy(_)
            | HirTy::Function(_)
            | HirTy::Slice(_) => true,
            HirTy::InlineArray(arr) => self.is_implicitly_copyable(arr.inner),
            HirTy::Named(named) => self
                .signature
                .structs
                .get(named.name)
                .is_some_and(|sig| sig.is_trivially_copyable),
            HirTy::Generic(generic) => self
                .signature
                .structs
                .get(generic.name)
                .is_some_and(|sig| sig.is_trivially_copyable),
            _ => false,
        }
    }

    fn ensure_identifier_copy_allowed(
        &self,
        scope_stack: &[ScopeFrame<'hir>],
        value: &HirExpr<'hir>,
        dst_name: Option<&'hir str>,
    ) -> HirResult<()> {
        let src = match self.strip_noop_unary(value) {
            HirExpr::Ident(id) => id,
            _ => return Ok(()),
        };

        if dst_name.is_some_and(|dst| dst == src.name) {
            return Ok(());
        }

        let Some(src_local) = self.find_local(scope_stack, src.name) else {
            return Ok(());
        };

        // Compiler temporaries can transfer ownership without explicit copy().
        if src_local.is_compiler_temp {
            return Ok(());
        }

        if self.is_implicitly_copyable(src_local.ty) {
            return Ok(());
        }

        let path = src.span.path;
        let src_text = utils::get_file_content(path).unwrap_or_default();
        Err(HirError::TypeIsNotTriviallyCopyable(
            TypeIsNotTriviallyCopyableError {
                src: NamedSource::new(path, src_text),
                span: src.span,
                type_name: format!("{}", src_local.ty),
            },
        ))
    }

    fn consumed_compiler_temp_from_assign(
        &self,
        scope_stack: &[ScopeFrame<'hir>],
        assign: &HirAssignStmt<'hir>,
    ) -> Option<(&'hir str, crate::atlas_c::utils::Span)> {
        let dst = match self.strip_noop_unary(&assign.dst) {
            HirExpr::Ident(id) => id,
            _ => return None,
        };
        let src = match self.strip_noop_unary(&assign.val) {
            HirExpr::Ident(id) => id,
            _ => return None,
        };

        if src.name == dst.name {
            return None;
        }

        let src_local = self.find_local(scope_stack, src.name)?;
        if !src_local.is_compiler_temp {
            return None;
        }

        let dst_local = self.find_local(scope_stack, dst.name)?;
        if dst_local.is_compiler_temp {
            return None;
        }

        if !std::ptr::eq(src_local.ty, dst_local.ty) {
            return None;
        }

        Some((src.name, src.span))
    }

    fn consumed_compiler_temp_from_value(
        &self,
        scope_stack: &[ScopeFrame<'hir>],
        value: &HirExpr<'hir>,
        dst_name: &'hir str,
        dst_ty: &'hir HirTy<'hir>,
    ) -> Option<(&'hir str, crate::atlas_c::utils::Span)> {
        let src = match self.strip_noop_unary(value) {
            HirExpr::Ident(id) => id,
            _ => return None,
        };

        if src.name == dst_name {
            return None;
        }

        let src_local = self.find_local(scope_stack, src.name)?;
        if !src_local.is_compiler_temp {
            return None;
        }

        if self.is_compiler_temp_name(dst_name) {
            return None;
        }

        if !std::ptr::eq(src_local.ty, dst_ty) {
            return None;
        }

        Some((src.name, src.span))
    }

    fn find_local<'a>(
        &self,
        scope_stack: &'a [ScopeFrame<'hir>],
        name: &'hir str,
    ) -> Option<&'a LocalVar<'hir>> {
        for frame in scope_stack.iter().rev() {
            if let Some(local) = frame.locals.iter().rev().find(|v| v.name == name) {
                return Some(local);
            }
        }
        None
    }

    fn returned_identifier_name(&self, expr: &HirExpr<'hir>) -> Option<&'hir str> {
        match self.strip_noop_unary(expr) {
            HirExpr::Ident(id) => Some(id.name),
            _ => None,
        }
    }

    fn validate_expr(
        &self,
        expr: &HirExpr<'hir>,
        scope_stack: &mut Vec<ScopeFrame<'hir>>,
    ) -> HirResult<()> {
        match self.strip_noop_unary(expr) {
            HirExpr::Ident(id) => self.validate_deleted_use(scope_stack, id.name, id.span),
            HirExpr::Delete(del) => self.validate_expr(&del.expr, scope_stack),
            HirExpr::Unary(unary) => self.validate_expr(&unary.expr, scope_stack),
            HirExpr::Casting(cast) => self.validate_expr(&cast.expr, scope_stack),
            HirExpr::HirBinaryOperation(binary) => {
                self.validate_expr(&binary.lhs, scope_stack)?;
                self.validate_expr(&binary.rhs, scope_stack)
            }
            HirExpr::Call(call) => {
                self.validate_expr(&call.callee, scope_stack)?;
                for arg in &call.args {
                    self.validate_expr(arg, scope_stack)?;
                }
                Ok(())
            }
            HirExpr::ListLiteral(list) => {
                for item in &list.items {
                    self.validate_expr(item, scope_stack)?;
                }
                Ok(())
            }
            HirExpr::ObjLiteral(obj) => {
                for field in &obj.fields {
                    self.validate_expr(&field.value, scope_stack)?;
                }
                Ok(())
            }
            HirExpr::FieldAccess(field) => self.validate_expr(&field.target, scope_stack),
            HirExpr::Indexing(indexing) => {
                self.validate_expr(&indexing.target, scope_stack)?;
                self.validate_expr(&indexing.index, scope_stack)
            }
            HirExpr::StaticAccess(_) => Ok(()),
            HirExpr::IntrinsicCall(intrinsic) => {
                for arg in &intrinsic.args {
                    self.validate_expr(arg, scope_stack)?;
                }
                Ok(())
            }
            HirExpr::ThisLiteral(_)
            | HirExpr::FloatLiteral(_)
            | HirExpr::CharLiteral(_)
            | HirExpr::IntegerLiteral(_)
            | HirExpr::UnitLiteral(_)
            | HirExpr::BooleanLiteral(_)
            | HirExpr::UnsignedIntegerLiteral(_)
            | HirExpr::StringLiteral(_)
            | HirExpr::NullLiteral(_) => Ok(()),
        }
    }

    fn validate_deleted_use(
        &self,
        scope_stack: &[ScopeFrame<'hir>],
        name: &'hir str,
        access_span: crate::atlas_c::utils::Span,
    ) -> HirResult<()> {
        for frame in scope_stack.iter().rev() {
            if let Some(state) = frame.states.get(name) {
                if matches!(state, OwnershipState::Deleted(_)) {
                    let path = access_span.path;
                    let src = utils::get_file_content(path).unwrap_or_default();
                    let delete_span = match state {
                        OwnershipState::Deleted(span) => *span,
                        OwnershipState::Alive => access_span,
                    };
                    return Err(HirError::TryingToAccessADeletedValue(
                        TryingToAccessADeletedValueError {
                            delete_span,
                            access_span,
                            src: NamedSource::new(path, src),
                        },
                    ));
                }
                return Ok(());
            }
        }
        Ok(())
    }

    fn collect_scope_drops(
        &self,
        scope_stack: &[ScopeFrame<'hir>],
        excluded_name: Option<&'hir str>,
    ) -> Vec<HirStatement<'hir>> {
        let mut drops = Vec::new();
        for frame in scope_stack.iter().rev() {
            for local in frame.locals.iter().rev() {
                if Some(local.name) == excluded_name {
                    continue;
                }
                if !matches!(frame.states.get(local.name), Some(OwnershipState::Alive)) {
                    continue;
                }
                if self.should_auto_delete_local(local) {
                    drops.push(self.delete_stmt_for(
                        crate::atlas_c::utils::Span::default(),
                        local.name,
                        local.ty,
                    ));
                }
            }
        }
        drops
    }

    fn delete_stmt_for(
        &self,
        span: crate::atlas_c::utils::Span,
        name: &'hir str,
        ty: &'hir HirTy<'hir>,
    ) -> HirStatement<'hir> {
        HirStatement::Expr(HirExprStmt {
            span,
            expr: HirExpr::Delete(HirDeleteExpr {
                span,
                expr: Box::new(HirExpr::Ident(HirIdentExpr { name, span, ty })),
            }),
        })
    }

    fn deleted_identifier(
        &self,
        expr: &HirExpr<'hir>,
    ) -> Option<(&'hir str, crate::atlas_c::utils::Span)> {
        match self.strip_noop_unary(expr) {
            HirExpr::Delete(delete) => match self.strip_noop_unary(&delete.expr) {
                HirExpr::Ident(id) => Some((id.name, id.span)),
                _ => None,
            },
            _ => None,
        }
    }

    fn mark_deleted(
        &self,
        scope_stack: &mut [ScopeFrame<'hir>],
        name: &'hir str,
        delete_span: crate::atlas_c::utils::Span,
    ) {
        for frame in scope_stack.iter_mut().rev() {
            if frame.states.contains_key(name) {
                frame
                    .states
                    .insert(name, OwnershipState::Deleted(delete_span));
                return;
            }
        }
    }

    fn mark_assigned_alive(
        &self,
        scope_stack: &mut [ScopeFrame<'hir>],
        assign: &HirAssignStmt<'hir>,
    ) {
        if let HirExpr::Ident(id) = self.strip_noop_unary(&assign.dst) {
            for frame in scope_stack.iter_mut().rev() {
                if frame.states.contains_key(id.name) {
                    frame.states.insert(id.name, OwnershipState::Alive);
                    return;
                }
            }
        }
    }

    fn pre_delete_before_assign(
        &self,
        scope_stack: &[ScopeFrame<'hir>],
        assign: &HirAssignStmt<'hir>,
    ) -> Option<HirStatement<'hir>> {
        let ident = match self.strip_noop_unary(&assign.dst) {
            HirExpr::Ident(id) => id,
            _ => return None,
        };

        for frame in scope_stack.iter().rev() {
            let Some(local) = frame.locals.iter().rev().find(|v| v.name == ident.name) else {
                continue;
            };
            if !self.should_auto_delete_local(local) {
                return None;
            }
            if !matches!(frame.states.get(ident.name), Some(OwnershipState::Alive)) {
                return None;
            }
            return Some(self.delete_stmt_for(assign.span, ident.name, local.ty));
        }
        None
    }

    fn register_local(&self, scope_stack: &mut [ScopeFrame<'hir>], var: LocalVar<'hir>) {
        if let Some(frame) = scope_stack.last_mut() {
            frame.locals.push(var);
            frame.states.insert(var.name, OwnershipState::Alive);
        }
    }

    fn is_compiler_temp_name(&self, name: &str) -> bool {
        name.starts_with("__tmp")
    }

    fn strip_noop_unary<'a>(&self, mut expr: &'a HirExpr<'hir>) -> &'a HirExpr<'hir> {
        while let HirExpr::Unary(unary) = expr {
            if unary.op == Some(HirUnaryOp::AsRef) || unary.op == Some(HirUnaryOp::Deref) {
                break;
            }
            if unary.op.is_some() {
                break;
            }
            expr = &unary.expr;
        }
        expr
    }
}
