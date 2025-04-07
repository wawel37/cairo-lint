use crate::context::{CairoLintKind, Lint};
use crate::helper;
use crate::queries::{get_all_function_bodies, get_all_function_calls};
use cairo_lang_defs::ids::{
    FreeFunctionLongId, FunctionTitleId, FunctionWithBodyId, ImplFunctionLongId, ModuleItemId,
    TraitFunctionLongId,
};
use cairo_lang_defs::plugin::PluginDiagnostic;
use cairo_lang_diagnostics::Severity;
use cairo_lang_semantic::db::SemanticGroup;
use cairo_lang_semantic::expr::compute::Environment;
use cairo_lang_semantic::expr::inference::InferenceId;
use cairo_lang_semantic::items::function_with_body::{
    function_with_body_signature, SemanticExprLookup,
};
use cairo_lang_semantic::resolve::Resolver;
use cairo_lang_semantic::types::peel_snapshots;
use cairo_lang_semantic::ExprFunctionCall;
use cairo_lang_syntax::node::kind::SyntaxKind;
use cairo_lang_syntax::node::{ast, SyntaxNode, TypedStablePtr, TypedSyntaxNode};
use cairo_lang_utils::Intern;
use itertools::Itertools;

const T_COPY_CLONE: &str = "core::clone::TCopyClone";

pub struct CloneOnCopy;

/// ## What it does
///
/// Checks for usage of `.clone()` on a `Copy` type.
///
/// ## Example
///
/// ```cairo
///     let a: felt252 = 'Hello';
///     let b = a.clone()
/// ```
impl Lint for CloneOnCopy {
    fn allowed_name(&self) -> &'static str {
        "clone_on_copy"
    }

    fn diagnostic_message(&self) -> &'static str {
        "using `clone` on type which implements `Copy` trait"
    }

    fn kind(&self) -> CairoLintKind {
        CairoLintKind::CloneOnCopy
    }

    fn has_fixer(&self) -> bool {
        true
    }

    fn fix(&self, db: &dyn SemanticGroup, node: SyntaxNode) -> Option<(SyntaxNode, String)> {
        fix_clone_on_copy(db, node)
    }
}

pub fn check_clone_on_copy(
    db: &dyn SemanticGroup,
    item: &ModuleItemId,
    diagnostics: &mut Vec<PluginDiagnostic>,
) {
    let function_bodies = get_all_function_bodies(db, item);
    for function_body in function_bodies.iter() {
        let function_call_exprs = get_all_function_calls(function_body);
        for function_call_expr in function_call_exprs {
            check_clone_usage(db, &function_call_expr, diagnostics);
        }
    }
}

fn check_clone_usage(
    db: &dyn SemanticGroup,
    expr: &ExprFunctionCall,
    diagnostics: &mut Vec<PluginDiagnostic>,
) {
    let function_name = expr.function.full_path(db).split("::").take(3).join("::");

    if function_name == T_COPY_CLONE {
        diagnostics.push(PluginDiagnostic {
            stable_ptr: expr.stable_ptr.untyped(),
            message: CloneOnCopy.diagnostic_message().to_string(),
            severity: Severity::Warning,
        });
    }
}

fn fix_clone_on_copy(db: &dyn SemanticGroup, node: SyntaxNode) -> Option<(SyntaxNode, String)> {
    let expr_binary = match node.kind(db.upcast()) {
        SyntaxKind::ExprBinary => ast::ExprBinary::from_syntax_node(db.upcast(), node),
        _ => {
            return None;
        }
    };
    let module_file_id = helper::find_module_file_containing_node(db, &node)?;

    let expr = expr_binary.lhs(db.upcast());
    // let mut is_snapshot = false

    let ty = node.ancestors_with_self(db.upcast()).find_map(|node| {
        if let Some(trait_item_func) = ast::TraitItemFunction::cast(db.upcast(), node) {
            let trait_fn_id = FunctionWithBodyId::Trait(
                TraitFunctionLongId(module_file_id, trait_item_func.stable_ptr(db.upcast()))
                    .intern(db),
            );

            return db
                .lookup_expr_by_ptr(trait_fn_id, expr.stable_ptr(db.upcast()))
                .ok()
                .map(|r| db.expr_semantic(trait_fn_id, r).ty());
        }

        if let Some(func_with_body) = ast::FunctionWithBody::cast(db.upcast(), node) {
            if let Some(_func) = node.ancestor_of_kind(db.upcast(), SyntaxKind::ItemImpl) {
                let function_id = FunctionWithBodyId::Impl(
                    ImplFunctionLongId(module_file_id, func_with_body.stable_ptr(db.upcast()))
                        .intern(db),
                );

                return db
                    .lookup_expr_by_ptr(function_id, expr.stable_ptr(db.upcast()))
                    .ok()
                    .map(|r| db.expr_semantic(function_id, r).ty());
            } else {
                let function_id = FunctionWithBodyId::Free(
                    FreeFunctionLongId(module_file_id, func_with_body.stable_ptr(db.upcast()))
                        .intern(db),
                );

                // db.function_body(function_id).ok()?.arenas.ptterns.iter();

                let params = func_with_body
                    .declaration(db.upcast())
                    .signature(db.upcast())
                    .parameters(db.upcast())
                    .elements(db.upcast());

                let mut environment = Environment::empty();

                let (title_id, _free_function_id) = match function_id {
                    FunctionWithBodyId::Free(free_function_id) => (
                        Some(FunctionTitleId::Free(free_function_id)),
                        Some(free_function_id),
                    ),
                    _ => (None, None),
                };

                for param in params {
                    println!("PARAM = {:?}", param.as_syntax_node().get_text(db.upcast()));
                    for parameter in function_with_body_signature(db, function_id)
                        .unwrap()
                        .params
                    {
                        let _ = environment.add_param(
                            db,
                            &mut Default::default(),
                            parameter,
                            &param,
                            title_id,
                        );
                    }
                }

                println!("{:?}", environment);
                // let diagnostics = Default::default();
                // let mut diagnostics_builder = DiagnosticsBuilder::default();

                let mut _resolver = Resolver::new(db, module_file_id, InferenceId::NoContext);

                // let generic_function = GenericFunctionId::Free(free_function_id.unwrap());

                // let func_id = resolver.specialize_function(
                //     &mut diagnostics_builder,
                //     func_with_body
                //         .name(db.upcast())
                //         .token(db.upcast())
                //         .stable_ptr(db.upcast())
                //         .untyped(),
                //     generic_function,
                // );

                // let signature = function_with_body_signature(db, function_id).ok()?;

                // let mut ctx = ComputationContext::new(
                //     db,
                //     &mut diagnostics_builder,
                //     resolver,
                //     Some(&signature),
                //     environment,
                //     ContextFunction::Global,
                // );

                // let expr_and_id = compute_expr_semantic(&mut ctx, &expr);
                // let (n, _) = peel_snapshots(db, expr_and_id.ty());
                // println!("{n}");
                // if n > 0 {
                //     is_snapshot = true;
                // }

                // println!("EXPR = {:?}", expr_and_id);
                // println!("{:?}", diagnostics_builder);
                // // if let Variable(id) = item {}

                db.lookup_expr_by_ptr(function_id, expr.stable_ptr(db.upcast()))
                    .ok()
                    .map(|r| db.expr_semantic(function_id, r).ty());
            }
        }

        None
    });
    match ty {
        Some(valid_ty) => {
            let (n, _) = peel_snapshots(db, valid_ty);

            // if !is_snapshot {
            //     n -= 1;
            // }

            let fixed_expr = format!(
                "{}{}",
                "*".repeat(n),
                expr.as_syntax_node().get_text(db.upcast())
            );
            Some((node, fixed_expr))
        }
        _ => None,
    }
}
