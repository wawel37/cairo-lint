use crate::context::{CairoLintKind, Lint};
use crate::helper;
use crate::queries::{get_all_function_bodies, get_all_function_calls};
use cairo_lang_defs::ids::{
    FreeFunctionLongId, FunctionWithBodyId, ImplFunctionLongId, ModuleFileId, ModuleItemId,
    TraitFunctionLongId,
};
use cairo_lang_defs::plugin::PluginDiagnostic;
use cairo_lang_diagnostics::Severity;
use cairo_lang_semantic::db::SemanticGroup;
use cairo_lang_semantic::items::function_with_body::SemanticExprLookup;
use cairo_lang_semantic::types::peel_snapshots;
use cairo_lang_semantic::{Expr, ExprFunctionCall};
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
        // let function_call_exprs = get_all_function_calls_db(function_body, db.upcast());
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
    let ast_expr_binary = ast::ExprBinary::cast(db.upcast(), node)?;
    println!("{:?}", ast_expr_binary.stable_ptr(db.upcast()));
    let module_file_id = helper::find_module_file_containing_node(db, &node)?;

    let ast_expr = ast_expr_binary.lhs(db.upcast());

    // It breaks inside this method
    let expr_semantic = get_expr_semantic(db, module_file_id, &ast_expr)?;

    let (mut snapshot_count, _) = peel_snapshots(db, expr_semantic.ty());

    if let Expr::Snapshot(_) = expr_semantic {
        snapshot_count -= 1;
    };

    let fixed_expr = format!(
        "{}{}",
        "*".repeat(snapshot_count),
        ast_expr.as_syntax_node().get_text(db.upcast())
    );

    Some((node, fixed_expr))
}

fn get_expr_semantic(
    db: &dyn SemanticGroup,
    module_file_id: ModuleFileId,
    ast_expr: &ast::Expr,
) -> Option<Expr> {
    let expr_ptr = ast_expr.stable_ptr(db.upcast());

    ast_expr
        .as_syntax_node()
        .ancestors_with_self(db.upcast())
        .find_map(|ancestor| {
            let function_id = if let Some(trait_func) =
                ast::TraitItemFunction::cast(db.upcast(), ancestor)
            {
                FunctionWithBodyId::Trait(
                    TraitFunctionLongId(module_file_id, trait_func.stable_ptr(db.upcast()))
                        .intern(db),
                )
            } else if let Some(func_with_body) = ast::FunctionWithBody::cast(db.upcast(), ancestor)
            {
                if ancestor
                    .ancestor_of_kind(db.upcast(), SyntaxKind::ItemImpl)
                    .is_some()
                {
                    FunctionWithBodyId::Impl(
                        ImplFunctionLongId(module_file_id, func_with_body.stable_ptr(db.upcast()))
                            .intern(db),
                    )
                } else {
                    FunctionWithBodyId::Free(
                        FreeFunctionLongId(module_file_id, func_with_body.stable_ptr(db.upcast()))
                            .intern(db),
                    )
                }
            } else {
                // println!("{}", ancestor.get_text_without_trivia(db.upcast()));
                return None;
            };

            println!("{:?}", db.lookup_expr_by_ptr(function_id, expr_ptr));

            let body_data = match function_id {
                FunctionWithBodyId::Free(id) => db.priv_free_function_body_data(id).ok()?,
                FunctionWithBodyId::Impl(id) => db.priv_impl_function_body_data(id).ok()?,
                FunctionWithBodyId::Trait(id) => db.priv_trait_function_body_data(id).ok()??,
            };
            println!("{:?}", expr_ptr);
            println!("{:?}", body_data.expr_lookup); //.get(&ptr).copied().to_maybe();

            // It breaks here, while looking for expr, because `(*fun())` is not in the HashMap (`body_data.expr_lookup`).
            // There is whole expression `((*fun()).clone()`, but I need `Expr`, not `ExprBinary`.
            // Probably in semantic there is different form than `(*fun())`
            // Related test: tests/clone_on_copy/mod.rs:525
            db.lookup_expr_by_ptr(function_id, expr_ptr).ok().map(|id| {
                println!("{}", ancestor.get_text_without_trivia(db.upcast()));

                db.expr_semantic(function_id, id)
            })
        })
}
