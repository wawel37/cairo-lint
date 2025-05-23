use crate::{
    context::{CairoLintKind, Lint},
    queries::get_all_function_bodies,
};
use cairo_lang_defs::{ids::ModuleItemId, plugin::PluginDiagnostic};
use cairo_lang_diagnostics::Severity;
use cairo_lang_semantic::{db::SemanticGroup, Expr};
use cairo_lang_syntax::node::{ast, db::SyntaxGroup, SyntaxNode, TypedStablePtr, TypedSyntaxNode};
use if_chain::if_chain;

pub struct RedundantBracketsInEnumCall;

/// ## What it does
///
/// Detects calls to enum variant constructors with redundant parentheses
///
/// ## Example
///
/// ```cairo
/// enum MyEnum {
///     Data: u8,
///     Empty,
/// }
///
/// fn main() {
///     let a = MyEnum::Empty(()); // redundant parentheses
/// }
/// ```
///
/// Can be simplified to:
///
/// ```cairo
/// enum MyEnum {
///     Data: u8,
///     Empty,
/// }
///
/// fn main() {
///     let a = MyEnum::Empty;
/// }
/// ```
impl Lint for RedundantBracketsInEnumCall {
    fn allowed_name(&self) -> &'static str {
        "redundant_brackets_in_enum_call"
    }

    fn diagnostic_message(&self) -> &'static str {
        "redundant parentheses in enum call"
    }

    fn kind(&self) -> CairoLintKind {
        CairoLintKind::EnumEmptyVariantBrackets
    }

    fn has_fixer(&self) -> bool {
        true
    }

    fn fix(&self, db: &dyn SemanticGroup, node: SyntaxNode) -> Option<(SyntaxNode, String)> {
        fix_redundant_brackets_in_enum_call(db.upcast(), node)
    }
}

pub fn check_redundant_brackets_in_enum_call(
    db: &dyn SemanticGroup,
    item: &ModuleItemId,
    diagnostics: &mut Vec<PluginDiagnostic>,
) {
    let function_bodies = get_all_function_bodies(db, item);
    for function_body in function_bodies.iter() {
        for (_, expr) in &function_body.arenas.exprs {
            if is_redundant_enum_brackets_call(expr, db) {
                diagnostics.push(PluginDiagnostic {
                    stable_ptr: expr.stable_ptr().untyped(),
                    message: RedundantBracketsInEnumCall.diagnostic_message().to_string(),
                    severity: Severity::Warning,
                    relative_span: None,
                });
            }
        }
    }
}

fn is_redundant_enum_brackets_call(expr: &Expr, db: &dyn SemanticGroup) -> bool {
    if_chain! {
        // Check if the expression is a constructor call for an enum variant,
        if let Expr::EnumVariantCtor(enum_expr) = expr;

        // Check if the type of the enum variant is of unit type `()`.
        if enum_expr.variant.ty.is_unit(db.upcast());

        let node = enum_expr.stable_ptr.lookup(db.upcast());
        if let ast::Expr::FunctionCall(_) = node;

        then {
            return true;
        }
    }

    false
}

fn fix_redundant_brackets_in_enum_call(
    db: &dyn SyntaxGroup,
    node: SyntaxNode,
) -> Option<(SyntaxNode, String)> {
    let ast_expr = ast::Expr::from_syntax_node(db, node);

    let ast::Expr::FunctionCall(call_expr) = &ast_expr else {
        panic!("Expr should be a FunctionCall");
    };

    // Retrieve parentheses that can be removed
    let arguments = call_expr.arguments(db).as_syntax_node().get_text(db);

    let fixed_expr = ast_expr
        .as_syntax_node()
        .get_text(db)
        .strip_suffix(&arguments)?
        .to_string();

    Some((node, fixed_expr))
}
