mod bitwise_for_parity_check;
mod bool_comparison;
mod breaks;
mod clone_on_copy;
mod double_comparison;
mod double_parens;
mod duplicate_underscore_args;
mod empty_enum_brackets_variant;
mod enum_variant_names;
mod eq_op;
mod erasing_operations;
mod helpers;
mod ifs;
mod int_operations;
mod loops;
mod manual;
mod panic;
mod performance;
mod redundant_brackets_in_enum_call;
mod redundant_op;
mod single_match;
mod unused_imports;
mod unused_variables;

pub const CRATE_CONFIG: &str = r#"
edition = "2024_07"

[experimental_features]
negative_impls = true
coupons = true
associated_item_constraints = true
"#;
