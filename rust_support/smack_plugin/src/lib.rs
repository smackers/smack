#![crate_type="dylib"]
#![feature(quote, plugin_registrar, rustc_private)]

extern crate syntax;
extern crate rustc;
//extern crate rustc_plugin;

use syntax::parse::token;
use syntax::ast::{TokenTree, Expr};
use syntax::ext::base::{ExtCtxt, MacResult, DummyResult, MacEager};
use syntax::ext::build::AstBuilder;  // trait for expr_usize
use syntax::ext::quote::rt::Span;
use rustc::plugin::Registry;
use syntax::util::small_vector::SmallVector;
use syntax::ptr::P;
use syntax::ast::Ident;
use syntax::parse::token::gensym_ident;
use syntax::codemap;

fn expand_assert(cx: &mut ExtCtxt, sp: Span, args: &[TokenTree])
        -> Box<MacResult + 'static> {
    if args.len() == 0 {
        cx.span_err(
            sp,
            &format!("assert! requires one expression"));
    }
    let mut parser = cx.new_parser_from_tts(args);
    let parsed: P<Expr> = parser.parse_expr();

    let new_expr = quote_stmt!(cx, unsafe{__VERIFIER_assert($parsed)});
    let rval = quote_expr!(cx, 0);

    let result = cx.block_all(sp, vec!(new_expr.unwrap()), Some(rval));
    MacEager::expr(cx.expr_block(result))
}

fn expand_assume(cx: &mut ExtCtxt, sp: Span, args: &[TokenTree])
        -> Box<MacResult + 'static> {
    if args.len() == 0 {
        cx.span_err(
            sp,
            &format!("assume! requires one expression"));
    }
    let mut parser = cx.new_parser_from_tts(args);
    let parsed: P<Expr> = parser.parse_expr();

    let new_expr = quote_stmt!(cx, unsafe{__VERIFIER_assume($parsed)});
    let rval = quote_expr!(cx, 0);

    let result = cx.block_all(sp, vec!(new_expr.unwrap()), Some(rval));
    MacEager::expr(cx.expr_block(result))
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("assert", expand_assert);
    reg.register_macro("assume", expand_assume);
}
