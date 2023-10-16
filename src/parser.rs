use chumsky::{input::ValueInput, prelude::*};

use crate::{
    ast::SExpr, 
    lexer::Token, ast::{Literal, Define, Type, MapDef, FuncArg, FuncSignature, Op, DefaultToDef}, types::FunctionKind
};

pub type Span = SimpleSpan<usize>;
//pub type Spanned<T> = (T, Span);

pub fn literal_parser<'a, I>() -> impl Parser<'a, I, Literal, extra::Err<Rich<'a, Token, Span>>> + Clone
where
    I: ValueInput<'a, Token = Token, Span = SimpleSpan>
{
    select! {
        Token::LiteralAsciiString(str) => Literal::AsciiString(str),
        Token::LiteralUtf8String(str) => Literal::Utf8String(str),
        Token::LiteralInteger(int) => Literal::Integer(int)
    }
}

/// Parser for expressions
fn expr_parser<'a, I>() -> 
impl Parser<'a, I, SExpr, extra::Err<Rich<'a, Token>>> + Clone
where
    I: ValueInput<'a, Token = Token, Span = SimpleSpan>
{
    recursive(|expr| {

        let default_to = just(Token::OpDefaultTo)
            .ignore_then(literal_parser())
            .then(expr)
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(default, tail)| {
                eprintln!("default-to: {{ default: {default:?}, tail: {tail:?} }}");
                SExpr::Op(Op::DefaultTo(DefaultToDef {
                    default, tail: Box::new(tail)
                }))
            });

        let map_get = just(Token::OpMapGetOpt)
            .ignore_then(ident_parser())
            .then(ident_parser())
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(map, key)| {
                eprintln!("map-get?: {{ map: {map:?}, key: {key:?} }}");
                SExpr::Op(Op::MapGet)
            });

        default_to
            .or(map_get)
    })
}

/// Parser for parsing identifiers.
pub fn ident_parser<'tokens, 'src: 'tokens, I>() -> 
impl Parser<'tokens, I, String, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where 
    I: ValueInput<'tokens, Token = Token, Span = SimpleSpan>
{
    select! { Token::Identifier(ident) => ident }
        .labelled("identifier")
}

pub fn top_level_parser<'tokens, 'src: 'tokens, I>() -> 
impl Parser<'tokens, I, Vec<SExpr>, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where 
    I: ValueInput<'tokens, Token = Token, Span = SimpleSpan>
{
    let ident = select! { 
        Token::Identifier(ident) => ident 
    }.labelled("identifier");

    let ty = select! {
        Token::Int => Type::Int,
        Token::UInt => Type::UInt,
        Token::Principal => Type::Principal
    }.labelled("type");

    let func_visibility = select! {
        Token::OpDefinePublic => FunctionKind::Public,
        Token::OpDefinePrivate => FunctionKind::Private,
        Token::OpDefineReadOnly => FunctionKind::ReadOnly
    }.labelled("function definition");

    // Parses a single function argument in the format `(<name> <type>)`.
    let func_typedef = ident
        .then(ty)
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|(name, ty)| {
            eprintln!("func_typedef: {name}->{ty:?}");
            FuncArg { name, ty }
        });

    // Parses a function's signature in the format `(<name> (arg1 ty1) (arg2 ty2) ...)`.
    let func_signature = ident
        .then(func_typedef.repeated().collect::<Vec<_>>())
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|(name, args)| {
            eprintln!("func_signature: {name}->{args:?}");
            FuncSignature { name, args }
        });

    let define_fn = func_visibility
        .then(func_signature)
        .then(expr_parser())
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|(kind, sig)| {
            eprintln!("define_fn: {kind:?}->{sig:?}");
            todo!()
        });

    // Parses `define-map` syntax.
    let define_map = just(Token::OpDefineMap) 
        .ignore_then(ident)
        .then(ty.labelled("key-type"))
        .then(ty.labelled("value-type"))
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|((name, key_ty), val_ty)| {
            eprintln!("define-map {} {:?} {:?}", name, key_ty, val_ty);
            SExpr::Define(Define::Map(MapDef { name, key_ty, val_ty }))
        });

    define_map
        .or(define_fn)
        .repeated()
        .collect::<Vec<_>>()
}