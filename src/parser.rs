use std::marker::PhantomData;

use anyhow::bail;
use chumsky::{input::ValueInput, prelude::*, primitive::Just};

use crate::{
    ast::SExpr,
    ast::{
        DefaultToDef, Define, FuncArg, FuncDef, FuncKind, FuncSignature, Literal, MapDef, Op, Type, Keyword,
    },
    lexer::Token,
};

pub type Span = SimpleSpan<usize>;
//pub type Spanned<T> = (T, Span);

struct Parsers<'a, I, O, E = extra::Err<Rich<'a, Token>>>
where
    I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
    _phantom_input: &'a PhantomData<I>,
    _phantom_output: O,
    _phantom_extra: E,
}

impl<'a, I: ValueInput<'a, Token = Token, Span = SimpleSpan>> Parsers<'a, I, String> {
    pub fn ident() -> impl Parser<'a, I, String, extra::Err<Rich<'a, Token>>> + Clone {
        select! { Token::Identifier(ident) => ident }.labelled("identifier")
    }

    pub fn literal() -> impl Parser<'a, I, SExpr, extra::Err<Rich<'a, Token, Span>>> + Clone
    where
        I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
    {
        select! {
            Token::LiteralAsciiString(str) => SExpr::Literal(Literal::AsciiString(str)),
            Token::LiteralUtf8String(str) => SExpr::Literal(Literal::Utf8String(str)),
            Token::LiteralInteger(int) => SExpr::Literal(Literal::Integer(int))
        }
        .labelled("literal")
    }

    pub fn keyword() -> impl Parser<'a, I, SExpr, extra::Err<Rich<'a, Token, Span>>> + Clone {
        select! {
            Token::BlockHeight => SExpr::Keyword(Keyword::BlockHeight),
            Token::BurnBlockHeight => SExpr::Keyword(Keyword::BurnBlockHeight),
            Token::ChainId => SExpr::Keyword(Keyword::ChainId),
            Token::ContractCaller => SExpr::Keyword(Keyword::ContractCaller),
            Token::False => SExpr::Keyword(Keyword::False),
            Token::IsInMainnet => SExpr::Keyword(Keyword::IsInMainnet),
            Token::IsInRegTest => SExpr::Keyword(Keyword::IsInRegTest),
            Token::None => SExpr::Keyword(Keyword::None),
            Token::StxLiquidSupply => SExpr::Keyword(Keyword::StxLiquidSupply),
            Token::True => SExpr::Keyword(Keyword::True),
            Token::TxSender => SExpr::Keyword(Keyword::TxSender),
            Token::TxSponsorOpt => SExpr::Keyword(Keyword::TxSponsor),
        }
    }
}

/// Parser for expressions
fn expr_parser<'a, I>() -> impl Parser<'a, I, SExpr, extra::Err<Rich<'a, Token>>> + Clone
where
    I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
    recursive(|expr| {
        let default_to = just(Token::OpDefaultTo)
            .ignore_then(Parsers::literal())
            .then(expr.clone())
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(default, tail)| {
                eprintln!("default-to: {{ default: {default:?}, tail: {tail:?} }}");
                SExpr::Op(Op::DefaultTo(DefaultToDef {
                    default: Box::new(default),
                    tail: Box::new(tail),
                }))
            });

        let map_get = just(Token::OpMapGetOpt)
            .ignore_then(ident_parser())
            .then(Parsers::ident())
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(map, key)| {
                eprintln!("map-get?: {{ map: {map:?}, key: {key:?} }}");
                SExpr::Op(Op::MapGet)
            });

        let map_set = just(Token::OpMapSet)
            .ignore_then(Parsers::ident())
            .then(Parsers::literal().or(Parsers::keyword().or(expr.clone())))
            .then(Parsers::literal().or(Parsers::keyword().or(expr.clone())))
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(map, key)| {
                eprintln!("map-get?: {{ map: {map:?}, key: {key:?} }}");
                SExpr::Op(Op::MapSet)
            });

        let ok_err = one_of([Token::OpOk, Token::OpErr])
            .then(expr.clone())
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(token, tail)| {
                let tail = Box::new(tail);
                match token {
                    Token::OpOk => SExpr::Op(Op::Ok(tail)),
                    Token::OpErr => SExpr::Op(Op::Err(tail)),
                    _ => unimplemented!(
                        "bug: token '{token:?}' is not supported by this matching pattern."
                    ),
                }
            });

        default_to.or(map_get).or(map_set).or(ok_err)
    })
}

/// Parser for parsing identifiers.
pub fn ident_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, String, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = SimpleSpan>,
{
    select! { Token::Identifier(ident) => ident }.labelled("identifier")
}

/// Parser for a Clarity contract's top-level functions.
pub fn top_level_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Vec<SExpr>, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = SimpleSpan>,
{
    /*let ident = select! {
        Token::Identifier(ident) => ident
    }
    .labelled("identifier");*/

    let ty = select! {
        Token::Int => Type::Int,
        Token::UInt => Type::UInt,
        Token::Principal => Type::Principal
    }
    .labelled("type");

    // Parses define-(public|private|readonly) operations and returns the
    // associated [`FuncKind`].
    let func_visibility = select! {
        Token::OpDefinePublic => FuncKind::Public,
        Token::OpDefinePrivate => FuncKind::Private,
        Token::OpDefineReadOnly => FuncKind::ReadOnly
    }
    .labelled("function definition");

    // Parses a single function argument in the format `(<name> <type>)`.
    // This parser is a helper parser for the `define_fn` parser below.
    let func_typedef = ident_parser()
        .then(ty)
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|(name, ty)| {
            eprintln!("func_typedef: {name}->{ty:?}");
            FuncArg { name, ty }
        });

    // Parses a function's signature in the format `(<name> (arg1 ty1) (arg2 ty2) ...)`.
    // This parser is a helper parser for the `define_fn` parser below.
    let func_signature = ident_parser()
        .then(func_typedef.repeated().collect::<Vec<_>>())
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|(name, args)| {
            eprintln!("func_signature: {name}->{args:?}");
            FuncSignature { name, args }
        });

    // Parses function definitions (public, private, readonly).
    let define_fn = func_visibility
        .then(func_signature)
        .then(expr_parser())
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|((kind, sig), body)| {
            eprintln!("define_fn:\nkind: {kind:?}\nsignature: {sig:?}\nbody: {body:?}\n");
            let func_def = Box::new(FuncDef {
                signature: sig,
                body,
            });
            match kind {
                FuncKind::Private => SExpr::Define(Define::PrivateFunction(func_def)),
                FuncKind::Public => SExpr::Define(Define::PublicFunction(func_def)),
                FuncKind::ReadOnly => SExpr::Define(Define::ReadOnlyFunction(func_def)),
            }
        });

    // Parses `define-map` syntax.
    let define_map = just(Token::OpDefineMap)
        .ignore_then(ident_parser())
        .then(ty.labelled("key-type"))
        .then(ty.labelled("value-type"))
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|((name, key_ty), val_ty)| {
            eprintln!("define-map {} {:?} {:?}", name, key_ty, val_ty);
            SExpr::Define(Define::Map(MapDef {
                name,
                key_ty,
                val_ty,
            }))
        });

    define_map.or(define_fn).repeated().collect::<Vec<_>>()
}
