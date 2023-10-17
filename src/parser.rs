use std::marker::PhantomData;

use chumsky::{input::ValueInput, prelude::*};

use crate::{
    ast::SExpr,
    ast::{
        ArgDef, DefaultToDef, Define, FuncDef, FuncKind, FuncSignature, Keyword, Literal, MapDef,
        Op, TupleDef, Type,
    },
    lexer::Token,
};

pub type Span = SimpleSpan<usize>;
//pub type Spanned<T> = (T, Span);

/// Struct whose impl holds generic parser implementations.
struct Parse<'a, I, O, E = extra::Err<Rich<'a, Token>>>
where
    I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
    _phantom_input: &'a PhantomData<I>,
    _phantom_output: O,
    _phantom_extra: E,
}

impl<'a, I: ValueInput<'a, Token = Token, Span = SimpleSpan>> Parse<'a, I, String> {
    /// Parses identifier tokens to expressions.
    pub fn ident() -> impl Parser<'a, I, String, extra::Err<Rich<'a, Token>>> + Clone {
        select! { Token::Identifier(ident) => ident }.labelled("identifier")
    }

    /// Parses literal tokens to expressions.
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

    /// Parses keyword tokens to expressions.
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

    pub fn arg() -> impl Parser<'a, I, ArgDef, extra::Err<Rich<'a, Token, Span>>> + Clone {
        Parse::ident()
            .then(Parse::ty())
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(name, ty)| {
                eprintln!("func_typedef: {name}->{ty:?}");
                ArgDef { name, ty }
            })
    }

    /// Parses type definitions.
    pub fn ty() -> impl Parser<'a, I, SExpr, extra::Err<Rich<'a, Token, Span>>> + Clone {
        select! {
            Token::Int => SExpr::TypeDef(Type::Int),
            Token::UInt => SExpr::TypeDef(Type::UInt),
            Token::Principal => SExpr::TypeDef(Type::Principal)
        }
        .labelled("type")
    }

    pub fn tuple() -> impl Parser<'a, I, SExpr, extra::Err<Rich<'a, Token, Span>>> + Clone {
        let explicit_def = just(Token::OpTuple)
            .ignore_then(Self::ident())
            .then(Self::arg().repeated().at_least(1).collect::<Vec<_>>())
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(name, args)| {
                eprintln!("tuple_def: {{ name: {name}, args: {args:?} }}");
                SExpr::Define(Define::Tuple(TupleDef { name, args }))
            });

        let implicit_def = Self::ident()
            .then(
                Self::ident()
                    .then(just(Token::Colon).ignored())
                    .then(Self::ty())
                    .map(|((name, _), ty)| ArgDef { name, ty })
                    .separated_by(just(Token::Comma))
                    .at_least(1)
                    .collect::<Vec<_>>(),
            )
            .map(|(name, args)| {
                eprintln!("tuple_def: {{ name: {name}, args: {args:?} }}");
                SExpr::Define(Define::Tuple(TupleDef { name, args }))
            });

        explicit_def.or(implicit_def)
    }
}

/// Parser for expressions
fn expr_parser<'a, I>() -> impl Parser<'a, I, SExpr, extra::Err<Rich<'a, Token>>> + Clone
where
    I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
    recursive(|expr| {
        // default-to: (default-to default-value option-value)
        let default_to = just(Token::OpDefaultTo)
            .ignore_then(Parse::literal())
            .then(expr.clone())
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(default, tail)| {
                eprintln!("default-to: {{ default: {default:?}, tail: {tail:?} }}");
                SExpr::Op(Op::DefaultTo(DefaultToDef {
                    default: Box::new(default),
                    tail: Box::new(tail),
                }))
            });

        // map-get: (map-get? map-name key-tuple)
        let map_get = just(Token::OpMapGetOpt)
            .ignore_then(Parse::ident())
            .then(Parse::ident())
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(map, key)| {
                eprintln!("map-get?: {{ map: {map:?}, key: {key:?} }}");
                SExpr::Op(Op::MapGet)
            });

        // map-set: (map-set map-name key-tuple value-tuple)
        let map_set = just(Token::OpMapSet)
            .ignore_then(Parse::ident())
            .then(Parse::literal().or(Parse::keyword().or(expr.clone())))
            .then(Parse::literal().or(Parse::keyword().or(expr.clone())))
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|((map, key), value)| {
                eprintln!("map-set?: {{ map: {map:?}, key: {key:?}, value: {value:?} }}");
                SExpr::Op(Op::MapSet)
            });

        // ok: (ok value)
        // err: (err value)
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

/// Parser for a Clarity contract's top-level functions.
pub fn top_level_parser<'tokens, I>(
) -> impl Parser<'tokens, I, Vec<SExpr>, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = SimpleSpan>,
{
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
    let func_typedef = Parse::ident()
        .then(Parse::ty())
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|(name, ty)| {
            eprintln!("func_typedef: {name}->{ty:?}");
            ArgDef { name, ty }
        });

    // Parses a function's signature in the format `(<name> (arg1 ty1) (arg2 ty2) ...)`.
    // This parser is a helper parser for the `define_fn` parser below.
    let func_signature = Parse::ident()
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

            // Create the function definition.
            let func_def = Box::new(FuncDef {
                signature: sig,
                body,
            });

            // Return the correct `Define` variant for the function depending on
            // its stated visibility.
            match kind {
                FuncKind::Private => SExpr::Define(Define::PrivateFunction(func_def)),
                FuncKind::Public => SExpr::Define(Define::PublicFunction(func_def)),
                FuncKind::ReadOnly => SExpr::Define(Define::ReadOnlyFunction(func_def)),
            }
        })
        .labelled("function definition");

    // Parses `define-map` syntax.
    let define_map = just(Token::OpDefineMap)
        .ignore_then(Parse::ident())
        .then(Parse::ty().labelled("key-type"))
        .then(Parse::ty().labelled("value-type"))
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|((name, key_ty), val_ty)| {
            eprintln!("define-map {} {:?} {:?}", name, key_ty, val_ty);
            SExpr::Define(Define::Map(MapDef {
                name,
                key_ty: Box::new(key_ty),
                val_ty: Box::new(val_ty),
            }))
        })
        .labelled("map definition");

    define_map.or(define_fn).repeated().collect::<Vec<_>>()
}

#[cfg(test)]
mod test {
    use std::ops::Range;

    use super::Span;
    use crate::lexer::Token;
    use crate::parser::*;
    use anyhow::{anyhow, bail, Result};
    use chumsky::{
        combinator::{IntoIter, Map},
        input::{SpannedInput, Stream},
        prelude::*,
    };
    use internal::LexerInternal;
    use logos::*;

    #[test]
    fn my_test() {
        let src = "hello";
        // Create a logos lexer over the source code
        let token_iter: Vec<_> = Token::lexer(src)
            .spanned()
            // Convert logos errors into tokens. We want parsing to be recoverable and not fail at the lexing stage, so
            // we have a dedicated `Token::Error` variant that represents a token error that was previously encountered
            .map(|(tok, span)| match tok {
                // Turn the `Range<usize>` spans logos gives us into chumsky's `SimpleSpan` via `Into`, because it's easier
                // to work with
                Ok(tok) => (
                    tok,
                    <std::ops::Range<usize> as Into<SimpleSpan>>::into(span),
                ),
                Err(_) => (Token::Error, span.into()),
            })
            .collect();

        let token_stream = Stream::from_iter(token_iter)
            // Tell chumsky to split the (Token, SimpleSpan) stream into its parts so that it can handle the spans for us
            // This involves giving chumsky an 'end of input' span: we just use a zero-width span at the end of the string
            .spanned((src.len()..src.len()).into());

        Parse::arg().parse(token_stream);
    }

    #[test]
    fn my_test2() {
        let src = "hello";

        // Generate Error token and parsing for recoverability
        let token_iter: Vec<_> = Token::lexer(src)
            .spanned()
            .map(|(tok, span)| match tok {
                Ok(tok) => (
                    tok,
                    <std::ops::Range<usize> as Into<SimpleSpan>>::into(span),
                ),
                Err(_) => (Token::Error, span.into()),
            })
            .collect();

        // Define 'end of input' span for optimized usage
        let src_len = src.len();
        let zero_width_span_at_end = (src_len..src_len).into();

        // Let chumsky handle the spans
        let token_stream = Stream::from_iter(token_iter).spanned(zero_width_span_at_end);

        Parse::arg().parse(token_stream);
    }

    impl<'a, I: ValueInput<'a, Token = Token, Span = SimpleSpan> + Clone> Parse<'a, I, String> {
        fn for_test<O>(input: I, parser: impl Parser<'a, I, O>) -> Result<O> {
            let tmp = Parse::arg().parse(input.clone());
            let tmp2 = parser.parse(input.clone());
            todo!()
        }
    }
}
