use std::marker::PhantomData;

use chumsky::{input::ValueInput, prelude::*};

use crate::{
    ast::SExpr,
    ast::{
        ArgDef, DefaultToDef, Define, FuncDef, FuncKind, FuncSignature, Keyword, Literal, MapDef,
        Op, TupleDef, Type, self,
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

    /// Parses a single argument in the format (arg ty)
    pub fn arg() -> impl Parser<'a, I, ArgDef, extra::Err<Rich<'a, Token, Span>>> + Clone {
        Parse::ident()
            .then(Parse::ty())
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(name, ty)| {
                eprintln!("func_typedef: {name}->{ty:?}");
                ArgDef { name, ty }
            })
    }

    /// Parses multiple arguments in the format `(arg1 ty1) (arg2 ty2) ...`,
    /// at least `at_least` times and optionally at most `at_most` times.
    pub fn args(at_least: usize, at_most: Option<usize>) -> impl Parser<'a, I, Vec<ArgDef>, extra::Err<Rich<'a, Token, Span>>> + Clone {
        let mut parser = Parse::ident()
            .then(Parse::ty())
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(name, ty)| {
                eprintln!("func_typedef: {name}->{ty:?}");
                ArgDef { name, ty }
            })
            .separated_by(just(Token::Whitespace))
            .at_least(at_least);

        if let Some(max) = at_most {
            parser = parser.at_most(max)
        }

        parser.collect::<Vec<_>>()
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

    /// Explicit tuple definitions: (tuple (key0 expr0) (key1 expr1) ...)
    fn tuple_explicit() -> impl Parser<'a, I, SExpr, extra::Err<Rich<'a, Token, Span>>> + Clone {
        just(Token::OpTuple)
            .ignore_then(Self::ident())
            .then(Self::args(2, Some(2)))
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(name, args)| {
                eprintln!("tuple_def: {{ name: {name}, args: {args:?} }}");
                SExpr::Define(Define::Tuple(TupleDef { name, args }))
            })
    }

    /// Parses implicit tuple definitions: { x: int, y: uint }
    fn tuple_implicit() -> impl Parser<'a, I, SExpr, extra::Err<Rich<'a, Token, Span>>> + Clone {
        Self::ident()
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
            })
    }

    /// Parses tuple definitions.
    pub fn tuple() -> impl Parser<'a, I, SExpr, extra::Err<Rich<'a, Token, Span>>> + Clone {
        Self::tuple_explicit()
            .or(Self::tuple_implicit())
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

        default_to
            .or(map_get)
            .or(map_set)
            .or(ok_err)
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
    use crate::lexer::Token;
    use crate::parser::*;
    use ariadne::{Report, ReportKind, Label, Color};
    use chumsky::input::{SpannedInput, Stream};
    use logos::*;

    #[test]
    fn ident_single_token() {
        let src = "hello";
        
        let token_stream = src.lex();
        let result = Parse::ident().parse(token_stream);
        
        assert!(!result.has_errors());
        assert_eq!(result.into_output(), Some(src.to_string()));
    }

    #[test]
    fn tuple_explicit_def() {
        let src = r#"(tuple (name "blockstack") (id 1337))"#;

        let result = Parse::tuple_explicit().parse(src.lex());
        result.report(src);
        eprintln!("result: {result:?}");
    }

    // *************************************************************************
    // CONVENIENCE HELPERS BELOW
    // *************************************************************************

    type LexedInput = SpannedInput<
        Token, 
        SimpleSpan, 
        Stream<std::vec::IntoIter<(Token, chumsky::span::SimpleSpan)>>
    >;

    trait TestParseResult {
        fn report(&self, src: &str);
    }

    impl TestParseResult for ParseResult<SExpr, Rich<'_, Token>> {
        fn report(&self, src: &str) {
            if let Err(errs) = self.clone().into_result() {
                    for err in errs {
                        Report::build(ReportKind::Error, (), err.span().start)
                            .with_code(3)
                            .with_message(err.to_string())
                            .with_label(
                                Label::new(err.span().into_range())
                                    .with_message(err.reason().to_string())
                                    .with_color(Color::Red),
                            )
                            .finish()
                            .print(ariadne::Source::from(src))
                            .unwrap();
                    }
                    panic!("parsing failed")
            }
        }
    }

    trait Lex {
        fn lex(&self) -> LexedInput;
    }

    impl Lex for &str {
        fn lex(&self) -> LexedInput {
            lex(self)
        }
    }

    impl Lex for String {
        fn lex(&self) -> LexedInput {
            lex(self)
        }
    }

    fn lex(src: &str) -> LexedInput
    {
        let token_iter = Token::lexer(src)
            .spanned()
            .map(|(tok, span)| match tok {
                Ok(tok) => (
                    tok,
                    <std::ops::Range<usize> as Into<SimpleSpan>>::into(span),
                ),
                Err(_) => (Token::Error, span.into()),
            })
            .collect::<Vec<_>>();

        // Define 'end of input' span for optimized usage
        let src_len = src.len();
        let zero_width_span_at_end = (src_len..src_len).into();

        let stream = Stream::from_iter(token_iter)
            // Tell chumsky to split the (Token, SimpleSpan) stream into its parts so that it can handle the spans for us
            // This involves giving chumsky an 'end of input' span: we just use a zero-width span at the end of the string
            .spanned(zero_width_span_at_end);

        stream
    }
}
