use std::marker::PhantomData;

use chumsky::{input::ValueInput, prelude::*};

use crate::{
    ast::SExpr,
    ast::{
        ArgDef, DefaultToDef, Define, FuncDef, FuncKind, FuncSignature, Keyword, Literal, MapDef,
        Op, Type
    },
    lexer::Token,
};

// Aliases to help keep the code a little a little more sane.
pub type Span = SimpleSpan<usize>;

macro_rules! returns {
    ($ty:ty) => {
        impl Parser<'a, I, $ty, extra::Err<Rich<'a, Token<'a>, Span>>> + Clone
    };
}

/// Struct whose impl holds general parser implementations.
struct Parse<'a, I, O, E = extra::Err<Rich<'a, Token<'a>>>>
where
    I: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan>,
{
    _phantom_input: &'a PhantomData<I>,
    _phantom_output: O,
    _phantom_extra: E,
}

#[allow(dead_code)]
impl<'a, I: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan>> Parse<'a, I, String> {
    /// Parses identifier tokens to expressions.
    pub fn ident() -> returns!(&'a str) {
        select! { Token::Identifier(ident) => {
                //eprintln!("ident: {ident}");
                ident
            }
        }.labelled("identifier")
    }

    /// Parses literal tokens to expressions.
    pub fn literal() -> impl Parser<'a, I, SExpr<'a>, extra::Err<Rich<'a, Token<'a>, Span>>> + Clone
    where
        I: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan>,
    {
        select! {
            Token::LiteralAsciiString(str) => SExpr::Literal(Literal::AsciiString(str)),
            Token::LiteralUtf8String(str) => SExpr::Literal(Literal::Utf8String(str)),
            Token::LiteralInt(i) => SExpr::Literal(Literal::Int(i)),
            Token::LiteralUInt(i) => SExpr::Literal(Literal::UInt(i)),
            Token::LiteralPrincipal(str) => SExpr::Literal(Literal::Principal(str))
        }
        .labelled("literal")
    }

    /// Parses keyword tokens to expressions.
    pub fn keyword() -> returns!(SExpr<'a>) {
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
        }.labelled("keyword")
    }

    /// Parses a single argument in the format (arg ty)
    pub fn arg() -> returns!(ArgDef<'a>) {
        Parse::ident()
            .then(Parse::ty())
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(name, ty)| {
                //println!("arg(): {name}->{ty:?}");
                ArgDef { name, ty }
            }).labelled("argument")
    }

    /// Parses multiple arguments in the format `(arg1 ty1) (arg2 ty2) ...`,
    /// at least `at_least` times and optionally at most `at_most` times.
    pub fn args(at_least: usize, at_most: Option<usize>) -> returns!(Vec<ArgDef<'a>>) {
        let mut parser = Parse::ident()
            .then(Parse::ty())
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(name, ty)| {
                //eprintln!("args: {name}->{ty:?}");
                ArgDef { name, ty }
            })
            // Using `separated_by(just(Token::Whitespace))` doesn't work here
            // because we've explicitly ignored whitespace in the Logos lexer.
            .repeated()
            .at_least(at_least);

        if let Some(max) = at_most {
            parser = parser.at_most(max)
        }

        parser.collect::<Vec<_>>().labelled("arguments")
    }

    /// Parses type definitions.
    pub fn ty() -> returns!(SExpr<'a>) {
        let simple_types = select! {
            Token::Int => SExpr::TypeDef(Type::Int),
            Token::UInt => SExpr::TypeDef(Type::UInt),
            Token::Principal => SExpr::TypeDef(Type::Principal)
        };

        simple_types
    }

    /// Explicit tuple definitions: (tuple (key0 type0) (key1 type1) ...)
    fn tuple_def_explicit() -> returns!(Vec<ArgDef<'a>>) {
        just(Token::OpTuple)
            .ignore_then(
                Parse::ident()
                    .then(Parse::ty())
                    .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
                    .map(|(name, ty)| {
                        //eprintln!("args: {name}->{ty:?}");
                        ArgDef { name, ty }
                    })
                    // Using `separated_by(just(Token::Whitespace))` doesn't work here
                    // because we've explicitly ignored whitespace in the Logos lexer.
                    .repeated()
                    .collect()
            )
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .labelled("tuple definition")
    }

    /// Parses implicit tuple definitions: { key0: type0, key1: type1 }
    fn tuple_def_implicit() -> returns!(Vec<ArgDef<'a>>) {
        Parse::ident()
            .then(just(Token::Colon).ignored())
            .then(Parse::ty())
            .map(|((name, _), ty)| {
                //eprintln!("arg: {{ name: {name}, type: {ty:?} }}");
                ArgDef { name, ty }
            })
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect()
            .delimited_by(just(Token::BraceOpen), just(Token::BraceClose))
            .labelled("tuple definition")
    }

    /* /// Parses tuple definitions.
    pub fn tuple() -> impl Parser<'a, I, SExpr, extra::Err<Rich<'a, Token, Span>>> + Clone {
        Self::tuple_def_explicit()
            .or(Self::tuple_implicit())
    }*/
}

/// Parser for expressions
fn expr_parser<'a, I>() -> returns!(SExpr<'a>)
where
    I: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan>,
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
pub fn top_level_parser<'a, I>(
) -> returns!(Vec<SExpr<'a>>)
where
    I: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan>,
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
    fn literal_ascii_string() {
        let src = r#"" he l lo worl d!""#;
        
        let result = Parse::literal()
            .parse(src.lex())
            .unwrap_report(src);

        assert_eq!(result, SExpr::Literal(Literal::AsciiString(" he l lo worl d!")));
    }

    #[test]
    fn literal_utf8_string() {
        let src = r#"u" he l lo worl d!""#;
        
        let result = Parse::literal()
            .parse(src.lex())
            .unwrap_report(src);

        assert_eq!(result, SExpr::Literal(Literal::Utf8String(" he l lo worl d!")));
    }

    #[test]
    fn literal_int() {
        let src = "  12345 ";

        let result = Parse::literal()
            .parse(src.lex())
            .unwrap_report(src);

        assert_eq!(result, SExpr::Literal(Literal::Int(12345)));
    }

    #[test]
    fn literal_uint() {
        let src = "  u12345 ";

        let result = Parse::literal()
            .parse(src.lex())
            .unwrap_report(src);

        assert_eq!(result, SExpr::Literal(Literal::UInt(12345)));
    }

    #[test]
    fn ident_single_token() {
        let src = "hello";
        
        let token_stream = src.lex();
        let result = Parse::ident()
            .parse(token_stream)
            .unwrap_report(src);
        
        //assert!(!result.has_errors());
        assert_eq!(result, src.to_string());
    }

    #[test]
    fn arg_parse_unary() {
        let src = "(hello uint)";

        let result = Parse::arg()
            .parse(src.lex())
            .unwrap_report(src);

        assert_eq!("hello", result.name);
        assert_eq!(SExpr::TypeDef(Type::UInt), result.ty);
    }

    #[test]
    fn args_parse_binary() {
        let src = "(hello uint) (world int)";

        let result = Parse::args(2, Some(2))
            .parse(src.lex())
            .unwrap_report(src);

        // first arg
        assert_eq!("hello", result[0].name);
        assert_eq!(SExpr::TypeDef(Type::UInt), result[0].ty);
        // second arg
        assert_eq!("world", result[1].name);
        assert_eq!(SExpr::TypeDef(Type::Int), result[1].ty);
    }

    #[test]
    fn args_parse_variadic() {
        let src = "(hello uint) (world int) (who principal)";

        let result = Parse::args(1, None)
            .parse(src.lex())
            .unwrap_report(src);

        // first arg
        assert_eq!("hello", result[0].name);
        assert_eq!(SExpr::TypeDef(Type::UInt), result[0].ty);
        // second arg
        assert_eq!("world", result[1].name);
        assert_eq!(SExpr::TypeDef(Type::Int), result[1].ty);
        // third arg
        assert_eq!("who", result[2].name);
        assert_eq!(SExpr::TypeDef(Type::Principal), result[2].ty);
    }

    #[test]
    fn tuple_explicit_def_single_entry() {
        let src = r#"(tuple (x int))"#;

        let result = Parse::tuple_def_explicit()
            .parse(src.lex())
            .unwrap_report(src);

        assert_eq!(result.len(), 1);
        assert_eq!(result[0].name, "x");
        assert_eq!(result[0].ty, SExpr::TypeDef(Type::Int));
    }

    #[test]
    fn tuple_explicit_def_multiple_entries() {
        let src = "(tuple (x int) (y uint) (z principal))";

        let result = Parse::tuple_def_explicit()
            .parse(src.lex())
            .unwrap_report(src);

        assert_eq!(result.len(), 3);
        // first entry
        assert_eq!(result[0].name, "x");
        assert_eq!(result[0].ty, SExpr::TypeDef(Type::Int));
        // second entry
        assert_eq!(result[1].name, "y");
        assert_eq!(result[1].ty, SExpr::TypeDef(Type::UInt));
        // third entry
        assert_eq!(result[2].name, "z");
        assert_eq!(result[2].ty, SExpr::TypeDef(Type::Principal));
    }

    #[test]
    fn tuple_implicit_def_single_entry() {
        let src = "{ x: int }"; // parser shouldn't have name since it can't be specified in this format

        let result = Parse::tuple_def_implicit()
            .parse(src.lex())
            .unwrap_report(src);

        assert_eq!(result.len(), 1);
        assert_eq!(result[0].name, "x");
        assert_eq!(result[0].ty, SExpr::TypeDef(Type::Int));
    }

    #[test]
    fn tuple_implicit_def_multiple_entries() {
        let src = "{ x: int, y: uint, z: principal }";

        let result = Parse::tuple_def_implicit()
            .parse(src.lex())
            .unwrap_report(src);

        assert_eq!(result.len(), 3);
        // first entry
        assert_eq!(result[0].name, "x");
        assert_eq!(result[0].ty, SExpr::TypeDef(Type::Int));
        // second entry
        assert_eq!(result[1].name, "y");
        assert_eq!(result[1].ty, SExpr::TypeDef(Type::UInt));
        // third entry
        assert_eq!(result[2].name, "z");
        assert_eq!(result[2].ty, SExpr::TypeDef(Type::Principal));
    }

    // *************************************************************************
    // CONVENIENCE HELPERS BELOW
    // *************************************************************************
    /* #region Test Helpers */

    /// Alias to help keep the code a little cleaner.
    type LexedInput<'a> = SpannedInput<
        Token<'a>, 
        SimpleSpan, 
        Stream<std::vec::IntoIter<(Token<'a>, chumsky::span::SimpleSpan)>>
    >;

    /// Test helper trait which can take a [ParseResult] and print out a report
    /// to the console.
    trait TestParseResult<O> {
        fn unwrap_report(&self, src: &str) -> O;
    }

    /// Implement reporting for the standard [ParseResult]. This will write to
    /// stdio so that it only shows when using `--capture-input` (i.e. not when
    /// running a test batch).
    impl<'a, O> TestParseResult<O> for ParseResult<O, Rich<'_, Token<'a>>> where O: Clone {
        fn unwrap_report(&self, src: &str) -> O {
            let result = self.clone().into_result();
            if let Err(errs) = result {
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
                panic!("parsing failed");
            } else {
                result.unwrap()
            }
        }
    }

    /// Test helper trait to simplify lexing.
    trait Lex {
        fn lex(&self) -> LexedInput;
        fn lex_unchecked(&self) -> LexedInput;
    }

    /// Lexing for &str's.
    impl Lex for &str {
        fn lex(&self) -> LexedInput {
            lex(self)
        }
        fn lex_unchecked(&self) -> LexedInput {
            lex_unchecked(self)
        }
    }

    /// Lexing for Strings.
    impl Lex for String {
        fn lex(&self) -> LexedInput {
            lex(self)
        }
        fn lex_unchecked(&self) -> LexedInput {
            lex_unchecked(self)
        }
    }

    /// Helper function for lexing Clarity source using Logos and converting it
    /// into a spanned token stream input which Chumsky can understand.
    fn lex(src: &str) -> LexedInput {
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

        // Define 'end of input' span for optimized usage. This basically just 
        // creates a `Range(src.len(), src.len())`.
        let src_len = src.len();
        let zero_width_span_at_end = (src_len..src_len).into();

        Stream::from_iter(token_iter)
            // Tell chumsky to split the (Token, SimpleSpan) stream into its parts so that it can handle the spans for us
            // This involves giving chumsky an 'end of input' span: we just use a zero-width span at the end of the string
            .spanned(zero_width_span_at_end)
    }

    fn lex_unchecked(src: &str) -> LexedInput {
        let token_iter = Token::lexer(src)
            .spanned()
            .map(|(tok, span)| match tok {
                Ok(tok) => (
                    tok,
                    <std::ops::Range<usize> as Into<SimpleSpan>>::into(span),
                ),
                Err(err) => { 
                    panic!("lexing failed: {err:?}");
                },
            })
            .collect::<Vec<_>>();

        // Define 'end of input' span for optimized usage. This basically just 
        // creates a `Range(src.len(), src.len())`.
        let src_len = src.len();
        let zero_width_span_at_end = (src_len..src_len).into();

        Stream::from_iter(token_iter)
            // Tell chumsky to split the (Token, SimpleSpan) stream into its parts so that it can handle the spans for us
            // This involves giving chumsky an 'end of input' span: we just use a zero-width span at the end of the string
            .spanned(zero_width_span_at_end)
    }

    /* #endregion */
}
