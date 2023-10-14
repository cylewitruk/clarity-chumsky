use std::time::Instant;
use std::vec::IntoIter;

use anyhow::bail;
use anyhow::Result;
pub(crate) use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::input::Input;
use chumsky::input::Stream;
use chumsky::span::SimpleSpan;
use chumsky::Parser;
use expressions::SExpr;
use logos::Logos;

use crate::tokens::Token;
use crate::source::*;

mod errors;
mod expressions;
mod parser;
mod tokens;
mod value_ext;
mod source;
mod types;

fn main() -> Result<()> {
    //let source = CONTRACT_SRC;
    let source = SRC;

    // ***************************
    // ** LEXING
    // ***************************

    let now = Instant::now();

    // Create a logos lexer over the source code
    let token_iter: Vec<_> = Token::lexer(source)
        .spanned()
        // Convert logos errors into tokens. We want parsing to be recoverable and not fail at the lexing stage, so
        // we have a dedicated `Token::Error` variant that represents a token error that was previously encountered
        .map(|(tok, span)| match tok {
            // Turn the `Range<usize>` spans logos gives us into chumsky's `SimpleSpan` via `Into`, because it's easier
            // to work with
            Ok(tok) => (tok, span.into()),
            Err(()) => (Token::Error, span.into()),
        })
        .collect();

    let elapsed = Instant::now().duration_since(now);
    println!("lexer elapsed: {:?}", elapsed);

    // Debug output
    let lexer = Token::lexer(source);
    for token in lexer.into_iter() {
        //let _ = dbg!(token).map_err(|e| println!("error: {e:?}"));
    }

    // ***************************
    // ** PARSING
    // ***************************
    let now = Instant::now();
    let sexpr = parse(source, token_iter.into_iter())?;
    let elapsed = Instant::now().duration_since(now);
    println!("parser elapsed: {:?}", elapsed);

    // ***************************
    // ** EVAL
    // ***************************

    let now = Instant::now();
    match sexpr.eval() {
        Ok(out) => println!(
            "eval result = {}, time = {:?}",
            out,
            Instant::now().duration_since(now)
        ),
        Err(err) => println!("eval runtime error: {}", err),
    }
    let elapsed = Instant::now().duration_since(now);
    println!("eval elapsed: {:?}", elapsed);

    Ok(())
}

fn parse(source: &str, token_iter: IntoIter<(Token, SimpleSpan)>) -> Result<SExpr> {
    // Turn the token iterator into a stream that chumsky can use for things like backtracking
    let token_stream = Stream::from_iter(token_iter)
        // Tell chumsky to split the (Token, SimpleSpan) stream into its parts so that it can handle the spans for us
        // This involves giving chumsky an 'end of input' span: we just use a zero-width span at the end of the string
        .spanned((source.len()..source.len()).into());

    let now = Instant::now();
    // Parse the token stream with our chumsky parser
    match parser::parser().parse(token_stream).into_result() {
        // If parsing was successful, attempt to evaluate the s-expression
        Ok(sexpr) => {
            println!("parsing time = {:?}", Instant::now().duration_since(now));
            Ok(sexpr)
        }
        // If parsing was unsuccessful, generate a nice user-friendly diagnostic with ariadne. You could also use
        // codespan, or whatever other diagnostic library you care about. You could even just display-print the errors
        // with Rust's built-in `Display` trait, but it's a little crude
        Err(errs) => {
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
                    .eprint(Source::from(source))
                    .unwrap();
            }
            bail!("parsing failed")
        }
    }
}

