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
use num_bigint::BigInt;
use num_bigint::BigUint;

use crate::tokens::Token;

mod errors;
mod expressions;
mod parser;
mod tokens;
mod value_ext;

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

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ClarityType {
    Bool,
    Integer(IntegerType),
    CallableContract,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum IntegerType {
    I32,
    U32,
    I64,
    U64,
    I128,
    U128,
    I256,
    U256,
    I512,
    U512,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ClarityInteger {
    I32(i32),
    U32(u32),
    I64(i64),
    U64(u64),
    I128(i128),
    U128(u128),
    I256(BigInt),
    U256(BigUint),
    I512(BigInt),
    U512(BigUint),
}

#[derive(Debug, Clone, PartialEq)]
pub struct RefinedInteger {
    pub low_val: ClarityInteger,
    pub high_val: ClarityInteger
}

impl RefinedInteger {
    pub fn new(
        low_val: ClarityInteger, 
        high_val: ClarityInteger
    ) -> Self {
        Self { low_val, high_val }
    }
}

#[allow(dead_code)]
const SRC: &str = r"
;; This is a comment

;; I256
(int -170141183460469231731687303715884105729 100)
;; U256
(int 170141183460469231731687303715884105729 100)
// U512
(int 0 6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216824503042047)

(-
  (* (+ 1 2 3 4 5) 7)
  (/ 5 3)
)
";

#[allow(dead_code)]
const CONTRACT_SRC: &str = r"
;; A simple betting game using flip-coin with player matching
;;
;; For more details see docs/flip-coin.md

(define-constant default-amount u1000)
(define-constant new-slot {bet-true: none, bet-false: none, amount: default-amount, created-at: u0})
(define-constant err-bet-exists u10)
(define-constant err-flip-failed u11)

;; storage
(define-map gamblers (tuple (height uint)) (tuple (bet-true principal) (bet-false principal)))
(define-map amounts (tuple (height uint)) (tuple (amount uint)))
(define-map matched-bets (tuple (created-at uint)) (tuple (height uint)))

(define-data-var pending-payout (optional uint) none)
(define-data-var next-slot {bet-true: (optional principal), bet-false: (optional principal),
  amount: uint, created-at: uint}
  new-slot)

;; store information about tax office to pay tax on prize immediately
(use-trait tax-office-trait .flip-coin-tax-office.tax-office-trait)

;; return next slot
(define-read-only (get-next-slot)
  (var-get next-slot)
)

;; returns how much stx were bet at the given block
(define-read-only (get-amount-at (height uint))
  (match (map-get? amounts {height: height})
    amount (get amount amount)
    u0
  )
)

;; returns the winner at the given block. If there was no winner `(none)` is returned
(define-read-only (get-optional-winner-at (height uint))
  (match (map-get? gamblers {height: height})
    game-slot  (let ((value (contract-call? .flip-coin flip-coin-at (+ height u1))))
                  (if value
                    (some (get bet-true game-slot))
                    (some (get bet-false game-slot))
                ))
    none
  )
)


;; splits the prize money
;; 10% goes to another account
;; the rest to the winner
(define-private (shared-amounts (amount uint))
   (let ((shared (/ (* amount u10) u100)))
    {winner: (- amount shared),
    shared: shared,}
  )
)
;; pays the bet amount at the given block
;; height must be below the current height
;; 10% goes to the tax office
(define-private (payout (height (optional uint)))
 (match height
  some-height (if (<= block-height some-height)
    true
    (let ((shared-prize (shared-amounts (get-amount-at some-height))))
      (begin
        (unwrap-panic (as-contract (stx-transfer? (get winner shared-prize) tx-sender (unwrap-panic (get-optional-winner-at some-height)))))
        (unwrap-panic (as-contract (contract-call? .flip-coin-jackpot pay-tax (get shared shared-prize))))
        (var-set pending-payout none)
      )
    ))
  true
 )
)

(define-private (next-gambler (value bool))
  (if value
        (get bet-true (var-get next-slot))
        (get bet-false (var-get next-slot))
  )
)

(define-data-var trigger (optional uint) none)
(define-private (panic)
  (ok {created-at: (unwrap-panic (var-get trigger)), bet-at: u0})
)

(define-private (update-game-after-payment (values (tuple (bet-true principal) (bet-false principal))) (amount uint))
  (if (map-insert gamblers {height: block-height}
                    {
                      bet-true: (get bet-true values),
                      bet-false: (get bet-false values)
                    })
      (if (map-insert amounts {height: block-height}  {amount: (+ amount amount)})
          (let ((created-at block-height))
            (begin
              (map-insert matched-bets {created-at: created-at} {height: block-height})
              (var-set next-slot new-slot)
              (var-set pending-payout (some block-height))
              (ok {
                    created-at: created-at,
                    bet-at: block-height
                  })
            )
          )
          (panic))
      (panic)))

;; bet 1000 uSTX on the each value for the given users.
;; Only one set of users can bet for each block.
;; if payout needs to be done then this function call will do it (note that the caller
;; needs to provide corresponding post conditions)
(define-public (bet (values (tuple (bet-true principal) (bet-false principal))))
  (let ((amount default-amount))
    (begin
      (payout (var-get pending-payout))
      (if (is-some (next-gambler true))
        (err err-bet-exists)
        (begin
          (match (stx-transfer? (* u2 amount) tx-sender (as-contract tx-sender))
            success (update-game-after-payment values amount)
            error (err error)))))))

(define-public (fund-slot (amount uint) (account principal))
  (stx-transfer? amount tx-sender account)
)";
