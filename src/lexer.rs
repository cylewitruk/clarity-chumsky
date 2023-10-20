use std::fmt;

use logos::{Logos, Lexer};

use crate::errors::ClarityError;

/// Removes surrounding quotes from an ASCII string literal token.
fn literal_ascii_string<'a>(lex: &mut Lexer<'a, Token<'a>>) -> &'a str {
    lex.slice().trim_matches('"')
}

/// Removes `u` unsigned indicator and surrounding quotes from a UTF8 string
/// literal token.
fn literal_utf8_string<'a>(lex: &mut Lexer<'a, Token<'a>>) -> &'a str {
    lex.slice().trim_start_matches('u').trim_matches('"')
}

/// Parses a numeric literal into an `i128`.
fn literal_int<'a>(lex: &mut Lexer<'a, Token<'a>>) -> i128 {
    lex.slice().parse::<i128>().unwrap()
}

/// Removes `u` unsigned indicator and parses the numeric literal into an `u128`.
fn literal_uint<'a>(lex: &mut Lexer<'a, Token<'a>>) -> u128 {
    lex.slice().trim_start_matches('u').parse::<u128>().unwrap()
}

/// Removes the preceeding `'` from a principal literal.
fn literal_principal<'a>(lex: &mut Lexer<'a, Token<'a>>) -> &'a str {
    lex.slice().trim_start_matches("'")
}

/// Enum of all tokens in the Clarity language.
#[derive(Logos, Clone, Debug, PartialEq)]
#[logos(error = ClarityError<'s>)]
pub enum Token<'a> {
    Error,

    #[regex(r";;[^\n]*\n", logos::skip)]
    Comment,
    #[regex(r"[ \t\f\n]+", logos::skip)]
    Whitespace,
    #[token(",")]
    Comma,

    // Optional/response
    #[token("default-to")]
    OpDefaultTo,
    #[token("err")]
    OpErr,
    #[token("ok")]
    OpOk,
    #[token("some")]
    OpSome,

    // Literals
    #[regex("u[0-9]+", priority = 2, callback = literal_uint)]
    LiteralUInt(u128),
    #[regex("[0-9]+", callback = literal_int)]
    LiteralInt(i128),
    #[regex("0b[01]+")]
    LiteralBinary,
    #[regex("0x[0-9a-fA-F]+")]
    LiteralHex,
    #[regex(r#""[^"]*""#, callback = literal_ascii_string)]
    LiteralAsciiString(&'a str),
    #[regex(r#"u"[^"]*""#, callback = literal_utf8_string)]
    LiteralUtf8String(&'a str),
    #[regex("'ST[A-Z0-9]{39}", callback = literal_principal)]
    LiteralPrincipal(&'a str),
    #[token("(")]
    ParenOpen,
    #[token(")")]
    ParenClose,
    #[token("{")]
    BraceOpen,
    #[token("}")]
    BraceClose,
    #[token(":")]
    Colon,
    #[token("'")]
    SingleQuote,
    #[token("\"")]
    DoubleQuote,

    // Types
    #[token("uint")]
    UInt,
    #[token("int")]
    Int,
    #[token("string-ascii")]
    AsciiString,
    #[token("string-utf8")]
    Utf8String,
    #[token("principal")]
    Principal,

    // Keywords
    #[token("block-height")]
    BlockHeight,
    #[token("burn-block-height")]
    BurnBlockHeight,
    #[token("chain-id")]
    ChainId,
    #[token("contract-caller")]
    ContractCaller,
    #[token("false")]
    False,
    #[token("is-in-mainnet")]
    IsInMainnet,
    #[token("is-in-regtest")]
    IsInRegTest,
    #[token("none")]
    None,
    #[token("stx-liquid-supply")]
    StxLiquidSupply,
    #[token("true")]
    True,
    #[token("tx-sender")]
    TxSender,
    #[token("tx-sponsor?")]
    TxSponsorOpt,

    // Arithmetic
    #[token("+")]
    OpAdd,
    #[token("-")]
    OpSub,
    #[token("*")]
    OpMul,
    #[token("/")]
    OpDiv,
    #[token("mod")]
    OpMod,

    // Bit operations
    #[token("bit-and")]
    OpBitAnd,
    #[token("bit-not")]
    OpBitNot,
    #[token("bit-or")]
    OpBitOr,
    #[token("bit-shift-left")]
    OpBitLShift,
    #[token("bit-shift-right")]
    #[token("bit-xor")]
    OpBitXor,
    #[token("xor")]
    OpXor,

    // Comparison
    #[token(">")]
    OpGreaterThan,
    #[token("<")]
    OpLessThan,
    #[token(">=")]
    OpGreaterThanOrEq,
    #[token("<=")]
    OpLessThanOrEq,
    #[token("is-eq")]
    OpIsEq,
    #[token("is-err")]
    OpIsErr,
    #[token("is-none")]
    OpIsNone,
    #[token("is-ok")]
    OpIsOk,
    #[token("is-some")]
    OpIsSome,
    #[token("is-standard")]
    OpIsStandard,

    // Var functions
    #[token("var-get")]
    OpVarGet,
    #[token("var-set")]
    OpVarSet,
    #[token("let")]
    OpLet,

    // Map functions
    #[token("map-delete")]
    OpMapDelete,
    #[token("map-get?")]
    OpMapGetOpt,
    #[token("map-insert")]
    OpMapInsert,
    #[token("map-set")]
    OpMapSet,

    // Tuple functions
    #[token("get")]
    OpGet,
    #[token("merge")]
    OpMerge,
    #[token("tuple")]
    OpTuple,

    // Define functions
    #[token("define-constant")]
    OpDefineConstant,
    #[token("define-data-var")]
    OpDefineDataVar,
    #[token("define-fungible-token")]
    OpDefineFungibleToken,
    #[token("define-map")]
    OpDefineMap,
    #[token("define-non-fungible-token")]
    OpDefineNonFungibleToken,
    #[token("define-private")]
    OpDefinePrivate,
    #[token("define-public")]
    OpDefinePublic,
    #[token("define-read-only")]
    OpDefineReadOnly,
    #[token("define-trait")]
    OpDefineTrait,

    // Conversion functions
    #[token("buff-to-uint-be")]
    OpBuffToUintBe,
    #[token("buff-to-uint-le")]
    OpBuffToUintLe,
    #[token("buff-to-int-be")]
    OpBuffToIntBe,
    #[token("buff-to-int-le")]
    OpButtToIntLe,
    #[token("to-int")]
    OpToInt,
    #[token("to-uint")]
    OpToUInt,
    #[token("string-to-int?")]
    OpStringToIntOpt,
    #[token("string-to-uint?")]
    OpStringToUIntOpt,
    #[token("int-to-ascii")]
    OpIntToAscii,
    #[token("int-to-utf8")]
    OpIntToUtf8,
    #[token("from-consensus-buff?")]
    OpFromConsensusBufOpt,

    // Stx functions
    #[token("stx-account")]
    OpStxAccount,
    #[token("stx-burn?")]
    OpStxBurnOpt,
    #[token("stx-get-balance")]
    OpStxGetBalance,
    #[token("stx-transfer-memo?")]
    OpStxTransferMemoOpt,
    #[token("stx-transfer?")]
    OpStxTransferOpt,

    // Fungible token functions
    #[token("ft-burn?")]
    OpFtBurnOpt,
    #[token("ft-get-balance")]
    OpFtGetBalance,
    #[token("ft-get-supply")]
    OpFtGetSupply,
    #[token("ft-mint?")]
    OpFtMintOpt,
    #[token("ft-transfer?")]
    OpFtTransferOpt,

    // NFT functions
    #[token("nft-burn?")]
    OpNftBurnOpt,
    #[token("nft-get-owner?")]
    OpNftGetOwnerOpt,
    #[token("nft-mint?")]
    OpNftMintOpt,
    #[token("nft-transfer?")]
    OpNftTransferOpt,

    // Sequence functions
    #[token("append")]
    OpAppend,
    #[token("concat")]
    OpConcat,
    #[token("element-at")]
    OpElementAt,
    #[token("element-at?")]
    OpElementAtOpt,
    #[token("filter")]
    OpFilter,
    #[token("fold")]
    OpFold,
    #[token("index-of")]
    OpIndexOf,
    #[token("index-of?")]
    OpIndexOfOpt,
    #[token("len")]
    OpLen,
    #[token("list")]
    OpList,
    #[token("map")]
    OpMap,
    #[token("replace-at?")]
    OpReplaceAtOpt,
    #[token("slice?")]
    OpSliceOpt,

    // Unwrap functions
    #[token("unwrap!")]
    OpUnwrapThrow,
    #[token("unwrap-err!")]
    OpUnwrapErrThrow,
    #[token("unwrap-err-panic")]
    OpUnwrapErrPanic,
    #[token("unwrap-panic")]
    OpUnwrapPanic,

    // Control flow
    #[token("and")]
    OpAnd,
    #[token("or")]
    OpOr,
    #[token("if")]
    OpIf,
    #[token("begin")]
    OpBegin,
    #[token("match")]
    OpMatch,
    #[token("try!")]
    OpTryThrow,

    // Contract functions
    #[token("contract-call?")]
    OpContractCallOpt,
    #[token("contract-of")]
    OpContractOf,
    #[token("as-contract")]
    OpAsContract,

    // Other functions
    #[token("as-max-len?")]
    OpAsMaxLenOpt,
    #[token("asserts!")]
    OpAssertsThrow,
    #[token("at-block")]
    OpAtBlock,
    #[token("get-block-info?")]
    OpGetBlockInfoOpt,
    #[token("get-burn-block-info?")]
    OpGetBurnBlockInfoOpt,
    #[token("impl-trait")]
    OpImplTrait,
    #[token("use-trait")]
    OpUseTrait,
    #[token("print")]
    OpPrint,

    // Computation
    #[token("hash160")]
    OpHash160,
    #[token("pow")]
    OpPow,
    #[token("sqrti")]
    OpSqrti,
    #[token("sha256")]
    OpSha256,
    #[token("sha512")]
    OpSha512,
    #[token("sha512/256")]
    OpSha512_256,
    #[token("log2")]
    OpLog2,
    #[token("keccak256")]
    OpKeccak256,

    #[regex(r"[a-zA-Z$_][a-zA-Z0-9\\-]*", priority = 0)]
    Identifier(&'a str),
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Comment => write!(f, "<comment>"),
            Token::OpAdd => write!(f, "+"),
            Token::OpSub => write!(f, "-"),
            Token::OpMul => write!(f, "*"),
            Token::OpDiv => write!(f, "/"),
            Token::ParenOpen => write!(f, "("),
            Token::ParenClose => write!(f, ")"),
            Token::Whitespace => write!(f, "<whitespace>"),
            Token::Error => write!(f, "<error>"),
            Token::OpMod => write!(f, "mod"),
            Token::OpBitAnd => write!(f, "bit-and"),
            Token::OpBitNot => write!(f, "bit-not"),
            Token::OpBitOr => write!(f, "bit-or"),
            Token::OpBitLShift => write!(f, "bit-shift-left"),
            Token::OpBitXor => write!(f, "bit-xor"),
            Token::OpXor => write!(f, "xor"),
            Token::OpGreaterThan => write!(f, ">"),
            Token::OpLessThan => write!(f, "<"),
            Token::OpGreaterThanOrEq => write!(f, ">="),
            Token::OpLessThanOrEq => write!(f, "<="),
            Token::OpMapDelete => write!(f, "map-delete"),
            Token::OpMapGetOpt => write!(f, "map-get?"),
            Token::OpMapInsert => write!(f, "map-insert"),
            Token::OpMapSet => write!(f, "map-set"),
            Token::OpGet => write!(f, "get"),
            Token::OpMerge => write!(f, "merge"),
            Token::OpTuple => write!(f, "tuple"),
            Token::OpBuffToUintBe => write!(f, "buff-to-uint-be"),
            Token::OpBuffToUintLe => write!(f, "buff-to-uint-le"),
            Token::OpBuffToIntBe => write!(f, "buff-to-int-be"),
            Token::OpButtToIntLe => write!(f, "buff-to-int-le"),
            Token::OpToInt => write!(f, "to-int"),
            Token::OpToUInt => write!(f, "to-uint"),
            Token::OpStringToIntOpt => write!(f, "string-to-int?"),
            Token::OpStringToUIntOpt => write!(f, "string-to-uint?"),
            Token::OpIntToAscii => write!(f, "int-to-ascii"),
            Token::OpIntToUtf8 => write!(f, "int-to-utf8"),
            Token::OpStxAccount => write!(f, "stx-account"),
            Token::OpStxBurnOpt => write!(f, "stx-burn?"),
            Token::OpStxGetBalance => write!(f, "stx-get-balance"),
            Token::OpStxTransferMemoOpt => write!(f, "stx-transfer-memo?"),
            Token::OpStxTransferOpt => write!(f, "stx-transfer?"),
            Token::OpUnwrapThrow => write!(f, "unwrap!"),
            Token::OpUnwrapErrThrow => write!(f, "unwrap-err!"),
            Token::OpUnwrapErrPanic => write!(f, "unwrap-err-panic"),
            Token::OpUnwrapPanic => write!(f, "unwrap-panic"),
            Token::OpAnd => write!(f, "and"),
            Token::OpOr => write!(f, "or"),
            Token::OpIf => write!(f, "if"),
            Token::OpDefaultTo => write!(f, "default-to"),
            Token::OpErr => write!(f, "err"),
            Token::OpIsNone => write!(f, "is-none"),
            Token::OpIsSome => write!(f, "is-some"),
            Token::OpOk => write!(f, "ok"),
            Token::OpSome => write!(f, "is-some"),
            Token::OpHash160 => write!(f, "hash160"),
            Token::OpPow => write!(f, "pow"),
            Token::OpSqrti => write!(f, "sqrti"),
            Token::OpSha256 => write!(f, "sha256"),
            Token::OpSha512 => write!(f, "sha512"),
            Token::OpSha512_256 => write!(f, "sha512/256"),
            Token::OpLog2 => write!(f, "log2"),
            Token::OpKeccak256 => write!(f, "keccak256"),
            Token::OpDefineConstant => write!(f, "define-constant"),
            Token::OpDefineDataVar => write!(f, "define-data-var"),
            Token::OpDefineFungibleToken => write!(f, "define-fungible-token"),
            Token::OpDefineMap => write!(f, "define-map"),
            Token::OpDefineNonFungibleToken => write!(f, "define-non-fungible-token"),
            Token::OpDefinePrivate => write!(f, "define-private"),
            Token::OpDefinePublic => write!(f, "define-public"),
            Token::OpDefineReadOnly => write!(f, "define-read-only"),
            Token::OpDefineTrait => write!(f, "define-trait"),
            Token::OpVarGet => write!(f, "var-get"),
            Token::OpVarSet => write!(f, "var-set"),
            Token::OpLet => write!(f, "let"),
            Token::OpFromConsensusBufOpt => write!(f, "from-consensus-buf?"),
            Token::OpFtBurnOpt => write!(f, "ft-burn?"),
            Token::OpFtGetBalance => write!(f, "ft-get-balance"),
            Token::OpFtGetSupply => write!(f, "ft-get-supply"),
            Token::OpFtMintOpt => write!(f, "ft-mint?"),
            Token::OpFtTransferOpt => write!(f, "ft-transfer?"),
            Token::OpNftBurnOpt => write!(f, "nft-burn?"),
            Token::OpNftGetOwnerOpt => write!(f, "nft-get-owner?"),
            Token::OpNftMintOpt => write!(f, "nft-mint?"),
            Token::OpNftTransferOpt => write!(f, "nft-transfer?"),
            Token::OpAppend => write!(f, "append"),
            Token::OpConcat => write!(f, "concat"),
            Token::OpElementAt => write!(f, "element-at"),
            Token::OpElementAtOpt => write!(f, "element-at?"),
            Token::OpFilter => write!(f, "filter"),
            Token::OpFold => write!(f, "fold"),
            Token::OpIndexOf => write!(f, "index-of"),
            Token::OpIndexOfOpt => write!(f, "index-of?"),
            Token::OpLen => write!(f, "len"),
            Token::OpList => write!(f, "list"),
            Token::OpMap => write!(f, "map"),
            Token::OpReplaceAtOpt => write!(f, "replace-at?"),
            Token::OpSliceOpt => write!(f, "slice?"),
            Token::OpBegin => write!(f, "begin"),
            Token::OpIsEq => write!(f, "is-eq"),
            Token::OpIsErr => write!(f, "is-err"),
            Token::OpIsOk => write!(f, "is-ok"),
            Token::OpIsStandard => write!(f, "is-standard"),
            Token::OpMatch => write!(f, "match"),
            Token::OpTryThrow => write!(f, "try!"),
            Token::OpContractCallOpt => write!(f, "contract-call?"),
            Token::OpContractOf => write!(f, "contract-of"),
            Token::OpAsContract => write!(f, "as-contract"),
            Token::OpAsMaxLenOpt => write!(f, "as-max-len?"),
            Token::OpAssertsThrow => write!(f, "asserts!"),
            Token::OpAtBlock => write!(f, "at-block"),
            Token::OpGetBlockInfoOpt => write!(f, "get-block-info?"),
            Token::OpGetBurnBlockInfoOpt => write!(f, "get-burn-block-info?"),
            Token::OpImplTrait => write!(f, "impl-trait"),
            Token::OpUseTrait => write!(f, "use-trait"),
            Token::OpPrint => write!(f, "print"),
            Token::Identifier(str) => write!(f, "<ident: {str}>"),
            Token::UInt => write!(f, "<uint>"),
            Token::Int => write!(f, "<int>"),
            Token::LiteralBinary => write!(f, "<binary>"),
            Token::LiteralHex => write!(f, "<hex>"),
            Token::BraceOpen => write!(f, "{{"),
            Token::BraceClose => write!(f, "}}"),
            Token::BlockHeight => write!(f, "block-height"),
            Token::BurnBlockHeight => write!(f, "burn-block-height"),
            Token::ChainId => write!(f, "chain-id"),
            Token::ContractCaller => write!(f, "contract-caller"),
            Token::False => write!(f, "false"),
            Token::IsInMainnet => write!(f, "is-in-mainnet"),
            Token::IsInRegTest => write!(f, "is-in-regtest"),
            Token::None => write!(f, "none"),
            Token::StxLiquidSupply => write!(f, "stx-liquid-supply"),
            Token::True => write!(f, "true"),
            Token::TxSender => write!(f, "tx-sender"),
            Token::TxSponsorOpt => write!(f, "tx-sponsor?"),
            Token::LiteralInt(i) => write!(f, "<int: {i}>"),
            Token::LiteralUInt(i) => write!(f, "<uint: {i}>"),
            Token::Colon => write!(f, ":"),
            Token::SingleQuote => write!(f, "'"),
            Token::DoubleQuote => write!(f, "\""),
            Token::AsciiString => write!(f, "<string-ascii>"),
            Token::Utf8String => write!(f, "<string-utf8>"),
            Token::Principal => write!(f, "<principal>"),
            Token::Comma => write!(f, ","),
            Token::LiteralAsciiString(str) => write!(f, "<ascii> \"{str}\""),
            Token::LiteralUtf8String(str) => write!(f, "<utf8> \"{str}\""),
            Token::LiteralPrincipal(str) => write!(f, "<principal: \"{str}\""),
        }
    }
}
