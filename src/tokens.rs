use std::fmt;

use lazy_static::lazy_static;
use logos::{Lexer, Logos};
use num_bigint::{BigInt, BigUint};
use regex::Regex;

use crate::{ClarityInteger, IntegerType, RefinedInteger};

lazy_static! {
    static ref REFINED_INT_REGEX: Regex = Regex::new(
        r"\(int\s+(?P<sign_low>[-+])?(?P<low>[\d]+)\s+(?P<sign_high>[-+])?(?P<high>[\d]+)\)"
    ).unwrap();

    static ref I256_MIN: BigInt = BigInt::parse_bytes(
        "-57896044618658097711785492504343953926634992332820282019728792003956564819968".as_bytes(),
        10
    ).unwrap();

    static ref U256_MAX: BigUint = BigUint::parse_bytes(
        "115792089237316195423570985008687907853269984665640564039457584007913129639935".as_bytes(),
        10
    ).unwrap();

    static ref I256_MAX: BigInt = BigInt::parse_bytes(
        "57896044618658097711785492504343953926634992332820282019728792003956564819967".as_bytes(),
        10
    ).unwrap();

    static ref I512_MIN: BigInt = BigInt::parse_bytes(concat!(
        r#"-6703903964971298549787012499102923063739682910296196688861780721860882015036773"#,
        r#"488400937149083451713845015929093243025426876941405973284973216824503042048"#).as_bytes(),
        10
    ).unwrap();
    
    static ref I512_MAX: BigInt = BigInt::parse_bytes(concat!(
        r#"670390396497129854978701249910292306373968291029619668886178072186088201503677"#,
        r#"r#"3488400937149083451713845015929093243025426876941405973284973216824503042047"#).as_bytes(),
    10).unwrap();

    static ref U512_MAX: BigUint = BigUint::parse_bytes(concat!(
        r#"13407807929942597099574024998205846127479365820592393377723561443721764030073546"#,
        r#"976801874298166903427690031858186486050853753882811946569946433649006084095"#).as_bytes(), 
        10
    ).unwrap();
}

fn parse_int(lex: &mut Lexer<Token>) -> ClarityInteger {
    let slice = lex.slice();
    if let Some(stripped) = slice.strip_prefix('u') {
        let uint: u128 = stripped.parse().unwrap();
        ClarityInteger::U128(uint)
    } else {
        let int: i128 = slice.parse().unwrap();
        ClarityInteger::I128(int)
    }
}

fn parse_refined_int(lex: &mut Lexer<Token>) -> RefinedInteger {
    let slice = lex.slice();
    let caps = REFINED_INT_REGEX.captures(slice).unwrap();

    let low = &caps["low"];
    let high = &caps["high"];

    let is_low_negative = caps.name("sign_low").map_or(false, |f| f.as_str().eq("-"));
    let is_high_negative = caps.name("sign_high").map_or(false, |f| f.as_str().eq("-"));

    eprintln!("parse_refined_int: {slice}, is_low_negative: {:?}, low: {}, is_high_negative: {:?}, high: {:?}",
        is_low_negative, &caps["low"], is_high_negative, &caps["high"]);

    let low_val: ClarityInteger;
    let high_val: ClarityInteger;
    

    if is_low_negative {
        let low = BigInt::parse_bytes(low.as_bytes(), 10).unwrap() * -1;
        low_val = match get_refined_integer_type_signed(&low) {
            IntegerType::I32 => ClarityInteger::I32(low.try_into().unwrap()),
            IntegerType::I64 => ClarityInteger::I64(low.try_into().unwrap()),
            IntegerType::I128 => ClarityInteger::I128(low.try_into().unwrap()),
            IntegerType::I256 => ClarityInteger::I256(low),
            IntegerType::I512 => ClarityInteger::I512(low),
            _ => panic!("signed integers larger than 512 bits are not currently supported"),
        };
        eprintln!("LOW SIG: {low_val:?}");
    } else {
        let low = BigUint::parse_bytes(low.as_bytes(), 10).unwrap();
        low_val = match get_refined_integer_type_unsigned(&low) {
            IntegerType::U32 => ClarityInteger::U32(low.try_into().unwrap()),
            IntegerType::U64 => ClarityInteger::U64(low.try_into().unwrap()),
            IntegerType::U128 => ClarityInteger::U128(low.try_into().unwrap()),
            IntegerType::U256 => ClarityInteger::U256(low),
            IntegerType::U512 => ClarityInteger::U512(low),
            _ => panic!("unsigned integers larger than 512 bits are not currently supported.")
        };
        eprintln!("LOW UNS: {low_val:?}");
    }

    if is_high_negative {
        let high = BigInt::parse_bytes(high.as_bytes(), 10).unwrap() * -1;
        high_val = match get_refined_integer_type_signed(&high) {
            IntegerType::I32 => ClarityInteger::I32(high.try_into().unwrap()),
            IntegerType::I64 => ClarityInteger::I64(high.try_into().unwrap()),
            IntegerType::I128 => ClarityInteger::I128(high.try_into().unwrap()),
            IntegerType::I256 => ClarityInteger::I256(high),
            IntegerType::I512 => ClarityInteger::I512(high),
            _ => panic!("signed integers larger than 512 bits are not currently supported"),
        };
        eprintln!("HIGH SIG: {high_val:?}");
    } else {
        let high = BigUint::parse_bytes(high.as_bytes(), 10).unwrap();
        high_val = match get_refined_integer_type_unsigned(&high) {
            IntegerType::U32 => ClarityInteger::U32(high.try_into().unwrap()),
            IntegerType::U64 => ClarityInteger::U64(high.try_into().unwrap()),
            IntegerType::U128 => ClarityInteger::U128(high.try_into().unwrap()),
            IntegerType::U256 => ClarityInteger::U256(high),
            IntegerType::U512 => ClarityInteger::U512(high),
            _ => panic!("unsigned integers larger than 512 bits are not currently supported.")
        };
        eprintln!("HIGH UNS: {high_val:?}");
    }
        
    RefinedInteger::new(low_val, high_val)
}

fn get_refined_integer_type_signed(int: &BigInt) -> IntegerType {
    if *int >= i32::MIN.into() && *int <= i32::MAX.into() {
        IntegerType::I32
    } else if *int >= i64::MIN.into() && *int <= i64::MAX.into() {
        IntegerType::I64
    } else if *int >= i128::MIN.into() && *int <= i128::MAX.into() {
        IntegerType::I128
    } else if *int >= *I256_MIN && *int <= *I256_MAX {
        IntegerType::I256
    } else if *int >= *I512_MIN && *int <= *I512_MAX {
        IntegerType::I512
    } else {
        panic!("integer type not supported (out of range");
    }
}

fn get_refined_integer_type_unsigned(int: &BigUint) -> IntegerType {
    if *int <= u32::MAX.into() {
        IntegerType::U32
    } else if *int <= u64::MAX.into() {
        IntegerType::U64
    } else if *int <= u128::MAX.into() {
        IntegerType::U128
    } else if *int <= *U256_MAX {
        IntegerType::U256
    } else if *int <= *U512_MAX {
        IntegerType::U512
    } else {
        panic!("integer type not supported (out of range)");
    }
}

#[derive(Logos, Clone, Debug, PartialEq)]
pub enum Token {
    Error,

    #[regex(r";;[^\n]*\n", logos::skip)]
    Comment,
    // Note: could specify separate regex's here to match the +/-/low/high combinations and
    // route to different parsing methods for each to optimize performance.
    #[regex(r"\(int\s+(?P<sign_low>[-+])?(?P<low>[\d]+)\s+(?P<sign_high>[-+])?(?P<high>[\d]+)\)",
        callback = parse_refined_int)]
    RefinedInteger(RefinedInteger),
    #[regex("[a-zA-Z$_][a-zA-Z0-9$_]*", priority = 1)]
    Identifier,
    #[token("uint")]
    TypeUInt,
    #[token("int")]
    TypeInt,
    #[regex("u?[0-9]+", priority = 2, callback = parse_int )]
    LiteralInteger(ClarityInteger),
    #[regex("0b[01]+")]
    LiteralBinary,
    #[regex("0x[0-9a-fA-F]+")]
    LiteralHex,
    #[regex(r#"u"([^"\\]|\\t|\\u|\\n|\\")*""#)]
    LiteralUtf8String,
    #[regex(r#""([^"\\]|\\t|\\u|\\n|\\")*""#)]
    LiteralAsciiString,
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
    #[regex(r"[ \t\f\n]+", logos::skip)]
    Whitespace,

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
    #[token("define-readonly")]
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

    // Optional/response
    #[token("default-to")]
    OpDefaultTo,
    #[token("err")]
    OpErr,
    #[token("ok")]
    OpOk,
    #[token("some")]
    OpSome,

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
}

impl fmt::Display for Token {
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
            Token::OpOk => write!(f, "is-ok"),
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
            Token::Identifier => write!(f, "<identifier>"),
            Token::TypeUInt => write!(f, "<uint>"),
            Token::TypeInt => write!(f, "<int>"),
            Token::LiteralBinary => write!(f, "<binary>"),
            Token::LiteralHex => write!(f, "<hex>"),
            Token::LiteralAsciiString => write!(f, "<string-ascii>"),
            Token::LiteralUtf8String => write!(f, "<string-utf8"),
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
            Token::LiteralInteger(ty) => write!(f, "{ty:?}"),
            Token::Colon => write!(f, ":"),
            Token::SingleQuote => write!(f, "'"),
            Token::DoubleQuote => write!(f, "\""),
            Token::RefinedInteger(_) => write!(f, "{self:?}"),
        }
    }
}
