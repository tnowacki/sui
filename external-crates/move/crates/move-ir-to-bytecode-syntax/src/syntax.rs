// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::anyhow;
use std::{
    collections::{BTreeMap, BTreeSet},
    str::FromStr,
};

use crate::lexer::*;
use move_command_line_common::files::FileHash;
use move_core_types::{account_address::AccountAddress, u256};
use move_ir_types::{ast::*, location::*};
use move_symbol_pool::Symbol;

pub type Error = Spanned<anyhow::Error>;
pub type Result<T> = std::result::Result<T, Error>;

pub(crate) struct Context<'lexer, 'input> {
    errors: Vec<Error>,
    tokens: &'lexer mut Lexer<'input>,
}

impl<'lexer, 'input> Context<'lexer, 'input> {
    fn new(tokens: &'lexer mut Lexer<'input>) -> Self {
        Self {
            errors: vec![],
            tokens,
        }
    }

    /// Advances token and records a resulting diagnostic (if any).
    fn advance(&mut self) {
        if let Err(err) = self.tokens.advance_inner() {
            self.errors.push(err);
        }
    }
}

pub(crate) fn error(loc: Loc, message: impl AsRef<str>) -> Error {
    sp(loc, anyhow!("{}", message.as_ref()))
}

pub(crate) fn invalid_token(loc: Loc, message: impl AsRef<str>) -> Error {
    sp(loc, anyhow!("Invalid token. {}", message.as_ref()))
}

pub(crate) fn make_loc(file_hash: FileHash, start: usize, end: usize) -> Loc {
    Loc::new(file_hash, start as u32, end as u32)
}

fn current_token_loc(context: &Context) -> Loc {
    let start_loc = context.tokens.start_loc();
    make_loc(
        context.tokens.file_hash(),
        start_loc,
        start_loc + context.tokens.content().len(),
    )
}

pub(crate) fn spanned<T>(file_hash: FileHash, start: usize, end: usize, value: T) -> Spanned<T> {
    Spanned {
        loc: make_loc(file_hash, start, end),
        value,
    }
}

// Check for the specified token and consume it if it matches.
// Returns true if the token matches.
fn match_token(context: &mut Context, tok: Tok) -> Result<bool> {
    if context.tokens.peek() == tok {
        context.advance();
        Ok(true)
    } else {
        Ok(false)
    }
}

fn consume_token(context: &mut Context, tok: Tok) -> Result<()> {
    if context.tokens.peek() != tok {
        return Err(invalid_token(
            current_token_loc(context),
            format!("expected {:?}, not {:?}", tok, context.tokens.peek()),
        ));
    }
    context.advance();
    Ok(())
}

fn adjust_token(context: &mut Context, list_end_tokens: &[Tok]) -> Result<()> {
    if context.tokens.peek() == Tok::GreaterGreater && list_end_tokens.contains(&Tok::Greater) {
        context.tokens.replace_token(Tok::Greater, 1)?;
    }
    Ok(())
}

fn parse_comma_list<F, R>(
    context: &mut Context,
    list_end_tokens: &[Tok],
    parse_list_item: F,
    allow_trailing_comma: bool,
) -> Result<Vec<R>>
where
    F: Fn(&mut Context) -> Result<R>,
{
    let mut v = vec![];
    adjust_token(context, list_end_tokens)?;
    if !list_end_tokens.contains(&context.tokens.peek()) {
        loop {
            v.push(parse_list_item(context)?);
            adjust_token(context, list_end_tokens)?;
            if list_end_tokens.contains(&context.tokens.peek()) {
                break;
            }
            consume_token(context, Tok::Comma)?;
            adjust_token(context, list_end_tokens)?;
            if list_end_tokens.contains(&context.tokens.peek()) && allow_trailing_comma {
                break;
            }
        }
    }
    Ok(v)
}

fn parse_list<C, F, R>(
    context: &mut Context,
    mut parse_list_continue: C,
    parse_list_item: F,
) -> Result<Vec<R>>
where
    C: FnMut(&mut Context) -> Result<bool>,
    F: Fn(&mut Context) -> Result<R>,
{
    let mut v = vec![];
    loop {
        v.push(parse_list_item(context)?);
        if !parse_list_continue(context)? {
            break Ok(v);
        }
    }
}

fn parse_name(context: &mut Context) -> Result<Symbol> {
    if context.tokens.peek() != Tok::NameValue {
        return Err(error(current_token_loc(context), "expected a name"));
    }
    let name = context.tokens.content();
    context.advance();
    Ok(Symbol::from(name))
}

fn parse_name_begin_ty(context: &mut Context) -> Result<Symbol> {
    if context.tokens.peek() != Tok::NameBeginTyValue {
        return Err(error(
            current_token_loc(context),
            "expected a name with a type argument",
        ));
    }
    let s = context.tokens.content();
    // The token includes a "<" at the end, so chop that off to get the name.
    let name = &s[..s.len() - 1];
    context.advance();
    Ok(Symbol::from(name))
}

fn parse_dot_name<'input>(context: &mut Context<'_, 'input>) -> Result<&'input str> {
    if context.tokens.peek() != Tok::DotNameValue {
        return Err(error(
            current_token_loc(context),
            "expected a name with a dot suffix",
        ));
    }
    let name = context.tokens.content();
    context.advance();
    Ok(name)
}

// AccountAddress: AccountAddress = {
//     < s: r"0[xX][0-9a-fA-F]+" > => { ... }
// };

fn parse_account_address(context: &mut Context) -> Result<AccountAddress> {
    if !matches!(
        context.tokens.peek(),
        Tok::AccountAddressValue | Tok::NameValue
    ) {
        return Err(error(
            current_token_loc(context),
            "expected a name or address",
        ));
    }
    let loc = current_token_loc(context);
    let addr = parse_address_literal(context, context.tokens.content(), loc).unwrap();
    context.advance();
    Ok(addr)
}

fn parse_address_literal(
    context: &mut Context,
    literal: &str,
    location: Loc,
) -> Result<AccountAddress> {
    let Some(addr) = AccountAddress::from_hex_literal(literal)
        .ok()
        .or_else(|| context.tokens.resolve_named_address(literal))
    else {
        return Err(error(location, "expected a name"));
    };
    Ok(addr)
}

// Var: Var = {
//     <n:Name> =>? Var::parse(n),
// };

fn parse_var_(context: &mut Context) -> Result<Var_> {
    Ok(Var_(parse_name(context)?))
}

fn parse_var(context: &mut Context) -> Result<Var> {
    let start_loc = context.tokens.start_loc();
    let var = parse_var_(context)?;
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, var))
}

// Field: Field = {
//     <n:Name> =>? parse_field(n),
// };

fn parse_field(context: &mut Context) -> Result<Field> {
    let start_loc = context.tokens.start_loc();
    let f = Field_(parse_name(context)?);
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, f))
}

/// field-ident: name-and-type-actuals '::' field
fn parse_field_ident(context: &mut Context) -> Result<FieldIdent> {
    let start_loc = context.tokens.start_loc();
    let (name, type_actuals) = parse_name_and_type_actuals(context)?;
    // For now, the lexer produces 2 ':' tokens instead of a single '::' token.
    consume_token(context, Tok::Colon)?;
    consume_token(context, Tok::Colon)?;
    let field = parse_field(context)?;
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(
        context.tokens.file_hash(),
        start_loc,
        end_loc,
        FieldIdent_ {
            struct_name: DatatypeName(name),
            type_actuals,
            field,
        },
    ))
}

// CopyableVal: CopyableVal = {
//     AccountAddress => CopyableVal::Address(<>),
//     "true" => CopyableVal::Bool(true),
//     "false" => CopyableVal::Bool(false),
//     <i: U64> => CopyableVal::U64(i),
//     <buf: ByteArray> => CopyableVal::ByteArray(buf),
// }

fn parse_copyable_val(context: &mut Context) -> Result<CopyableVal> {
    let start_loc = context.tokens.start_loc();
    let val = match context.tokens.peek() {
        Tok::AccountAddressValue => {
            let addr = parse_account_address(context)?;
            CopyableVal_::Address(addr)
        }
        Tok::True => {
            context.advance();
            CopyableVal_::Bool(true)
        }
        Tok::False => {
            context.advance();
            CopyableVal_::Bool(false)
        }
        Tok::U8Value => {
            let mut s = context.tokens.content();
            if s.ends_with("u8") {
                s = &s[..s.len() - 2]
            }
            let i = u8::from_str(s).unwrap();
            context.advance();
            CopyableVal_::U8(i)
        }
        Tok::U16Value => {
            let mut s = context.tokens.content();
            if s.ends_with("u16") {
                s = &s[..s.len() - 3]
            }
            let i = u16::from_str(s).unwrap();
            context.advance();
            CopyableVal_::U16(i)
        }
        Tok::U32Value => {
            let mut s = context.tokens.content();
            if s.ends_with("u32") {
                s = &s[..s.len() - 3]
            }
            let i = u32::from_str(s).unwrap();
            context.advance();
            CopyableVal_::U32(i)
        }
        Tok::U64Value => {
            let mut s = context.tokens.content();
            if s.ends_with("u64") {
                s = &s[..s.len() - 3]
            }
            let i = u64::from_str(s).unwrap();
            context.advance();
            CopyableVal_::U64(i)
        }
        Tok::U128Value => {
            let mut s = context.tokens.content();
            if s.ends_with("u128") {
                s = &s[..s.len() - 4]
            }
            let i = u128::from_str(s).unwrap();
            context.advance();
            CopyableVal_::U128(i)
        }
        Tok::U256Value => {
            let mut s = context.tokens.content();
            if s.ends_with("256") {
                s = &s[..s.len() - 4]
            }
            let i = u256::U256::from_str(s).unwrap();
            context.advance();
            CopyableVal_::U256(i)
        }
        Tok::ByteArrayValue => {
            let s = context.tokens.content();
            let buf = hex::decode(&s[2..s.len() - 1]).unwrap_or_else(|_| {
                // The lexer guarantees this, but tracking this knowledge all the way to here is tedious
                unreachable!("The string {:?} is not a valid hex-encoded byte array", s)
            });
            context.advance();
            CopyableVal_::ByteArray(buf)
        }
        t => {
            return Err(error(
                current_token_loc(context),
                format!("unrecognized token kind {:?}", t),
            ));
        }
    };
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, val))
}

// Get the precedence of a binary operator. The minimum precedence value
// is 1, and larger values have higher precedence. For tokens that are not
// binary operators, this returns a value of zero so that they will be
// below the minimum value and will mark the end of the binary expression
// for the code in parse_rhs_of_binary_exp.
// Precedences are not sequential to make it easier to add new binops without
// renumbering everything.
fn get_precedence(token: Tok) -> u32 {
    match token {
        // Reserved minimum precedence value is 1 (specified in parse_exp_)
        // TODO
        // Tok::EqualEqualGreater may not work right,
        // since parse_spec_exp calls parse_rhs_of_spec_exp
        // with min_prec = 1.  So parse_spec_expr will stop parsing instead of reading ==>
        Tok::EqualEqualGreater => 1,
        Tok::PipePipe => 5,
        Tok::AmpAmp => 10,
        Tok::EqualEqual => 15,
        Tok::ExclaimEqual => 15,
        Tok::Less => 15,
        Tok::Greater => 15,
        Tok::LessEqual => 15,
        Tok::GreaterEqual => 15,
        Tok::Pipe => 25,
        Tok::Caret => 30,
        Tok::Amp => 35,
        Tok::LessLess => 40,
        Tok::GreaterGreater => 40,
        Tok::Plus => 45,
        Tok::Minus => 45,
        Tok::Star => 50,
        Tok::Slash => 50,
        Tok::Percent => 50,
        _ => 0, // anything else is not a binary operator
    }
}

fn parse_exp(context: &mut Context) -> Result<Exp> {
    let lhs = parse_unary_exp(context)?;
    parse_rhs_of_binary_exp(context, lhs, /* min_prec */ 1)
}

fn parse_rhs_of_binary_exp(context: &mut Context, lhs: Exp, min_prec: u32) -> Result<Exp> {
    let mut result = lhs;
    let mut next_tok_prec = get_precedence(context.tokens.peek());

    // Continue parsing binary expressions as long as they have they
    // specified minimum precedence.
    while next_tok_prec >= min_prec {
        let op_token = context.tokens.peek();
        context.advance();

        let mut rhs = parse_unary_exp(context)?;

        // If the next token is another binary operator with a higher
        // precedence, then recursively parse that expression as the RHS.
        let this_prec = next_tok_prec;
        next_tok_prec = get_precedence(context.tokens.peek());
        if this_prec < next_tok_prec {
            rhs = parse_rhs_of_binary_exp(context, rhs, this_prec + 1)?;
            next_tok_prec = get_precedence(context.tokens.peek());
        }

        let op = match op_token {
            Tok::EqualEqual => BinOp::Eq,
            Tok::ExclaimEqual => BinOp::Neq,
            Tok::Less => BinOp::Lt,
            Tok::Greater => BinOp::Gt,
            Tok::LessEqual => BinOp::Le,
            Tok::GreaterEqual => BinOp::Ge,
            Tok::PipePipe => BinOp::Or,
            Tok::AmpAmp => BinOp::And,
            Tok::Caret => BinOp::Xor,
            Tok::LessLess => BinOp::Shl,
            Tok::GreaterGreater => BinOp::Shr,
            Tok::Pipe => BinOp::BitOr,
            Tok::Amp => BinOp::BitAnd,
            Tok::Plus => BinOp::Add,
            Tok::Minus => BinOp::Sub,
            Tok::Star => BinOp::Mul,
            Tok::Slash => BinOp::Div,
            Tok::Percent => BinOp::Mod,
            _ => panic!("Unexpected token that is not a binary operator"),
        };
        let start_loc = result.loc.start();
        let end_loc = context.tokens.previous_end_loc();
        let e = Exp_::BinopExp(Box::new(result), op, Box::new(rhs));
        result = spanned(context.tokens.file_hash(), start_loc as usize, end_loc, e);
    }

    Ok(result)
}

// QualifiedFunctionName : FunctionCall = {
//     <f: Builtin> => FunctionCall::Builtin(f),
//     <module_dot_name: DotName> <type_actuals: TypeActuals> =>? { ... }
// }

fn parse_qualified_function_name(context: &mut Context) -> Result<FunctionCall> {
    let start_loc = context.tokens.start_loc();
    let call = match context.tokens.peek() {
        Tok::VecPack(_)
        | Tok::VecLen
        | Tok::VecImmBorrow
        | Tok::VecMutBorrow
        | Tok::VecPushBack
        | Tok::VecPopBack
        | Tok::VecUnpack(_)
        | Tok::VecSwap
        | Tok::Freeze
        | Tok::ToU8
        | Tok::ToU16
        | Tok::ToU32
        | Tok::ToU64
        | Tok::ToU128
        | Tok::ToU256 => {
            let f = parse_builtin(context)?;
            FunctionCall_::Builtin(f)
        }
        Tok::DotNameValue => {
            let module_dot_name = parse_dot_name(context)?;
            let type_actuals = parse_type_actuals(context)?;
            let v: Vec<&str> = module_dot_name.split('.').collect();
            assert!(v.len() == 2);
            FunctionCall_::ModuleFunctionCall {
                module: ModuleName(Symbol::from(v[0])),
                name: FunctionName(Symbol::from(v[1])),
                type_actuals,
            }
        }
        t => {
            return Err(invalid_token(
                current_token_loc(context),
                format!(
                    "unrecognized token kind for qualified function name {:?}",
                    t
                ),
            ));
        }
    };
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(
        context.tokens.file_hash(),
        start_loc,
        end_loc,
        call,
    ))
}

// UnaryExp : Exp = {
//     "!" <e: Sp<UnaryExp>> => Exp::UnaryExp(UnaryOp::Not, Box::new(e)),
//     "*" <e: Sp<UnaryExp>> => Exp::Dereference(Box::new(e)),
//     "&mut " <e: Sp<UnaryExp>> "." <f: Field> => { ... },
//     "&" <e: Sp<UnaryExp>> "." <f: Field> => { ... },
//     CallOrTerm,
// }

fn parse_borrow_field_(context: &mut Context, mutable: bool) -> Result<Exp_> {
    // This could be either a field borrow (from UnaryExp) or
    // a borrow of a local variable (from Term). In the latter case,
    // only a simple name token is allowed, and it must not be
    // the start of a pack expression.
    let e = if context.tokens.peek() == Tok::NameValue {
        if context.tokens.lookahead()? != Tok::LBrace {
            let var = parse_var(context)?;
            return Ok(Exp_::BorrowLocal(mutable, var));
        }
        let start_loc = context.tokens.start_loc();
        let name = parse_name(context)?;
        let end_loc = context.tokens.previous_end_loc();
        let type_actuals: Vec<Type> = vec![];
        spanned(
            context.tokens.file_hash(),
            start_loc,
            end_loc,
            parse_pack_(context, name, type_actuals)?,
        )
    } else {
        parse_unary_exp(context)?
    };
    consume_token(context, Tok::Period)?;
    let field = parse_field_ident(context)?;
    Ok(Exp_::Borrow {
        is_mutable: mutable,
        exp: Box::new(e),
        field,
    })
}

fn parse_unary_exp_(context: &mut Context) -> Result<Exp_> {
    match context.tokens.peek() {
        Tok::Exclaim => {
            context.advance();
            let e = parse_unary_exp(context)?;
            Ok(Exp_::UnaryExp(UnaryOp::Not, Box::new(e)))
        }
        Tok::Star => {
            context.advance();
            let e = parse_unary_exp(context)?;
            Ok(Exp_::Dereference(Box::new(e)))
        }
        Tok::AmpMut => {
            context.advance();
            parse_borrow_field_(context, true)
        }
        Tok::Amp => {
            context.advance();
            parse_borrow_field_(context, false)
        }
        _ => parse_call_or_term_(context),
    }
}

fn parse_unary_exp(context: &mut Context) -> Result<Exp> {
    let start_loc = context.tokens.start_loc();
    let e = parse_unary_exp_(context)?;
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, e))
}

// Call: Exp = {
//     <f: Sp<QualifiedFunctionName>> <exp: Sp<CallOrTerm>> => Exp::FunctionCall(f, Box::new(exp)),
// }

fn parse_call(context: &mut Context, f: FunctionCall, start_loc: usize) -> Result<Exp> {
    let exp = parse_call_or_term(context)?;
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(
        context.tokens.file_hash(),
        start_loc,
        end_loc,
        Exp_::FunctionCall(f, Box::new(exp)),
    ))
}

// CallOrTerm: Exp = {
//     <f: Sp<QualifiedFunctionName>> <exp: Sp<CallOrTerm>> => Exp::FunctionCall(f, Box::new(exp)),
//     Term,
// }

fn parse_call_or_term_(context: &mut Context) -> Result<Exp_> {
    match context.tokens.peek() {
        Tok::VecPack(_)
        | Tok::VecLen
        | Tok::VecImmBorrow
        | Tok::VecMutBorrow
        | Tok::VecPushBack
        | Tok::VecPopBack
        | Tok::VecUnpack(_)
        | Tok::VecSwap
        | Tok::Freeze
        | Tok::ToU8
        | Tok::ToU16
        | Tok::ToU32
        | Tok::ToU64
        | Tok::ToU128
        | Tok::ToU256 => {
            let f = parse_qualified_function_name(context)?;
            let exp = parse_call_or_term(context)?;
            Ok(Exp_::FunctionCall(f, Box::new(exp)))
        }
        Tok::DotNameValue => {
            let f = parse_qualified_function_name(context)?;
            if context.tokens.peek() == Tok::LBrace {
                let FunctionCall_::ModuleFunctionCall {
                    module: ModuleName(enum_name),
                    name: FunctionName(variant_name),
                    type_actuals,
                } = f.value
                else {
                    return Err(invalid_token(f.loc, "Invalid variant pack call"));
                };
                parse_variant_pack_(context, enum_name, variant_name, type_actuals)
            } else {
                let exp = parse_call_or_term(context)?;
                Ok(Exp_::FunctionCall(f, Box::new(exp)))
            }
        }
        _ => parse_term_(context),
    }
}

fn parse_call_or_term(context: &mut Context) -> Result<Exp> {
    let start_loc = context.tokens.start_loc();
    let v = parse_call_or_term_(context)?;
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, v))
}

// FieldExp: (Field_, Exp_) = {
//     <f: Sp<Field>> ":" <e: Sp<Exp>> => (f, e)
// }

fn parse_field_exp(context: &mut Context) -> Result<(Field, Exp)> {
    let f = parse_field(context)?;
    consume_token(context, Tok::Colon)?;
    let e = parse_exp(context)?;
    Ok((f, e))
}

// Term: Exp = {
//     "move(" <v: Sp<Var>> ")" => Exp::Move(v),
//     "copy(" <v: Sp<Var>> ")" => Exp::Copy(v),
//     "&mut " <v: Sp<Var>> => Exp::BorrowLocal(true, v),
//     "&" <v: Sp<Var>> => Exp::BorrowLocal(false, v),
//     Sp<CopyableVal> => Exp::Value(<>),
//     <name_and_type_actuals: NameAndTypeActuals> "{" <fs:Comma<FieldExp>> "}" =>? { ... },
//     "(" <exps: Comma<Sp<Exp>>> ")" => Exp::ExprList(exps),
// }

fn parse_pack_(context: &mut Context, name: Symbol, type_actuals: Vec<Type>) -> Result<Exp_> {
    consume_token(context, Tok::LBrace)?;
    let fs = parse_comma_list(context, &[Tok::RBrace], parse_field_exp, true)?;
    consume_token(context, Tok::RBrace)?;
    Ok(Exp_::Pack(
        DatatypeName(name),
        type_actuals,
        fs.into_iter().collect::<Vec<_>>(),
    ))
}

fn parse_variant_pack_(
    context: &mut Context,
    enum_name: Symbol,
    variant_name: Symbol,
    type_actuals: Vec<Type>,
) -> Result<Exp_> {
    consume_token(context, Tok::LBrace)?;
    let fs = parse_comma_list(context, &[Tok::RBrace], parse_field_exp, true)?;
    consume_token(context, Tok::RBrace)?;
    Ok(Exp_::PackVariant(
        DatatypeName(enum_name),
        VariantName(variant_name),
        type_actuals,
        fs.into_iter().collect::<Vec<_>>(),
    ))
}

fn parse_term_(context: &mut Context) -> Result<Exp_> {
    match context.tokens.peek() {
        Tok::Move => {
            context.advance();
            let v = parse_var(context)?;
            consume_token(context, Tok::RParen)?;
            Ok(Exp_::Move(v))
        }
        Tok::Copy => {
            context.advance();
            let v = parse_var(context)?;
            consume_token(context, Tok::RParen)?;
            Ok(Exp_::Copy(v))
        }
        Tok::AmpMut => {
            context.advance();
            let v = parse_var(context)?;
            Ok(Exp_::BorrowLocal(true, v))
        }
        Tok::Amp => {
            context.advance();
            let v = parse_var(context)?;
            Ok(Exp_::BorrowLocal(false, v))
        }
        Tok::AccountAddressValue
        | Tok::True
        | Tok::False
        | Tok::U8Value
        | Tok::U16Value
        | Tok::U32Value
        | Tok::U64Value
        | Tok::U128Value
        | Tok::U256Value
        | Tok::ByteArrayValue => Ok(Exp_::Value(parse_copyable_val(context)?)),
        Tok::NameValue | Tok::NameBeginTyValue => {
            let (name, type_actuals) = parse_name_and_type_actuals(context)?;
            parse_pack_(context, name, type_actuals)
        }
        Tok::LParen => {
            context.advance();
            let exps = parse_comma_list(context, &[Tok::RParen], parse_exp, true)?;
            consume_token(context, Tok::RParen)?;
            Ok(Exp_::ExprList(exps))
        }
        Tok::At => {
            context.advance();
            let address = parse_account_address(context)?;
            Ok(Exp_::address(address).value)
        }
        t => Err(invalid_token(
            current_token_loc(context),
            format!("unrecognized token kind for term {:?}", t),
        )),
    }
}

// QualifiedStructIdent : QualifiedStructIdent = {
//     <module_dot_struct: DotName> =>? { ... }
// }

fn parse_qualified_struct_ident(context: &mut Context) -> Result<QualifiedDatatypeIdent> {
    let module_dot_struct = parse_dot_name(context)?;
    let v: Vec<&str> = module_dot_struct.split('.').collect();
    assert!(v.len() == 2);
    let m: ModuleName = ModuleName(Symbol::from(v[0]));
    let n: DatatypeName = DatatypeName(Symbol::from(v[1]));
    Ok(QualifiedDatatypeIdent::new(m, n))
}

// ModuleName: ModuleName = {
//     <n: Name> =>? ModuleName::parse(n),
// }

fn parse_module_name(context: &mut Context) -> Result<ModuleName> {
    Ok(ModuleName(parse_name(context)?))
}

// Builtin: Builtin = {
//     "exists<" <name_and_type_actuals: NameAndTypeActuals> ">" =>? { ... },
//     "borrow_global<" <name_and_type_actuals: NameAndTypeActuals> ">" =>? { ... },
//     "borrow_global_mut<" <name_and_type_actuals: NameAndTypeActuals> ">" =>? { ... },
//     "move_to<" <name_and_type_actuals: NameAndTypeActuals> ">" =>? { ... },
//     "move_from<" <name_and_type_actuals: NameAndTypeActuals> ">" =>? { ... },
//     "vec_*<" <type_actuals: TypeActuals> ">" =>? { ... },
//     "freeze" => Builtin::Freeze,
// }

fn parse_builtin(context: &mut Context) -> Result<Builtin> {
    match context.tokens.peek() {
        Tok::VecPack(num) => {
            context.advance();
            let type_actuals = parse_type_actuals(context)?;
            Ok(Builtin::VecPack(type_actuals, num))
        }
        Tok::VecLen => {
            context.advance();
            let type_actuals = parse_type_actuals(context)?;
            Ok(Builtin::VecLen(type_actuals))
        }
        Tok::VecImmBorrow => {
            context.advance();
            let type_actuals = parse_type_actuals(context)?;
            Ok(Builtin::VecImmBorrow(type_actuals))
        }
        Tok::VecMutBorrow => {
            context.advance();
            let type_actuals = parse_type_actuals(context)?;
            Ok(Builtin::VecMutBorrow(type_actuals))
        }
        Tok::VecPushBack => {
            context.advance();
            let type_actuals = parse_type_actuals(context)?;
            Ok(Builtin::VecPushBack(type_actuals))
        }
        Tok::VecPopBack => {
            context.advance();
            let type_actuals = parse_type_actuals(context)?;
            Ok(Builtin::VecPopBack(type_actuals))
        }
        Tok::VecUnpack(num) => {
            context.advance();
            let type_actuals = parse_type_actuals(context)?;
            Ok(Builtin::VecUnpack(type_actuals, num))
        }
        Tok::VecSwap => {
            context.advance();
            let type_actuals = parse_type_actuals(context)?;
            Ok(Builtin::VecSwap(type_actuals))
        }
        Tok::Freeze => {
            context.advance();
            Ok(Builtin::Freeze)
        }
        Tok::ToU8 => {
            context.advance();
            Ok(Builtin::ToU8)
        }
        Tok::ToU16 => {
            context.advance();
            Ok(Builtin::ToU16)
        }
        Tok::ToU32 => {
            context.advance();
            Ok(Builtin::ToU32)
        }
        Tok::ToU64 => {
            context.advance();
            Ok(Builtin::ToU64)
        }
        Tok::ToU128 => {
            context.advance();
            Ok(Builtin::ToU128)
        }
        Tok::ToU256 => {
            context.advance();
            Ok(Builtin::ToU256)
        }
        t => Err(invalid_token(
            current_token_loc(context),
            format!("unrecognized token kind for builtin {:?}", t),
        )),
    }
}

// LValue: LValue = {
//     <l:Sp<Var>> => LValue::Var(l),
//     "*" <e: Sp<Exp>> => LValue::Mutate(e),
//     "_" => LValue::Pop,
// }

fn parse_lvalue_(context: &mut Context) -> Result<LValue_> {
    match context.tokens.peek() {
        Tok::NameValue => {
            let l = parse_var(context)?;
            Ok(LValue_::Var(l))
        }
        Tok::Star => {
            context.advance();
            let e = parse_exp(context)?;
            Ok(LValue_::Mutate(e))
        }
        Tok::Underscore => {
            context.advance();
            Ok(LValue_::Pop)
        }
        t => Err(error(
            current_token_loc(context),
            format!("unrecognized token kind for lvalue {:?}", t),
        )),
    }
}

fn parse_lvalue(context: &mut Context) -> Result<LValue> {
    let start_loc = context.tokens.start_loc();
    let lv = parse_lvalue_(context)?;
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, lv))
}

// FieldBindings: (Field_, Var_) = {
//     <f: Sp<Field>> ":" <v: Sp<Var>> => (f, v),
//     <f: Sp<Field>> => { ... }
// }

fn parse_field_bindings(context: &mut Context) -> Result<(Field, Var)> {
    let f = parse_field(context)?;
    if context.tokens.peek() == Tok::Colon {
        context.advance(); // consume the colon
        let v = parse_var(context)?;
        Ok((f, v))
    } else {
        Ok((
            f.clone(),
            Spanned {
                loc: f.loc,
                value: Var_(f.value.0),
            },
        ))
    }
}

// pub Cmd : Cmd = {
//     <lvalues: Comma<Sp<LValue>>> "=" <e: Sp<Exp>> => Cmd::Assign(lvalues, e),
//     <name_and_type_actuals: NameAndTypeActuals> "{" <bindings: Comma<FieldBindings>> "}" "=" <e: Sp<Exp>> =>? { ... },
//     "abort" <err: Sp<Exp>?> => { ... },
//     "return" <v: Comma<Sp<Exp>>> => Cmd::Return(Box::new(Spanned::unsafe_no_loc(Exp::ExprList(v)))),
//     "continue" => Cmd::Continue,
//     "break" => Cmd::Break,
//     <Sp<Call>> => Cmd::Exp(Box::new(<>)),
//     "(" <Comma<Sp<Exp>>> ")" => Cmd::Exp(Box::new(Spanned::unsafe_no_loc(Exp::ExprList(<>)))),
// }

fn parse_assign_(context: &mut Context) -> Result<Statement_> {
    let lvalues = parse_comma_list(context, &[Tok::Equal], parse_lvalue, false)?;
    if lvalues.is_empty() {
        return Err(invalid_token(
            current_token_loc(context),
            "could not parse lvalues in assignment",
        ));
    }
    consume_token(context, Tok::Equal)?;
    let e = parse_exp(context)?;
    Ok(Statement_::Assign(lvalues, e))
}

fn parse_unpack_(
    context: &mut Context,
    name: Symbol,
    type_actuals: Vec<Type>,
) -> Result<Statement_> {
    consume_token(context, Tok::LBrace)?;
    let bindings = parse_comma_list(context, &[Tok::RBrace], parse_field_bindings, true)?;
    consume_token(context, Tok::RBrace)?;
    consume_token(context, Tok::Equal)?;
    let e = parse_exp(context)?;
    Ok(Statement_::Unpack(
        DatatypeName(name),
        type_actuals,
        bindings.into_iter().collect(),
        Box::new(e),
    ))
}

// <enum>.<variant>("<" <type_actuals> ">")? { <bindings> } (&|&mut)? = <exp>
fn parse_variant_unpack_(
    context: &mut Context,
    enum_name: Symbol,
    variant_name: Symbol,
    type_actuals: Vec<Type>,
    unpack_type: UnpackType,
) -> Result<Statement_> {
    consume_token(context, Tok::LBrace)?;
    let bindings = parse_comma_list(context, &[Tok::RBrace], parse_field_bindings, true)?;
    consume_token(context, Tok::RBrace)?;
    consume_token(context, Tok::Equal)?;
    let e = parse_exp(context)?;
    Ok(Statement_::UnpackVariant(
        DatatypeName(enum_name),
        VariantName(variant_name),
        type_actuals,
        bindings.into_iter().collect(),
        Box::new(e),
        unpack_type,
    ))
}

// variant_switch <enum_name> e { (<variant_name> => <lbl>)* }
fn parse_variant_switch_(context: &mut Context) -> Result<Statement_> {
    let name = parse_name(context)?;
    let e = parse_exp(context)?;
    consume_token(context, Tok::LBrace)?;
    let lbls = parse_comma_list(context, &[Tok::RBrace], parse_variant_switch_arm, true)?;
    consume_token(context, Tok::RBrace)?;
    Ok(Statement_::VariantSwitch(
        DatatypeName(name),
        lbls,
        Box::new(e),
    ))
}

// <variant_name> : <lbl>
fn parse_variant_switch_arm(context: &mut Context) -> Result<(VariantName, BlockLabel)> {
    let v = parse_name(context)?;
    consume_token(context, Tok::Colon)?;
    let lbl = parse_label(context)?;
    Ok((VariantName(v), lbl))
}

/// Parses a statement.
fn parse_statement_(context: &mut Context) -> Result<Statement_> {
    match context.tokens.peek() {
        Tok::Abort => {
            context.advance();
            let val = if context.tokens.peek() == Tok::Semicolon {
                None
            } else {
                Some(Box::new(parse_exp(context)?))
            };
            Ok(Statement_::Abort(val))
        }
        Tok::Assert => {
            context.advance();
            let e = parse_exp(context)?;
            consume_token(context, Tok::Comma)?;
            let err = parse_exp(context)?;
            consume_token(context, Tok::RParen)?;
            let cond = {
                let loc = e.loc;
                sp(loc, Exp_::UnaryExp(UnaryOp::Not, Box::new(e)))
            };
            Ok(Statement_::Assert(Box::new(cond), Box::new(err)))
        }
        Tok::Jump => {
            consume_token(context, Tok::Jump)?;
            Ok(Statement_::Jump(parse_label(context)?))
        }
        Tok::JumpIf => {
            consume_token(context, Tok::JumpIf)?;
            consume_token(context, Tok::LParen)?;
            let cond = parse_exp(context)?;
            consume_token(context, Tok::RParen)?;
            Ok(Statement_::JumpIf(Box::new(cond), parse_label(context)?))
        }
        Tok::JumpIfFalse => {
            consume_token(context, Tok::JumpIfFalse)?;
            consume_token(context, Tok::LParen)?;
            let cond = parse_exp(context)?;
            consume_token(context, Tok::RParen)?;
            Ok(Statement_::JumpIfFalse(
                Box::new(cond),
                parse_label(context)?,
            ))
        }
        Tok::NameValue => {
            // This could be either an LValue for an assignment or
            // NameAndTypeActuals (with no type_actuals) for an unpack.
            if context.tokens.lookahead()? == Tok::LBrace {
                let name = parse_name(context)?;
                parse_unpack_(context, name, vec![])
            } else {
                parse_assign_(context)
            }
        }
        Tok::Return => {
            context.advance();
            let start = context.tokens.start_loc();
            let v = parse_comma_list(context, &[Tok::Semicolon], parse_exp, true)?;
            let end = context.tokens.start_loc();
            Ok(Statement_::Return(Box::new(spanned(
                context.tokens.file_hash(),
                start,
                end,
                Exp_::ExprList(v),
            ))))
        }
        Tok::Star | Tok::Underscore => parse_assign_(context),
        Tok::NameBeginTyValue => {
            let (name, tys) = parse_name_and_type_actuals(context)?;
            parse_unpack_(context, name, tys)
        }
        Tok::VariantSwitch => {
            consume_token(context, Tok::VariantSwitch)?;
            parse_variant_switch_(context)
        }
        Tok::VecPack(_)
        | Tok::VecLen
        | Tok::VecImmBorrow
        | Tok::VecMutBorrow
        | Tok::VecPushBack
        | Tok::VecPopBack
        | Tok::VecUnpack(_)
        | Tok::VecSwap
        | Tok::Freeze
        | Tok::ToU8
        | Tok::ToU16
        | Tok::ToU32
        | Tok::ToU64
        | Tok::ToU128
        | Tok::DotNameValue
        | Tok::ToU256 => {
            let start_loc = context.tokens.start_loc();
            let f = parse_qualified_function_name(context)?;
            if context.tokens.peek() == Tok::LBrace {
                let FunctionCall_::ModuleFunctionCall {
                    module: ModuleName(enum_name),
                    name: FunctionName(variant_name),
                    type_actuals,
                } = f.value
                else {
                    return Err(error(f.loc, "Invalid variant unpack call"));
                };
                parse_variant_unpack_(
                    context,
                    enum_name,
                    variant_name,
                    type_actuals,
                    UnpackType::ByValue,
                )
            } else {
                Ok(Statement_::Exp(Box::new(parse_call(
                    context, f, start_loc,
                )?)))
            }
        }
        x @ (Tok::Amp | Tok::AmpMut) => {
            let start_loc = current_token_loc(context);
            context.advance();
            let f = parse_qualified_function_name(context)?;
            if context.tokens.peek() == Tok::LBrace {
                let FunctionCall_::ModuleFunctionCall {
                    module: ModuleName(enum_name),
                    name: FunctionName(variant_name),
                    type_actuals,
                } = f.value
                else {
                    return Err(invalid_token(f.loc, "Invalid variant unpack call"));
                };
                let unpack_type = match x {
                    Tok::Amp => UnpackType::ByImmRef,
                    Tok::AmpMut => UnpackType::ByMutRef,
                    _ => unreachable!(),
                };
                parse_variant_unpack_(context, enum_name, variant_name, type_actuals, unpack_type)
            } else {
                Err(invalid_token(
                    start_loc,
                    format!("invalid token kind for statement {:?}", x),
                ))
            }
        }
        Tok::LParen => {
            context.advance();
            let start = context.tokens.start_loc();
            let v = parse_comma_list(context, &[Tok::RParen], parse_exp, true)?;
            consume_token(context, Tok::RParen)?;
            let end = context.tokens.start_loc();
            Ok(Statement_::Exp(Box::new(spanned(
                context.tokens.file_hash(),
                start,
                end,
                Exp_::ExprList(v),
            ))))
        }
        t => Err(invalid_token(
            current_token_loc(context),
            format!("invalid token kind for statement {:?}", t),
        )),
    }
}

/// Parses a statement with its location.
fn parse_statement(context: &mut Context) -> Result<Statement> {
    let start_loc = context.tokens.start_loc();
    let c = parse_statement_(context)?;
    let end_loc = context.tokens.previous_end_loc();
    let cmd = spanned(context.tokens.file_hash(), start_loc, end_loc, c);
    consume_token(context, Tok::Semicolon)?;
    Ok(cmd)
}

/// Parses a label declaration for a block, e.g.: `label b0:`.
fn parse_block_label(context: &mut Context) -> Result<BlockLabel> {
    consume_token(context, Tok::Label)?;
    let label = parse_label(context)?;
    consume_token(context, Tok::Colon)?;
    Ok(label)
}

/// Parses a label identifier, e.g.: the `b0` in the statement `jump b0;`.
fn parse_label(context: &mut Context) -> Result<BlockLabel> {
    let start = context.tokens.start_loc();
    let name = parse_name(context)?;
    let end = context.tokens.previous_end_loc();
    Ok(spanned(
        context.tokens.file_hash(),
        start,
        end,
        BlockLabel_(name),
    ))
}

/// Parses a sequence of blocks, such as would appear within the `{` and `}` delimiters of a
/// function body.
fn parse_blocks(context: &mut Context) -> Result<Vec<Block>> {
    let mut blocks = vec![];
    while context.tokens.peek() != Tok::RBrace {
        blocks.push(parse_block(context)?);
    }
    Ok(blocks)
}

/// Parses a block: its block label `label b:`, and a sequence of 0 or more statements.
fn parse_block(context: &mut Context) -> Result<Block> {
    let start_loc = context.tokens.start_loc();
    let label = parse_block_label(context)?;
    let mut statements = vec![];
    while !matches!(context.tokens.peek(), Tok::Label | Tok::RBrace) {
        statements.push(parse_statement(context)?);
    }
    Ok(spanned(
        context.tokens.file_hash(),
        start_loc,
        context.tokens.previous_end_loc(),
        Block_::new(label, statements),
    ))
}

// Declaration: (Var_, Type) = {
//   "let" <v: Sp<Var>> ":" <t: Type> ";" => (v, t),
// }

fn parse_declaration(context: &mut Context) -> Result<(Var, Type)> {
    consume_token(context, Tok::Let)?;
    let v = parse_var(context)?;
    consume_token(context, Tok::Colon)?;
    let t = parse_type(context)?;
    consume_token(context, Tok::Semicolon)?;
    Ok((v, t))
}

// Declarations: Vec<(Var_, Type)> = {
//     <Declaration*>
// }

fn parse_declarations(context: &mut Context) -> Result<Vec<(Var, Type)>> {
    let mut decls: Vec<(Var, Type)> = vec![];
    // Declarations always begin with the "let" token so continue parsing
    // them until we hit something else.
    while context.tokens.peek() == Tok::Let {
        decls.push(parse_declaration(context)?);
    }
    Ok(decls)
}

// FunctionBlock: (Vec<(Var_, Type)>, Block) = {
//     "{" <locals: Declarations> <stmts: Statements> "}" => (locals, Block::new(stmts))
// }

fn parse_function_block_(context: &mut Context) -> Result<(Vec<(Var, Type)>, Vec<Block>)> {
    consume_token(context, Tok::LBrace)?;
    let locals = parse_declarations(context)?;
    let statements = parse_blocks(context)?;
    consume_token(context, Tok::RBrace)?;
    Ok((locals, statements))
}

fn token_to_ability(token: Tok, contents: &str) -> Option<Ability> {
    match (token, contents) {
        (Tok::Copy, _) => Some(Ability::Copy),
        (Tok::NameValue, Ability::DROP) => Some(Ability::Drop),
        (Tok::NameValue, Ability::STORE) => Some(Ability::Store),
        (Tok::NameValue, Ability::KEY) => Some(Ability::Key),
        _ => None,
    }
}

// Ability: Ability = {
//     "copy" => Ability::Copy,
//     "drop" => Ability::Drop,
//     "store" => Ability::Store,
//     "key" => Ability::Key,
// }
fn parse_ability(context: &mut Context) -> Result<(Ability, Loc)> {
    let a = match token_to_ability(context.tokens.peek(), context.tokens.content()) {
        Some(a) => (a, current_token_loc(context)),
        None => {
            return Err(invalid_token(
                current_token_loc(context),
                "could not parse ability",
            ));
        }
    };
    context.advance();
    Ok(a)
}

// Type: Type = {
//     "address" => Type::Address,
//     "signer" => Type::Signer,
//     "u64" => Type::U64,
//     "bool" => Type::Bool,
//     "bytearray" => Type::ByteArray,
//     <s: QualifiedStructIdent> <tys: TypeActuals> => Type::Struct(s, tys),
//     "&" <t: Type> => Type::Reference(false, Box::new(t)),
//     "&mut " <t: Type> => Type::Reference(true, Box::new(t)),
//     <n: Name> =>? Ok(Type::TypeParameter(TypeVar::parse(n)?)),
// }

fn parse_type(context: &mut Context) -> Result<Type> {
    let start_loc = context.tokens.start_loc();
    let t = match context.tokens.peek() {
        Tok::NameValue if matches!(context.tokens.content(), "address") => {
            context.advance();
            Type_::Address
        }
        Tok::NameValue if matches!(context.tokens.content(), "u8") => {
            context.advance();
            Type_::U8
        }
        Tok::NameValue if matches!(context.tokens.content(), "u16") => {
            context.advance();
            Type_::U16
        }
        Tok::NameValue if matches!(context.tokens.content(), "u32") => {
            context.advance();
            Type_::U32
        }
        Tok::NameValue if matches!(context.tokens.content(), "u64") => {
            context.advance();
            Type_::U64
        }
        Tok::NameValue if matches!(context.tokens.content(), "u128") => {
            context.advance();
            Type_::U128
        }
        Tok::NameValue if matches!(context.tokens.content(), "u256") => {
            context.advance();
            Type_::U256
        }
        Tok::NameValue if matches!(context.tokens.content(), "bool") => {
            context.advance();
            Type_::Bool
        }
        Tok::NameValue if matches!(context.tokens.content(), "signer") => {
            context.advance();
            Type_::Signer
        }
        Tok::NameBeginTyValue if matches!(context.tokens.content(), "vector<") => {
            context.advance();
            let ty = parse_type(context)?;
            adjust_token(context, &[Tok::Greater])?;
            consume_token(context, Tok::Greater)?;
            Type_::Vector(Box::new(ty))
        }
        Tok::DotNameValue => {
            let s = parse_qualified_struct_ident(context)?;
            let tys = parse_type_actuals(context)?;
            Type_::Datatype(s, tys)
        }
        Tok::Amp => {
            context.advance();
            Type_::Reference(false, Box::new(parse_type(context)?))
        }
        Tok::AmpMut => {
            context.advance();
            Type_::Reference(true, Box::new(parse_type(context)?))
        }
        Tok::NameValue => Type_::TypeParameter(TypeVar_(parse_name(context)?)),
        t => {
            return Err(invalid_token(
                current_token_loc(context),
                format!("invalid token kind for type {:?}", t),
            ));
        }
    };
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, t))
}

// TypeVar: TypeVar = {
//     <n: Name> =>? TypeVar::parse(n),
// }
// TypeVar_ = Sp<TypeVar>;

fn parse_type_var(context: &mut Context) -> Result<TypeVar> {
    let start_loc = context.tokens.start_loc();
    let type_var = TypeVar_(parse_name(context)?);
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(
        context.tokens.file_hash(),
        start_loc,
        end_loc,
        type_var,
    ))
}

fn parse_type_parameter_with_phantom_decl(context: &mut Context) -> Result<DatatypeTypeParameter> {
    let is_phantom =
        if context.tokens.peek() == Tok::NameValue && context.tokens.content() == "phantom" {
            context.advance();
            true
        } else {
            false
        };
    let (type_var, abilities) = parse_type_parameter(context)?;
    Ok((is_phantom, type_var, abilities))
}

// TypeFormal: (TypeVar_, Kind) = {
//     <type_var: Sp<TypeVar>> <k: (":" <Ability> ("+" <Ability>)*)?> =>? {
// }

fn parse_type_parameter(context: &mut Context) -> Result<(TypeVar, BTreeSet<Ability>)> {
    let type_var = parse_type_var(context)?;
    if context.tokens.peek() == Tok::Colon {
        context.advance(); // consume the ":"
        let abilities = parse_list(
            context,
            |context| {
                if context.tokens.peek() == Tok::Plus {
                    context.advance();
                    Ok(true)
                } else {
                    Ok(false)
                }
            },
            parse_ability,
        )?;
        let mut ability_set = BTreeSet::new();
        for (ability, location) in abilities {
            let was_new_element = ability_set.insert(ability);
            if !was_new_element {
                return Err(error(location, format!("Duplicate ability '{}'", ability)));
            }
        }
        Ok((type_var, ability_set))
    } else {
        Ok((type_var, BTreeSet::new()))
    }
}

// TypeActuals: Vec<Type> = {
//     <tys: ('<' <Comma<Type>> ">")?> => { ... }
// }

fn parse_type_actuals(context: &mut Context) -> Result<Vec<Type>> {
    let tys = if context.tokens.peek() == Tok::Less {
        context.advance(); // consume the '<'
        let list = parse_comma_list(context, &[Tok::Greater], parse_type, true)?;
        consume_token(context, Tok::Greater)?;
        list
    } else {
        vec![]
    };
    Ok(tys)
}

// NameAndTypeFormals: (String, Vec<(TypeVar_, Kind)>) = {
//     <n: NameBeginTy> <k: Comma<TypeFormal>> ">" => (n, k),
//     <n: Name> => (n, vec![]),
// }

fn parse_name_and_type_parameters<T, F>(
    context: &mut Context,
    param_parser: F,
) -> Result<(Symbol, Vec<T>)>
where
    F: Fn(&mut Context) -> Result<T>,
{
    let mut has_types = false;
    let n = if context.tokens.peek() == Tok::NameBeginTyValue {
        has_types = true;
        parse_name_begin_ty(context)?
    } else {
        parse_name(context)?
    };
    let k = if has_types {
        let list = parse_comma_list(context, &[Tok::Greater], param_parser, true)?;
        consume_token(context, Tok::Greater)?;
        list
    } else {
        vec![]
    };
    Ok((n, k))
}

// NameAndTypeActuals: (String, Vec<Type>) = {
//     <n: NameBeginTy> '<' <tys: Comma<Type>> ">" => (n, tys),
//     <n: Name> => (n, vec![]),
// }

fn parse_name_and_type_actuals(context: &mut Context) -> Result<(Symbol, Vec<Type>)> {
    let mut has_types = false;
    let n = if context.tokens.peek() == Tok::NameBeginTyValue {
        has_types = true;
        parse_name_begin_ty(context)?
    } else {
        parse_name(context)?
    };
    let tys = if has_types {
        let list = parse_comma_list(context, &[Tok::Greater], parse_type, true)?;
        consume_token(context, Tok::Greater)?;
        list
    } else {
        vec![]
    };
    Ok((n, tys))
}

// ArgDecl : (Var_, Type) = {
//     <v: Sp<Var>> ":" <t: Type> => (v, t)
// }

fn parse_arg_decl(context: &mut Context) -> Result<(Var, Type)> {
    let v = parse_var(context)?;
    consume_token(context, Tok::Colon)?;
    let t = parse_type(context)?;
    Ok((v, t))
}

// ReturnType: Vec<Type> = {
//     ":" <t: Type> <v: ("*" <Type>)*> => { ... }
// }

fn parse_return_type(context: &mut Context) -> Result<Vec<Type>> {
    consume_token(context, Tok::Colon)?;
    let t = parse_type(context)?;
    let mut v = vec![t];
    while context.tokens.peek() == Tok::Star {
        context.advance();
        v.push(parse_type(context)?);
    }
    Ok(v)
}

// FunctionVisibility : FunctionVisibility = {
//   (Public("("<v: Script | Friend>")")?)?
// }
fn parse_function_visibility(context: &mut Context) -> Result<FunctionVisibility> {
    let visibility = if match_token(context, Tok::Public)? {
        let sub_public_vis = if match_token(context, Tok::LParen)? {
            let sub_token = context.tokens.peek();
            match &sub_token {
                Tok::Script | Tok::Friend => (),
                t => {
                    return Err(invalid_token(
                        current_token_loc(context),
                        format!("expected 'script' or 'friend', not {:?}", t),
                    ));
                }
            }
            context.advance();
            consume_token(context, Tok::RParen)?;
            Some(sub_token)
        } else {
            None
        };
        match sub_public_vis {
            None => FunctionVisibility::Public,
            Some(Tok::Friend) => FunctionVisibility::Friend,
            _ => panic!("Unexpected token that is not a visibility modifier"),
        }
    } else {
        FunctionVisibility::Internal
    };
    Ok(visibility)
}

// FunctionDecl : (FunctionName, Function_) = {
//   <f: Sp<MoveFunctionDecl>> => (f.value.0, Spanned { span: f.loc, value: f.value.1 }),
//   <f: Sp<NativeFunctionDecl>> => (f.value.0, Spanned { span: f.loc, value: f.value.1 }),
// }

// MoveFunctionDecl : (FunctionName, Function) = {
//     <v: FunctionVisibility> <name_and_type_parameters: NameAndTypeFormals>
//     "(" <args: (ArgDecl)*> ")" <ret: ReturnType?>
//         <acquires: AcquireList?>
//         <locals_body: FunctionBlock> =>? { ... }
// }

// NativeFunctionDecl: (FunctionName, Function) = {
//     <nat: NativeTag> <v: FunctionVisibility> <name_and_type_parameters: NameAndTypeFormals>
//     "(" <args: Comma<ArgDecl>> ")" <ret: ReturnType?>
//         <acquires: AcquireList?>
//         ";" =>? { ... }
// }

fn parse_function_decl(context: &mut Context) -> Result<(FunctionName, Function)> {
    let start_loc = context.tokens.start_loc();

    let is_native = if context.tokens.peek() == Tok::Native {
        context.advance();
        true
    } else {
        false
    };

    let visibility = parse_function_visibility(context)?;
    let is_entry = if context.tokens.peek() == Tok::NameValue && context.tokens.content() == "entry"
    {
        context.advance();
        true
    } else {
        false
    };

    let (name, type_parameters) = parse_name_and_type_parameters(context, parse_type_parameter)?;
    consume_token(context, Tok::LParen)?;
    let args = parse_comma_list(context, &[Tok::RParen], parse_arg_decl, true)?;
    consume_token(context, Tok::RParen)?;

    let ret = if context.tokens.peek() == Tok::Colon {
        Some(parse_return_type(context)?)
    } else {
        None
    };

    let body = if is_native {
        consume_token(context, Tok::Semicolon)?;
        FunctionBody::Native
    } else {
        let (locals, body) = parse_function_block_(context)?;
        FunctionBody::Move { locals, code: body }
    };

    let end_loc = context.tokens.previous_end_loc();
    let func_name = FunctionName(name);
    let func = Function_::new(
        make_loc(context.tokens.file_hash(), start_loc, end_loc),
        visibility,
        is_entry,
        args,
        ret.unwrap_or_default(),
        type_parameters,
        body,
    );

    Ok((
        func_name,
        spanned(context.tokens.file_hash(), start_loc, end_loc, func),
    ))
}

// FieldDecl : (Field_, Type) = {
//     <f: Sp<Field>> ":" <t: Type> => (f, t)
// }

fn parse_field_decl(context: &mut Context) -> Result<(Field, Type)> {
    let f = parse_field(context)?;
    consume_token(context, Tok::Colon)?;
    let t = parse_type(context)?;
    Ok((f, t))
}

// StructDecl: StructDefinition_ = {
//     "struct" <name_and_type_parameters:
//     NameAndTypeFormals> ("has" <Ability> ("," <Ability)*)? "{" <data: Comma<FieldDecl>> "}"
//     =>? { ... }
//     <native: NativeTag> <name_and_type_parameters: NameAndTypeFormals>
//     ("has" <Ability> ("," <Ability)*)?";" =>? { ... }
// }
fn parse_struct_decl(context: &mut Context) -> Result<StructDefinition> {
    let start_loc = context.tokens.start_loc();

    let is_native = if context.tokens.peek() == Tok::Native {
        context.advance();
        true
    } else {
        false
    };

    consume_token(context, Tok::Struct)?;
    let (name, type_parameters) =
        parse_name_and_type_parameters(context, parse_type_parameter_with_phantom_decl)?;

    let mut abilities = BTreeSet::new();
    if context.tokens.peek() == Tok::NameValue && context.tokens.content() == "has" {
        context.advance();
        let abilities_vec = parse_comma_list(
            context,
            &[Tok::LBrace, Tok::Semicolon],
            parse_ability,
            false,
        )?;
        for (ability, location) in abilities_vec {
            let was_new_element = abilities.insert(ability);
            if !was_new_element {
                return Err(error(location, format!("Duplicate ability '{}'", ability)));
            }
        }
    }

    if is_native {
        consume_token(context, Tok::Semicolon)?;
        let end_loc = context.tokens.previous_end_loc();
        return Ok(spanned(
            context.tokens.file_hash(),
            start_loc,
            end_loc,
            StructDefinition_::native(abilities, name, type_parameters),
        ));
    }

    consume_token(context, Tok::LBrace)?;
    let fields = parse_comma_list(context, &[Tok::RBrace], parse_field_decl, true)?;
    consume_token(context, Tok::RBrace)?;
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(
        context.tokens.file_hash(),
        start_loc,
        end_loc,
        StructDefinition_::move_declared(abilities, name, type_parameters, fields),
    ))
}

// EnumDecl: EnumDefinition = {
//     "enum" <name_and_type_parameters:
//     NameAndTypeFormals> ("has" <Ability> ("," <Ability)*)? "{" <data: Comma<VariantDecl>> "}"
//     => { ... }
// }
fn parse_enum_decl(context: &mut Context) -> Result<EnumDefinition> {
    let start_loc = context.tokens.start_loc();

    consume_token(context, Tok::Enum)?;

    let (name, type_parameters) =
        parse_name_and_type_parameters(context, parse_type_parameter_with_phantom_decl)?;

    let mut abilities = BTreeSet::new();
    if context.tokens.peek() == Tok::NameValue && context.tokens.content() == "has" {
        context.advance();
        let abilities_vec = parse_comma_list(
            context,
            &[Tok::LBrace, Tok::Semicolon],
            parse_ability,
            false,
        )?;
        for (ability, location) in abilities_vec {
            let was_new_element = abilities.insert(ability);
            if !was_new_element {
                return Err(error(location, format!("Duplicate ability '{}'", ability)));
            }
        }
    }

    consume_token(context, Tok::LBrace)?;
    let variants = parse_comma_list(context, &[Tok::RBrace], parse_variant_decl, true)?;
    consume_token(context, Tok::RBrace)?;
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(
        context.tokens.file_hash(),
        start_loc,
        end_loc,
        EnumDefinition_::new(abilities, name, type_parameters, variants),
    ))
}

// VariantDecl: VariantDecl = {
//     <name_and_type_parameters:
//     NameAndTypeFormals> "{" <data: Comma<FieldDecl>> "}"
//     => { ... }
// }
fn parse_variant_decl(context: &mut Context) -> Result<VariantDefinition> {
    let start_loc = context.tokens.start_loc();

    let name = parse_name(context)?;

    consume_token(context, Tok::LBrace)?;
    let fields = parse_comma_list(context, &[Tok::RBrace], parse_field_decl, true)?;
    consume_token(context, Tok::RBrace)?;

    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(
        context.tokens.file_hash(),
        start_loc,
        end_loc,
        VariantDefinition_::new(name, fields),
    ))
}

// ModuleIdent: ModuleIdent = {
//     <a: AccountAddress> "." <m: ModuleName> => ModuleIdent::new(m, a),
// }

fn parse_module_ident(context: &mut Context) -> Result<ModuleIdent> {
    if context.tokens.peek() == Tok::DotNameValue {
        let start_loc = current_token_loc(context);
        let module_dot_name = parse_dot_name(context)?;
        let v: Vec<&str> = module_dot_name.split('.').collect();
        assert!(v.len() == 2);
        let address = parse_address_literal(context, v[0], start_loc)?;
        return Ok(ModuleIdent::new(ModuleName(Symbol::from(v[1])), address));
    }
    let a = parse_account_address(context)?;
    consume_token(context, Tok::Period)?;
    let m = parse_module_name(context)?;
    Ok(ModuleIdent::new(m, a))
}

// FriendDecl: ModuleIdent = {
//     "friend" <ident: ModuleIdent> ";" => { ... }
// }

fn parse_friend_decl(context: &mut Context) -> Result<ModuleIdent> {
    consume_token(context, Tok::Friend)?;
    let ident = parse_module_ident(context)?;
    consume_token(context, Tok::Semicolon)?;
    Ok(ident)
}

// ImportAlias: ModuleName = {
//     "as" <alias: ModuleName> => { ... }
// }

fn parse_import_alias(context: &mut Context) -> Result<ModuleName> {
    consume_token(context, Tok::As)?;
    let alias = parse_module_name(context)?;
    if alias == ModuleName::module_self() {
        panic!(
            "Invalid use of reserved module alias '{}'",
            ModuleName::self_name()
        );
    }
    Ok(alias)
}

// ImportDecl: ImportDefinition = {
//     "import" <ident: ModuleIdent> <alias: ImportAlias?> ";" => { ... }
// }

fn parse_import_decl(context: &mut Context) -> Result<ImportDefinition> {
    consume_token(context, Tok::Import)?;
    let ident = parse_module_ident(context)?;
    let alias = if context.tokens.peek() == Tok::As {
        Some(parse_import_alias(context)?)
    } else {
        None
    };
    consume_token(context, Tok::Semicolon)?;
    Ok(ImportDefinition::new(ident, alias))
}

// pub Module : ModuleDefinition = {
//     "module" <n: Name> "{"
//         <friends: (FriendDecl)*>
//         <imports: (ImportDecl)*>
//         <structs: (StructDecl)*>
//         <enums: (EnumDecl)*>
//         <functions: (FunctionDecl)*>
//     "}" =>? ModuleDefinition::new(n, imports, structs, functions),
// }

fn is_struct_decl(context: &mut Context) -> Result<bool> {
    let t = context.tokens.peek();
    Ok(t == Tok::Struct || (t == Tok::Native && context.tokens.lookahead()? == Tok::Struct))
}

fn is_enum_decl(context: &mut Context) -> bool {
    context.tokens.peek() == Tok::Enum
}

fn parse_module(context: &mut Context) -> Result<ModuleDefinition> {
    let start_loc = context.tokens.start_loc();
    consume_token(context, Tok::Module)?;
    let identifier = parse_module_ident(context)?;
    consume_token(context, Tok::LBrace)?;

    let mut friends = vec![];
    while context.tokens.peek() == Tok::Friend {
        friends.push(parse_friend_decl(context)?);
    }

    let mut imports = vec![];
    while context.tokens.peek() == Tok::Import {
        imports.push(parse_import_decl(context)?);
    }

    let mut structs: Vec<StructDefinition> = vec![];
    while is_struct_decl(context)? {
        structs.push(parse_struct_decl(context)?);
    }

    let mut enums: Vec<EnumDefinition> = vec![];
    while is_enum_decl(context) {
        enums.push(parse_enum_decl(context)?);
    }

    let mut functions: Vec<(FunctionName, Function)> = vec![];
    while context.tokens.peek() != Tok::RBrace {
        functions.push(parse_function_decl(context)?);
    }
    context.advance(); // consume the RBrace
    let end_loc = context.tokens.previous_end_loc();
    let loc = make_loc(context.tokens.file_hash(), start_loc, end_loc);

    Ok(ModuleDefinition::new(
        None,
        loc,
        identifier,
        friends,
        imports,
        vec![],
        structs,
        enums,
        vec![],
        functions,
    ))
}

// pub ScriptOrModule: ScriptOrModule = {
//     <s: Script> => ScriptOrModule::Script(s),
//     <m: Module> => ScriptOrModule::Module(m),
// }

pub fn parse_module_string(input: &str) -> std::result::Result<ModuleDefinition, Vec<Error>> {
    parse_module_string_with_named_addresses(input, &BTreeMap::new())
}

pub fn parse_module_string_with_named_addresses(
    input: &str,
    named_addresses: &BTreeMap<String, AccountAddress>,
) -> std::result::Result<ModuleDefinition, Vec<Error>> {
    let file_hash = FileHash::new(input);
    let mut tokens = Lexer::new(file_hash, input, named_addresses);
    let mut context = Context::new(&mut tokens);
    context.advance();
    let unit_res = parse_module(&mut context).and_then(|unit| {
        consume_token(&mut context, Tok::EOF)?;
        Ok(unit)
    });
    let mut errors = context.errors;
    match unit_res {
        Ok(unit) => {
            if !errors.is_empty() {
                Err(errors)
            } else {
                Ok(unit)
            }
        }
        Err(err) => {
            errors.push(err);
            Err(errors)
        }
    }
}
