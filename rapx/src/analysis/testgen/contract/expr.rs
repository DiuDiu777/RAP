use super::primitive::PrimitiveSpKind;
use serde::de::{Error, Visitor};
use serde::{Deserialize, Deserializer};
use std::collections::BTreeSet;
use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SafetyPredicate {
    raw: String,
    kind: PrimitiveSpKind,
    args: Vec<PredicateArg>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PredicateArg {
    Expr(ContractExpr),
    Type(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ContractExpr {
    Arg(usize),
    Integer(String),
    Const(String),
    SizeOf(String),
    Unary {
        op: UnaryOp,
        expr: Box<ContractExpr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<ContractExpr>,
        rhs: Box<ContractExpr>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnaryOp {
    Neg,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PredicateParseError {
    message: String,
}

impl PredicateParseError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for PredicateParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for PredicateParseError {}

impl SafetyPredicate {
    pub fn parse(input: &str) -> Result<Self, PredicateParseError> {
        let input = input.trim();
        let open = input
            .find('(')
            .ok_or_else(|| PredicateParseError::new("missing predicate argument list"))?;
        if !input.ends_with(')') {
            return Err(PredicateParseError::new(
                "predicate argument list must end with ')'",
            ));
        }
        let tag = input[..open].trim();
        if tag.is_empty() {
            return Err(PredicateParseError::new("missing predicate tag"));
        }

        let inner = &input[open + 1..input.len() - 1];
        let args = split_top_level(inner, ',')?
            .into_iter()
            .filter(|arg| !arg.trim().is_empty())
            .map(parse_predicate_arg)
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Self {
            raw: input.to_owned(),
            kind: PrimitiveSpKind::from_tag(tag),
            args,
        })
    }

    pub fn raw(&self) -> &str {
        &self.raw
    }

    pub fn kind(&self) -> &PrimitiveSpKind {
        &self.kind
    }

    pub fn arg_indices(&self) -> Vec<usize> {
        let mut indices = BTreeSet::new();
        for arg in &self.args {
            if let PredicateArg::Expr(expr) = arg {
                collect_arg_indices(expr, &mut indices);
            }
        }
        indices.into_iter().collect()
    }

    pub fn args(&self) -> &[PredicateArg] {
        &self.args
    }
}

impl<'de> Deserialize<'de> for SafetyPredicate {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct PredicateVisitor;

        impl<'de> Visitor<'de> for PredicateVisitor {
            type Value = SafetyPredicate;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "a safety predicate string")
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                SafetyPredicate::parse(value).map_err(E::custom)
            }
        }

        deserializer.deserialize_str(PredicateVisitor)
    }
}

fn parse_predicate_arg(arg: &str) -> Result<PredicateArg, PredicateParseError> {
    let arg = arg.trim();
    if is_bare_type_arg(arg) {
        return Ok(PredicateArg::Type(arg.to_owned()));
    }
    Parser::new(arg)?.parse_expression().map(PredicateArg::Expr)
}

fn is_bare_type_arg(arg: &str) -> bool {
    if arg.starts_with("arg") || arg.starts_with("size_of") {
        return false;
    }
    arg.chars()
        .all(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == ':' || ch == '<' || ch == '>')
}

fn collect_arg_indices(expr: &ContractExpr, indices: &mut BTreeSet<usize>) {
    match expr {
        ContractExpr::Arg(idx) => {
            indices.insert(*idx);
        }
        ContractExpr::Unary { expr, .. } => collect_arg_indices(expr, indices),
        ContractExpr::Binary { lhs, rhs, .. } => {
            collect_arg_indices(lhs, indices);
            collect_arg_indices(rhs, indices);
        }
        ContractExpr::Integer(_) | ContractExpr::Const(_) | ContractExpr::SizeOf(_) => {}
    }
}

fn split_top_level(input: &str, delimiter: char) -> Result<Vec<&str>, PredicateParseError> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (idx, ch) in input.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| PredicateParseError::new("unbalanced predicate expression"))?;
            }
            _ if ch == delimiter && depth == 0 => {
                parts.push(&input[start..idx]);
                start = idx + ch.len_utf8();
            }
            _ => {}
        }
    }
    if depth != 0 {
        return Err(PredicateParseError::new("unbalanced predicate expression"));
    }
    parts.push(&input[start..]);
    Ok(parts)
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Ident(String),
    Number(String),
    LParen,
    RParen,
    Plus,
    Minus,
    Star,
    Slash,
    Lt,
    Le,
    Gt,
    Ge,
    EqEq,
    Ne,
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(input: &str) -> Result<Self, PredicateParseError> {
        Ok(Self {
            tokens: tokenize(input)?,
            pos: 0,
        })
    }

    fn parse_expression(mut self) -> Result<ContractExpr, PredicateParseError> {
        let expr = self.parse_comparison()?;
        if self.pos != self.tokens.len() {
            return Err(PredicateParseError::new(
                "trailing tokens in predicate expression",
            ));
        }
        Ok(expr)
    }

    fn parse_comparison(&mut self) -> Result<ContractExpr, PredicateParseError> {
        let mut lhs = self.parse_add_sub()?;
        while let Some(op) = self.peek_binary_op(0) {
            if !matches!(
                op,
                BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge
                    | BinaryOp::Eq
                    | BinaryOp::Ne
            ) {
                break;
            }
            self.pos += 1;
            let rhs = self.parse_add_sub()?;
            lhs = ContractExpr::Binary {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }
        Ok(lhs)
    }

    fn parse_add_sub(&mut self) -> Result<ContractExpr, PredicateParseError> {
        let mut lhs = self.parse_mul_div()?;
        while let Some(op) = self.peek_binary_op(1) {
            self.pos += 1;
            let rhs = self.parse_mul_div()?;
            lhs = ContractExpr::Binary {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }
        Ok(lhs)
    }

    fn parse_mul_div(&mut self) -> Result<ContractExpr, PredicateParseError> {
        let mut lhs = self.parse_unary()?;
        while let Some(op) = self.peek_binary_op(2) {
            self.pos += 1;
            let rhs = self.parse_unary()?;
            lhs = ContractExpr::Binary {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }
        Ok(lhs)
    }

    fn parse_unary(&mut self) -> Result<ContractExpr, PredicateParseError> {
        if self.consume(&Token::Minus) {
            return Ok(ContractExpr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(self.parse_unary()?),
            });
        }
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> Result<ContractExpr, PredicateParseError> {
        match self.next() {
            Some(Token::Ident(ident)) if ident.starts_with("arg") => {
                let idx = ident[3..]
                    .parse::<usize>()
                    .map_err(|_| PredicateParseError::new("invalid argN reference"))?;
                Ok(ContractExpr::Arg(idx))
            }
            Some(Token::Ident(ident)) if ident == "size_of" => {
                self.expect(Token::LParen)?;
                let ty = self.parse_type_name()?;
                self.expect(Token::RParen)?;
                Ok(ContractExpr::SizeOf(ty))
            }
            Some(Token::Ident(ident)) => Ok(ContractExpr::Const(ident)),
            Some(Token::Number(number)) => Ok(ContractExpr::Integer(number)),
            Some(Token::LParen) => {
                let expr = self.parse_comparison()?;
                self.expect(Token::RParen)?;
                Ok(expr)
            }
            _ => Err(PredicateParseError::new("expected predicate expression")),
        }
    }

    fn parse_type_name(&mut self) -> Result<String, PredicateParseError> {
        match self.next() {
            Some(Token::Ident(ident)) => Ok(ident),
            _ => Err(PredicateParseError::new("expected type name in size_of")),
        }
    }

    fn peek_binary_op(&self, precedence: usize) -> Option<BinaryOp> {
        let op = match self.tokens.get(self.pos)? {
            Token::Plus => BinaryOp::Add,
            Token::Minus => BinaryOp::Sub,
            Token::Star => BinaryOp::Mul,
            Token::Slash => BinaryOp::Div,
            Token::Lt => BinaryOp::Lt,
            Token::Le => BinaryOp::Le,
            Token::Gt => BinaryOp::Gt,
            Token::Ge => BinaryOp::Ge,
            Token::EqEq => BinaryOp::Eq,
            Token::Ne => BinaryOp::Ne,
            _ => return None,
        };
        let actual = match op {
            BinaryOp::Lt
            | BinaryOp::Le
            | BinaryOp::Gt
            | BinaryOp::Ge
            | BinaryOp::Eq
            | BinaryOp::Ne => 0,
            BinaryOp::Add | BinaryOp::Sub => 1,
            BinaryOp::Mul | BinaryOp::Div => 2,
        };
        (actual == precedence).then_some(op)
    }

    fn expect(&mut self, token: Token) -> Result<(), PredicateParseError> {
        if self.consume(&token) {
            Ok(())
        } else {
            Err(PredicateParseError::new(
                "unexpected token in predicate expression",
            ))
        }
    }

    fn consume(&mut self, token: &Token) -> bool {
        if self.tokens.get(self.pos) == Some(token) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn next(&mut self) -> Option<Token> {
        let token = self.tokens.get(self.pos).cloned();
        if token.is_some() {
            self.pos += 1;
        }
        token
    }
}

fn tokenize(input: &str) -> Result<Vec<Token>, PredicateParseError> {
    let mut tokens = Vec::new();
    let chars = input.chars().collect::<Vec<_>>();
    let mut idx = 0usize;
    while idx < chars.len() {
        let ch = chars[idx];
        if ch.is_whitespace() {
            idx += 1;
            continue;
        }
        if ch.is_ascii_digit() {
            let start = idx;
            idx += 1;
            while idx < chars.len() && (chars[idx].is_ascii_alphanumeric() || chars[idx] == '_') {
                idx += 1;
            }
            tokens.push(Token::Number(chars[start..idx].iter().collect()));
            continue;
        }
        if ch.is_ascii_alphabetic() || ch == '_' {
            let start = idx;
            idx += 1;
            while idx < chars.len()
                && (chars[idx].is_ascii_alphanumeric() || chars[idx] == '_' || chars[idx] == ':')
            {
                idx += 1;
            }
            tokens.push(Token::Ident(chars[start..idx].iter().collect()));
            continue;
        }
        match ch {
            '(' => tokens.push(Token::LParen),
            ')' => tokens.push(Token::RParen),
            '+' => tokens.push(Token::Plus),
            '-' => tokens.push(Token::Minus),
            '*' => tokens.push(Token::Star),
            '/' => tokens.push(Token::Slash),
            '<' if chars.get(idx + 1) == Some(&'=') => {
                tokens.push(Token::Le);
                idx += 1;
            }
            '<' => tokens.push(Token::Lt),
            '>' if chars.get(idx + 1) == Some(&'=') => {
                tokens.push(Token::Ge);
                idx += 1;
            }
            '>' => tokens.push(Token::Gt),
            '=' if chars.get(idx + 1) == Some(&'=') => {
                tokens.push(Token::EqEq);
                idx += 1;
            }
            '!' if chars.get(idx + 1) == Some(&'=') => {
                tokens.push(Token::Ne);
                idx += 1;
            }
            _ => {
                return Err(PredicateParseError::new(format!(
                    "unsupported token `{ch}` in predicate expression"
                )));
            }
        }
        idx += 1;
    }
    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_compound_valid_num_expression() {
        let predicate =
            SafetyPredicate::parse("ValidNum(arg1 * size_of(T) <= isize::MAX)").unwrap();
        assert_eq!(predicate.kind(), &PrimitiveSpKind::ValidNum);
        assert_eq!(predicate.arg_indices(), vec![1]);
    }

    #[test]
    fn parses_multi_arg_inbound_with_type_parameter() {
        let predicate = SafetyPredicate::parse("InBound(arg0, arg1, T)").unwrap();
        assert_eq!(predicate.kind(), &PrimitiveSpKind::InBound);
        assert_eq!(predicate.arg_indices(), vec![0, 1]);
    }

    #[test]
    fn parses_not_equal_numeric_expression() {
        let predicate = SafetyPredicate::parse("ValidNum(arg1 != 0)").unwrap();
        assert_eq!(predicate.kind(), &PrimitiveSpKind::ValidNum);
        assert_eq!(predicate.arg_indices(), vec![1]);
    }

    #[test]
    fn rejects_unsupported_expression_token() {
        let err = SafetyPredicate::parse("ValidNum(!arg1)")
            .expect_err("unsupported unary operators should be rejected");
        assert!(err.to_string().contains("unsupported"));
    }
}
