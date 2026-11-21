mod algo1;
mod algo2;

use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::path::Path;
use std::process;

pub type VarId = usize;
pub type AllocId = usize;

#[derive(Debug, Clone, PartialEq)]
pub enum Operand {
    Num(String),
    Bool(bool),
    Str(String),
    Var { name: String, id: VarId },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Op {
    Add,
    Sub,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Single(Operand),
    Binary { left: Operand, op: Op, right: Operand },
}

#[derive(Debug, Clone)]
pub enum Stmt {
    VarDecl {
        id: VarId,
        expr: Expr,
        raw_line: String,
    },
    Assign {
        name: String,
        id: VarId,
        expr: Expr,
        raw_line: String,
    },
    Input {
        name: String,
        id: VarId,
        raw_line: String,
    },
    Print {
        expr: Expr,
        raw_line: String,
    },
    If {
        cond: Expr,
        cond_line: String,
        then_block: Vec<Stmt>,
        else_block: Option<Vec<Stmt>>,
    },
    While {
        cond: Expr,
        cond_line: String,
        body: Vec<Stmt>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Val {
    Num,
    Bool,
    Alloc(AllocId),
}

pub type ValState = HashMap<VarId, HashSet<Val>>;

struct SymbolTable {
    scopes: Vec<HashMap<String, VarId>>,
    next_id: VarId,
    id_to_name: Vec<String>,
}

impl SymbolTable {
    fn new() -> SymbolTable {
        SymbolTable {
            scopes: vec![HashMap::new()],
            next_id: 0,
            id_to_name: Vec::new(),
        }
    }

    fn enter_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn exit_scope(&mut self) {
        self.scopes.pop();
    }

    fn declare(&mut self, name: &str) -> VarId {
        let id = self.next_id;
        self.next_id += 1;
        self.id_to_name.push(name.to_string());

        let last_idx = self.scopes.len() - 1;
        self.scopes[last_idx].insert(name.to_string(), id);
        id
    }

    fn resolve(&self, name: &str) -> Result<VarId, String> {
        let mut i = self.scopes.len();
        while i > 0 {
            i -= 1;
            if let Some(&id) = self.scopes[i].get(name) {
                return Ok(id);
            }
        }
        Err(format!("Undeclared variable '{}'", name))
    }
}

fn strip_comment(line: &str) -> String {
    let chars: Vec<char> = line.chars().collect();
    let mut in_quotes = false;
    let mut out = String::new();
    let mut i = 0;

    while i < chars.len() {
        if chars[i] == '"' {
            in_quotes = !in_quotes;
        }
        if !in_quotes && i + 1 < chars.len() && chars[i] == '/' && chars[i + 1] == '/' {
            break;
        }
        out.push(chars[i]);
        i += 1;
    }
    out
}

fn parse_operand(raw: &str, symtab: &SymbolTable) -> Result<Operand, String> {
    let s = raw.trim();
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        let inner = &s[1..s.len() - 1];
        return Ok(Operand::Str(inner.to_string()));
    }
    if s == "true" {
        return Ok(Operand::Bool(true));
    }
    if s == "false" {
        return Ok(Operand::Bool(false));
    }
    if s.parse::<f64>().is_ok() {
        return Ok(Operand::Num(s.to_string()));
    }

    let id = symtab.resolve(s)?;
    Ok(Operand::Var {
        name: s.to_string(),
        id,
    })
}

fn parse_expr(raw: &str, symtab: &SymbolTable) -> Result<Expr, String> {
    let s = raw.trim();
    let chars: Vec<char> = s.chars().collect();
    let mut in_quotes = false;
    let mut i = 0;

    while i < chars.len() {
        if chars[i] == '"' {
            in_quotes = !in_quotes;
            i += 1;
            continue;
        }

        if !in_quotes {
            let two_char_op = if i + 1 < chars.len() {
                match (chars[i], chars[i + 1]) {
                    ('=', '=') => Some(Op::Eq),
                    ('!', '=') => Some(Op::Neq),
                    ('<', '=') => Some(Op::Le),
                    ('>', '=') => Some(Op::Ge),
                    _ => None,
                }
            } else {
                None
            };

            if let Some(op) = two_char_op {
                let left_str: String = chars[..i].iter().collect();
                let right_str: String = chars[i + 2..].iter().collect();
                let left = parse_operand(&left_str, symtab)?;
                let right = parse_operand(&right_str, symtab)?;
                return Ok(Expr::Binary { left, op, right });
            }

            let one_char_op = match chars[i] {
                '<' => Some(Op::Lt),
                '>' => Some(Op::Gt),
                '+' => Some(Op::Add),
                '-' if i > 0 => Some(Op::Sub),
                _ => None,
            };

            if let Some(op) = one_char_op {
                let left_str: String = chars[..i].iter().collect();
                let right_str: String = chars[i + 1..].iter().collect();
                let left = parse_operand(&left_str, symtab)?;
                let right = parse_operand(&right_str, symtab)?;
                return Ok(Expr::Binary { left, op, right });
            }
        }
        i += 1;
    }

    let operand = parse_operand(s, symtab)?;
    Ok(Expr::Single(operand))
}

fn get_condition(header: &str) -> Result<String, String> {
    let open = match header.find('(') {
        Some(idx) => idx,
        None => return Err(format!("Expected '(' in '{}'", header)),
    };
    let close = match header.rfind(')') {
        Some(idx) => idx,
        None => return Err(format!("Expected ')' in '{}'", header)),
    };
    if close <= open {
        return Err(format!("Malformed parentheses in '{}'", header));
    }
    Ok(header[open + 1..close].trim().to_string())
}

fn starts_with_kw(line: &str, kw: &str) -> bool {
    if !line.starts_with(kw) {
        return false;
    }
    let rest = &line[kw.len()..];
    rest.is_empty() || rest.starts_with(' ') || rest.starts_with('(')
}

fn parse_program(source: &str) -> Result<(Vec<Stmt>, Vec<String>), String> {
    let mut lines: Vec<String> = Vec::new();

    for raw in source.lines() {
        let stripped = strip_comment(raw);
        let cleaned = stripped.trim();
        if cleaned.is_empty() {
            continue;
        }

        if cleaned == "} else {" || cleaned == "}else{" {
            lines.push("}".to_string());
            lines.push("else".to_string());
            lines.push("{".to_string());
        } else if cleaned.ends_with('{') && cleaned.len() > 1 {
            let before = cleaned[..cleaned.len() - 1].trim();
            lines.push(before.to_string());
            lines.push("{".to_string());
        } else if cleaned.starts_with('}') && cleaned.len() > 1 {
            lines.push("}".to_string());
            let after = cleaned[1..].trim();
            if after.ends_with('{') && after.len() > 1 {
                let mid = after[..after.len() - 1].trim();
                lines.push(mid.to_string());
                lines.push("{".to_string());
            } else {
                lines.push(after.to_string());
            }
        } else {
            lines.push(cleaned.to_string());
        }
    }

    let mut symtab = SymbolTable::new();
    let mut pos = 0;
    let stmts = parse_stmt_list(&lines, &mut pos, false, &mut symtab)?;
    Ok((stmts, symtab.id_to_name))
}

fn parse_stmt_list(
    lines: &[String],
    pos: &mut usize,
    stop_at_brace: bool,
    symtab: &mut SymbolTable,
) -> Result<Vec<Stmt>, String> {
    let mut stmts = Vec::new();

    while *pos < lines.len() {
        let line = lines[*pos].trim();

        if line == "}" {
            if stop_at_brace {
                *pos += 1;
                return Ok(stmts);
            } else {
                return Err("Unexpected '}'".to_string());
            }
        }

        if starts_with_kw(line, "if") {
            let cond_str = get_condition(line)?;
            let cond = parse_expr(&cond_str, symtab)?;
            let cond_line = format!("if ({})", cond_str);
            *pos += 1;

            if *pos >= lines.len() || lines[*pos] != "{" {
                return Err("Expected '{' after if".to_string());
            }
            *pos += 1;

            symtab.enter_scope();
            let then_block = parse_stmt_list(lines, pos, true, symtab)?;
            symtab.exit_scope();

            let mut else_block = None;
            if *pos < lines.len() && lines[*pos] == "else" {
                *pos += 1;
                if *pos >= lines.len() || lines[*pos] != "{" {
                    return Err("Expected '{' after else".to_string());
                }
                *pos += 1;

                symtab.enter_scope();
                let parsed_else = parse_stmt_list(lines, pos, true, symtab)?;
                symtab.exit_scope();
                else_block = Some(parsed_else);
            }

            stmts.push(Stmt::If {
                cond,
                cond_line,
                then_block,
                else_block,
            });
        } else if starts_with_kw(line, "while") {
            let cond_str = get_condition(line)?;
            let cond = parse_expr(&cond_str, symtab)?;
            let cond_line = format!("while ({})", cond_str);
            *pos += 1;

            if *pos >= lines.len() || lines[*pos] != "{" {
                return Err("Expected '{' after while".to_string());
            }
            *pos += 1;

            symtab.enter_scope();
            let body = parse_stmt_list(lines, pos, true, symtab)?;
            symtab.exit_scope();

            stmts.push(Stmt::While {
                cond,
                cond_line,
                body,
            });
        } else if line.starts_with("var ") {
            let without_var = line[4..].trim();
            let without_semi = without_var.trim_end_matches(';').trim();
            let eq_idx = match without_semi.find('=') {
                Some(idx) => idx,
                None => return Err(format!("Expected '=' in '{}'", line)),
            };

            let name = without_semi[..eq_idx].trim().to_string();
            let expr_str = without_semi[eq_idx + 1..].trim();
            let expr = parse_expr(expr_str, symtab)?;
            let id = symtab.declare(&name);
            *pos += 1;

            stmts.push(Stmt::VarDecl {
                id,
                expr,
                raw_line: line.to_string(),
            });
        } else if line.starts_with("input ") {
            let without_input = line[6..].trim();
            let name = without_input.trim_end_matches(';').trim().to_string();
            let id = symtab.resolve(&name)?;
            *pos += 1;

            stmts.push(Stmt::Input {
                name,
                id,
                raw_line: line.to_string(),
            });
        } else if line.starts_with("print ") {
            let without_print = line[6..].trim();
            let expr_str = without_print.trim_end_matches(';').trim();
            let expr = parse_expr(expr_str, symtab)?;
            *pos += 1;

            stmts.push(Stmt::Print {
                expr,
                raw_line: line.to_string(),
            });
        } else {
            let without_semi = line.trim_end_matches(';').trim();
            let eq_idx = match without_semi.find('=') {
                Some(idx) => idx,
                None => return Err(format!("Unrecognized statement '{}'", line)),
            };

            let name = without_semi[..eq_idx].trim().to_string();
            let expr_str = without_semi[eq_idx + 1..].trim();
            let id = symtab.resolve(&name)?;
            let expr = parse_expr(expr_str, symtab)?;
            *pos += 1;

            stmts.push(Stmt::Assign {
                name,
                id,
                expr,
                raw_line: line.to_string(),
            });
        }
    }

    if stop_at_brace {
        return Err("Unclosed '{' block".to_string());
    }

    Ok(stmts)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: cargo run --bin Lox-transformer <input_file.lox>");
        process::exit(1);
    }

    let input_path = Path::new(&args[1]);
    let source = match fs::read_to_string(input_path) {
        Ok(content) => content,
        Err(err) => {
            eprintln!("Error reading '{}': {}", input_path.display(), err);
            process::exit(1);
        }
    };

    match transform_lox(&source) {
        Ok(output_code) => {
            let stem = match input_path.file_stem() {
                Some(s) => match s.to_str() {
                    Some(name) => name,
                    None => "output",
                },
                None => "output",
            };
            let output_path = input_path.with_file_name(format!("{}_o.rs", stem));

            if let Err(err) = fs::write(&output_path, output_code) {
                eprintln!("Error writing '{}': {}", output_path.display(), err);
                process::exit(1);
            }
            process::exit(0);
        }
        Err(err_msg) => {
            eprintln!("Error: {}", err_msg);
            process::exit(1);
        }
    }
}

fn transform_lox(source: &str) -> Result<String, String> {
    let (stmts, id_to_name) = parse_program(source)?;

    let mut type_state: ValState = HashMap::new();
    let mut next_alloc: AllocId = 1;
    algo1::analyze_block(&stmts, &mut type_state, &mut next_alloc)?;

    let mut emit_state: ValState = HashMap::new();
    let mut in_scope: Vec<VarId> = Vec::new();
    let empty_live: HashSet<VarId> = HashSet::new();
    let mut emit_alloc: AllocId = 1;
    let mut out_lines: Vec<String> = Vec::new();

    algo2::emit_block(
        &stmts,
        &mut emit_state,
        &mut in_scope,
        &empty_live,
        &empty_live,
        &mut emit_alloc,
        &id_to_name,
        0,
        &mut out_lines,
    )?;

    if out_lines.is_empty() {
        Ok(String::new())
    } else {
        Ok(format!("{}\n", out_lines.join("\n")))
    }
}