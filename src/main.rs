use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::path::Path;
use std::process;

type VarId = usize;
type AllocId = usize;

#[derive(Debug, Clone, PartialEq)]
enum Operand {
    Num(String),
    Bool(bool),
    Str(String),
    Var { name: String, id: VarId },
}

#[derive(Debug, Clone, PartialEq)]
enum Op {
    Add,
    Sub,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
}

// Expression can either just a operand or a binary operation on two operands
#[derive(Debug, Clone, PartialEq)]
enum Expr {
    Single(Operand),
    Binary { left: Operand, op: Op, right: Operand },
}

#[derive(Debug, Clone)]
enum Stmt {
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
enum Val {
    Num,
    Bool,
    Alloc(AllocId),
}

type ValState = HashMap<VarId, HashSet<Val>>;

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

///////////////////////////TYPE INFERENCE///////////////////////////

// Check possible types of a given operand set
fn is_all_num(set: &HashSet<Val>) -> bool {
    !set.is_empty() && set.iter().all(|v| *v == Val::Num)
}
fn is_all_bool(set: &HashSet<Val>) -> bool {
    !set.is_empty() && set.iter().all(|v| *v == Val::Bool)
}
fn is_all_str(set: &HashSet<Val>) -> bool {
    !set.is_empty() && set.iter().all(|v| matches!(v, Val::Alloc(_)))
}

// Return all possible types of a Operand
fn eval_operand(op: &Operand, state: &ValState, alloc_id: AllocId) -> Result<HashSet<Val>, String> {
    let mut out = HashSet::new();
    match op {
        Operand::Num(_) => {
            out.insert(Val::Num);
        }
        Operand::Bool(_) => {
            out.insert(Val::Bool);
        }
        Operand::Str(_) => {
            out.insert(Val::Alloc(alloc_id));
        }
        Operand::Var { name, id } => match state.get(id) {
            Some(vals) if !vals.is_empty() => return Ok(vals.clone()),
            _ => return Err(format!("Variable '{}' used before initialization", name)),
        },
    }
    Ok(out)
}

// Evalaute the type of a expression
fn eval_expr(expr: &Expr, state: &ValState, alloc_id: AllocId) -> Result<HashSet<Val>, String> {
    match expr {
        Expr::Single(op) => eval_operand(op, state, alloc_id),
        Expr::Binary { left, op, right } => {
            let l_set = eval_operand(left, state, alloc_id)?;
            let r_set = eval_operand(right, state, alloc_id)?;

            let mut out = HashSet::new();
            match op {
                Op::Add => {
                    if is_all_num(&l_set) && is_all_num(&r_set) {
                        out.insert(Val::Num);
                    } else if is_all_str(&l_set) && is_all_str(&r_set) {
                        out.insert(Val::Alloc(alloc_id));
                    } else {
                        return Err("Type error: '+' requires two numbers or two strings".to_string());
                    }
                }
                Op::Sub => {
                    if is_all_num(&l_set) && is_all_num(&r_set) {
                        out.insert(Val::Num);
                    } else {
                        return Err("Type error: '-' requires numeric operands".to_string());
                    }
                }
                Op::Lt | Op::Le | Op::Gt | Op::Ge => {
                    if is_all_num(&l_set) && is_all_num(&r_set) {
                        out.insert(Val::Bool);
                    } else {
                        return Err("Type error: comparison requires numeric operands".to_string());
                    }
                }
                Op::Eq | Op::Neq => {
                    let same_num = is_all_num(&l_set) && is_all_num(&r_set);
                    let same_bool = is_all_bool(&l_set) && is_all_bool(&r_set);
                    let same_str = is_all_str(&l_set) && is_all_str(&r_set);
                    if same_num || same_bool || same_str {
                        out.insert(Val::Bool);
                    } else {
                        return Err("Type error: equality operands have incompatible types".to_string());
                    }
                }
            }
            Ok(out)
        }
    }
}

// Given two states, returns a merged state
fn merge_states(a: &ValState, b: &ValState) -> ValState {
    let mut merged = a.clone();
    for (var_id, b_vals) in b {
        let entry = merged.entry(*var_id).or_insert_with(HashSet::new);
        for val in b_vals {
            entry.insert(*val);
        }
    }
    merged
}

// We also have access of raw line so if the expression is not parsed then give error with the line no
// remove this comment
fn analyze_block(
    stmts: &[Stmt],
    state: &mut ValState,
    next_alloc: &mut AllocId,
) -> Result<(), String> {
    for stmt in stmts {
        match stmt {
            Stmt::VarDecl { id, expr, .. } | Stmt::Assign { id, expr, .. } => {
                let site = *next_alloc;
                *next_alloc += 1;
                let vals = eval_expr(expr, state, site)?;
                state.insert(*id, vals);
            }
            Stmt::Input { id, .. } => {
                let mut vals = HashSet::new();
                vals.insert(Val::Num);
                state.insert(*id, vals);
            }
            Stmt::Print { expr, .. } => {
                let site = *next_alloc;
                *next_alloc += 1;
                let _ = eval_expr(expr, state, site)?;
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
                ..
            } => {
                // Site 0 is reserved for bool / Actual allocation id starts from 1
                let cond_vals = eval_expr(cond, state, 0)?;
                if !is_all_bool(&cond_vals) {
                    return Err("Type error: 'if' condition must evaluate to bool".to_string());
                }

                let mut then_state = state.clone();
                analyze_block(then_block, &mut then_state, next_alloc)?;

                let mut else_state = state.clone();
                if let Some(eb) = else_block {
                    analyze_block(eb, &mut else_state, next_alloc)?;
                }

                let joined = merge_states(&then_state, &else_state);
                let existing_keys: Vec<VarId> = state.keys().cloned().collect();
                for k in existing_keys {
                    if let Some(v) = joined.get(&k) {
                        state.insert(k, v.clone());
                    }
                }
            }
            Stmt::While { cond, body, .. } => {
                let base_alloc = *next_alloc;
                loop {
                    // Site 0 is reserved for bool / Actual allocation id starts from 1
                    let cond_vals = eval_expr(cond, state, 0)?;
                    if !is_all_bool(&cond_vals) {
                        return Err("Type error: 'while' condition must evaluate to bool".to_string());
                    }

                    let mut iter_alloc = base_alloc;
                    let mut body_state = state.clone();
                    analyze_block(body, &mut body_state, &mut iter_alloc)?;
                    *next_alloc = iter_alloc;

                    let mut changed = false;
                    let existing_keys: Vec<VarId> = state.keys().cloned().collect();
                    for k in existing_keys {
                        if let Some(new_vals) = body_state.get(&k) {
                            let cur_vals = state.entry(k).or_insert_with(HashSet::new);
                            for val in new_vals {
                                if cur_vals.insert(*val) {
                                    changed = true;
                                }
                            }
                        }
                    }

                    if !changed {
                        break;
                    }
                }
            }
        }
    }
    Ok(())
}

///////////////////////////LIVE VAR ANALYSIS///////////////////////////

// Returns the ids of variables referenced in a expression
fn expr_vars(expr: &Expr) -> HashSet<VarId> {
    let mut vars = HashSet::new();
    match expr {
        Expr::Single(Operand::Var { id, .. }) => {
            vars.insert(*id);
        }
        Expr::Binary { left, right, .. } => {
            if let Operand::Var { id, .. } = left {
                vars.insert(*id);
            }
            if let Operand::Var { id, .. } = right {
                vars.insert(*id);
            }
        }
        _ => {}
    }
    vars
}

// Returns the ids reachable through given set of live variables.
fn live_allocs(state: &ValState, live_vars: &HashSet<VarId>) -> HashSet<AllocId> {
    let mut allocs = HashSet::new();
    for var_id in live_vars {
        if let Some(vals) = state.get(var_id) {
            for val in vals {
                if let Val::Alloc(a) = val {
                    allocs.insert(*a);
                }
            }
        }
    }
    allocs
}

// Computes variables live before the block and immediately after each statement
fn compute_liveness(
    stmts: &[Stmt],
    live_after: &HashSet<VarId>,
) -> (HashSet<VarId>, Vec<HashSet<VarId>>) {
    let mut live_after_each = vec![HashSet::new(); stmts.len()];
    let mut cur_live = live_after.clone();

    let mut i = stmts.len();
    while i > 0 {
        i -= 1;
        live_after_each[i] = cur_live.clone();

        match &stmts[i] {
            Stmt::VarDecl { id, expr, .. } | Stmt::Assign { id, expr, .. } => {
                cur_live.remove(id);
                for v in expr_vars(expr) {
                    cur_live.insert(v);
                }
            }
            Stmt::Input { id, .. } => {
                cur_live.remove(id);
            }
            Stmt::Print { expr, .. } => {
                for v in expr_vars(expr) {
                    cur_live.insert(v);
                }
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
                ..
            } => {
                let (live_then, _) = compute_liveness(then_block, &cur_live);
                let live_else = match else_block {
                    Some(eb) => compute_liveness(eb, &cur_live).0,
                    None => cur_live.clone(),
                };
                cur_live = live_then;
                for v in live_else {
                    cur_live.insert(v);
                }
                for v in expr_vars(cond) {
                    cur_live.insert(v);
                }
            }
            Stmt::While { cond, body, .. } => {
                let mut head_live = cur_live.clone();
                for v in expr_vars(cond) {
                    head_live.insert(v);
                }
                loop {
                    let (body_in, _) = compute_liveness(body, &head_live);
                    let mut changed = false;
                    for v in body_in {
                        if head_live.insert(v) {
                            changed = true;
                        }
                    }
                    if !changed {
                        break;
                    }
                }
                cur_live = head_live;
            }
        }
    }

    (cur_live, live_after_each)
}

// Finds an in-scope variable that uniquely owns the specified allocation
fn find_drop_target(
    alloc_id: AllocId,
    state: &ValState,
    in_scope: &[VarId],
    preferred: Option<VarId>,
    id_to_name: &[String],
) -> Result<String, String> {
    if let Some(pref_id) = preferred {
        if in_scope.contains(&pref_id) {
            if let Some(vals) = state.get(&pref_id) {
                if vals.len() == 1 && vals.contains(&Val::Alloc(alloc_id)) {
                    return Ok(id_to_name[pref_id].clone());
                }
            }
        }
    }

    for &var_id in in_scope {
        if let Some(vals) = state.get(&var_id) {
            if vals.len() == 1 && vals.contains(&Val::Alloc(alloc_id)) {
                return Ok(id_to_name[var_id].clone());
            }
        }
    }

    Err("Cannot statically determine a single variable to drop heap string".to_string())
}

// Produces the indentation string
fn indent_str(indent: usize) -> String {
    "    ".repeat(indent)
}

// Emits a transformed block with safe drop statements for heap strings
fn emit_block(
    stmts: &[Stmt],
    state: &mut ValState,
    in_scope: &mut Vec<VarId>,
    live_in_vars: &HashSet<VarId>,
    live_after_block: &HashSet<VarId>,
    next_alloc: &mut AllocId,
    id_to_name: &[String],
    indent: usize,
    out_lines: &mut Vec<String>,
) -> Result<HashSet<AllocId>, String> {
    let (_, live_after_each) = compute_liveness(stmts, live_after_block);
    let mut currently_alive = live_allocs(state, live_in_vars);

    for (idx, stmt) in stmts.iter().enumerate() {
        let live_after = &live_after_each[idx];
        let pad = indent_str(indent);

        match stmt {
            Stmt::VarDecl {
                id, expr, raw_line, ..
            } => {
                let site = *next_alloc;
                *next_alloc += 1;
                let in_state = state.clone();
                let new_vals = eval_expr(expr, &in_state, site)?;

                state.insert(*id, new_vals.clone());
                in_scope.push(*id);

                let needed_after = live_allocs(state, live_after);
                for val in &new_vals {
                    if let Val::Alloc(a) = val {
                        currently_alive.insert(*a);
                    }
                }

                out_lines.push(format!("{}{}", pad, raw_line));

                let mut to_drop: Vec<AllocId> = Vec::new();
                for &a in &currently_alive {
                    if !needed_after.contains(&a) {
                        to_drop.push(a);
                    }
                }
                to_drop.sort();
                for a in to_drop {
                    let target = find_drop_target(a, state, in_scope, Some(*id), id_to_name)?;
                    out_lines.push(format!("{}drop {};", pad, target));
                    currently_alive.remove(&a);
                }
            }
            Stmt::Assign {
                name,
                id,
                expr,
                raw_line,
            } => {
                let site = *next_alloc;
                *next_alloc += 1;
                let in_state = state.clone();
                let new_vals = eval_expr(expr, &in_state, site)?;

                let mut out_state = in_state.clone();
                out_state.insert(*id, new_vals.clone());
                let needed_after = live_allocs(&out_state, live_after);

                if let Some(old_vals) = in_state.get(id) {
                    let mut has_live_alloc = false;
                    let mut has_dead_alloc = false;
                    let mut has_non_alloc = false;
                    let mut any_dying = false;
                    let mut any_still_aliased = false;

                    for val in old_vals {
                        match val {
                            Val::Alloc(old_a) => {
                                if currently_alive.contains(old_a) {
                                    has_live_alloc = true;
                                    if needed_after.contains(old_a) {
                                        any_still_aliased = true;
                                    } else {
                                        any_dying = true;
                                    }
                                } else {
                                    has_dead_alloc = true;
                                }
                            }
                            _ => has_non_alloc = true,
                        }
                    }

                    if has_live_alloc && any_dying {
                        if has_non_alloc || has_dead_alloc || any_still_aliased {
                            return Err(format!(
                                "Unsafe overwrite of '{}' across mixed paths",
                                name
                            ));
                        }
                        out_lines.push(format!("{}drop {};", pad, name));
                        for val in old_vals {
                            if let Val::Alloc(old_a) = val {
                                currently_alive.remove(old_a);
                            }
                        }
                    }
                }

                *state = out_state;
                for val in &new_vals {
                    if let Val::Alloc(a) = val {
                        currently_alive.insert(*a);
                    }
                }

                out_lines.push(format!("{}{}", pad, raw_line));

                let mut to_drop: Vec<AllocId> = Vec::new();
                for &a in &currently_alive {
                    if !needed_after.contains(&a) {
                        to_drop.push(a);
                    }
                }
                to_drop.sort();
                for a in to_drop {
                    let target = find_drop_target(a, state, in_scope, None, id_to_name)?;
                    out_lines.push(format!("{}drop {};", pad, target));
                    currently_alive.remove(&a);
                }
            }
            Stmt::Input { name, id, raw_line } => {
                let in_state = state.clone();
                let mut num_set = HashSet::new();
                num_set.insert(Val::Num);

                let mut out_state = in_state.clone();
                out_state.insert(*id, num_set);
                let needed_after = live_allocs(&out_state, live_after);

                if let Some(old_vals) = in_state.get(id) {
                    let mut has_live_alloc = false;
                    let mut has_dead_alloc = false;
                    let mut has_non_alloc = false;
                    let mut any_dying = false;
                    let mut any_still_aliased = false;

                    for val in old_vals {
                        match val {
                            Val::Alloc(old_a) => {
                                if currently_alive.contains(old_a) {
                                    has_live_alloc = true;
                                    if needed_after.contains(old_a) {
                                        any_still_aliased = true;
                                    } else {
                                        any_dying = true;
                                    }
                                } else {
                                    has_dead_alloc = true;
                                }
                            }
                            _ => has_non_alloc = true,
                        }
                    }

                    if has_live_alloc && any_dying {
                        if has_non_alloc || has_dead_alloc || any_still_aliased {
                            return Err(format!(
                                "Unsafe input overwrite of '{}' across mixed paths",
                                name
                            ));
                        }
                        out_lines.push(format!("{}drop {};", pad, name));
                        for val in old_vals {
                            if let Val::Alloc(old_a) = val {
                                currently_alive.remove(old_a);
                            }
                        }
                    }
                }

                *state = out_state;
                out_lines.push(format!("{}{}", pad, raw_line));
            }
            Stmt::Print { expr, raw_line } => {
                let site = *next_alloc;
                *next_alloc += 1;
                let _ = eval_expr(expr, state, site)?;
                let needed_after = live_allocs(state, live_after);

                out_lines.push(format!("{}{}", pad, raw_line));

                let mut pref = None;
                if let Expr::Single(Operand::Var { id, .. }) = expr {
                    pref = Some(*id);
                }

                let mut to_drop: Vec<AllocId> = Vec::new();
                for &a in &currently_alive {
                    if !needed_after.contains(&a) {
                        to_drop.push(a);
                    }
                }
                to_drop.sort();
                for a in to_drop {
                    let target = find_drop_target(a, state, in_scope, pref, id_to_name)?;
                    out_lines.push(format!("{}drop {};", pad, target));
                    currently_alive.remove(&a);
                }
            }
            Stmt::If {
                cond,
                cond_line,
                then_block,
                else_block,
            } => {
                let (mut then_live_in, _) = compute_liveness(then_block, live_after);
                let (mut else_live_in, _) = match else_block {
                    Some(eb) => compute_liveness(eb, live_after),
                    None => (live_after.clone(), Vec::new()),
                };

                let mut branch_entry_vars = then_live_in.clone();
                for v in &else_live_in {
                    branch_entry_vars.insert(*v);
                }
                for v in expr_vars(cond) {
                    branch_entry_vars.insert(v);
                }

                let entry_allocs = live_allocs(state, &branch_entry_vars);
                for (var_id, vals) in state.iter() {
                    for val in vals {
                        if let Val::Alloc(a) = val {
                            if entry_allocs.contains(a) {
                                then_live_in.insert(*var_id);
                                else_live_in.insert(*var_id);
                            }
                        }
                    }
                }

                let alloc_checkpoint = *next_alloc;
                let mut then_state = state.clone();
                let mut then_scope = in_scope.clone();
                let mut then_lines = Vec::new();
                let then_alive_end = emit_block(
                    then_block,
                    &mut then_state,
                    &mut then_scope,
                    &then_live_in,
                    live_after,
                    next_alloc,
                    id_to_name,
                    indent + 1,
                    &mut then_lines,
                )?;

                *next_alloc = alloc_checkpoint;
                let mut else_state = state.clone();
                let mut else_scope = in_scope.clone();
                let mut else_lines = Vec::new();
                let empty_else = Vec::new();
                let eb_slice = match else_block {
                    Some(eb) => eb.as_slice(),
                    None => empty_else.as_slice(),
                };
                let else_alive_end = emit_block(
                    eb_slice,
                    &mut else_state,
                    &mut else_scope,
                    &else_live_in,
                    live_after,
                    next_alloc,
                    id_to_name,
                    indent + 1,
                    &mut else_lines,
                )?;

                if then_alive_end != else_alive_end {
                    return Err(
                        "Cannot balance heap string lifetimes across if/else branches".to_string(),
                    );
                }

                out_lines.push(format!("{}{}", pad, cond_line));
                out_lines.push(format!("{}{{", pad));
                for l in then_lines {
                    out_lines.push(l);
                }
                out_lines.push(format!("{}}}", pad));

                if !else_lines.is_empty() || else_block.is_some() {
                    out_lines.push(format!("{}else", pad));
                    out_lines.push(format!("{}{{", pad));
                    for l in else_lines {
                        out_lines.push(l);
                    }
                    out_lines.push(format!("{}}}", pad));
                }

                let joined = merge_states(&then_state, &else_state);
                for &k in in_scope.iter() {
                    if let Some(v) = joined.get(&k) {
                        state.insert(k, v.clone());
                    }
                }
                currently_alive = then_alive_end;
            }
            Stmt::While {
                cond,
                cond_line,
                body,
            } => {
                let mut loop_state = state.clone();
                let base_alloc = *next_alloc;
                loop {
                    let mut iter_alloc = base_alloc;
                    let mut body_s = loop_state.clone();
                    analyze_block(body, &mut body_s, &mut iter_alloc)?;
                    *next_alloc = iter_alloc;

                    let mut changed = false;
                    for &k in in_scope.iter() {
                        if let Some(new_vals) = body_s.get(&k) {
                            let cur_vals = loop_state.entry(k).or_insert_with(HashSet::new);
                            for val in new_vals {
                                if cur_vals.insert(*val) {
                                    changed = true;
                                }
                            }
                        }
                    }
                    if !changed {
                        break;
                    }
                }

                let mut head_live = live_after.clone();
                for v in expr_vars(cond) {
                    head_live.insert(v);
                }
                loop {
                    let (body_in, _) = compute_liveness(body, &head_live);
                    let mut changed = false;
                    for v in body_in {
                        if head_live.insert(v) {
                            changed = true;
                        }
                    }
                    if !changed {
                        break;
                    }
                }

                let header_alive = live_allocs(&loop_state, &head_live);
                let mut body_state = loop_state.clone();
                let mut body_scope = in_scope.clone();
                let mut body_lines = Vec::new();
                let body_end_alive = emit_block(
                    body,
                    &mut body_state,
                    &mut body_scope,
                    &head_live,
                    &head_live,
                    next_alloc,
                    id_to_name,
                    indent + 1,
                    &mut body_lines,
                )?;

                if body_end_alive != header_alive {
                    return Err("Loop iteration leaks or double-frees heap strings".to_string());
                }

                out_lines.push(format!("{}{}", pad, cond_line));
                out_lines.push(format!("{}{{", pad));
                for l in body_lines {
                    out_lines.push(l);
                }
                out_lines.push(format!("{}}}", pad));

                *state = loop_state;
                currently_alive = header_alive;

                let needed_after = live_allocs(state, live_after);
                let mut to_drop: Vec<AllocId> = Vec::new();
                for &a in &currently_alive {
                    if !needed_after.contains(&a) {
                        to_drop.push(a);
                    }
                }
                to_drop.sort();
                for a in to_drop {
                    let target = find_drop_target(a, state, in_scope, None, id_to_name)?;
                    out_lines.push(format!("{}drop {};", pad, target));
                    currently_alive.remove(&a);
                }
            }
        }
    }
    let needed_after_block = live_allocs(state, live_after_block);
    let pad = indent_str(indent);
    let mut to_drop: Vec<AllocId> = Vec::new();
    for &a in &currently_alive {
        if !needed_after_block.contains(&a) {
            to_drop.push(a);
        }
    }
    to_drop.sort();
    for a in to_drop {
        let target = find_drop_target(a, state, in_scope, None, id_to_name)?;
        out_lines.push(format!("{}drop {};", pad, target));
        currently_alive.remove(&a);
    }

    Ok(currently_alive)
}


// Removes a line comment while preserving comment markers inside strings
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

// Parses a literal or variable reference into an operand
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

// Parses a single-operand or binary expression
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

// Extracts the expression enclosed in a control-flow header's parentheses
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

// Checks whether a line begins with a complete keyword token.
fn starts_with_kw(line: &str, kw: &str) -> bool {
    if !line.starts_with(kw) {
        return false;
    }
    let rest = &line[kw.len()..];
    rest.is_empty() || rest.starts_with(' ') || rest.starts_with('(')
}

// Normalizes and parses source text into statements and variable names
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
        } else if cleaned.starts_with('}') && cleaned.len() > 1 {
            lines.push("}".to_string());
            let after = cleaned[1..].trim();
            if after.ends_with("{}") && after.len() > 2 {
                let mid = after[..after.len() - 2].trim();
                lines.push(mid.to_string());
                lines.push("{".to_string());
                lines.push("}".to_string());
            } else if after.ends_with('{') && after.len() > 1 {
                let mid = after[..after.len() - 1].trim();
                lines.push(mid.to_string());
                lines.push("{".to_string());
            } else {
                lines.push(after.to_string());
            }
        } else if cleaned.ends_with("{}") && cleaned.len() > 2 {
            let before = cleaned[..cleaned.len() - 2].trim();
            lines.push(before.to_string());
            lines.push("{".to_string());
            lines.push("}".to_string());
        } else if cleaned.ends_with('{') && cleaned.len() > 1 {
            let before = cleaned[..cleaned.len() - 1].trim();
            lines.push(before.to_string());
            lines.push("{".to_string());
        } else {
            lines.push(cleaned.to_string());
        }
    }

    let mut symtab = SymbolTable::new();
    let mut pos = 0;
    let stmts = parse_stmt_list(&lines, &mut pos, false, &mut symtab)?;
    Ok((stmts, symtab.id_to_name))
}

// Parses statements until the input ends or the current block closes
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

// Reads the input program, transforms it, and writes the generated output file
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
            let output_path = input_path.with_file_name(format!("{}_o.lox", stem));

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

// Analyzes and emits a transformed Lox program with explicit string drops
fn transform_lox(source: &str) -> Result<String, String> {
    let (stmts, id_to_name) = parse_program(source)?;

    let mut type_state: ValState = HashMap::new();
    let mut next_alloc: AllocId = 1;
    analyze_block(&stmts, &mut type_state, &mut next_alloc)?;

    let mut emit_state: ValState = HashMap::new();
    let mut in_scope: Vec<VarId> = Vec::new();
    let empty_live: HashSet<VarId> = HashSet::new();
    let mut emit_alloc: AllocId = 1;
    let mut out_lines: Vec<String> = Vec::new();

    emit_block(
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
