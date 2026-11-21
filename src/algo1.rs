use std::collections::HashSet;
use crate::*;

pub fn is_all_num(set: &HashSet<Val>) -> bool {
    !set.is_empty() && set.iter().all(|v| matches!(v, Val::Num))
}

pub fn is_all_bool(set: &HashSet<Val>) -> bool {
    !set.is_empty() && set.iter().all(|v| matches!(v, Val::Bool))
}

pub fn is_all_str(set: &HashSet<Val>) -> bool {
    !set.is_empty() && set.iter().all(|v| matches!(v, Val::Alloc(_)))
}

pub fn eval_operand(op: &Operand, state: &ValState, site_id: AllocId) -> Result<HashSet<Val>, String> {
    let mut out = HashSet::new();
    match op {
        Operand::Num(_) => {
            out.insert(Val::Num);
        }
        Operand::Bool(_) => {
            out.insert(Val::Bool);
        }
        Operand::Str(_) => {
            out.insert(Val::Alloc(site_id));
        }
        Operand::Var { name, id } => match state.get(id) {
            Some(vals) if !vals.is_empty() => return Ok(vals.clone()),
            _ => return Err(format!("Variable '{}' used before initialization", name)),
        },
    }
    Ok(out)
}

pub fn eval_expr(expr: &Expr, state: &ValState, site_id: AllocId) -> Result<HashSet<Val>, String> {
    match expr {
        Expr::Single(op) => eval_operand(op, state, site_id),
        Expr::Binary { left, op, right } => {
            let l_set = eval_operand(left, state, site_id)?;
            let r_set = eval_operand(right, state, site_id)?;

            let mut out = HashSet::new();
            match op {
                Op::Add => {
                    if is_all_num(&l_set) && is_all_num(&r_set) {
                        out.insert(Val::Num);
                    } else if is_all_str(&l_set) && is_all_str(&r_set) {
                        out.insert(Val::Alloc(site_id));
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

pub fn merge_states(a: &ValState, b: &ValState) -> ValState {
    let mut merged = a.clone();
    for (var_id, b_vals) in b {
        let entry = merged.entry(*var_id).or_insert_with(HashSet::new);
        for val in b_vals {
            entry.insert(*val);
        }
    }
    merged
}

pub fn analyze_block(
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