use std::collections::HashSet;
use crate::*;
use crate::algo1::{analyze_block, eval_expr, merge_states};

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

fn indent_str(indent: usize) -> String {
    "    ".repeat(indent)
}

pub fn emit_block(
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

    Ok(currently_alive)
}