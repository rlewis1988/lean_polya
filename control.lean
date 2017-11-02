import .blackboard .proof_reconstruction .sum_form .prod_form
open polya tactic

meta def expr_to_ineq : expr → tactic (expr × expr × ineq)
| `(%%x ≤ (%%c : ℚ)*%%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.le (slope.some c'))
| `(%%x < (%%c : ℚ)*%%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.lt (slope.some c'))
| `(%%x ≥ (%%c : ℚ)*%%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.ge (slope.some c'))
| `(%%x > (%%c : ℚ)*%%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.gt (slope.some c'))
| _ := failed

meta def expr_to_eq : expr → tactic (expr × expr × ℚ)
| `(%%x = (%%c : ℚ)*%%y) := do c' ← eval_expr rat c, return $ (x, y, c')
| _ := failed


meta def expr_to_sign : expr → tactic (expr × gen_comp)
| `(@eq ℚ %%x (has_zero.zero ℚ)) := return (x, gen_comp.eq)
| `(%%x > (has_zero.zero ℚ)) := return (x, gen_comp.gt)
| `(%%x < (has_zero.zero ℚ)) := return (x, gen_comp.lt)
| `(%%x ≥ (has_zero.zero ℚ)) := return (x, gen_comp.ge)
| `(%%x ≤ (has_zero.zero ℚ)) := return (x, gen_comp.le)
| `(%%x ≠ (has_zero.zero ℚ)) := return (x, gen_comp.ne)
| _ := failed


meta def add_comp_to_blackboard (e : expr) (b : blackboard) : tactic blackboard :=
(do (x, y, ie1) ← expr_to_ineq e,
    id ← return $ ineq_data.mk ie1 (ineq_proof.hyp x y _ e),
--    trace "tac_add_ineq",
    tac_add_ineq b id)
--    return (add_ineq id b).2)
<|>
(do (x, y, ie1) ← expr_to_eq e,
    id ← return $ eq_data.mk ie1 (eq_proof.hyp x y _ e),
--    trace "tac_add_eq",
    tac_add_eq b id)
    --return (add_eq id b).2)
<|>
(do (x, c) ← expr_to_sign e,
    sd ← return $ sign_data.mk c (sign_proof.hyp x _ e),
--    trace "calling tac-add-sign",
    bb ← tac_add_sign b sd,
    trace "tac_add_sign done", return bb)
<|>
fail "add_comp_to_blackboard failed"

meta def add_proof_to_blackboard (b : blackboard) (e : expr) : tactic blackboard :=
(do (x, y, ie1) ← infer_type e >>= expr_to_ineq,
--    trace x, trace y, trace ie1,
    id ← return $ ineq_data.mk ie1 (ineq_proof.hyp x y _ e),
    --return (add_ineq id b).2)
    tac_add_ineq b id)
<|>
(do (x, y, ie1) ← infer_type e >>= expr_to_eq,
    id ← return $ eq_data.mk ie1 (eq_proof.hyp x y _ e),
    --return (add_eq id b).2)
    tac_add_eq b id)
<|>
(do (x, c) ← infer_type e >>= expr_to_sign,
    sd ← return $ sign_data.mk c (sign_proof.hyp x _ e),
--    trace "calling tac-add-sign",
    bb ← tac_add_sign b sd,
--    trace "tac_add_sign done",
    return bb)
<|>
fail "add_comp_to_blackboard failed"

meta def add_proofs_to_blackboard (b : blackboard) (l : list expr) : tactic blackboard :=
monad.foldl add_proof_to_blackboard b l


meta structure module_op :=
(α : Type)
(a : α)
(op : α → polya_state unit)

meta def cycle_ops : ℕ → list (polya_state unit) → polya_state ℕ | n ops := 
do set_changed ff,
   ops.mmap' id,
   ch ← is_changed, cntr ← contr_found,
   if ch && bnot cntr then cycle_ops (n+1) ops else return (n+1)

meta def polya_on_hyps (hys : list name) : tactic unit :=
do exps ← hys.mmap get_local,
   bb ← add_proofs_to_blackboard blackboard.mk_empty exps,
   bb.trace_expr_pairs,
   (n, bb) ← return $ cycle_ops 0 [add_new_ineqs, prod_form.add_new_ineqs] bb,
   trace ("number of cycles:", n),
   trace ("contr found", bb.contr_found),
   pf ← bb.contr.reconstruct,
   apply pf

section
open tactic interactive interactive.types lean.parser

meta def tactic.interactive.add_comp_to_blackboard' (e : parse texpr) (b : blackboard) : tactic blackboard :=
do e' ← i_to_expr e, add_comp_to_blackboard e' b

meta def tactic.interactive.polya (ns : parse (many ident)) : tactic unit :=
polya_on_hyps ns

end
