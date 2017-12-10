import .blackboard .proof_reconstruction .sum_form .prod_form data.hash_map
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


/-meta def add_comp_to_blackboard (e : expr) (b : blackboard) : tactic blackboard :=
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
fail "add_comp_to_blackboard failed"-/

meta def add_proof_to_blackboard (b : blackboard) (e : expr) : tactic blackboard :=
--infer_type e >>= trace >>
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


meta structure module_op (α : Type) :=
(a : α)
(op : α → polya_state α)

meta def module_op.update {α} : module_op α → polya_state (module_op α)
| ⟨a, op⟩ := do a' ← op a, return ⟨a', op⟩

meta structure polya_bundle :=
(modules : hash_map ℕ (λ _, sigma module_op))
(num_modules : ℕ)
(bb : blackboard)

meta def polya_bundle.set_changed (b : bool) : polya_bundle → polya_bundle
| ⟨modules, n, bb⟩ := ⟨modules, n, bb.set_changed b⟩

meta def polya_bundle.is_changed (pb : polya_bundle) : bool :=
pb.bb.is_changed

meta def polya_bundle.contr_found (pb : polya_bundle) : bool :=
pb.bb.contr_found

meta def polya_bundle.set_blackboard (pb : polya_bundle) (bb' : blackboard) : polya_bundle :=
{pb with bb := bb'}

meta def polya_bundle.update_ith (i : ℕ) : polya_bundle → polya_bundle
| ⟨modules, n, bb⟩ := 
  match modules.find i with
  | some ⟨α, a, op⟩ := 
   let (a', bb') := op a bb,
       modules' := modules.insert i ⟨α, a', op⟩ in
   ⟨modules', n, bb'⟩
  | none := ⟨modules, n, bb⟩
  end

meta def polya_bundle.one_cycle (bundle : polya_bundle) : polya_bundle :=
(list.upto bundle.num_modules).reverse.foldl (λ pb k, pb.update_ith k) bundle

meta def polya_bundle.cycle : ℕ → polya_bundle → (ℕ × polya_bundle) | n pb :=
let pb' := pb.set_changed ff,
    pb' := pb'.one_cycle,
    ch := pb'.is_changed, cont := pb'.contr_found in
if ch && bnot cont then polya_bundle.cycle (n+1) pb' else ((n+1), pb')

meta def add_module : module_op (rb_set sum_form_comp_data) :=
{ a := mk_rb_set,
  op := @sum_form.add_new_ineqs }

meta def mul_module : module_op (rb_set prod_form_comp_data) :=
{ a := mk_rb_set,
  op := @prod_form.add_new_ineqs }

meta def polya_bundle.default : polya_bundle :=
{ modules := let m' : hash_map ℕ (λ _, sigma module_op) := ((mk_hash_map id).insert 0 ⟨_, add_module⟩) in m'.insert 1 ⟨_, mul_module⟩, -- elab issues
  num_modules := 2,
  bb := blackboard.mk_empty
}

lemma rat_one_gt_zero : (1 : ℚ) > 0 := zero_lt_one

meta def polya_on_hyps (hys : list name) (rct : bool := tt) : tactic unit :=
do exps ← hys.mmap get_local,
   bb ← add_proof_to_blackboard blackboard.mk_empty `(rat_one_gt_zero),
   bb ← add_proofs_to_blackboard bb exps,
   let pb := polya_bundle.default.set_blackboard bb,
   let (n, pb) := pb.cycle 0,
   trace ("number of cycles:", n),
   trace ("contr found", pb.contr_found),
   if bnot pb.contr_found then /-bb.trace >>-/ fail "polya failed, no contradiction found" else
   if rct then pb.bb.contr.reconstruct >>= apply
   else skip

/-meta def cycle_ops : ℕ → list (Σ α, module_op α) → polya_state ℕ | n ops := 
do set_changed ff,
   ops' ← ops.mmap (λ m, do m' ← m.2.update, return $ sigma.mk m.1 m'),
   ch ← is_changed, cntr ← contr_found,
   if ch && bnot cntr then cycle_ops (n+1) ops' else return (n+1)

meta def polya_on_hyps (hys : list name) : tactic unit :=
do exps ← hys.mmap get_local,
   bb ← add_proofs_to_blackboard blackboard.mk_empty exps,
   bb.trace_expr_pairs,
   (n, bb) ← return $ cycle_ops 0 [add_new_ineqs, prod_form.add_new_ineqs] bb,
   trace ("number of cycles:", n),
   trace ("contr found", bb.contr_found),
   pf ← bb.contr.reconstruct,
   apply pf-/

section
open tactic interactive interactive.types lean.parser

--meta def tactic.interactive.add_comp_to_blackboard' (e : parse texpr) (b : blackboard) : tactic blackboard :=
--do e' ← i_to_expr e, add_comp_to_blackboard e' b

meta def tactic.interactive.polya (ns : parse (many ident)) : tactic unit :=
polya_on_hyps ns

meta def tactic.interactive.polya_l (ns : parse (many ident)) : tactic unit :=
polya_on_hyps ns ff

end
