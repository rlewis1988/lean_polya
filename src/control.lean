import .blackboard .proof_reconstruction .additive .multiplicative data.hash_map .normalizer

open polya tactic


meta structure module_op (α : Type) :=
(a : α)
(op : α → polya_state α)

meta def module_op.update {α} : module_op α → polya_state (module_op α)
| ⟨a, op⟩ := do a' ← op a, return ⟨a', op⟩

meta structure polya_bundle :=
(modules : hash_map ℕ (λ _, sigma module_op))
(num_modules : ℕ)
(bb : blackboard)

namespace polya_bundle


meta def set_changed (b : bool) : polya_bundle → polya_bundle
| ⟨modules, n, bb⟩ := ⟨modules, n, bb.set_changed b⟩

meta def is_changed (pb : polya_bundle) : bool :=
pb.bb.is_changed

meta def contr_found (pb : polya_bundle) : bool :=
pb.bb.contr_found

meta def set_blackboard (pb : polya_bundle) (bb' : blackboard) : polya_bundle :=
{ pb with bb := bb' }

meta def update_ith (i : ℕ) : polya_bundle → polya_bundle
| ⟨modules, n, bb⟩ := 
  match modules.find i with
  | some ⟨α, a, op⟩ := 
   let (a', bb') := (op a).run bb,
       modules' := modules.insert i ⟨α, a', op⟩ in
   ⟨modules', n, bb'⟩
  | none := ⟨modules, n, bb⟩
  end

meta def one_cycle (bundle : polya_bundle) : polya_bundle :=
(list.range bundle.num_modules).reverse.foldl (λ pb k, pb.update_ith k) bundle

meta def cycle : ℕ → polya_bundle → (ℕ × polya_bundle) | n pb :=
let pb' := pb.set_changed ff,
    pb' := pb'.one_cycle,
    ch := pb'.is_changed, cont := pb'.contr_found in
if ch && bnot cont then cycle (trace_val (n+1)) pb' else ((n+1), pb')

end polya_bundle

open native

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

lemma one_gt_zero : (1 : α) > 0 := zero_lt_one

meta def polya_on_hyps (hys : list name) (rct : bool := tt) : tactic unit :=
do exps ← hys.mmap get_local,
   bb ← add_proof_to_blackboard blackboard.mk_empty `(one_gt_zero),
   bb ← add_proofs_to_blackboard bb exps,
   let pb := polya_bundle.default.set_blackboard bb,
   let (n, pb) := pb.cycle 0,
   trace ("number of cycles:", n),
   trace ("contr found", pb.contr_found),
   if bnot pb.contr_found then /-bb.trace >>-/ fail "polya failed, no contradiction found" else
   if rct then pb.bb.contr.reconstruct >>= apply >> skip
   else skip

private meta def try_add_hyp (h : expr) (bb : blackboard) : tactic blackboard :=
add_proof_to_blackboard bb h <|> return bb

private meta def try_add_hyps : list expr → blackboard → tactic blackboard
| [] bb := return bb
| (h::t) bb := do b ← try_add_hyp h bb, try_add_hyps t b

meta def polya_on_all_hyps (rct : bool := tt) : tactic unit :=
do hyps ← local_context,
   bb ← add_proof_to_blackboard blackboard.mk_empty `(one_gt_zero),
   bb ← try_add_hyps hyps bb,
   bb.trace_exprs,
   let pb := polya_bundle.default.set_blackboard bb,
   let (n, pb) := pb.cycle 0,
   trace ("number of cycles:", n),
   trace ("contr found", pb.contr_found),
   if bnot pb.contr_found then /-bb.trace >>-/ fail "polya failed, no contradiction found" else
   if rct then pb.bb.contr.reconstruct >>= apply >> skip
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
