import .control
open polya monad native

meta structure polya_cache := 
(sum_cache : rb_set sum_form_comp_data)
(prod_cache : rb_set prod_form_comp_data)
(bb : blackboard)

meta def polya_tactic := state_t polya_cache tactic

namespace polya_tactic

meta instance : monad polya_tactic := state_t.monad
meta instance : monad_state polya_cache polya_tactic := state_t.monad_state

meta instance polya_tactic.of_tactic : has_monad_lift tactic polya_tactic :=
state_t.has_monad_lift

private meta def lift_polya_state (α) (m : polya_state α) : polya_tactic α :=
do
    s ← get,
    let (a, bb') := m.run s.bb,
    put ⟨s.sum_cache, s.prod_cache, bb'⟩,
    return a

meta instance polya_tactic.of_polya_state : has_monad_lift polya_state polya_tactic :=
⟨lift_polya_state⟩

meta instance tpt (α) : has_coe (tactic α) (polya_tactic α) :=
⟨monad_lift⟩

meta instance pst (α) : has_coe (polya_state α) (polya_tactic α) :=
⟨monad_lift⟩

meta instance : alternative polya_tactic := state_t.alternative

meta def step {α} (c : polya_tactic α) : polya_tactic unit :=
c >> return ()

meta def save_info (p : pos) : polya_tactic unit :=
return ()

meta def execute (c : polya_tactic unit) : tactic unit :=
do bb ← add_proof_to_blackboard blackboard.mk_empty `(one_gt_zero),
let pc : polya_cache := ⟨mk_rb_set, mk_rb_set, bb⟩ in 
c.run pc >> return ()


/-meta def istep {α} (line0 col0 line col : ℕ) (c : polya_tactic α) : polya_tactic unit :=
tactic.istep line0 col0 line col c-/


meta def assert_claims_with_names : list expr → list name → tactic unit 
| [] _ := tactic.skip
| (h::hs) (n::ns) := tactic.note n none h >> assert_claims_with_names hs ns
| (h::hs) [] := do n ← tactic.mk_fresh_name, tactic.note n none h, assert_claims_with_names hs []

namespace interactive
open lean lean.parser interactive interactive.types

meta def add_expr (e : parse texpr) : polya_tactic unit :=
do
    ps ← get,
    bb' ← ↑(tactic.i_to_expr e >>= process_expr_tac ps.bb),
    put ⟨ps.sum_cache, ps.prod_cache, bb'⟩

meta def add_comparison (e : parse texpr) : polya_tactic unit :=
do
    ps ← get,
    bb' ← ↑(tactic.i_to_expr e >>= add_proof_to_blackboard ps.bb),
    put ⟨ps.sum_cache, ps.prod_cache, bb'⟩

meta def add_hypotheses (ns : parse (many ident)) : polya_tactic unit :=
do 
    ps ← get,
    exps ← ns.mmap ↑tactic.get_local,
    bb' ← add_proofs_to_blackboard ps.bb exps,
    put ⟨ps.sum_cache, ps.prod_cache, bb'⟩

meta def additive : polya_tactic unit :=
do
    ps ← get,
    let (nsc, bb') := (sum_form.add_new_ineqs ps.sum_cache).run ps.bb in
    put ⟨nsc, ps.prod_cache, bb'⟩

meta def multiplicative : polya_tactic unit :=
do
    ps ← get,
    let (nsc, bb') := (prod_form.add_new_ineqs ps.prod_cache).run ps.bb in
    put ⟨ps.sum_cache, nsc, bb'⟩

meta def trace_exprs : polya_tactic unit :=
do
    ps ← get,
    ps.bb.trace_exprs

meta def trace_state : polya_tactic unit :=
do
    ps ← get,
    ps.bb.trace

meta def trace_contr : polya_tactic unit :=
do
    ps ← get,
    match ps.bb.contr with
    | contrad.none := tactic.trace "no contradiction found"
    | _ := tactic.trace "contradiction found"
    end

meta def reconstruct : polya_tactic unit :=
do
    ps ← get,
    e ← ps.bb.contr.reconstruct,
    _ ← tactic.apply e,
    return ()

meta def extract_comparisons_between (lhs rhs : parse parser.pexpr) (nms : parse with_ident_list) : polya_tactic unit :=
do lhs' ← tactic.i_to_expr lhs,
   rhs' ← tactic.i_to_expr rhs,
   iqs ← get_ineqs lhs' rhs',
   iqse ← iqs.data.mmap (λ iq, iq.prf.reconstruct),
   assert_claims_with_names iqse nms

end interactive
end polya_tactic 

open lean.parser interactive

--meta def tactic.interactive.add_comp_to_blackboard' (e : parse texpr) (b : blackboard) : tactic blackboard :=
--do e' ← i_to_expr e, add_comp_to_blackboard e' b

meta def tactic.interactive.polya (ns : parse (many ident)) : tactic unit :=
polya_on_hyps ns

meta def tactic.interactive.polya_l (ns : parse (many ident)) : tactic unit :=
polya_on_hyps ns ff

meta def tactic.interactive.polya_all (rct : parse (optional (tk "!"))) : tactic unit :=
polya_on_all_hyps rct.is_some
