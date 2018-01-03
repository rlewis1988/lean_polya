import .control
open polya monad

meta structure polya_cache := 
(sum_cache : rb_set sum_form_comp_data)
(prod_cache : rb_set prod_form_comp_data)
(bb : blackboard)

meta def polya_tactic := state_t polya_cache tactic

namespace polya_tactic

meta instance : monad polya_tactic :=
state_t.monad _ _

private meta def lift_tactic (α) : tactic α → polya_tactic α :=
state_t.lift

private meta def lift_polya_state (α) : polya_state α → polya_tactic α :=
λ t s, let (a, bb') := t s.bb in return (a, ⟨s.sum_cache, s.prod_cache, bb'⟩)

meta instance polya_tactic.of_tactic : has_monad_lift tactic polya_tactic :=
⟨lift_tactic⟩

meta instance polya_tactic.of_polya_state : has_monad_lift polya_state polya_tactic :=
⟨lift_polya_state⟩

meta instance tpt (α) : has_coe (tactic α) (polya_tactic α) :=
⟨monad_lift⟩

meta instance pst (α) : has_coe (polya_state α) (polya_tactic α) :=
⟨monad_lift⟩

meta def polya_tactic_orelse {α} (t₁ t₂ : polya_tactic α) : polya_tactic α :=
λ ss ts, result.cases_on (t₁ ss ts)
  result.success
  (λ e₁ ref₁ s', result.cases_on (t₂ ss ts)
    result.success
    result.exception)

meta instance : monad_fail polya_tactic :=
{ polya_tactic.monad with fail := λ α s, (tactic.fail (to_fmt s) : polya_tactic α) }

meta instance : alternative polya_tactic :=
{ polya_tactic.monad with
  failure := λ α, @tactic.failed α,
  orelse := @polya_tactic_orelse }

meta def step {α} (c : polya_tactic α) : polya_tactic unit :=
c >> return ()

meta def save_info (p : pos) : polya_tactic unit :=
return ()

meta def execute (c : polya_tactic unit) : tactic unit :=
do bb ← add_proof_to_blackboard blackboard.mk_empty `(rat_one_gt_zero),
let pc : polya_cache := ⟨mk_rb_set, mk_rb_set, bb⟩ in 
c pc >> return ()


/-meta def istep {α} (line0 col0 line col : ℕ) (c : polya_tactic α) : polya_tactic unit :=
tactic.istep line0 col0 line col c-/


meta def assert_claims_with_names : list expr → list name → tactic unit 
| [] _ := tactic.skip
| (h::hs) (n::ns) := tactic.note n none h >> assert_claims_with_names hs ns
| (h::hs) [] := do n ← tactic.mk_fresh_name, tactic.note n none h, assert_claims_with_names hs []

namespace interactive
open lean lean.parser interactive interactive.types

meta def add_expr (e : parse texpr) : polya_tactic unit :=
λ ps, do bb' ← tactic.i_to_expr e >>= process_expr_tac ps.bb, return ((), ⟨ps.sum_cache, ps.prod_cache, bb'⟩)

meta def add_comparison (e : parse texpr) : polya_tactic unit :=
λ ps, do bb' ← tactic.i_to_expr e >>= add_proof_to_blackboard ps.bb, return ((), ⟨ps.sum_cache, ps.prod_cache, bb'⟩)

meta def add_hypotheses (ns : parse (many ident)) : polya_tactic unit :=
λ ps,
do exps ← ns.mmap tactic.get_local,
   bb' ← add_proofs_to_blackboard ps.bb exps,
   return ((), ⟨ps.sum_cache, ps.prod_cache, bb'⟩)

meta def additive : polya_tactic unit :=
λ ps,
let (nsc, bb') := sum_form.add_new_ineqs ps.sum_cache ps.bb in
return ((), ⟨nsc, ps.prod_cache, bb'⟩)

meta def multiplicative : polya_tactic unit :=
λ ps,
let (nsc, bb') := prod_form.add_new_ineqs ps.prod_cache ps.bb in
return ((), ⟨ps.sum_cache, nsc, bb'⟩)

meta def trace_exprs : polya_tactic unit :=
do ps ← state_t.read,
   ps.bb.trace_exprs

meta def trace_state : polya_tactic unit :=
do ps ← state_t.read,
   ps.bb.trace

meta def trace_contr : polya_tactic unit :=
do ps ← state_t.read,
   match ps.bb.contr with
   | contrad.none := tactic.trace "no contradiction found"
   | _ := tactic.trace "contradiction found"
   end

meta def reconstruct : polya_tactic unit :=
do ps ← state_t.read,
   e ← ps.bb.contr.reconstruct,
   tactic.apply e


meta def extract_comparisons_between (lhs rhs : parse parser.pexpr) (nms : parse with_ident_list) : polya_tactic unit :=
do lhs' ← tactic.i_to_expr lhs,
   rhs' ← tactic.i_to_expr rhs,
   iqs ← get_ineqs lhs' rhs',
   iqse ← iqs.data.mmap (λ iq, iq.prf.reconstruct),
   assert_claims_with_names iqse nms

end interactive
end polya_tactic 
#exit
