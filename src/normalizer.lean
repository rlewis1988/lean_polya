import datatypes -- blackboard
import tactic.field

namespace field
variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

namespace nterm

def mk_unit : @nterm γ _ → @nterm γ _ × γ
| (nterm.const c) := (1, c)
| (nterm.mul t (nterm.const c)) := (t, c)
| t := (t, 1)

theorem mk_unit_eval {t nt : @nterm γ _} {c : γ} :
  mk_unit t = (nt, c) → nterm.eval ρ t = nterm.eval ρ nt * c :=
sorry

def scale (t : @nterm γ _) (a : γ) : @nterm γ _ :=
if a = 0 then
  0
else if a = 1 then
  t
else match t with
| (nterm.const b) := a * b
| (nterm.mul t (nterm.const b)) := if a * b = 1 then t else t * (a * b : γ)
| t := t * a
end

theorem scale_eval {t : @nterm γ _} {a : γ} :
  nterm.eval ρ (scale t a) = nterm.eval ρ t * a :=
begin
  sorry
end

def norm2 (t1 t2 : @nterm γ _) : @nterm γ _ × @nterm γ _ × γ :=
(t1.norm.mk_unit.fst, t2.norm.scale (t1.norm.mk_unit.snd⁻¹), t1.norm.mk_unit.snd)

def correctness2 {t1 t2 nt1 nt2 : @nterm γ _} {c : γ} :
  nonzero ρ t1.norm_hyps → nonzero ρ t2.norm_hyps → norm2 t1 t2 = (nt1, nt2, c) →
    nterm.eval ρ ( t1 - t2 ) = nterm.eval ρ ( (nt1 - nt2) * c ) :=
begin
  intros H1 H2,
  intro h, unfold norm2 at h, simp only [prod.mk.inj_iff] at h,
  cases h with h1 h, cases h with h2 h3,
  by_cases hc : c = 0,
  { sorry },
  { have : (c : α) ≠ 0, by { sorry }, --todo: norm_cast should work after the update
    have hl : nterm.eval ρ nt1 = nterm.eval ρ t1 / c,
    by {
      apply eq.symm,
      rw ← nterm.correctness,
      { rw div_eq_iff_mul_eq this,
        apply eq.symm, apply mk_unit_eval,
        rw [← h1, ← h3, prod.mk.eta]},
      { apply H1 }},
    have hr : nterm.eval ρ nt2 = nterm.eval ρ t2 / c,
    by {
      rw [← h2, scale_eval, h3, division_def, nterm.correctness],
      { norm_cast },
      { apply H2 }},
    rw [nterm.eval_mul, nterm.eval_const, nterm.eval_sub, nterm.eval_sub],
    rw [sub_mul, hl, hr],
    rw [div_mul_eq_mul_div_comm _ _ this, div_mul_eq_mul_div_comm _ _ this],
    rw [div_self this, mul_one, mul_one] }
end

end nterm
end field

--namespace tactic.field
--open field
--
--end tactic.field

namespace polya
namespace canonize
open tactic

meta def prove_inequality (lhs rhs pf : expr) (op : gen_comp) : tactic expr :=
sorry

meta def canonize_hyp (e : expr) : tactic expr :=
do tp ← infer_type e, match tp with
--| `(0 > %%e) := do ce ← expr.canonize e,
--  mk_app ``canonized_inequality [e, `(0 > %%ce)]
--| `(0 ≥ %%e) := do ce ← expr.canonize e,
--  mk_app ``canonized_inequality [e, `(0 ≥ %%ce)]
--| `(0 < %%e) := do ce ← expr.canonize e,
--  mk_app ``canonized_inequality [e, `(0 < %%ce)]
--| `(0 ≤ %%e) := do ce ← expr.canonize e,
--  mk_app ``canonized_inequality [e, `(0 ≤ %%ce)]
--| `(%%e > 0) := do ce ← expr.canonize e,
--  mk_app ``canonized_inequality [e, `(%%ce > 0)]
--| `(%%e ≥ 0) := do ce ← expr.canonize e,
--  mk_app ``canonized_inequality [e, `(%%ce ≥ 0)]
--| `(%%e < 0) := do ce ← expr.canonize e,
--  mk_app ``canonized_inequality [e, `(%%ce < 0)]
--| `(%%e ≤ 0) := do ce ← expr.canonize e,
--  mk_app ``canonized_inequality [e, `(%%ce ≤ 0)]
| `(%%lhs ≤ %%rhs) := prove_inequality lhs rhs e gen_comp.le
| `(%%lhs < %%rhs) := prove_inequality lhs rhs e gen_comp.lt
| `(%%lhs ≥ %%rhs) := prove_inequality lhs rhs e gen_comp.ge
| `(%%lhs > %%rhs) := prove_inequality lhs rhs e gen_comp.gt
| `(%%lhs = %%rhs) := prove_inequality lhs rhs e gen_comp.eq
| `(%%lhs ≠ %%rhs) := prove_inequality lhs rhs e gen_comp.ne
| _ := do s ← to_string <$> pp e, fail $ "didn't recognize " ++ s
end

end canonize
end polya
