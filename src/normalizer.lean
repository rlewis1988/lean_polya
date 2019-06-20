import datatypes -- blackboard

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
begin
  intro h,
  cases t,
  case mul : x y {
    cases y,
    case const : c {
      unfold mk_unit at h, rw [prod.mk.inj_iff] at h,
      cases h with h1 h2, subst h1, subst h2,
      simp [eval] },
    repeat {
      unfold mk_unit at h, rw [prod.mk.inj_iff] at h,
      cases h with h1 h2, subst h1, subst h2,
      simp [eval] }},
  repeat {
    unfold mk_unit at h, rw [prod.mk.inj_iff] at h,
    cases h with h1 h2, subst h1, subst h2,
    simp [eval] }
end

def scale (t : @nterm γ _) (a : γ) : @nterm γ _ :=
if a = 0 then
  0
else if a = 1 then
  t
else match t with
| (nterm.const b) := (b * a : γ)
| (nterm.mul t (nterm.const b)) :=
  if b * a = 1 then t else t * (b * a : γ)
| t := t * a
end

theorem scale_eval {t : @nterm γ _} {a : γ} :
  nterm.eval ρ (scale t a) = nterm.eval ρ t * a :=
begin
  by_cases h1 : a = 0,
  { simp [scale, h1] },
  by_cases h2 : a = 1,
  { simp [scale, h1, h2] },
  cases t, case mul : x y
  { cases y, case const : b
    { by_cases h3 : b * a = 1,
      { unfold scale,
        rw [if_neg h1, if_neg h2, if_pos h3],
        unfold eval, --todo: fix norm_cast
        rw [mul_assoc, ← morph.morph_mul],
        rw [h3, morph.morph1, mul_one] },
      { unfold scale,
        rw [if_neg h1, if_neg h2, if_neg h3],
        unfold eval,
        rw [mul_assoc, ← morph.morph_mul],
        rw [nterm.eval_mul, nterm.eval_const],
        refl }},
    repeat { simp [scale, h1, h2, eval] }},
  repeat { simp [scale, h1, h2, eval] }
end

def norm2 (t1 t2 : @nterm γ _) : @nterm γ _ × @nterm γ _ × γ :=
if t1.norm.mk_unit.snd = 0 then
  (0, t2.norm, 1)
else
  (t1.norm.mk_unit.fst, t2.norm.scale (t1.norm.mk_unit.snd⁻¹), t1.norm.mk_unit.snd)

def correctness2 {t1 t2 nt1 nt2 : @nterm γ _} {c : γ} :
  nonzero ρ t1.norm_hyps → nonzero ρ t2.norm_hyps → norm2 t1 t2 = (nt1, nt2, c) →
    nterm.eval ρ ( t1 - t2 ) = nterm.eval ρ ( (nt1 - nt2) * c ) :=
begin
  intros H1 H2,
  intro h, unfold norm2 at h,
  by_cases h0 : t1.norm.mk_unit.snd = 0,
  { rw [if_pos h0, prod.mk.inj_iff, prod.mk.inj_iff] at h,
    cases h with h1 h, cases h with h2 h3,
    subst h1, subst h2, subst h3,
    have h4 : nterm.eval ρ t1 = 0, by {
      apply eq.trans,
      { apply eq.symm, apply nterm.correctness, apply H1 },
      { rw mk_unit_eval,
        { rw [morph.morph0, mul_zero] },
        { rw [← h0, prod.mk.eta] }}},
    suffices : eval ρ t2 = eval ρ t2.norm,
    by { simp [h4, this] },
    apply eq.symm,
    apply nterm.correctness,
    apply H2 },
  rw [if_neg h0, prod.mk.inj_iff, prod.mk.inj_iff] at h,
  cases h with h1 h, cases h with h2 h3,
  rw [h3] at h0 h2,
  have : (c : α) ≠ 0, by {
    intro h, apply h0, --todo: norm_cast should work after the update
    apply morph.morph_inj c h },
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
    rw [← h2, scale_eval, division_def, nterm.correctness],
    { norm_cast },
    { apply H2 }},
  rw [nterm.eval_mul, nterm.eval_const, nterm.eval_sub, nterm.eval_sub],
  rw [sub_mul, hl, hr],
  rw [div_mul_eq_mul_div_comm _ _ this, div_mul_eq_mul_div_comm _ _ this],
  rw [div_self this, mul_one, mul_one]
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
