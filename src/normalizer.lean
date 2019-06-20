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
  if b * a = 1 then t else t * ↑(b * a : γ)
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

def scale2 (t1 t2 : @nterm γ _) : @nterm γ _ × @nterm γ _ × γ :=
if t1.mk_unit.snd = 0 then
  (0, t2, 1)
else
  (t1.mk_unit.fst, t2.scale (t1.mk_unit.snd⁻¹), t1.mk_unit.snd)

def scale2_eval {t1 t2 nt1 nt2 : @nterm γ _} {c : γ} :
  scale2 t1 t2 = (nt1, nt2, c) → nterm.eval ρ ( t1 - t2 ) = nterm.eval ρ ( (nt1 - nt2) * c ) :=
begin
  intro h, unfold scale2 at h,
  by_cases h0 : t1.mk_unit.snd = 0,
  { rw [if_pos h0, prod.mk.inj_iff, prod.mk.inj_iff] at h,
    cases h with h1 h, cases h with h2 h3,
    subst h1, subst h2, subst h3,
    have h4 : nterm.eval ρ t1 = 0, by {
      rw mk_unit_eval,
      { rw [morph.morph0, mul_zero] },
      { rw [← h0, prod.mk.eta] }},
    simp [h4] },
  rw [if_neg h0, prod.mk.inj_iff, prod.mk.inj_iff] at h,
  cases h with h1 h, cases h with h2 h3,
  rw [h3] at h0 h2,
  have : (c : α) ≠ 0, by {
    intro h, apply h0, --todo: norm_cast should work after the update
    apply morph.morph_inj c h },
  have hl : nterm.eval ρ nt1 = nterm.eval ρ t1 / c,
  by {
    apply eq.symm, apply (div_eq_iff_mul_eq this).mpr,
    apply eq.symm, apply mk_unit_eval,
    rw [← h1, ← h3, prod.mk.eta] },
  have hr : nterm.eval ρ nt2 = nterm.eval ρ t2 / c,
  by {
    rw [← h2, scale_eval, division_def],
    { norm_cast }},
  rw [nterm.eval_mul, nterm.eval_const, nterm.eval_sub, nterm.eval_sub],
  rw [sub_mul, hl, hr],
  rw [div_mul_eq_mul_div_comm _ _ this, div_mul_eq_mul_div_comm _ _ this],
  rw [div_self this, mul_one, mul_one],
end

end nterm

open nterm

def aux (t1 t2 : @eterm γ _) : @nterm γ _ × @nterm γ _ × γ :=
scale2 (norm t1) (norm t2)

theorem eval_aux {t1 t2 : @eterm γ _} {nt1 nt2 : @nterm γ _} {c : γ} :
  nonzero ρ t1.to_nterm.norm_hyps →
  nonzero ρ t2.to_nterm.norm_hyps →
  (nt1, nt2, c) = aux t1 t2 →
  eterm.eval ρ t1 - eterm.eval ρ t2 =
    (nterm.eval ρ nt1 - nterm.eval ρ nt2) * c :=
begin
  intros _ _ h0,
  have h1 : eterm.eval ρ t1 = nterm.eval ρ (norm t1),
  by { apply correctness, assumption },
  have h2 : eterm.eval ρ t2 = nterm.eval ρ (norm t2),
  by { apply correctness, assumption },
  rw [h1, h2, ← nterm.eval_sub, ← nterm.eval_sub],
  apply eq.trans,
  { apply scale2_eval, unfold aux at h0, apply eq.symm h0  },
  { apply nterm.eval_mul }
end

end field

namespace tactic.field
open field tactic

--todo: move to tactic.field
meta def prove_norm_hyps (t : @eterm ℚ _) (s : cache_ty) : tactic (list expr × expr) :=
do
  let t_expr : expr := reflect t,
  ρ ← s.dict_expr,

  let nhyps := norm_hyps t,
  nhyps ← monad.mapm (nterm_to_expr `(ℝ) s) nhyps,
  nhyps ← monad.mapm (λ e, to_expr ``(%%e ≠ 0)) nhyps,
  mvars ← monad.mapm mk_meta_var nhyps,

  pe ← to_expr $ mvars.foldr (λ e pe, ``((and.intro %%e %%pe))) ``(trivial),
  h ← to_expr ``(∀ x ∈ norm_hyps %%t_expr, nterm.eval %%ρ x ≠ 0),
  ((), pr) ← solve_aux h (refine ``(list.pall_iff_forall_prop.mp _) >> exact pe >> done),

  return (mvars, pr)

end tactic.field

namespace polya

namespace gen_comp

@[reducible] def to_rel : gen_comp → ℝ → ℝ → Prop
| le := (≤)
| lt := (<)
| ge := (≥)
| gt := (>)
| eq := (=)
| ne := (≠)

variables {u v x y a : ℝ}

lemma lemma_pos_le (h : u - v = (x - y) * a) : a > 0 → u ≤ v → x ≤ y := sorry
lemma lemma_pos_lt (h : u - v = (x - y) * a) : a > 0 → u < v → x < y := sorry
lemma lemma_pos_ge (h : u - v = (x - y) * a) : a > 0 → u ≥ v → x ≥ y := sorry
lemma lemma_pos_gt (h : u - v = (x - y) * a) : a > 0 → u > v → x > y := sorry
lemma lemma_pos_eq (h : u - v = (x - y) * a) : a > 0 → u = v → x = y := sorry
lemma lemma_pos_ne (h : u - v = (x - y) * a) : a > 0 → u ≠ v → x ≠ y := sorry

lemma lemma_neg_le (h : u - v = (x - y) * a) : a < 0 → u ≤ v → x ≥ y := sorry
lemma lemma_neg_lt (h : u - v = (x - y) * a) : a < 0 → u < v → x > y := sorry
lemma lemma_neg_ge (h : u - v = (x - y) * a) : a < 0 → u ≥ v → x ≤ y := sorry
lemma lemma_neg_gt (h : u - v = (x - y) * a) : a < 0 → u > v → x < y := sorry
lemma lemma_neg_eq (h : u - v = (x - y) * a) : a < 0 → u = v → x = y := sorry
lemma lemma_neg_ne (h : u - v = (x - y) * a) : a < 0 → u ≠ v → x ≠ y := sorry

open tactic

meta def foo (op : gen_comp) (a : ℚ) (pr1 pr2 : expr) : tactic expr :=
do
  h3 ← to_expr $
    if a > 0 then ``((%%(reflect a) : ℝ) > 0)
    else ``((%%(reflect a) : ℝ) < 0),
  ((), pr3) ← solve_aux h3 `[sorry],
  let f : name := match op with
  | le := if a > 0 then ``lemma_pos_le else ``lemma_neg_le 
  | lt := if a > 0 then ``lemma_pos_lt else ``lemma_neg_lt
  | ge := if a > 0 then ``lemma_pos_ge else ``lemma_neg_ge
  | gt := if a > 0 then ``lemma_pos_gt else ``lemma_neg_gt
  | eq := if a > 0 then ``lemma_pos_eq else ``lemma_neg_eq
  | ne := if a > 0 then ``lemma_pos_ne else ``lemma_neg_ne
  end,
  mk_app f [pr1, pr3, pr2]

end gen_comp

namespace canonize
open tactic field tactic.field

meta def prove_inequality (lhs rhs pf : expr) (op : gen_comp) : tactic (expr × list expr × expr) :=
do
  gs ← get_goals,
  f ← mk_meta_var `(false),
  set_goals [f],

  let (t1, s) := (eterm_of_expr lhs).run ∅,
  let (t2, s) := (eterm_of_expr rhs).run s,
  ρ ← s.dict_expr,

  (mvars1, h_aux_1) ← prove_norm_hyps t1 s,
  (mvars2, h_aux_2) ← prove_norm_hyps t2 s,

  let (t1', t2', c) := aux t1 t2,
  lhs' ← nterm_to_expr `(ℝ) s t1',
  rhs' ← nterm_to_expr `(ℝ) s t2',
  let c_expr : expr := reflect c,
  let op' := if c > 0 then op else op.reverse,

  h_aux_3 ← to_expr ``((%%(reflect t1'), %%(reflect t2'), %%(c_expr)) = aux %%(reflect t1) %%(reflect t2))
    >>= mk_meta_var,

  e1 ← to_expr ``(%%lhs - %%rhs),
  e2 ← to_expr ``(eterm.eval %%ρ %%(reflect t1) - eterm.eval %%ρ %%(reflect t2)),
  e3 ← to_expr ``((nterm.eval %%ρ %%(reflect t1') - nterm.eval %%ρ %%(reflect t2')) * ↑%%(c_expr)),
  e4 ← to_expr ``((%%lhs' - %%rhs') * ↑%%(c_expr)),

  h1 ← to_expr ``(%%e1 = %%e2),
  ((), pr1) ← solve_aux h1 `[refl, done],
  pr2 ← to_expr ``(eval_aux %%h_aux_1 %%h_aux_2 %%h_aux_3),
  h3 ← to_expr ``(%%e3 = %%e4),
  ((), pr3) ← solve_aux h3 `[refl, done],
  pr ← mk_eq_trans pr2 pr3 >>= mk_eq_trans pr1,
  pr ← gen_comp.foo op c pr pf,

  set_goals gs,
  return (h_aux_3, mvars1 ++ mvars2, pr)

meta def canonize_hyp (e : expr) : tactic (expr × list expr × expr) :=
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

constants x y z : ℝ
constant h1 : z + x * (2 : ℚ) - (3 : ℚ) * y < y * (5 : ℚ)
constant h2 : x * x⁻¹ + (3 : ℚ) * y = 1

run_cmd (do
  e ← to_expr ``(h1),
  (mv, l, pr) ← canonize_hyp e,
  gs ← get_goals,
  set_goals [mv],
  reflexivity,
  set_goals gs,
  
  infer_type mv >>= trace,
  trace "",
  infer_type pr >>= trace,
  trace "",
  monad.mapm (λ x, infer_type x >>= trace >> trace "") l
)

end canonize
end polya
