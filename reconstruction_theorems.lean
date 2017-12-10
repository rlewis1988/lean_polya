import .datatypes .norm_num
namespace polya


theorem eq_or_gt_of_ge {α} [decidable_linear_order α] {a b : α} (h : a ≥ b) : a = b ∨ a > b :=
have h1 : ¬ b > a, from not_lt_of_ge h,
eq_or_lt_of_not_lt h1

theorem eq_or_lt_of_le {α} [decidable_linear_order α] {a b : α} (h : a ≤ b) : a = b ∨ a < b :=
have h1 : ¬ b < a, from not_lt_of_ge h,
have h2 : b = a ∨ a < b, from eq_or_lt_of_not_lt h1,
h2.elim (λ e, or.inl (e.symm)) or.inr

theorem le_of_eq_or_lt {α} [decidable_linear_order α] {a b : α} (h : a = b ∨ a < b) : a ≤ b :=
h.elim (λ e, by rw e; reflexivity) le_of_lt

theorem ge_of_eq_or_gt {α} [decidable_linear_order α] {a b : α} (h : a = b ∨ a > b) : a ≥ b :=
h.elim (λ e, by rw e; change b ≤ b; reflexivity) le_of_lt

class comp_op (op : ℚ → ℚ → Prop) :=
(rev_op : ℚ → ℚ → Prop)
(rev_op_is_rev : ∀ {x y}, rev_op y x ↔ op x y)
(rel_of_sub_rel_zero : ∀ {x y : ℚ}, op (x-y) 0 ↔ op x y)
(op_mul : ∀ {x y c : ℚ}, c > 0 → op x y → op (c*x) (c*y))
(op_inv : ∀ {x y z : ℚ}, x > 0 → op z (x*y) → op ((rat.pow x (-1))*z) y)

class weak_comp_op (op) extends comp_op op :=
(strict_op : ℚ → ℚ → Prop)
(disj : ∀ {x y}, op x y ↔ x = y ∨ strict_op x y)
(ne_of_str : ∀ {x y}, strict_op x y → x ≠ y)

instance colt : comp_op (@has_lt.lt ℚ _) :=
{rev_op := @gt ℚ _,
 rev_op_is_rev := by intros; reflexivity,
 rel_of_sub_rel_zero := begin intros, constructor, exact lt_of_sub_neg, exact sub_neg_of_lt end,
 op_mul := begin intros, refine mul_lt_mul_of_pos_left _ _, repeat {assumption} end,
 op_inv := begin intros, fapply lt_of_mul_lt_mul_left, exact x, rw [←mul_assoc, rat.mul_pow_neg_one, one_mul], assumption, apply ne_of_gt, assumption, apply le_of_lt, assumption end }

instance cole : weak_comp_op (@has_le.le ℚ _) :=
{rev_op := @ge ℚ _,
 rev_op_is_rev := by intros; reflexivity,
 rel_of_sub_rel_zero := begin intros, constructor, apply le_of_sub_nonpos, apply sub_nonpos_of_le end,
 op_mul := begin intros, apply mul_le_mul_of_nonneg_left, assumption, apply le_of_lt, assumption end,
 strict_op := @has_lt.lt ℚ _,
 disj := begin intros, constructor, apply eq_or_lt_of_le, apply le_of_eq_or_lt end,
 ne_of_str := @ne_of_lt ℚ _,
 op_inv := begin intros, fapply le_of_mul_le_mul_left, exact x, rw [←mul_assoc, rat.mul_pow_neg_one, one_mul], assumption, apply ne_of_gt, assumption, assumption end}

instance cogt : comp_op (@gt ℚ _) :=
{rev_op := @has_lt.lt ℚ _,
 rev_op_is_rev := by intros; reflexivity,
 rel_of_sub_rel_zero := begin intros, constructor, exact lt_of_sub_pos, exact sub_pos_of_lt end,
 op_mul := begin intros, refine mul_lt_mul_of_pos_left _ _, repeat {assumption} end,
 op_inv := begin intros, fapply lt_of_mul_lt_mul_left, exact x, rw [←mul_assoc, rat.mul_pow_neg_one, one_mul], assumption, apply ne_of_gt, assumption, apply le_of_lt, assumption end}

instance coge : weak_comp_op (@ge ℚ _) :=
{rev_op := @has_le.le ℚ _,
 rev_op_is_rev := by intros; reflexivity,
 rel_of_sub_rel_zero := begin intros, constructor, apply le_of_sub_nonneg, apply sub_nonneg_of_le end,
 op_mul := begin intros, apply mul_le_mul_of_nonneg_left, assumption, apply le_of_lt, assumption end,
 strict_op := @gt ℚ _,
 disj := begin intros, constructor, apply eq_or_gt_of_ge, apply ge_of_eq_or_gt end,
 ne_of_str := @ne_of_gt ℚ _,
 op_inv := begin intros, fapply le_of_mul_le_mul_left, exact x, rw [←mul_assoc, rat.mul_pow_neg_one, one_mul], assumption, apply ne_of_gt, assumption, assumption end}

instance coeq : comp_op (@eq ℚ) :=
{rev_op := @eq ℚ,
 rev_op_is_rev := by cc,
 rel_of_sub_rel_zero := by intros; apply sub_eq_zero_iff_eq,
 op_mul := by cc,
 op_inv := begin intros, fapply eq_of_mul_eq_mul_left, exact x, apply ne_of_gt, assumption, rw [←mul_assoc, rat.mul_pow_neg_one, one_mul ], assumption, apply ne_of_gt, assumption end
}

@[reducible] private def strict_op := weak_comp_op.strict_op

@[reducible] private def rev := comp_op.rev_op
lemma rev_op_is_rev {o x y} [comp_op o] : rev o y x ↔ o x y := comp_op.rev_op_is_rev _ 

lemma op_mul_neg {o}  {x y c : ℚ} [comp_op o] (hc : c < 0) (h : o x y) : rev o (c*x) (c*y) :=
have o (x-y) 0, from (comp_op.rel_of_sub_rel_zero o).mpr h,
have o (-c*(x-y)) ((-c)*0), from comp_op.op_mul (neg_pos_of_neg hc) this,
have o (c*y - c*x) 0, begin
 rw [mul_sub, mul_zero, ←neg_mul_eq_neg_mul, ←neg_mul_eq_neg_mul, sub_neg_eq_add, add_comm] at this, assumption 
end,
rev_op_is_rev.mpr ((comp_op.rel_of_sub_rel_zero o).mp this)

/-
set_option pp.all true
example : (-1 : ℚ) < 0 :=
begin
apply neg_of_neg_pos, -- fails
--apply (@neg_of_neg_pos ℚ _), -- succeeds
--refine neg_of_neg_pos _, -- succeeds
end

example : (-1 : ℤ) < 0 :=
begin
apply neg_of_neg_pos, -- succeeds
end
-/

lemma op_neg {o} {x y : ℚ} [comp_op o] (h : o x y) : rev o (-x) (-y) :=
begin
rw [neg_eq_neg_one_mul, neg_eq_neg_one_mul y],
apply op_mul_neg,
refine neg_of_neg_pos _,
exact zero_lt_one,
assumption
end
 
theorem sym_op_pos {o} [comp_op o] {lhs rhs c : ℚ} (hc : c > 0) (h : o lhs (c*rhs)) : rev o rhs ((1/c)*lhs) :=
have h' : o ((1/c)*lhs) ((1/c)*(c*rhs)), from comp_op.op_mul (one_div_pos_of_pos hc) h,
suffices o ((1/c)*lhs) rhs, by rw rev_op_is_rev; assumption,
by rw [←mul_assoc, one_div_mul_cancel (ne_of_gt hc), one_mul] at h'; assumption
--comp_op.rev_recip hc h

theorem sym_op_neg {o} [comp_op o] {lhs rhs c : ℚ} (hc : c < 0) (h : o lhs (c*rhs)) : o rhs ((1/c)*lhs) :=
have h' : rev o ((1/c)*lhs) ((1/c)*(c*rhs)), begin
apply op_mul_neg,
refine one_div_neg_of_neg _, repeat {assumption}
end,
suffices rev o ((1/c)*lhs) rhs, begin
apply rev_op_is_rev.mp,
assumption
end,
by rw [←mul_assoc, one_div_mul_cancel (ne_of_lt hc), one_mul] at h'; assumption

theorem diseq_sym {lhs rhs c : ℚ} (hc : c ≠ 0) (h : lhs ≠ c*rhs) : rhs ≠ (1/c) * lhs := 
sorry

theorem eq_sym {lhs rhs c : ℚ} (hc : c ≠ 0) (h : lhs = c*rhs) : rhs = (1/c) * lhs :=
sorry

/-section ineq_sym
variables {lhs rhs c : ℚ}
theorem ineq_sym_le_pos (hc : c > 0) (h : lhs ≤ c*rhs) : rhs ≥ (1/c) * lhs := 
sorry

theorem ineq_sym_lt_pos (hc : c > 0) (h : lhs < c*rhs) : rhs > (1/c) * lhs := 
sorry

theorem ineq_sym_ge_pos (hc : c > 0) (h : lhs ≥ c*rhs) : rhs ≤ (1/c) * lhs := 
sorry

theorem ineq_sym_gt_pos (hc : c > 0) (h : lhs > c*rhs) : rhs < (1/c) * lhs := 
sorry

theorem ineq_sym_le_neg (hc : c < 0) (h : lhs ≤ c*rhs) : rhs ≤ (1/c) * lhs := 
sorry

theorem ineq_sym_lt_neg (hc : c < 0) (h : lhs < c*rhs) : rhs < (1/c) * lhs := 
sorry

theorem ineq_sym_ge_neg (hc : c < 0) (h : lhs ≥ c*rhs) : rhs ≥ (1/c) * lhs := 
sorry

theorem ineq_sym_gt_neg (hc : c < 0) (h : lhs > c*rhs) : rhs > (1/c) * lhs := 
sorry

meta def name_of_comp_pos : comp → name
| comp.le := ``ineq_sym_le_pos
| comp.lt := ``ineq_sym_lt_pos
| comp.ge := ``ineq_sym_ge_pos
| comp.gt := ``ineq_sym_gt_pos

meta def name_of_comp_neg : comp → name
| comp.le := ``ineq_sym_le_neg
| comp.lt := ``ineq_sym_lt_neg
| comp.ge := ``ineq_sym_ge_neg
| comp.gt := ``ineq_sym_gt_neg

meta def name_of_c_and_comp (c : ℚ) (cmp : comp) : name :=
if c ≥ 0 then name_of_comp_pos cmp else name_of_comp_neg cmp

end ineq_sym-/

/-theorem ineq_diseq_le {lhs rhs c : ℚ} (hc : lhs ≠ c*rhs) (h : lhs ≤ c*rhs) : lhs < c*rhs :=
or.elim (lt_or_eq_of_le h) (id) (λ hp, absurd hp hc)

theorem ineq_diseq_ge {lhs rhs c : ℚ} (hc : lhs ≠ c*rhs) (h : lhs ≥ c*rhs) : lhs > c*rhs :=
or.elim (lt_or_eq_of_le h) (id) (λ hp, absurd (eq.symm hp) hc)-/

theorem ineq_diseq {lhs rhs c : ℚ} {o} [weak_comp_op o] (hc : lhs ≠ c*rhs) (h : o lhs (c*rhs)) : 
        weak_comp_op.strict_op o lhs (c*rhs) :=
or.elim ((weak_comp_op.disj o).mp h) (λ t, absurd t hc) id

/-theorem ineq_diseq_sign_lhs_le {lhs rhs : ℚ} (hc : lhs ≠ 0) (h : lhs ≤ 0*rhs) : lhs < 0*rhs :=
sorry

theorem ineq_diseq_sign_lhs_ge {lhs rhs : ℚ} (hc : lhs ≠ 0) (h : lhs ≥ 0*rhs) : lhs > 0*rhs :=
sorry-/

theorem ineq_diseq_sign_lhs {lhs rhs : ℚ} (hc : lhs ≠ 0) {o} [weak_comp_op o] (h : o lhs (0*rhs)) :
        weak_comp_op.strict_op o lhs (0*rhs) :=
begin
apply ineq_diseq,
simp *, assumption
end

/-theorem ineq_diseq_sign_rhs_le {rhs : ℚ} (hc : rhs ≠ 0) (h : rhs ≤ 0) : rhs < 0 :=
sorry

theorem ineq_diseq_sign_rhs_ge {rhs : ℚ} (hc : rhs ≠ 0) (h : rhs ≥ 0) : rhs > 0 :=
sorry-/

theorem ineq_diseq_sign_rhs {rhs : ℚ} (hc : rhs ≠ 0) {o} [weak_comp_op o] (h : o rhs 0) : weak_comp_op.strict_op o rhs 0 :=
begin
cases (weak_comp_op.disj o).mp h,
repeat {cc}
end

theorem op_ineq {lhs rhs c : ℚ} (h1 : lhs ≤ c*rhs) (h2 : lhs ≥ c*rhs) : lhs = c*rhs :=
have h : lhs = c*rhs ∨ lhs < c*rhs, from eq_or_lt_of_le h1,
h.elim id (λ e, absurd h2 (not_le_of_gt e))

theorem op_zero_of_zero_op_neg_mul {o} [comp_op o] {c q : ℚ} (h : c < 0) (h2 : o 0 (c*q)) : o q 0 :=
have hc : 1 / c < 0, from one_div_neg_of_neg h,
have h' : _, from op_mul_neg hc h2,
have h'' : _, from rev_op_is_rev.mp h',
have hc' : (1/c)*(c*q) = q, by rw [←mul_assoc, one_div_mul_cancel, one_mul]; apply ne_of_lt h,
by rw [hc', mul_zero] at h''; assumption

theorem rev_op_zero_of_neg_mul_op_zero {o} [comp_op o] {c q : ℚ} (h : c < 0) (h2 : o (c*q) 0) : rev o q 0 :=
have hc : 1 / c < 0, from one_div_neg_of_neg h,
have h' : _, from op_mul_neg hc h2,
have hc' : (1/c)*(c*q) = q, by rw [←mul_assoc, one_div_mul_cancel, one_mul]; apply ne_of_lt h,
by rw [hc', mul_zero] at h'; assumption

theorem op_zero_of_pos_mul_op_zero {o} [comp_op o] {c q : ℚ} (h : c > 0) (h2 : o (c*q) 0) : o q 0 :=
have hc : 1 / c > 0, from one_div_pos_of_pos h,
have h' : _, from comp_op.op_mul hc h2,
have hc' : (1/c)*(c*q) = q, by rw [←mul_assoc, one_div_mul_cancel, one_mul]; apply ne_of_gt h,
by rw [hc', mul_zero] at h'; assumption

section
variables {lhs : ℚ} (rhs : ℚ)
/-theorem zero_mul_le (h : lhs ≤ 0) : lhs ≤ 0*rhs := by rw zero_mul; assumption
theorem zero_mul_lt (h : lhs < 0) : lhs < 0*rhs := by rw zero_mul; assumption
theorem zero_mul_ge (h : lhs ≥ 0) : lhs ≥ 0*rhs := by rw zero_mul; assumption
theorem zero_mul_gt (h : lhs > 0) : lhs > 0*rhs := by rw zero_mul; assumption

meta def zero_mul_name_of_comp : comp → name
| comp.le := ``zero_mul_le
| comp.lt := ``zero_mul_lt
| comp.ge := ``zero_mul_ge
| comp.gt := ``zero_mul_gt-/
theorem op_zero_mul {o} [comp_op o] (h : o lhs 0) : o lhs (0*rhs) := by simp *

variable {rhs}
/-theorem zero_mul_le' (h : lhs ≤ 0*rhs) : lhs ≤ 0 := by rw -(zero_mul rhs); assumption
theorem zero_mul_lt' (h : lhs < 0*rhs) : lhs < 0 := by rw -(zero_mul rhs); assumption
theorem zero_mul_ge' (h : lhs ≥ 0*rhs) : lhs ≥ 0 := by rw -(zero_mul rhs); assumption
theorem zero_mul_gt' (h : lhs > 0*rhs) : lhs > 0 := by rw -(zero_mul rhs); assumption-/

theorem op_zero_mul' {o} [comp_op o] (h : o lhs (0*rhs)) : o lhs 0 := by rw ←(zero_mul rhs); assumption


/-meta def zero_mul'_name_of_comp : comp → name
| comp.le := ``zero_mul_le'
| comp.lt := ``zero_mul_lt'
| comp.ge := ``zero_mul_ge'
| comp.gt := ``zero_mul_gt'-/

end

theorem eq_zero_of_eq_mul_zero {lhs rhs : ℚ} (h : lhs = 0*rhs) : lhs = 0 :=
by rw ←(zero_mul rhs); assumption

theorem ne_zero_of_ne_mul_zero {lhs rhs : ℚ} (h : lhs ≠ 0*rhs) : lhs ≠ 0 :=
by rw ←(zero_mul rhs); assumption

theorem eq_zero_of_two_eqs_rhs {lhs rhs c1 c2 : ℚ} (h : lhs = c1*rhs) (h2 : lhs = c2*rhs) (hc : c1 ≠ c2) : rhs = 0 :=
begin
 rw h at h2,
 have h3 := sub_eq_zero_of_eq h2,
 rw ←sub_mul at h3,
 cases eq_zero_or_eq_zero_of_mul_eq_zero h3,
 apply absurd (eq_of_sub_eq_zero a) hc,
 assumption
end

theorem eq_zero_of_two_eqs_lhs {lhs rhs c1 c2 : ℚ} (h : lhs = c1*rhs) (h2 : lhs = c2*rhs) (hc : c1 ≠ c2) : lhs = 0 :=
have hr : rhs = 0, from eq_zero_of_two_eqs_rhs h h2 hc,
begin rw hr at h, rw mul_zero at h, assumption end

section
variables {lhs rhs c : ℚ} (h : lhs = 0)
include h

/-
PUT THEOREMS FOR ineq_of_ineq_and_eq_zero_rhs here
-/

end

section
variables {lhs rhs c d : ℚ} 
--include h

/- there are 16 possibilities here!
theorem sub_le_zero_of_le {a b : ℚ} (h : a ≤ b) : a - b ≤ 0 := sorry
theorem sub_lt_zero_of_lt {a b : ℚ} (h : a < b) : a - b < 0 := sorry
theorem sub_ge_zero_of_ge {a b : ℚ} (h : a ≥ b) : a - b ≥ 0 := sorry
theorem sub_gt_zero_of_gt {a b : ℚ} (h : a > b) : a - b > 0 := sorry-/

theorem sub_op_zero_of_op {a b : ℚ} {o} [comp_op o] (h : o a b) : o (a-b) 0 :=
(comp_op.rel_of_sub_rel_zero _).mpr h

variable (h : lhs = d*rhs)
include h

-- is this used?
theorem op_eq_coeff_sub_pos {o} [comp_op o] (h1 : o lhs (c*rhs)) (h2 : d - c > 0) : o rhs 0 :=
have o (d*rhs) (c*rhs), by rw ←h; assumption,
have o (d*rhs - c*rhs) 0, from sub_op_zero_of_op this,
have o ((d-c)*rhs) 0, by rw sub_mul; assumption,
have dc : 1/(d-c) > 0, from one_div_pos_of_pos h2,
let cmp := comp_op.op_mul dc this in
begin
rw [mul_zero, ←mul_assoc, div_mul_cancel _ (ne_of_gt h2), one_mul] at cmp,
assumption
end

/-theorem le_gt_rhs (h1 : lhs ≤ c*rhs) (h2 : d - c > 0) : rhs ≤ 0 :=
have d*rhs ≤ c*rhs, by rw -h; assumption,
have d*rhs - c*rhs ≤ 0, from sub_le_zero_of_le this,
have (d - c)*rhs ≤ 0, by rw sub_mul; assumption,
show rhs ≤ 0, from nonpos_of_mul_nonpos_left this h2

theorem lt_gt_rhs (h1 : lhs < c*rhs) (h2 : d - c > 0) : rhs < 0 :=
have d*rhs < c*rhs, by rw -h; assumption,
have d*rhs - c*rhs < 0, from sub_lt_zero_of_lt this,
have (d - c)*rhs < 0, by rw sub_mul; assumption,
show rhs < 0, from neg_of_mul_neg_left this (le_of_lt h2)

theorem ge_gt_rhs (h1 : lhs ≥ c*rhs) (h2 : d - c > 0) : rhs ≥ 0 :=
have d*rhs ≥ c*rhs, by rw -h; assumption,
have d*rhs - c*rhs ≥ 0, from sub_ge_zero_of_ge this,
have (d - c)*rhs ≥ 0, by rw sub_mul; assumption,
show rhs ≥ 0, from nonneg_of_mul_nonneg_left this h2

theorem gt_gt_rhs (h1 : lhs > c*rhs) (h2 : d - c > 0) : rhs > 0 :=
have d*rhs > c*rhs, by rw -h; assumption,
have d*rhs - c*rhs > 0, from sub_gt_zero_of_gt this,
have (d - c)*rhs > 0, by rw sub_mul; assumption,
show rhs > 0, from pos_of_mul_pos_left this (le_of_lt h2)-/

omit h
theorem sub_lt_of_lt (h1 : lhs < c*rhs) : 1*lhs + (-c)*rhs < 0 :=
begin
 simp,
 apply sub_neg_of_lt _,
 rw mul_comm, assumption
end

theorem sub_le_of_le (h1 : lhs ≤ c*rhs) : 1*lhs + (-c)*rhs ≤ 0 :=
begin
 simp,
 apply sub_nonpos_of_le,
 rw mul_comm, assumption
end

theorem sub_lt_of_gt (h1 : lhs > c*rhs) : (-1)*lhs + c*rhs < 0 :=
begin
 rw [add_comm, ←neg_mul_eq_neg_mul, one_mul],
 apply sub_neg_of_lt _,
 assumption
end

theorem sub_le_of_ge (h1 : lhs ≥ c*rhs) : (-1)*lhs + c*rhs ≤ 0 :=
begin
 rw [add_comm, ←neg_mul_eq_neg_mul, one_mul],
 apply sub_nonpos_of_le,
 assumption
end

theorem mul_lt_of_gt {rhs : ℚ} (h1 : lhs > 0*rhs) : (-1)*lhs < 0 :=
by simp; simp at h1; apply neg_neg_of_pos h1

theorem mul_le_of_ge {rhs : ℚ} (h1 : lhs ≥ 0*rhs) : (-1)*lhs ≤ 0 :=
by simp; simp at h1; apply neg_nonpos_of_nonneg h1

theorem mul_lt_of_lt {rhs : ℚ} (h1 : lhs < 0*rhs) : 1*lhs < 0 :=
by simp; simp at h1; assumption

theorem mul_le_of_le {rhs : ℚ} (h1 : lhs ≤ 0*rhs) : 1*lhs ≤ 0 :=
by simp; simp at h1; assumption

end


meta def sum_form_name_of_comp_single : comp → name
| comp.lt := ``mul_lt_of_lt
| comp.le := ``mul_le_of_le
| comp.gt := ``mul_lt_of_gt
| comp.ge := ``mul_le_of_ge

meta def sum_form_name_of_comp : comp → name
| comp.lt := ``sub_lt_of_lt
| comp.le := ``sub_le_of_le
| comp.gt := ``sub_lt_of_gt
| comp.ge := ``sub_le_of_ge

theorem gt_self_contr {e : ℚ} (h : e > 1*e) : false :=
begin apply lt_irrefl e, rw one_mul at h, assumption end

theorem lt_self_contr {e : ℚ} (h : e < 1*e) : false :=
begin apply lt_irrefl e, rw one_mul at h, assumption end

theorem le_gt_contr {e : ℚ} (h1 : e ≤ 0) (h2 : e > 0) : false :=
not_le_of_gt h2 h1

theorem ge_lt_contr {e : ℚ} (h1 : e ≥ 0) (h2 : e < 0) : false :=
not_le_of_gt h2 h1

theorem gt_lt_contr {e : ℚ} (h1 : e > 0) (h2 : e < 0) : false :=
not_le_of_gt h1 (le_of_lt h2)

theorem op_of_sum_op_zero_pos {o} [comp_op o] {lhs rhs a b : ℚ} (h : o (a*lhs + b*rhs) 0)
        (h2 : a > 0) : o lhs (((-b)/a)*rhs) :=
have o (a*lhs - -(b*rhs)) 0, by rw sub_neg_eq_add; assumption,
have o (a*lhs) (-(b*rhs)), from (comp_op.rel_of_sub_rel_zero _).mp this,
let np := comp_op.op_mul (one_div_pos_of_pos h2) this in
begin
rw [←mul_assoc, one_div_mul_cancel (ne_of_gt h2), one_mul, neg_mul_eq_neg_mul, ←mul_assoc, div_mul_eq_mul_div, one_mul] at np, assumption
end

theorem op_of_sum_op_zero_neg {o} [comp_op o] {lhs rhs a b : ℚ} (h : o (a*lhs + b*rhs) 0)
        (h2 : a < 0) : rev o lhs (((-b)/a)*rhs) :=
have o (a*lhs - -(b*rhs)) 0, by rw sub_neg_eq_add; assumption,
have o (a*lhs) (-(b*rhs)), from (comp_op.rel_of_sub_rel_zero _).mp this,
let np := comp_op.op_mul (neg_pos_of_neg (one_div_neg_of_neg h2)) this in

begin
rw [←mul_assoc, ←neg_mul_eq_neg_mul, one_div_mul_cancel (ne_of_lt h2), ←neg_mul_eq_neg_mul, one_mul, neg_mul_neg, ←mul_assoc, div_mul_eq_mul_div, one_mul ] at np,
rw [←(neg_neg lhs), neg_div, ←neg_mul_eq_neg_mul],
apply op_neg,
assumption
end

theorem rev_op_zero_of_op {o} [comp_op o] {e : ℚ} (h : o e 0) : rev o (-e) 0 :=
suffices rev o (-e) (-0), by rw ←neg_zero; assumption,
begin
rw [neg_eq_neg_one_mul, neg_eq_neg_one_mul (0 : ℚ)],
apply op_mul_neg,
apply neg_of_neg_pos _,
exact zero_lt_one,
assumption
end

instance {o} [comp_op o] : comp_op (rev o) :=
{ op_inv := sorry,
  op_mul := sorry,
  rel_of_sub_rel_zero := sorry,
  rev_op_is_rev := sorry,
  rev_op := o
}

theorem rev_rev {o} [comp_op o] : rev (rev o) = o :=
begin
apply funext,
intro x, apply funext, intro y,
rw [rev_op_is_rev, rev_op_is_rev]
end

class one_op_one_div_class (o : ℚ → ℚ → Prop) :=
(oood : ∀ {x}, 0 < x → o x 1 → o 1 (rat.pow x (-1)))

instance ooodlt : one_op_one_div_class (@has_lt.lt rat _) :=
⟨begin intro, rw rat.pow_neg_one, apply one_lt_one_div end⟩

instance ooodle : one_op_one_div_class (@has_le.le rat _) :=
⟨begin intro, rw rat.pow_neg_one, apply one_le_one_div end⟩

instance ooodgt : one_op_one_div_class (@gt rat _) :=
⟨begin intros, rw rat.pow_neg_one, change 1/1 > 1/x, apply one_div_lt_one_div_of_lt, apply zero_lt_one, assumption end⟩

instance ooodge : one_op_one_div_class (@ge rat _) :=
⟨begin intros, rw rat.pow_neg_one, change 1/1 ≥ 1/x, apply one_div_le_one_div_of_le, apply zero_lt_one, assumption end⟩


instance {o} [comp_op o] [one_op_one_div_class o] : one_op_one_div_class (rev o) :=
⟨begin
 intros x h hr,
 apply rev_op_is_rev.mp,
 rw rev_rev,
 have : o ((rat.pow x (-1))*1) 1 := comp_op.op_inv h _,
 simp [rat.pow] at this, rw rat.pow_neg_one at this,
 rw rat.pow_neg_one,
 apply this,
 rw rev_op_is_rev at hr, rw mul_one, exact hr
end⟩

def one_op_one_div {o : ℚ → ℚ → Prop} [h : one_op_one_div_class o] := @one_op_one_div_class.oood _ h

theorem one_op_inv_mul_of_op_of_pos {o} [comp_op o] {lhs rhs c : ℚ} (h : o lhs (c*rhs)) (hp : lhs > 0) :
         o 1 (c*((rat.pow lhs (-1))*(rat.pow rhs 1))) :=
have (rat.pow lhs (-1)) > 0, by rw [rat.pow_neg_one]; apply one_div_pos_of_pos hp,
have o ( (rat.pow lhs (-1))*lhs) ( (rat.pow lhs (-1))*(c*rhs)), from comp_op.op_mul this h,
by simp only [rat.pow_neg_one, rat.pow_one] at ⊢ this; simp [mul_inv_cancel (ne_of_gt hp)] at this; simp *

theorem one_op_inv_mul_of_op_of_neg {o} [comp_op o] {lhs rhs c : ℚ} (h : o lhs (c*rhs)) (hp : lhs < 0) :
         rev o 1 (c*((rat.pow lhs (-1))*(rat.pow rhs 1))) :=
have (rat.pow lhs (-1)) < 0, by rw [rat.pow_neg_one]; apply one_div_neg_of_neg hp,
have rev o ( (rat.pow lhs (-1))*lhs) ( (rat.pow lhs (-1))*(c*rhs)), from op_mul_neg this h,
by simp only [rat.pow_neg_one, rat.pow_one] at ⊢ this; simp [mul_inv_cancel (ne_of_lt hp)] at this; simp *

-- change h arguments here to rat.pow rhs 1
theorem one_op_inv_mul_of_lt_of_pos_pos_flipped {lhs rhs c : ℚ} {o} [one_op_one_div_class o]
        (h : o (c*((rat.pow lhs (-1))*(rat.pow rhs 1))) 1) 
        (hl : lhs > 0) (hr : rhs > 0) (hc : c > 0) : o 1 ((1/c) * ((rat.pow lhs 1)*(rat.pow rhs (-1)))) :=
have rat.pow lhs (-1) > 0, by rw rat.pow_neg_one; apply one_div_pos_of_pos hl,
have c * ((rat.pow lhs (-1)) * rhs) > 0, by repeat {apply mul_pos _ _, repeat {assumption}},
have o 1 (rat.pow (c * ((rat.pow lhs (-1)) * (rat.pow rhs 1))) (-1)), by simp only [rat.pow_one] at *; apply one_op_one_div this h,
by simp only [rat.pow_neg_one, rat.pow_one] at ⊢ this; rw [←one_div_mul_one_div, ←one_div_mul_one_div, one_div_one_div] at this; assumption

theorem one_op_inv_mul_of_lt_of_pos_pos_flipped' {lhs rhs c : ℚ} {o} [comp_op o] [one_op_one_div_class o]
        (h : o 1 (c*((rat.pow lhs (-1))*(rat.pow rhs 1)))) 
        (hl : lhs > 0) (hr : rhs > 0) (hc : c > 0) : (rev o) 1 ((1/c) * ((rat.pow lhs 1)*(rat.pow rhs (-1)))) :=
have h' : _ := (comp_op.rev_op_is_rev _).mpr h,
one_op_inv_mul_of_lt_of_pos_pos_flipped h' hl hr hc

/-theorem one_lt_inv_mul_of_lt_of_pos_flipped' {lhs rhs c : ℚ} (h : 1 > (c*((1/lhs)*rhs))) 
        (hl : lhs > 0) (hr : rhs > 0) (hc : c > 0) : 1 < ((1/c) * (lhs*(1/rhs))) :=
/-have 1/lhs > 0, from one_div_pos_of_pos hl,
have c * ((1/lhs) * rhs) > 0, by repeat {apply mul_pos, repeat {assumption}},
have 1 < 1 / (c * ((1/lhs) * rhs)), from one_lt_one_div this h,
by rw [-one_div_mul_one_div, -one_div_mul_one_div, one_div_one_div] at this; assumption-/
one_lt_inv_mul_of_lt_of_pos_flipped h hl hr hc-/

/-theorem one_le_inv_mul_of_le_of_pos_flipped {lhs rhs c : ℚ} (h : 1 ≥ (c*((1/lhs)*rhs))) 
        (hl : lhs > 0) (hr : rhs > 0) (hc : c > 0) : 1 ≤ ((1/c) * (lhs*(1/rhs))) :=
have 1/lhs > 0, from one_div_pos_of_pos hl,
have c * ((1/lhs) * rhs) > 0, by repeat {apply mul_pos, repeat {assumption}},
have 1 ≤ 1 / (c * ((1/lhs) * rhs)), from one_le_one_div this h,
by rw [-one_div_mul_one_div, -one_div_mul_one_div, one_div_one_div] at this; assumption-/

theorem one_op_inv_mul_of_lt_of_pos_neg_flipped {lhs rhs c : ℚ} {o} [one_op_one_div_class o]
        (h : o (c*((rat.pow lhs (-1))*(rat.pow rhs 1))) 1) 
        (hl : lhs > 0) (hr : rhs < 0) (hc : c < 0) : o 1 ((1/c) * ((rat.pow lhs 1)*(rat.pow rhs (-1)))) :=
have rat.pow lhs (-1) > 0, by rw rat.pow_neg_one; apply one_div_pos_of_pos hl,
have c * ((rat.pow lhs (-1)) * rhs) > 0, 
  begin apply mul_pos_of_neg_of_neg _ _, assumption, apply mul_neg_of_pos_of_neg _ _, repeat {assumption} end,
have o 1 (rat.pow (c * ((rat.pow lhs (-1)) * (rat.pow rhs 1))) (-1)), by simp only [rat.pow_one] at *; apply one_op_one_div this h,
by simp only [rat.pow_neg_one, rat.pow_one] at this ⊢; rw [←one_div_mul_one_div, ←one_div_mul_one_div, one_div_one_div] at this; assumption

/-theorem one_lt_inv_mul_of_lt_of_neg_flipped {lhs rhs c : ℚ} (h : 1 > (c*((1/lhs)*rhs))) 
        (hl : lhs > 0) (hr : rhs < 0) (hc : c < 0) : 1 < ((1/c) * (lhs*(1/rhs))) :=
have 1/lhs > 0, from one_div_pos_of_pos hl,
have c * ((1/lhs) * rhs) > 0, 
  begin apply mul_pos_of_neg_of_neg, assumption, apply mul_neg_of_pos_of_neg, repeat {assumption} end,
have 1 < 1 / (c * ((1/lhs) * rhs)), from one_lt_one_div this h,
by rw [-one_div_mul_one_div, -one_div_mul_one_div, one_div_one_div] at this; assumption

theorem one_le_inv_mul_of_le_of_neg_flipped {lhs rhs c : ℚ} (h : 1 ≥ (c*((1/lhs)*rhs))) 
        (hl : lhs > 0) (hr : rhs < 0) (hc : c < 0) : 1 ≤ ((1/c) * (lhs*(1/rhs))) :=
have 1/lhs > 0, from one_div_pos_of_pos hl,
have c * ((1/lhs) * rhs) > 0, 
  begin apply mul_pos_of_neg_of_neg, assumption, apply mul_neg_of_pos_of_neg, repeat {assumption} end,
have 1 ≤ 1 / (c * ((1/lhs) * rhs)), from one_le_one_div this h,
by rw [-one_div_mul_one_div, -one_div_mul_one_div, one_div_one_div] at this; assumption-/
                             

theorem one_op_inv_mul_of_lt_of_neg_pos_flipped {lhs rhs c : ℚ} {o} [one_op_one_div_class o]
        (h : o (c*((rat.pow lhs (-1))*(rat.pow rhs 1))) 1) 
        (hl : lhs < 0) (hr : rhs > 0) (hc : c < 0) : o 1 ((1/c) * ((rat.pow lhs 1)*(rat.pow rhs (-1)))) :=
have rat.pow lhs (-1) < 0, by rw rat.pow_neg_one; apply one_div_neg_of_neg hl,
have c * ((rat.pow lhs (-1)) * rhs) > 0, 
  begin apply mul_pos_of_neg_of_neg _ _, assumption, apply mul_neg_of_neg_of_pos _ _, repeat {assumption} end,
have o 1 (rat.pow (c * ((rat.pow lhs (-1)) * (rat.pow rhs 1))) (-1)), by simp only [rat.pow_one] at *; apply one_op_one_div this h,
by simp only [rat.pow_neg_one, rat.pow_one] at ⊢ this; rw [←one_div_mul_one_div, ←one_div_mul_one_div, one_div_one_div] at this; assumption

theorem one_op_inv_mul_of_lt_of_neg_neg_flipped {lhs rhs c : ℚ} {o} [one_op_one_div_class o]
        (h : o (c*((rat.pow lhs (-1))*(rat.pow rhs 1))) 1) 
        (hl : lhs < 0) (hr : rhs < 0) (hc : c > 0) : o 1 ((1/c) * ((rat.pow lhs 1)*(rat.pow rhs (-1)))) :=
have rat.pow lhs (-1) < 0, by rw rat.pow_neg_one; apply one_div_neg_of_neg hl,
have c * ((rat.pow lhs (-1)) * rhs) > 0, 
  begin apply mul_pos _ _, assumption, apply mul_pos_of_neg_of_neg _ _, repeat {assumption} end,
have o 1 (rat.pow (c * ((rat.pow lhs (-1)) * (rat.pow rhs 1))) (-1)), by simp only [rat.pow_one] at *; apply one_op_one_div this h,
by simp only [rat.pow_neg_one,  rat.pow_one] at ⊢ this; rw [←one_div_mul_one_div, ←one_div_mul_one_div, one_div_one_div] at this; assumption


theorem one_eq_div_of_eq {lhs rhs c : ℚ} (h : lhs = c*rhs) (hl : lhs ≠ 0) : 1 = c*((rat.pow lhs (-1))*(rat.pow rhs 1)) :=
have (rat.pow lhs (-1))*lhs = (rat.pow lhs (-1))*(c*rhs), by cc,
sorry --by finish

theorem lt_pos_pow {a : ℚ} (h : 1 < a) : Π (n : ℕ), 1 < rat.pow a (int.of_nat (n+1))
| 0 := by simp [*, rat.pow]
| (k+1) := begin simp [*, rat.pow], rw ←(mul_one (1:ℚ)), apply mul_lt_mul _ _ _ _, assumption, apply le_of_lt, apply lt_pos_pow, exact zero_lt_one, apply le_trans, apply zero_le_one, apply le_of_lt, assumption end


theorem le_pos_pow {a : ℚ} (h : 1 ≤ a) : Π (n : ℕ), 1 ≤ rat.pow a (int.of_nat (n+1))
| 0 := by simp [*, rat.pow]
| (k+1) := begin simp [*, rat.pow], rw ←(mul_one (1:ℚ)), apply mul_le_mul, assumption, apply le_pos_pow, apply zero_le_one, apply le_trans, apply zero_le_one, assumption end

theorem lt_pos_pow' {a : ℚ} (h : 1 < a) : Π {z : ℤ} (hz : z > 0), 1 < rat.pow a z
| (int.of_nat 0) hz := false.elim $ lt_irrefl _ hz
| (int.of_nat (k+1)) hz := lt_pos_pow h _
| -[1+k] hz := false.elim $ lt_irrefl _ $ lt.trans (int.neg_succ_lt_zero _) hz

theorem le_pos_pow' {a : ℚ} (h : 1 ≤ a) : Π {z : ℤ} (hz : z > 0), 1 ≤ rat.pow a z
| (int.of_nat 0) hz := false.elim $ lt_irrefl _ hz
| (int.of_nat (k+1)) hz := le_pos_pow h _
| -[1+k] hz := false.elim $ lt_irrefl _ $ lt.trans (int.neg_succ_lt_zero _) hz

theorem eq_pow {a : ℚ} (h : 1 = a) (z : ℤ) : 1 = rat.pow a z :=
have rat.pow 1 z = 1, from rat.one_pow _,
by cc

theorem eq_pow' {a b : ℚ} {z : ℤ} (h : 1 = rat.pow (a * b) z) : 1 = rat.pow a z * rat.pow b z := sorry

theorem ne_of_strict_op {o} [weak_comp_op o] {a : ℚ} (h : strict_op o a 0) : a ≠ 0 :=
weak_comp_op.ne_of_str h

/-theorem op_inv_n {o} [comp_op o] {x y z : ℚ} {p : ℤ} (hx : x > 0) (h : o z ((rat.pow x p)*y)) : o ((rat.pow x (-p))*z) y := 
begin
induction p with a a,
induction a,
change int.of_nat 0 with 0 at h,
simp [rat.pow, int.of_nat],   
end-/


-- assumes lhs > rhs as exprs. 1 R coeff* lhs^el * rhs^er ==> ineq_data
theorem op_of_one_op_pos {o} [comp_op o] {lhs rhs c : ℚ} (hlhs : lhs > 0) {el er : ℤ} (h : o 1 (c*(rat.pow lhs (el) * rat.pow rhs er))) : o (rat.pow lhs (-el)) (c*rat.pow rhs er) :=
sorry

theorem op_of_one_op_neg {o} [comp_op o] {lhs rhs c : ℚ} (hlhs : lhs < 0) {el er : ℤ} (h : o 1 (c*(rat.pow lhs (el) * rat.pow rhs er))) : (rev o) (rat.pow lhs el) (c*rat.pow rhs er) :=
sorry

theorem op_of_inv_op_inv_pow {o} [comp_op o] {lhs rhs c : ℚ} (h : o (rat.pow lhs (-1)) (c*rat.pow rhs (-1))) : rev o lhs (c*rhs) := sorry

theorem op_of_op_pow {o} [comp_op o] {lhs rhs c : ℚ} (h : o (rat.pow lhs 1) (c*rat.pow rhs 1)) : o lhs (c*rhs) := 
by simp [rat.pow_one, *] at *

private meta def norm_num_inter : tactic unit := `[norm_num]

theorem one_op_of_op_inv {o} [comp_op o] {rhs c : ℚ} (h : o 1 (c*rat.pow rhs (-1))) : rev o 1 ((1/c)*rhs) :=
sorry

theorem one_op_of_op {o} [comp_op o] {rhs c : ℚ} (h : o 1 (c * rat.pow rhs 1)) : o 1 (c*rhs) :=
by simp [rat.pow_one, *] at *

end polya
--set_option pp.all true
--#check @
