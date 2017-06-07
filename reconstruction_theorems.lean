import .datatypes
namespace polya

class comp_op (op : ℚ → ℚ → Prop) :=
(rev_op : ℚ → ℚ → Prop)
(rev_op_is_rev : ∀ {x y}, rev_op y x ↔ op x y)
(rel_of_sub_rel_zero : ∀ {x y : ℚ}, op (x-y) 0 ↔ op x y)
(op_mul : ∀ {x y c : ℚ}, c > 0 → op x y → op (c*x) (c*y))

class weak_comp_op (op) extends comp_op op :=
(strict_op : ℚ → ℚ → Prop)
(disj : ∀ {x y}, op x y ↔ x = y ∨ strict_op x y)

instance colt : comp_op (@has_lt.lt ℚ _) :=
{rev_op := @gt ℚ _,
 rev_op_is_rev := sorry,
 rel_of_sub_rel_zero := sorry,
 op_mul := sorry}

instance cole : weak_comp_op (@has_le.le ℚ _) :=
{rev_op := @ge ℚ _,
 rev_op_is_rev := sorry,
 rel_of_sub_rel_zero := sorry,
 op_mul := sorry,
 strict_op := @has_lt.lt ℚ _,
 disj := sorry}

instance cogt : comp_op (@gt ℚ _) :=
{rev_op := @has_lt.lt ℚ _,
 rev_op_is_rev := sorry,
 rel_of_sub_rel_zero := sorry,
 op_mul := sorry}

instance coge : weak_comp_op (@ge ℚ _) :=
{rev_op := @has_le.le ℚ _,
 rev_op_is_rev := sorry,
 rel_of_sub_rel_zero := sorry,
 op_mul := sorry,
 strict_op := @gt ℚ _,
 disj := sorry}


@[reducible] private def rev := comp_op.rev_op
lemma rev_op_is_rev {o x y} [comp_op o] : rev o y x ↔ o x y := comp_op.rev_op_is_rev _ 

lemma op_mul_neg {o}  {x y c : ℚ} [comp_op o] (hc : c < 0) (h : o x y) : rev o (c*x) (c*y) :=
have o (x-y) 0, from (comp_op.rel_of_sub_rel_zero o).mpr h,
have o (-c*(x-y)) ((-c)*0), from comp_op.op_mul (neg_pos_of_neg hc) this,
have o (c*y - c*x) 0, begin
 rw [mul_sub, mul_zero, -neg_mul_eq_neg_mul, -neg_mul_eq_neg_mul, sub_neg_eq_add, add_comm] at this, assumption 
end,
rev_op_is_rev.mpr ((comp_op.rel_of_sub_rel_zero o).mp this)

lemma op_neg {o} {x y : ℚ} [comp_op o] (h : o x y) : rev o (-x) (-y) :=
begin
rw [neg_eq_neg_one_mul, neg_eq_neg_one_mul y],
apply op_mul_neg,
apply neg_of_neg_pos,
apply zero_lt_one,
assumption
end
 
theorem sym_op_pos {o} [comp_op o] {lhs rhs c : ℚ} (hc : c > 0) (h : o lhs (c*rhs)) : rev o rhs ((1/c)*lhs) :=
have h' : o ((1/c)*lhs) ((1/c)*(c*rhs)), from comp_op.op_mul (one_div_pos_of_pos hc) h,
suffices o ((1/c)*lhs) rhs, by rw rev_op_is_rev; assumption,
by rw [-mul_assoc, one_div_mul_cancel (ne_of_gt hc), one_mul] at h'; assumption
--comp_op.rev_recip hc h

theorem sym_op_neg {o} [comp_op o] {lhs rhs c : ℚ} (hc : c < 0) (h : o lhs (c*rhs)) : o rhs ((1/c)*lhs) :=
have h' : rev o ((1/c)*lhs) ((1/c)*(c*rhs)), begin
apply op_mul_neg,
apply one_div_neg_of_neg, repeat {assumption}
end,
suffices rev o ((1/c)*lhs) rhs, begin
apply rev_op_is_rev.mp,
assumption
end,
by rw [-mul_assoc, one_div_mul_cancel (ne_of_lt hc), one_mul] at h'; assumption

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
simph, assumption
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

theorem op_ineq {lhs rhs c : ℚ} (h1 : lhs ≤ c*rhs) (h2 : lhs ≥ c*rhs) : lhs = rhs :=
sorry

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
theorem op_zero_mul {o} [comp_op o] (h : o lhs 0) : o lhs (0*rhs) := by simph

variable {rhs}
/-theorem zero_mul_le' (h : lhs ≤ 0*rhs) : lhs ≤ 0 := by rw -(zero_mul rhs); assumption
theorem zero_mul_lt' (h : lhs < 0*rhs) : lhs < 0 := by rw -(zero_mul rhs); assumption
theorem zero_mul_ge' (h : lhs ≥ 0*rhs) : lhs ≥ 0 := by rw -(zero_mul rhs); assumption
theorem zero_mul_gt' (h : lhs > 0*rhs) : lhs > 0 := by rw -(zero_mul rhs); assumption-/

theorem op_zero_mul' {o} [comp_op o] (h : o lhs (0*rhs)) : o lhs 0 := by rw -(zero_mul rhs); assumption


/-meta def zero_mul'_name_of_comp : comp → name
| comp.le := ``zero_mul_le'
| comp.lt := ``zero_mul_lt'
| comp.ge := ``zero_mul_ge'
| comp.gt := ``zero_mul_gt'-/

end

theorem eq_zero_of_eq_mul_zero {lhs rhs : ℚ} (h : lhs = 0*rhs) : lhs = 0 :=
by rw -(zero_mul rhs); assumption

theorem ne_zero_of_ne_mul_zero {lhs rhs : ℚ} (h : lhs ≠ 0*rhs) : lhs ≠ 0 :=
by rw -(zero_mul rhs); assumption

theorem eq_zero_of_two_eqs_rhs {lhs rhs c1 c2 : ℚ} (h : lhs = c1*rhs) (h2 : lhs = c2*rhs) (hc : c1 ≠ c2) : rhs = 0 :=
begin
 rw h at h2,
 note h3 := sub_eq_zero_of_eq h2,
 rw -sub_mul at h3,
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
have o (d*rhs) (c*rhs), by rw -h; assumption,
have o (d*rhs - c*rhs) 0, from sub_op_zero_of_op this,
have o ((d-c)*rhs) 0, by rw sub_mul; assumption,
have dc : 1/(d-c) > 0, from one_div_pos_of_pos h2,
let cmp := comp_op.op_mul dc this in
begin
rw [mul_zero,-mul_assoc, div_mul_cancel _ (ne_of_gt h2), one_mul] at cmp,
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
 apply sub_neg_of_lt,
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
 rw [add_comm, -neg_mul_eq_neg_mul, one_mul],
 apply sub_neg_of_lt,
 assumption
end

theorem sub_le_of_ge (h1 : lhs ≥ c*rhs) : (-1)*lhs + c*rhs ≤ 0 :=
begin
 rw [add_comm, -neg_mul_eq_neg_mul, one_mul],
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
begin apply lt_irrefl, rw one_mul at h, assumption end

theorem lt_self_contr {e : ℚ} (h : e < 1*e) : false :=
begin apply lt_irrefl, rw one_mul at h, assumption end

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
rw [-mul_assoc, one_div_mul_cancel (ne_of_gt h2), one_mul, neg_mul_eq_neg_mul, -mul_assoc, div_mul_eq_mul_div, one_mul] at np, assumption
end

theorem op_of_sum_op_zero_neg {o} [comp_op o] {lhs rhs a b : ℚ} (h : o (a*lhs + b*rhs) 0)
        (h2 : a < 0) : rev o lhs (((-b)/a)*rhs) :=
have o (a*lhs - -(b*rhs)) 0, by rw sub_neg_eq_add; assumption,
have o (a*lhs) (-(b*rhs)), from (comp_op.rel_of_sub_rel_zero _).mp this,
let np := comp_op.op_mul (neg_pos_of_neg (one_div_neg_of_neg h2)) this in
--let np' := op_mul_neg (sorry : -1 < 0) np in
begin
rw [-mul_assoc, -neg_mul_eq_neg_mul, one_div_mul_cancel (ne_of_lt h2), -neg_mul_eq_neg_mul, one_mul, neg_mul_neg, -mul_assoc, div_mul_eq_mul_div, one_mul ] at np,
rw [-(neg_neg lhs), neg_div, -neg_mul_eq_neg_mul],
apply op_neg,
assumption
end

theorem rev_op_zero_of_op {o} [comp_op o] {e : ℚ} (h : o e 0) : rev o (-e) 0 :=
suffices rev o (-e) (-0), by rw -neg_zero; assumption,
begin
rw [neg_eq_neg_one_mul, neg_eq_neg_one_mul (0 : ℚ)],
apply op_mul_neg,
apply neg_of_neg_pos,
apply zero_lt_one,
assumption
end

end polya
