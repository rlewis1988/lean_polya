import data.num.lemmas data.complex.basic tactic

local attribute [elim_cast] znum.cast_inj
local attribute [squash_cast] znum.to_of_int
local attribute [move_cast] znum.cast_mul
local attribute [squash_cast] znum.cast_zero
local attribute [move_cast, squash_cast] znum.cast_bit0
local attribute [move_cast, squash_cast] znum.cast_bit1

open tactic

structure qnum : Type :=
(num : znum)
(denom : znum)
(pr : denom ≠ 0)

namespace qnum

def r (a b : qnum) : Prop :=
a.num * b.denom = a.denom * b.num

theorem r_rfl : reflexive r :=
assume _, mul_comm _ _

theorem r_symm : symmetric r :=
assume x y h, eq.trans (mul_comm _ _) (eq.trans (eq.symm h) (mul_comm _ _))

theorem r_trans : transitive r :=
begin
    intros x y z h1 h2,
    unfold r at h1 h2 ⊢,
    by_cases h : y.num = 0,
    { simp [h] at h1 h2,
      rw or_iff_not_imp_right at h1,
      rw or_iff_not_imp_left at h2,
      rw [h1, h2, zero_mul, mul_zero],
      repeat {apply y.pr}
    },
    { apply eq_of_mul_eq_mul_right h,
      apply eq_of_mul_eq_mul_right y.pr,
      apply @eq.trans _ _ ((x.num * y.denom) * (y.num * z.denom)) _,
      { ring },
      { rw [h1, h2], ring }}
end

def r_equiv : equivalence r :=
⟨r_rfl, r_symm, r_trans⟩

instance : setoid qnum := ⟨r, r_equiv⟩

def mul (a b : qnum) : qnum :=
{ num   := a.num * b.num,
  denom := a.denom * b.denom,
  pr    := mul_ne_zero a.pr b.pr }

def add (a b : qnum) : qnum :=
{ num   := a.num * b.denom + a.denom * b.num,
  denom := a.denom * b.denom,
  pr    := mul_ne_zero a.pr b.pr }

instance : has_add qnum := ⟨add⟩
instance : has_mul qnum := ⟨mul⟩

@[simp] theorem mul_num {a b : qnum} : (a * b).num = a.num * b.num :=
by simp [has_mul.mul, mul]
@[simp] theorem mul_denom {a b : qnum} : (a * b).denom = a.denom * b.denom :=
by simp [has_mul.mul, mul]

theorem mul_comm {a b : qnum} : a * b = b * a :=
begin
    unfold has_mul.mul, unfold mul,
    congr' 1; ring
end

theorem mul_assoc {a b c : qnum} : a * b * c = a * (b * c) :=
begin
    unfold has_mul.mul, unfold mul,
    ring, split; ring
end

theorem add_comm {a b : qnum} : a + b = b + a :=
begin
    unfold has_add.add, unfold add,
    ring, split; ring
end

theorem add_assoc {a b c : qnum} : a + b + c = a + (b + c) :=
begin
    unfold has_add.add, unfold add,
    ring, split; ring
end

def to_rat (a : qnum) : ℚ := rat.mk a.num a.denom

def of_rat (a : ℚ) : qnum := ⟨a.num, a.denom, ne_of_gt (by apply_mod_cast a.pos)⟩

section
variables {a b x y : qnum}

theorem foo : of_rat (to_rat a) ≈ a :=
begin
    unfold to_rat,
    unfold of_rat,
    unfold has_equiv.equiv,
    unfold setoid.r,
    unfold r,
    simp,
    sorry
end

theorem to_rat_mul : to_rat (a * b) = to_rat a * to_rat b :=
begin
    unfold to_rat,
    rw rat.mul_def,
    { norm_cast },
    { rw ← znum.cast_zero, --TODO
      norm_cast,
      exact a.pr },
    { rw ← znum.cast_zero, --TODO
      norm_cast,
      exact b.pr }
end

variables (h1 : a ≈ x) (h2 : b ≈ y)
include h1 h2

theorem add_equiv : a + b ≈ x + y :=
begin
    unfold has_equiv.equiv at *,
    unfold setoid.r at *,
    unfold r at *, 
    sorry
end

theorem mul_equiv : a * b ≈ x * y :=
begin
    unfold has_equiv.equiv at *,
    unfold setoid.r at *,
    unfold r at *,
    calc
    (a * b).num * (x * y).denom
        = (a.num * b.num) * (x.denom * y.denom) : rfl
    ... = (a.num * x.denom) * (b.num * y.denom) : by ring
    ... = (a.denom * x.num) * (b.denom * y.num) : by rw [h1, h2]
    ... = (a.denom * b.denom) * (x.num * y.num) : by ring
    ... = (a * b).denom * (x * y).num           : rfl
end

end

end qnum

def Qnum : Type := quotient qnum.setoid

namespace Qnum

def add : Qnum → Qnum → Qnum :=
begin
    apply quotient.lift₂ (λ a b, quotient.mk $ qnum.add a b),
    intros a1 a2 b1 b2 h1 h2,
    simp only [],
    apply quotient.sound,
    exact qnum.add_equiv h1 h2
end

def mul : Qnum → Qnum → Qnum :=
begin
    apply quotient.lift₂ (λ a b, quotient.mk $ qnum.mul a b),
    intros a1 a2 b1 b2 h1 h2,
    simp only [],
    apply quotient.sound,
    exact qnum.mul_equiv h1 h2
end

instance : has_add Qnum := ⟨add⟩
instance : has_mul Qnum := ⟨mul⟩

def to_rat : Qnum → ℚ :=
begin
    apply quotient.lift qnum.to_rat,
    intros a b h1,
    unfold has_equiv.equiv at h1,
    unfold setoid.r at h1,
    unfold qnum.r at h1,
    unfold qnum.to_rat,
    by_cases h2 : b.num = 0,
    { simp [h2, b.pr] at h1,
      rw [h1, h2],
      norm_cast, sorry },
    { rw [← div_eq_one_iff_eq, division_def, 
          rat.inv_def, rat.mul_def],
      { norm_cast, rw h1, sorry },
        { rw ← znum.cast_zero, --TODO
          exact_mod_cast a.pr },
        { rw ← znum.cast_zero,
          exact_mod_cast h2 },
        { intro h3, apply h2, sorry }}
end

theorem to_rat_mul {a b : Qnum} :
    to_rat (a * b) = to_rat a * to_rat b :=
begin
    cases quotient.exists_rep a with x h1,
    cases quotient.exists_rep b with y h2,
end

end Qnum
