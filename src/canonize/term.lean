import data.real.basic data.complex.basic
import data.num.lemmas

section
local attribute [semireducible] reflected
meta instance rat.reflect : has_reflect ℚ
| ⟨n, d, _, _⟩ := `(rat.mk_nat %%(reflect n) %%(reflect d))
end

local attribute [elim_cast] znum.cast_inj

namespace polya

class morph (γ : Type) [discrete_field γ] (α : Type) [discrete_field α] :=
(morph : γ → α)
(morph0 : morph 0 = 0)
(morph1 : morph 1 = 1)
(morph_add : ∀ a b : γ, morph (a + b) = morph a + morph b)
(morph_neg : ∀ a : γ, morph (-a) = - morph a)
(morph_mul : ∀ a b : γ, morph (a * b) = morph a * morph b)
(morph_inv : ∀ a : γ, morph (a⁻¹) = (morph a)⁻¹)
(morph_inj : ∀ a : γ, morph a = 0 → a = 0)

structure dict (α : Type) :=
(val : num → α)

variables {α : Type} [discrete_field α]
variable {ρ : dict α}

--TODO: replace rat with znum × znum
instance rat_morph [char_zero α] : morph ℚ α :=
{ morph     := rat.cast,
  morph0    := rat.cast_zero,
  morph1    := rat.cast_one,
  morph_add := rat.cast_add,
  morph_neg := rat.cast_neg,
  morph_mul := rat.cast_mul,
  morph_inv := rat.cast_inv,
  morph_inj := begin
      intros a ha,
      apply rat.cast_inj.mp,
      { rw rat.cast_zero, apply ha },
      { resetI, apply_instance }
    end,
}

variables {γ : Type} [discrete_field γ] [morph γ α]
instance morph_to_coe : has_coe γ α := ⟨morph.morph _⟩

/-
section
variables {δ : Type} [discrete_field δ] [morph δ γ]
instance morph_comp : morph δ α :=
{ morph     := λ x : δ, ((x : γ) : α),
  morph0    := by {unfold_coes, rw [morph.morph0, morph.morph0]},
  morph1    := by {unfold_coes, rw [morph.morph1, morph.morph1]},
  morph_add := by {intros, unfold_coes, rw [morph.morph_add, morph.morph_add]},
  morph_neg := by {intros, unfold_coes, rw [morph.morph_neg, morph.morph_neg]},
  morph_mul := by {intros, unfold_coes, rw [morph.morph_mul, morph.morph_mul]},
  morph_inv := by {intros, unfold_coes, rw [morph.morph_inv, morph.morph_inv]},
  morph_inj := by {intros _ h, unfold_coes at h,
    have : morph.morph γ a = 0, by apply morph.morph_inj _ h,
    apply morph.morph_inj _ this},
}
end
-/

namespace morph
variables (a b : γ)

theorem morph_sub : morph α (a - b) = morph _ a - morph _ b :=
by rw [sub_eq_add_neg, morph.morph_add, morph.morph_neg, ← sub_eq_add_neg]

theorem morph_div : morph α (a / b) = morph _ a / morph _ b :=
by rw [division_def, morph.morph_mul, morph.morph_inv, ← division_def]

theorem morph_pow_nat (n : ℕ) : morph α (a ^ n) = (morph _ a) ^ n :=
begin
  induction n with _ ih,
  { rw [pow_zero, pow_zero, morph.morph1] },
  { by_cases ha : a = 0,
    { rw [ha, morph.morph0, zero_pow, zero_pow],
      { apply morph.morph0 },
      { apply nat.succ_pos },
      { apply nat.succ_pos }},
    { rw [pow_succ, morph.morph_mul, ih, ← pow_succ] }}
end

theorem morph_pow (n : ℤ) : morph α (a ^ n) = (morph _ a) ^ n :=
begin
  cases n,
  { rw [int.of_nat_eq_coe, fpow_of_nat, fpow_of_nat],
    apply morph_pow_nat },
  { rw [int.neg_succ_of_nat_coe, fpow_neg, fpow_neg],
    rw [morph_div, morph.morph1],
    rw [fpow_of_nat, fpow_of_nat],
    rw morph_pow_nat }
end

end morph

@[derive decidable_eq, derive has_reflect]
inductive term : Type
| zero : term
| one : term
| atom : num → term
| add : term → term → term
| sub : term → term → term
| mul : term → term → term
| div : term → term → term
| neg : term → term
| inv : term → term
| pow : term → ℤ → term
| const : γ → term

namespace term

instance coe_atom : has_coe num (@term γ _) := ⟨atom⟩
instance coe_const: has_coe γ (@term γ _) := ⟨const⟩
instance : has_zero (@term γ _) := ⟨zero⟩
instance : has_one (@term γ _) := ⟨one⟩
instance : has_add (@term γ _) := ⟨add⟩
instance : has_mul (@term γ _) := ⟨mul⟩
instance : has_sub (@term γ _) := ⟨sub⟩
instance : has_div (@term γ _) := ⟨div⟩
instance : has_inv (@term γ _) := ⟨inv⟩
instance : has_pow (@term γ _) ℤ := ⟨pow⟩

def eval (ρ : dict α) : @term γ _ → α
| zero      := 0
| one       := 1
| (atom i)  := ρ.val i
| (add x y) := eval x + eval y
| (sub x y) := eval x - eval y
| (mul x y) := eval x * eval y
| (div x y) := (eval x) / (eval y)
| (neg x)   := - eval x
| (inv x)   := (eval x)⁻¹
| (pow x n) := eval x ^ n
| (const r) := morph.morph _ r

end term

@[derive decidable_eq, derive has_reflect]
inductive nterm : Type
| atom : num → nterm
| const : γ → nterm
| add : nterm → nterm → nterm
| mul : nterm → nterm → nterm
| pow : nterm → znum → nterm

namespace nterm

instance coe_atom : has_coe num (@nterm γ _) := ⟨atom⟩
instance coe_const: has_coe γ (@nterm γ _) := ⟨const⟩
instance : has_zero (@nterm γ _) := ⟨const 0⟩
instance : has_one (@nterm γ _) := ⟨const 1⟩
instance : has_add (@nterm γ _) := ⟨add⟩
instance : has_mul (@nterm γ _) := ⟨mul⟩
instance : has_pow (@nterm γ _) znum := ⟨pow⟩
instance : has_inv (@nterm γ _) := ⟨λ x, pow x (-1)⟩

def eval (ρ : dict α) : @nterm γ _ → α
| (atom i)  := ρ.val i
| (const c) := morph.morph _ c
| (add x y) := eval x + eval y
| (mul x y) := eval x * eval y
| (pow x n) := eval x ^ (n : ℤ)

def size : @nterm γ _ → ℕ
| (atom _)  := 1
| (const _) := 1
| (add x y) := 1 + size x + size y
| (mul x y) := 1 + size x + size y
| (pow x n) := 1 + size x

instance : has_coe_to_fun (dict α) := ⟨λ _, @nterm γ _ → α, eval⟩

def of_term : @term γ _ → @nterm γ _
| term.zero      := const 0
| term.one       := const 1
| (term.atom i)  := atom i
| (term.add x y) := of_term x + of_term y
| (term.sub x y) := of_term x + const (-1) * of_term y
| (term.mul x y) := of_term x * of_term y
| (term.div x y) := of_term x * of_term y ^ (-1 : znum)
| (term.neg x)   := const (-1) * of_term x
| (term.inv x)   := of_term x ^ (-1 : znum)
| (term.pow x n) := of_term x ^ (n : znum)
| (term.const n) := const n

theorem correctness1 : Π (x : @term γ _), term.eval ρ x = nterm.eval ρ (of_term x) :=
begin
    intro x,
    induction x;
    unfold of_term; unfold term.eval,
    { apply eq.symm, apply morph.morph0 },
    { apply eq.symm, apply morph.morph1 },
    { refl },
    { unfold has_add.add, congr; assumption },
    { unfold has_add.add, unfold has_mul.mul, unfold eval,
      rw [morph.morph_neg, morph.morph1, neg_one_mul],
      rw ← sub_eq_add_neg,
      congr; assumption },
    { congr; assumption },
    { unfold has_mul.mul, unfold has_pow.pow, unfold eval,
      simp only [znum.cast_zneg, znum.cast_one],
      rw [division_def, fpow_inv],
      congr; assumption },
    { unfold has_mul.mul, unfold eval,
      rw [morph.morph_neg, morph.morph1, neg_one_mul],
      congr; assumption },
    { unfold has_pow.pow, unfold eval,
      simp only [znum.cast_zneg, znum.cast_one],
      rw fpow_inv,
      congr; assumption },
    { unfold has_pow.pow, unfold eval,
      simp only [znum.of_int_cast], norm_cast,
      congr; assumption },
    { refl }
end

/-
def aux : (@nterm γ _) → (@nterm γ _) 
| (atom i)  := i
| (const n) := n
| (add x y) := aux x + aux y
| (mul x y) := aux x * aux y
| (pow x n) := aux x ^ n

example : ∀ (x : @nterm γ _), aux x = x :=
begin
  intro x,
  induction x; unfold aux,
  { unfold_coes },
  { unfold_coes },
  { apply congr, apply congr_arg, assumption, assumption },
  { apply congr, apply congr_arg, assumption, assumption },
  { apply congr, apply congr_arg, assumption, refl }
end
-/

def blt : @nterm γ _ → @nterm γ _ → bool :=
sorry
def lt : @nterm γ _ → @nterm γ _ → Prop :=
λ x y, blt x y

instance : has_lt (@nterm γ _) := ⟨lt⟩
instance : decidable_rel (@lt γ _) := by delta lt; apply_instance

meta def to_str [has_to_string γ] : (@nterm γ _) → string
| (atom i)  := "#" ++ to_string (i : ℕ)
| (const c) := to_string c
| (add x y) := "(" ++ to_str x ++ " + " ++ to_str y ++ ")"
| (mul x y) := "(" ++ to_str x ++ " * " ++ to_str y ++ ")"
| (pow x n) := to_str x ++ " ^ " ++ to_string (n : ℤ)

meta instance [has_to_string γ] : has_to_string (@nterm γ _) := ⟨to_str⟩
meta instance [has_to_string γ] : has_to_tactic_format (@nterm γ _) := ⟨λ x, return (to_str x : format)⟩

def eq_val (x y : @nterm γ _) : Type :=
{cs : finset (@nterm γ _) //
    ∀ {α : Type} [df : discrete_field α] [@morph γ _ α df] (ρ : dict α),
    by resetI; exact (∀ c ∈ cs, ρ c ≠ 0) → ρ x = ρ y}

infixr ` ~ ` := eq_val

namespace eq_val

variables {x y z x' y' z' : @nterm γ _} {a b c : γ} {n m : znum}

protected def rfl : x ~ x :=
⟨∅, assume _ _ _ _ _, rfl⟩

protected def symm (u : x ~ y) : y ~ x :=
⟨u.val, by {intros, apply eq.symm, apply u.property, assumption}⟩

protected def trans (u : x ~ y) (v : y ~ z) : x ~ z :=
⟨u.val ∪ v.val, by intros _ _ _ ρ H; resetI; exact
    eq.trans
        (u.property ρ $ λ c hc, H _ (finset.mem_union_left _ hc))
        (v.property ρ $ λ c hc, H _ (finset.mem_union_right _ hc))⟩

protected def add_comm : (x + y) ~ (y + x) :=
⟨∅, by {intros, resetI, apply add_comm}⟩

protected def add_assoc : (x + y + z) ~ (x + (y + z)) :=
⟨∅, by {intros, resetI, apply add_assoc}⟩

protected def mul_comm : (x * y) ~ (y * x) :=
⟨∅, by {intros, resetI, apply mul_comm}⟩

protected def mul_assoc : (x * y * z) ~ (x * (y * z)) :=
⟨∅, by {intros, resetI, apply mul_assoc}⟩

protected def distrib : x * (y + z) ~ x * y + x * z :=
⟨∅, by {intros, resetI, apply mul_add}⟩

protected def const_add : const (a + b) ~ const a + const b :=
⟨∅, by {intros, apply morph.morph_add}⟩

protected def const_mul : const (a * b) ~ const a * const b :=
⟨∅, by {intros, apply morph.morph_mul}⟩

protected def const_inv : const (a ^ ↑n) ~ (const a) ^ n :=
⟨∅, by {intros, apply morph.morph_pow}⟩

protected def congr_add (u : x ~ x') (v : y ~ y') : x + y ~ x' + y' :=
⟨u.val ∪ v.val, begin
  intros _ _ _ ρ H, resetI,
  unfold_coes, unfold has_add.add, unfold eval,
  apply congr, apply congr_arg,
  apply u.property, intros, apply H,
  apply finset.mem_union_left, assumption,
  apply v.property, intros, apply H,
  apply finset.mem_union_right, assumption,
end⟩

protected def congr_mul (u : x ~ x') (v : y ~ y') : x * y ~ x' * y' :=
⟨u.val ∪ v.val, begin
  intros _ _ _ ρ H, resetI,
  unfold_coes, unfold has_mul.mul, unfold eval,
  apply congr, apply congr_arg,
  apply u.property, intros, apply H,
  apply finset.mem_union_left, assumption,
  apply v.property, intros, apply H,
  apply finset.mem_union_right, assumption,
end⟩

protected def congr_pow (u : x ~ y) (v : n = m) : x ^ n ~ y ^ m :=
⟨u.val, begin
  intros _ _ _ ρ H, resetI,
  unfold_coes, unfold has_pow.pow, unfold eval,
  apply congr, apply congr_arg,
  apply u.property, intros, apply H,
  assumption, rw znum.cast_inj, assumption
end⟩

protected def pow_add : x ^ (n + m) ~ x ^ n * x ^ m :=
begin
  unfold has_pow.pow, unfold has_mul.mul,
  refine ⟨_, _⟩,
  { exact if n ≠ 0 ∧ m ≠ 0 ∧ (n + m) = 0 then {x} else ∅ },
  { intros _ _ _ ρ H,
    unfold_coes, unfold eval, resetI,
    by_cases h1 : n = 0,
    { rw [h1, znum.cast_zero, zero_add, fpow_zero, one_mul] },
    by_cases h2 : m = 0,
    { rw [h2, znum.cast_zero, add_zero, fpow_zero, mul_one] },
    by_cases h3 : n + m = 0,
    { rw znum.cast_add, apply fpow_add,
      have : n ≠ 0 ∧ m ≠ 0 ∧ n + m = 0, from ⟨h1, h2, h3⟩,
      apply H, simp [this] },
    by_cases h4 : eval ρ x = 0,
    { rw [h4, zero_fpow, zero_fpow],
      { rw zero_mul },
      { rw ← znum.cast_zero, norm_cast, exact h1 },
      { rw ← znum.cast_zero, norm_cast, exact h3 }},
    { rw znum.cast_add, apply fpow_add h4 }}
end

protected def pow_sub : x ^ (n - m) ~ x ^ n * x ^ (-m) :=
eq_val.trans
  (eq_val.congr_pow eq_val.rfl (sub_eq_add_neg n m))
  eq_val.pow_add

protected def pow_mul : x ^ (n * m) ~ (x ^ n) ^ m :=
⟨∅, begin
  intros, unfold_coes,
  unfold has_pow.pow, unfold eval,
  rw znum.cast_mul, apply fpow_mul
end⟩

protected def mul_pow : (x * y) ^ n ~ x ^ n * y ^ n :=
⟨∅, by {intros, apply mul_fpow}⟩

end eq_val

def r : @nterm γ _ → @nterm γ _ → Prop := measure size
theorem wf_r : @well_founded (@nterm γ _) r := measure_wf _


def norm : @nterm γ _ → @nterm γ _ := sorry

theorem correctness2 (x : @nterm γ _) : x ~ norm x :=
by sorry

end nterm

end polya
