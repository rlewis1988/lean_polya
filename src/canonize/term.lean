import data.real.basic data.complex.basic
import data.num.lemmas

section
local attribute [semireducible] reflected
meta instance rat.reflect : has_reflect ℚ
| ⟨n, d, _, _⟩ := `(rat.mk_nat %%(reflect n) %%(reflect d))
end

namespace polya

class morph (γ : Type) [ring γ] (α : Type) [discrete_field α] :=
(morph : γ → α)
(morph0 : morph 0 = 0)
(morph1 : morph 1 = 1)
(morph_add : ∀ a b : γ, morph (a + b) = morph a + morph b)
(morph_sub : ∀ a b : γ, morph (a - b) = morph a - morph b)
(morph_neg : ∀ a : γ, morph (-a) = - morph a)

structure dict (α : Type) :=
(val : ℕ → α)

variables {α : Type} [discrete_field α]
variable {ρ : dict α}

instance int_morph : morph ℤ α :=
{ morph     := int.cast,
  morph0    := int.cast_zero,
  morph1    := int.cast_one,
  morph_add := int.cast_add,
  morph_sub := int.cast_sub,
  morph_neg := int.cast_neg, }

instance znum_morph : morph znum α :=
{ morph     := coe,
  morph0    := znum.cast_zero,
  morph1    := znum.cast_one,
  morph_add := znum.cast_add,
  morph_sub := by simp,
  morph_neg := by simp, }

instance rat_morph [char_zero α] : morph ℚ α :=
{ morph     := rat.cast,
  morph0    := rat.cast_zero,
  morph1    := rat.cast_one,
  morph_add := rat.cast_add,
  morph_sub := rat.cast_sub,
  morph_neg := rat.cast_neg,
}

variables {γ : Type} [ring γ] [decidable_eq γ] [morph γ α]
instance : has_coe γ α := ⟨morph.morph _⟩

@[derive decidable_eq, derive has_reflect]
inductive term : Type
| zero : term
| one : term
| atom : ℕ → term
| add : term → term → term
| sub : term → term → term
| mul : term → term → term
| div : term → term → term
| neg : term → term
| inv : term → term
| pow : term → ℕ → term
| num : γ → term

namespace term

instance coe_atom : has_coe ℕ (@term γ _ _) := ⟨atom⟩
instance coe_const: has_coe γ (@term γ _ _) := ⟨num⟩
instance : has_zero (@term γ _ _) := ⟨zero⟩
instance : has_one (@term γ _ _) := ⟨one⟩
instance : has_add (@term γ _ _) := ⟨add⟩
instance : has_mul (@term γ _ _) := ⟨mul⟩
instance : has_sub (@term γ _ _) := ⟨sub⟩
instance : has_div (@term γ _ _) := ⟨div⟩
instance : has_inv (@term γ _ _) := ⟨inv⟩
instance : has_pow (@term γ _ _) ℕ := ⟨pow⟩

def eval (ρ : dict α) : @term γ _ _ → α
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
| (num r)   := morph.morph _ r

end term

@[derive decidable_eq, derive has_reflect]
inductive nterm : Type
| atom : ℕ → nterm
| const : γ → nterm
| add : nterm → nterm → nterm
| mul : nterm → nterm → nterm
| pow : nterm → ℤ → nterm

namespace nterm

instance coe_atom : has_coe ℕ (@nterm γ _ _) := ⟨atom⟩
instance coe_const: has_coe γ (@nterm γ _ _) := ⟨const⟩
instance : has_zero (@nterm γ _ _) := ⟨const 0⟩
instance : has_one (@nterm γ _ _) := ⟨const 1⟩
instance : has_add (@nterm γ _ _) := ⟨add⟩
instance : has_mul (@nterm γ _ _) := ⟨mul⟩
instance : has_pow (@nterm γ _ _) ℤ := ⟨pow⟩

def eval (ρ : dict α) : @nterm γ _ _ → α
| (atom i)  := ρ.val i
| (const c) := morph.morph _ c
| (add x y) := eval x + eval y
| (mul x y) := eval x * eval y
| (pow x n) := eval x ^ n

instance : has_coe_to_fun (dict α) := ⟨λ _, @nterm γ _ _ → α, eval⟩

def of_term : @term γ _ _ → @nterm γ _ _
| term.zero      := const 0
| term.one       := const 1
| (term.atom i)  := atom i
| (term.add x y) := add (of_term x) (of_term y)
| (term.sub x y) := add (of_term x) (mul (const (-1)) (of_term y))
| (term.mul x y) := mul (of_term x) (of_term y)
| (term.div x y) := mul (of_term x) (pow (of_term y) (-1))
| (term.neg x)   := mul (const (-1)) (of_term x)
| (term.inv x)   := pow (of_term x) (-1)
| (term.pow x n) := pow (of_term x) n
| (term.num n)   := const n

theorem keep_eval : Π (x : @term γ _ _), term.eval ρ x = eval ρ (of_term x) :=
begin
    intro x,
    induction x;
    unfold of_term; unfold term.eval; unfold eval,
    { apply eq.symm, apply morph.morph0 },
    { apply eq.symm, apply morph.morph1 },
    { congr; assumption },
    { rw [morph.morph_neg, morph.morph1, neg_one_mul],
      rw ← sub_eq_add_neg,
      congr; assumption },
    { congr; assumption },
    { rw division_def, rw fpow_inv,
      congr; assumption },
    { rw [morph.morph_neg, morph.morph1, neg_one_mul],
      congr; assumption },
    { rw fpow_inv,
      congr; assumption },
    { rw fpow_of_nat,
      congr; assumption },
end

def pp : (@nterm γ _ _) → (@nterm γ _ _)
| (atom i)  := i
| (const n) := n
| (add x y) := pp x + pp y
| (mul x y) := pp x * pp y
| (pow x n) := pp x ^ n

example (x : @nterm γ _ _) : pp x = x :=
begin
  induction x; unfold pp,
  { unfold_coes },
  { unfold_coes },
  { apply congr, apply congr_arg, assumption, assumption },
  { apply congr, apply congr_arg, assumption, assumption },
  { apply congr, apply congr_arg, assumption, refl }
end

def blt : @nterm γ _ _ → @nterm γ _ _ → bool :=
sorry
def lt : @nterm γ _ _ → @nterm γ _ _ → Prop :=
λ x y, blt x y

instance : has_lt (@nterm γ _ _) := ⟨lt⟩
instance : decidable_rel (@lt γ _ _) := by delta lt; apply_instance

def eq_val (x y : @nterm γ _ _) : Type :=
{cs : finset (@nterm γ _ _) //
    ∀ {α : Type} [df : discrete_field α] [@morph γ _ α df] (ρ : dict α),
    by resetI; exact (∀ c ∈ cs, ρ c ≠ 0) → ρ x = ρ y}

infixr ` ~ ` := eq_val

namespace eq_val

variables {a b c : @nterm γ _ _} {x y z : @nterm γ _ _} {n m : ℤ}

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
⟨∅, by {intros, resetI, unfold_coes, apply add_assoc}⟩

protected def mul_comm : (x * y) ~ (y * x) :=
⟨∅, by {intros, resetI, apply mul_comm}⟩

protected def mul_assoc : (x * y * z) ~ (x * (y * z)) :=
⟨∅, by {intros, resetI, unfold_coes, apply mul_assoc}⟩

protected def pow_add : (x ^ (n + m)) ~ x ^ n * x ^ m :=
begin
  unfold has_pow.pow, unfold has_mul.mul,
  refine ⟨_, _⟩,
  { exact if n ≠ 0 ∧ m ≠ 0 ∧ (n + m) = 0 then {x} else ∅ },
  { intros _ _ _ ρ H,
    unfold_coes, unfold eval, resetI,
    by_cases h1 : n = 0,
    { rw [h1, zero_add, fpow_zero, one_mul] },
    by_cases h2 : m = 0,
    { rw [h2, add_zero, fpow_zero, mul_one] },
    by_cases h3 : n + m = 0,
    { apply fpow_add,
      have : n ≠ 0 ∧ m ≠ 0 ∧ n + m = 0, from ⟨h1, h2, h3⟩,
      apply H, simp [this]
    },
    by_cases h4 : eval ρ x = 0,
    { rw [h4, zero_fpow n h1, zero_fpow (n + m) h3],
      simp },
    { apply fpow_add h4 }}
end

protected def congr_add (u : a ~ x) (v : b ~ y) : add a b ~ add x y :=
⟨u.val ∪ v.val, begin
  intros _ _ _ ρ H, resetI,
  unfold_coes, unfold eval,
  apply congr, apply congr_arg,
  apply u.property, intros, apply H,
  apply finset.mem_union_left, assumption,
  apply v.property, intros, apply H,
  apply finset.mem_union_right, assumption,
end⟩

protected def congr_mul (u : a ~ x) (v : b ~ y) : mul a b ~ mul x y :=
⟨u.val ∪ v.val, begin
  intros _ _ _ ρ H, resetI,
  unfold_coes, unfold eval,
  apply congr, apply congr_arg,
  apply u.property, intros, apply H,
  apply finset.mem_union_left, assumption,
  apply v.property, intros, apply H,
  apply finset.mem_union_right, assumption,
end⟩

protected def congr_pow {n} (u : x ~ y) : pow x n ~ pow y n :=
⟨u.val, begin
  intros _ _ _ ρ H, resetI,
  unfold_coes, unfold eval,
  apply congr, apply congr_arg,
  apply u.property, intros, apply H, assumption,
  refl
end⟩

end eq_val

def step : Type := Π (x : @nterm γ _ _), Σ (y : @nterm γ _ _), x ~ y

namespace step

def comp (f g : @step γ _ _) : @step γ _ _ :=
assume x,
let ⟨y, pr1⟩ := g x in
let ⟨z, pr2⟩ := f y in
⟨z, eq_val.trans pr1 pr2⟩

infixr ` ∘ ` := comp

end step

def id : @step γ _ _
| x := ⟨x, eq_val.rfl⟩

def canonize : @step γ _ _ := sorry

end nterm

end polya
