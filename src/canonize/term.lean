import data.real.basic data.complex.basic

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

instance default_morph : morph ℤ α :=
{ morph := int.cast,
  morph0 := int.cast_zero,
  morph1 := int.cast_one,
  morph_add := int.cast_add,
  morph_sub := int.cast_sub,
  morph_neg := int.cast_neg, }

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

instance : has_coe_to_fun (dict α) := ⟨λ _, @term γ _ _ → α, eval⟩

def blt : @term γ _ _ → @term γ _ _ → bool :=
sorry
def lt : @term γ _ _ → @term γ _ _ → Prop :=
λ x y, blt x y

instance : has_lt (@term γ _ _) := ⟨lt⟩
instance : decidable_rel (@lt γ _ _) := by delta lt; apply_instance

def eq_val (x y : @term γ _ _) : Type :=
{cs : finset (@term γ _ _) //
    ∀ {α : Type} [df : discrete_field α] [@morph γ _ α df] (ρ : dict α),
    by resetI; exact (∀ c ∈ cs, ρ c ≠ 0) → ρ x = ρ y}

infixr ` ~ ` := eq_val

namespace eq_val

variables {x y z : @term γ _ _} {n m : ℤ}

def rfl : x ~ x :=
⟨∅, assume _ _ _ _ _, rfl⟩

def symm (u : x ~ y) : y ~ x :=
⟨u.val, by {intros, apply eq.symm, apply u.property, assumption}⟩

def trans (u : x ~ y) (v : y ~ z) : x ~ z :=
⟨u.val ∪ v.val, by intros _ _ _ ρ H; resetI; exact
    eq.trans
        (u.property ρ $ λ c hc, H _ (finset.mem_union_left _ hc))
        (v.property ρ $ λ c hc, H _ (finset.mem_union_right _ hc))
⟩

def add_comm : (add x y) ~ (add y x) :=
⟨∅, by {intros, resetI, apply add_comm}⟩

end eq_val

def step : Type := Π (x : @term γ _ _), Σ (y : term), x ~ y

namespace step

def comp (f g : @step γ _ _) : step :=
assume x : term,
let ⟨y, pr1⟩ := g x in
let ⟨z, pr2⟩ := f y in
⟨z, eq_val.trans pr1 pr2⟩

infixr ` ∘ ` := comp

end step

def f : @step γ _ _ := sorry
def g : @step γ _ _ := sorry

def canonize : @step γ _ _ := f ∘ g

end term

@[derive decidable_eq, derive has_reflect]
inductive nterm : Type
| atom : ℕ → nterm
| const : γ → nterm
| add : nterm → nterm → nterm
| mul : nterm → nterm → nterm
| pow : nterm → ℤ → nterm

namespace nterm

def eval (ρ : dict α) : @nterm γ _ _ → α
| (atom i) := ρ.val i
| (const c) := ↑c
| (add x y) := eval x + eval y
| (mul x y) := eval x * eval y
| (pow x n) := eval x ^ n

instance : has_coe_to_fun (dict α) := ⟨λ _, @nterm γ _ _ → α, eval⟩

end nterm

end polya
