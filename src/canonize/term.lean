import data.real.basic data.complex.basic

section
local attribute [semireducible] reflected
meta instance rat.reflect : has_reflect ℚ
| ⟨n, d, _, _⟩ := `(rat.mk_nat %%(reflect n) %%(reflect d))
end

namespace polya

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
| pow : term → ℤ → term
| sca : ℚ → term

namespace term

def blt : term → term → bool :=
sorry
def lt : term → term → Prop :=
λ x y, blt x y

instance : has_lt term := ⟨lt⟩
instance : decidable_rel lt := by delta lt; apply_instance

structure dict (α : Type*) :=
(val : ℕ → α)

namespace dict
variables {α : Type*} [discrete_field α]
def eval (ρ : dict α) : term → α
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
| (sca r)   := ↑r
end dict

def eq_val (x y : term) : Type :=
{cs : finset term // ∀ {α : Type*} [discrete_field α] (ρ : dict α),
    by resetI; exact (∀ c ∈ cs, ρ.eval c ≠ 0) → ρ.eval x = ρ.eval y}

infixr ` ~ ` := eq_val

namespace eq_val

variables {x y z : term} {n m : ℤ}

def rfl : x ~ x :=
⟨∅, assume _ _ _ _, rfl⟩

def symm (u : x ~ y) : y ~ x :=
⟨u.val, by {intros, apply eq.symm, apply u.property, assumption}⟩

def trans (u : x ~ y) (v : y ~ z) : x ~ z :=
⟨u.val ∪ v.val, by intros _ _ ρ H; resetI; exact
    eq.trans
        (u.property ρ $ λ c hc, H _ (finset.mem_union_left _ hc))
        (v.property ρ $ λ c hc, H _ (finset.mem_union_right _ hc))
⟩

theorem add_comm : (add x y) ~ (add y x) :=
⟨∅, by {intros, resetI, apply add_comm}⟩

theorem pow_neg : pow x (-n) ~ inv (pow x n) :=
⟨∅, by {intros, unfold dict.eval, sorry}⟩

end eq_val

def step : Type := Π (x : term), Σ (y : term), x ~ y

namespace step

def comp (f g : step) : step :=
assume x : term,
let ⟨y, pr1⟩ := g x in
let ⟨z, pr2⟩ := f y in
⟨z, eq_val.trans pr1 pr2⟩

infixr ` ∘ ` := comp

end step

def f : step := sorry
def g : step := sorry

def canonize : step := f ∘ g

end term

end polya
