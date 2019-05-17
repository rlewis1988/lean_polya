import data.real.basic --data.list.alist data.finmap

section --TODO: move to data.rat?
local attribute [semireducible] reflected
meta instance rat.reflect : has_reflect ℚ
| ⟨n, d, _, _⟩ := `(rat.mk_nat %%(reflect n) %%(reflect d))
end

namespace list
open tactic
meta def expr_reflect (type : expr) : list expr → tactic expr
| [] := to_expr ``([] : list %%type)
| (h::t) := do e ← expr_reflect t, to_expr ``(list.cons (%%h : %%type) %%e)
end list

namespace polya

@[derive decidable_eq, derive has_reflect]
inductive term : Type
| zero : term
| one : term
| atm : ℕ → term
| add : term → term → term
| mul : term → term → term
| sca : term → ℚ → term
| exp : term → ℤ → term

namespace term

private def str : term → string
| zero := "zero"
| one  := "one"
| (atm i) := "(atm " ++ to_string i ++ ")"
| (add x y) := "(add " ++ str x ++ " " ++ str y ++ ")"
| (mul x y) := "(mul " ++ str x ++ " " ++ str y ++ ")"
| (sca x c) := "(sca " ++ str x ++ " " ++ to_string c ++ ")"
| (exp x n) := "(sca " ++ str x ++ " " ++ to_string n ++ ")"

instance : has_to_string term := ⟨str⟩
meta instance : has_to_format term := ⟨λ t, str t⟩
meta instance : has_to_tactic_format term := ⟨λ t, return (str t)⟩

private def blt : term → term → bool
| zero       zero       := ff
| _          zero       := ff
| zero       _          := tt
| one        one        := ff
| _          one        := ff
| one        _          := tt
| (atm i)    (atm j)    := i < j
| _          (atm _)    := ff
| (atm _)    _          := tt
| (add x x') (add y y') := blt x y ∨ (x = y ∧ blt x' y')
| _          (add _ _)  := ff
| (add _ _)  _          := tt
| (mul x x') (mul y y') := blt x y ∨ (x = y ∧ blt x' y')
| _          (mul _ _)  := ff
| (mul _ _)  _          := tt
| (sca x a)  (sca y b)  := blt x y ∨ (x = y ∧ a < b)
| _          (sca _ _)  := ff
| (sca _ _)  _          := tt
| (exp x n)  (exp y m)  := blt x y ∨ (x = y ∧ n < m)

def lt : term → term → Prop :=
λ x y, blt x y

instance : has_lt term := ⟨lt⟩
instance : decidable_rel lt := by delta lt; apply_instance

structure dict (α : Type*) :=
(val : ℕ → α)

variables {α : Type*} [discrete_field α]

def dict.eval (ρ : dict α) : term → α
| zero := 0
| one := 1
| (atm i) := ρ.val i
| (add x y) := dict.eval x + dict.eval y
| (mul x y) := dict.eval x * dict.eval y
| (sca x c) := dict.eval x * c
| (exp x n) := dict.eval x ^ n

section
variable {ρ : dict α}
variables (x y z : term) (i : ℕ) (c : ℚ) (n : ℤ)
theorem mul_zero : ρ.eval (sca x 0) = 0 := by {unfold dict.eval, apply_mod_cast mul_zero}
theorem add_comm : ρ.eval (add x y) = ρ.eval (add y x) := add_comm _ _
/- TODO: a lot of lemmas -/
end

--TODO: find a better name
def foo (ρ : dict α) (x y : term) : Type :=
{cs : list term // (∀ c ∈ cs, ρ.eval c ≠ 0) → ρ.eval x = ρ.eval y}

namespace foo

variable {ρ : dict α}
variables {x y z : term}

def of_eq (h : ρ.eval x = ρ.eval y) : foo ρ x y :=
⟨[], assume _, h⟩

def rfl : foo ρ x x := of_eq (congr_arg _ rfl)

def trans (u : foo ρ x y) (v : foo ρ y z) : foo ρ x z :=
⟨list.union u.val v.val,
    assume H, eq.trans
    (u.property $ assume c hc, H _ (list.mem_union_left hc _))
    (v.property $ assume c hc, H _ (list.mem_union_right _ hc))
⟩

end foo

def step (ρ : dict α) : Type := Π (x : term), Σ (y : term), foo ρ x y

namespace step

def comp {ρ : dict α} (f g : step ρ) : step ρ :=
assume x : term,
let ⟨y, pr1⟩ := g x in
let ⟨z, pr2⟩ := f y in
⟨z, foo.trans pr1 pr2⟩

infixr ` ∘ ` := comp

end step

variable {eval : dict α}
def f : step eval := sorry
def g : step eval := sorry

def canonize : step eval := f ∘ g

end term

end polya
