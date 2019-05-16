 import data.real.basic

@[derive decidable_eq]
inductive term : Type
| zero : term
| one : term
| atm : ℕ → term
| add : term → term → term
| mul : term → term → term
| sca : term → ℚ → term
| exp : term → ℤ → term

namespace term

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

--def dict (α : Type) := ℕ → α
structure dict (α : Type*) := (map : ℕ → α)
variables {α : Type*} [discrete_field α] (eval : dict α)

def eval_term (map : ℕ → α) : term → α
| zero := 0
| one := 1
| (atm i) := map i
| (add x y) := eval_term x + eval_term y
| (mul x y) := eval_term x * eval_term y
| (sca x c) := eval_term x * c
| (exp x n) := eval_term x ^ n

--instance : has_coe_to_fun (dict α) := ⟨λ _, ℕ → α, dict.map⟩
instance to_eval : has_coe_to_fun (dict α) := ⟨λ _, term → α, eval_term ∘ dict.map⟩

section
variables {x y : term} {i : ℕ} {c : ℚ} {n : ℤ}
@[simp] lemma eval_zero : eval zero = 0 := rfl
@[simp] lemma eval_one : eval one = 1 := rfl
@[simp] lemma eval_atm : eval (atm i) = eval.map i := rfl
@[simp] lemma eval_add : eval (add x y) = eval x + eval y := rfl
@[simp] lemma eval_mul : eval (mul x y) = eval x * eval y := rfl
@[simp] lemma eval_sca : eval (sca x c) = eval x * c := rfl
@[simp] lemma simp_exp : eval (exp x n) = eval x ^ n := rfl
end

section
variables (x y z : term) (i : ℕ) (c : ℚ) (n : ℤ)
theorem mul_zero : eval (sca x 0) = 0 := by simp
theorem add_comm : eval (add x y) = eval (add y x) := add_comm _ _
/- TODO: a lot of lemmas -/
end

--TODO: find a name
def foo (x y : term) : Type :=
{cs : list term // (∀ c ∈ cs, eval c ≠ 0) → eval x = eval y}

namespace foo

def of_eq {x y : term} (h : eval x = eval y) : foo eval x y :=
⟨[], λ _, h⟩

def rfl (x : term) : foo eval x x := of_eq _ (congr_arg _ rfl)

def trans (x y z : term) (u : foo eval x y) (v : foo eval y z) : foo eval x z :=
⟨list.union u.val v.val,
    assume H, eq.trans
    (u.property $ assume c hc, H _ (list.mem_union_left hc _))
    (v.property $ assume c hc, H _ (list.mem_union_right _ hc))
⟩

end foo

def canonize (x : term) : Σ (y : term), foo eval x y := ⟨x, foo.rfl eval x⟩

end term
