import data.real.basic data.complex.basic
import data.num.lemmas
import data.list.sort data.list.basic data.list.perm

section
local attribute [semireducible] reflected
meta instance rat.reflect : has_reflect ℚ
| ⟨n, d, _, _⟩ := `(rat.mk_nat %%(reflect n) %%(reflect d))
end

meta def tactic.interactive.intros' : tactic unit :=
`[repeat {intro}, resetI]

attribute [elim_cast] znum.cast_inj
attribute [squash_cast] znum.to_of_int
attribute [squash_cast] znum.cast_zero
attribute [move_cast] znum.cast_add

namespace polya

structure dict (α : Type) :=
(val : num → α)

class morph (γ : Type) [discrete_field γ] (α : Type) [discrete_field α] :=
(f : γ → α)
(morph0 : f 0 = 0)
(morph1 : f 1 = 1)
(morph_add : ∀ a b : γ, f (a + b) = f a + f b)
(morph_neg : ∀ a : γ, f (-a) = - f a)
(morph_mul : ∀ a b : γ, f (a * b) = f a * f b)
(morph_inv : ∀ a : γ, f (a⁻¹) = (f a)⁻¹)
(morph_inj : ∀ a : γ, f a = 0 → a = 0)

namespace morph

--TODO: replace ℚ with znum × znum
instance rat_morph {α} [discrete_field α] [char_zero α] : morph ℚ α :=
{ f         := rat.cast,
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

attribute [simp] morph.morph0
attribute [simp] morph.morph1
attribute [simp] morph.morph_mul
--TODO

section
variables {α : Type} [discrete_field α]
variables {γ : Type} [discrete_field γ]
variables [morph γ α]
variables {a b : γ}

theorem morph_sub : f α (a - b) = f _ a - f _ b :=
by rw [sub_eq_add_neg, morph.morph_add, morph.morph_neg, ← sub_eq_add_neg]

theorem morph_div : f α (a / b) = f _ a / f _ b :=
by rw [division_def, morph.morph_mul, morph.morph_inv, ← division_def]

theorem morph_pow_nat (n : ℕ) : f α (a ^ n) = (f _ a) ^ n :=
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

theorem morph_pow (n : ℤ) : f α (a ^ n) = (f _ a) ^ n :=
begin
  cases n,
  { rw [int.of_nat_eq_coe, fpow_of_nat, fpow_of_nat],
    apply morph_pow_nat },
  { rw [int.neg_succ_of_nat_coe, fpow_neg, fpow_neg],
    rw [morph_div, morph.morph1],
    rw [fpow_of_nat, fpow_of_nat],
    rw morph_pow_nat }
end

end

end morph

class coeff (γ : Type) : Type :=
(df : discrete_field γ)
(le : has_le γ)
(dec_le : decidable_rel le.le)

variables {α : Type} [discrete_field α]
variables {γ : Type} [coeff γ]

instance : discrete_field γ := coeff.df γ
instance : has_le γ := coeff.le γ
instance : decidable_rel (@has_le.le γ _) := coeff.dec_le γ

variables [morph γ α] {ρ : dict α}

@[derive decidable_eq, derive has_reflect]
inductive nterm : Type
| atom  : num → nterm
| const : γ → nterm
| add   : nterm → nterm → nterm
| mul   : nterm → nterm → nterm
| pow   : nterm → znum → nterm

namespace nterm

def ble  :
  @nterm γ _ → @nterm γ _ → bool
| (atom i)  (atom j)  := i ≤ j
| (atom _)  _         := tt
| _         (atom _)  := ff
| (const a) (const b) := a ≤ b
| (const _) _         := tt
| _         (const _) := ff
| (add x y) (add z w) := if x = z then ble y w else ble x z
| (add _ _) _         := tt
| _         (add _ _) := ff
| (mul x y) (mul z w) := if x = z then ble y w else ble x z
| (mul _ _) _         := tt
| _         (mul _ _) := ff
| (pow x n) (pow y m) := if x = y then n ≤ m else ble x y

def le : @nterm γ _ → @nterm γ _ → Prop := λ x y, ble x y
def lt : @nterm γ _ → @nterm γ _ → Prop := λ x y, ble x y ∧ x ≠ y
instance : has_le (@nterm γ _) := ⟨le⟩
instance : has_lt (@nterm γ _) := ⟨lt⟩
instance dec_le : decidable_rel (@le γ _) := by dunfold le; apply_instance
instance dec_lt : decidable_rel (@lt γ _) := by dunfold lt; apply_instance

instance coe_atom : has_coe num (@nterm γ _) := ⟨atom⟩
instance coe_const: has_coe γ (@nterm γ _) := ⟨const⟩
instance : has_zero (@nterm γ _) := ⟨const 0⟩
instance : has_one (@nterm γ _) := ⟨const 1⟩
instance : has_add (@nterm γ _) := ⟨add⟩
instance : has_mul (@nterm γ _) := ⟨mul⟩
instance : has_pow (@nterm γ _) znum := ⟨pow⟩

def neg (x : @nterm γ _) : @nterm γ _ := (-1 : γ) * x
instance : has_neg (@nterm γ _) := ⟨neg⟩
def sub (x y : @nterm γ _) : @nterm γ _ := x + (-y)
instance : has_sub (@nterm γ _) := ⟨sub⟩
def inv (x : @nterm γ _) : @nterm γ _ := pow x (-1)
instance : has_inv (@nterm γ _) := ⟨inv⟩
def div (x y : @nterm γ _) : @nterm γ _ := x * y⁻¹
instance : has_div (@nterm γ _) := ⟨div⟩

def eval (ρ : dict α) : @nterm γ _ → α
| (atom i)  := ρ.val i
| (const c) := morph.f _ c
| (add x y) := eval x + eval y
| (mul x y) := eval x * eval y
| (pow x n) := eval x ^ (n : ℤ)

section
variables {x y : @nterm γ _} {i : num} {n : znum} {c : γ}
@[simp] theorem eval_zero : (0 : @nterm γ _).eval ρ = 0 := by apply morph.morph0
@[simp] theorem eval_one : (1 : @nterm γ _).eval ρ = 1 := by apply morph.morph1
@[simp] theorem eval_atom : (i : @nterm γ _).eval ρ = ρ.val i := rfl
@[simp] theorem eval_const : (c : @nterm γ _).eval ρ = morph.f _ c := rfl
@[simp] theorem eval_add : (x + y).eval ρ = x.eval ρ + y.eval ρ := rfl
@[simp] theorem eval_mul : (x * y).eval ρ = x.eval ρ * y.eval ρ := rfl
@[simp] theorem eval_pow : (x ^ n).eval ρ = x.eval ρ ^ (n : ℤ) := rfl
@[simp] theorem eval_pow_zero : (x ^ (0 : znum)).eval ρ = 1 := by simp

@[simp] theorem eval_neg : (-x).eval ρ = - x.eval ρ :=
calc
eval ρ (-x)
    = eval ρ (neg x) : rfl
... = - eval ρ x     : by simp [neg, morph.morph_neg, morph.morph1]

@[simp] theorem eval_sub : (x - y).eval ρ = x.eval ρ - y.eval ρ :=
calc
eval ρ (x - y)
    = eval ρ (sub x y)    : rfl
... = eval ρ x - eval ρ y : by simp [sub, sub_eq_add_neg]

@[simp] theorem eval_inv : (x⁻¹).eval ρ = (x.eval ρ)⁻¹ :=
calc
eval ρ (x⁻¹)
    = eval ρ (inv x)        : rfl
... = (eval ρ x) ^ (-1 : ℤ) : by simp [inv, eval]
... = (eval ρ x)⁻¹          : fpow_inv _

@[simp] theorem eval_div : (x / y).eval ρ = x.eval ρ / y.eval ρ :=
calc
eval ρ (x / y)
    = eval ρ (div x y)    : rfl
... = eval ρ x / eval ρ y : by simp [div, div_eq_mul_inv]

end

meta def to_str [has_to_string γ] : (@nterm γ _) → string
| (atom i)  := "#" ++ to_string (i : ℕ)
| (const c) := to_string c
| (add x y) := "(" ++ to_str x ++ " + " ++ to_str y ++ ")"
| (mul x y) := "(" ++ to_str x ++ " * " ++ to_str y ++ ")"
| (pow x n) := to_str x ++ " ^ " ++ to_string (n : ℤ)

meta instance [has_to_string γ] : has_to_string (@nterm γ _) := ⟨to_str⟩
meta instance [has_to_string γ] : has_to_tactic_format (@nterm γ _) := ⟨λ x, return (to_str x : format)⟩

def sum : list (@nterm γ _) → @nterm γ _
| []      := (0 : @nterm γ _)
| (x::xs) := list.foldl add x xs

def prod : list (@nterm γ _) → @nterm γ _
| []      := (1 : @nterm γ _)
| (x::xs) := list.foldl mul x xs

theorem eval_sum (xs : list (@nterm γ _)) :
  (sum xs).eval ρ = list.sum (xs.map (nterm.eval ρ)) :=
begin
  cases xs with y xs,
  { simp [sum] },
  { unfold sum, 
    rw [list.map_cons, list.sum_cons],
    revert y,
    induction xs with x xs ih,
    { simp },
    { intro y,
      rw [list.map_cons, list.foldl_cons, list.sum_cons],
      rw [ih (add y x), ← add_assoc, ← eval_add],
      refl }}
end

theorem eval_prod (xs : list (@nterm γ _)) :
  (prod xs).eval ρ = list.prod (xs.map (nterm.eval ρ)) :=
begin
  cases xs with y xs,
  { simp [prod] },
  { unfold prod, 
    rw [list.map_cons, list.prod_cons],
    revert y,
    induction xs with x xs ih,
    { simp },
    { intro y,
      rw [list.map_cons, list.foldl_cons, list.prod_cons],
      rw [ih (mul y x), ← mul_assoc, ← eval_mul],
      refl }}
end

end nterm

end polya
