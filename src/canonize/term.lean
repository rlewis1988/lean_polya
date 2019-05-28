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

local attribute [elim_cast] znum.cast_inj
local attribute [squash_cast] znum.to_of_int

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

structure cterm : Type :=
(term : @nterm γ _)
(coeff : γ)

namespace cterm
def le (x y : @cterm γ _) : Prop := x.term ≤ y.term
instance : has_le (@cterm γ _) := ⟨le⟩
instance : decidable_rel (@cterm.le γ _) :=
by delta cterm.le; apply_instance

def mul (x : @cterm γ _) (a : γ) : @cterm γ _ :=
⟨x.term, x.coeff * a⟩

def of_nterm (x : @nterm γ _) : @cterm γ _ :=
⟨x, 1⟩

def to_nterm (x : @cterm γ _) : @nterm γ _ :=
if x.coeff = 0 then 0
else if x.coeff = 1 then x.term
else x.term * x.coeff

def eval (ρ : dict α) (x : @cterm γ _) : α :=
x.term.eval ρ * morph.f _ x.coeff

theorem eval_def {x : @nterm γ _} {a : γ} :
  eval ρ ⟨x, a⟩ = x.eval ρ * morph.f _ a :=
rfl

theorem eval_to_nterm (x : @cterm γ _) :
  x.to_nterm.eval ρ = x.eval ρ :=
begin
  unfold to_nterm, unfold eval,
  by_cases h1 : x.coeff = 0,
  { simp [h1, morph.morph0] },
  { by_cases h2 : x.coeff = 1,
    { simp [h2, morph.morph1] },
    { simp [h1, h2] }}
end

theorem eval_to_nterm' :
  @nterm.eval _ _ γ _ _ ρ ∘ cterm.to_nterm = cterm.eval ρ :=
begin
  unfold function.comp,
  simp [eval_to_nterm]
end

theorem eval_mul (x : @cterm γ _) (a : γ) :
  (x.mul a).eval ρ = x.eval ρ * (morph.f _ a) :=
begin
  simp [mul, eval, morph.morph_mul], 
  rw mul_assoc
end
-- TODO: morph lemmas as simp lemmas?

end cterm

structure sterm : Type :=
(terms : list (@cterm γ _))

namespace sterm

def append (S1 S2 : @sterm γ _) : @sterm γ _ :=
⟨S1.terms ++ S2.terms⟩

instance : has_append (@sterm γ _) := ⟨append⟩

theorem append_terms (S1 S2 : @sterm γ _) :
  (S1 ++ S2).terms = S1.terms ++ S2.terms := rfl

def mul (S : @sterm γ _) (a : γ) : @sterm γ _ :=
if a = 0 then ⟨[]⟩
else if a = 1 then S
else ⟨S.terms.map (λ x, x.mul a)⟩

def eval (ρ : dict α) (S : @sterm γ _) : α :=
list.sum (S.terms.map (cterm.eval ρ))

theorem eval_mul (S : @sterm γ _) (a : γ) :
(S.mul a).eval ρ = S.eval ρ * morph.f _ a :=
begin
  by_cases h : a = 0 ∨ a = 1,
  { cases h with h h,
    { simp [h, morph.morph0, mul, eval] },
    { simp [h, morph.morph1, mul, eval] }},
  { have h0 : ¬ a = 0, by { intro h0, apply h, left, exact h0 },
    have h1 : ¬ a = 1, by { intro h1, apply h, right, exact h1 },
    cases S with terms,
    simp [h0, h1, mul, eval], 
    induction terms with x xs ih,
    { simp },
    { simp [ih, add_mul, cterm.eval_mul] }
  }
end

theorem eval_add (S1 S2 : @sterm γ _) :
  (S1 ++ S2).eval ρ = S1.eval ρ + S2.eval ρ :=
begin
  unfold eval,
  simp only [append_terms],
  rw [list.map_append],
  apply list.sum_append 
end

def to_nterm (S : @sterm γ _) : @nterm γ _ :=
sum (S.terms.map (cterm.to_nterm))

theorem eval_to_nterm {S : @sterm γ _} :
  S.eval ρ = S.to_nterm.eval ρ :=
begin
  cases S with terms,
  unfold to_nterm, unfold eval,
  rw [eval_sum, list.map_map],
  rw cterm.eval_to_nterm'
end

def reduce_aux : @cterm γ _ → list (@cterm γ _) → list (@cterm γ _)
| x []      := [x]
| x (y::ys) :=
  if x.term = y.term then
    reduce_aux ⟨x.term, x.coeff + y.coeff⟩ ys
  else if x.coeff = 0 then
    reduce_aux y ys
  else
    x::(reduce_aux y ys)
  
theorem eval_reduce_aux (x : @cterm γ _) (xs : list (@cterm γ _)) :
  sterm.eval ρ ⟨reduce_aux x xs⟩ = sterm.eval ρ ⟨x::xs⟩ :=
begin
  revert x,
  induction xs with y ys ih,
  { simp [eval, reduce_aux] },
  { intro x,
    unfold eval,
    rw [list.map_cons, list.sum_cons],
    unfold eval at ih,
    by_cases h1 : x.term = y.term,
    { rw [list.map_cons, list.sum_cons],
      rw [← add_assoc],
      unfold cterm.eval,
      rw [h1, ← mul_add, ← morph.morph_add],
      rw [← cterm.eval_def, ← list.sum_cons, ← list.map_cons],
      rw [← ih],
      simp [reduce_aux, h1] },
    by_cases h2 : x.coeff = 0,
    { rw [list.map_cons, list.sum_cons],
      unfold cterm.eval,
      rw [h2, morph.morph0, mul_zero, zero_add],
      rw [← cterm.eval_def, ← list.sum_cons, ← list.map_cons],
      simp [reduce_aux, h1, h2, ih], refl
    },
    conv {
      to_lhs,
      simp [reduce_aux, h1, h2]
    },
    simp [ih]
  }
end

def reduce (S : @sterm γ _) : @sterm γ _ :=
match S.terms with
| []      := ⟨[]⟩
| (x::xs) := ⟨reduce_aux x xs⟩
end
 
theorem eval_reduce {S : @sterm γ _} :
  S.eval ρ = S.reduce.eval ρ :=
begin
  cases S with terms,
  cases terms with x xs,
  { simp [reduce] },
  { simp [reduce, eval_reduce_aux] }
end

def sort (S : @sterm γ _) : @sterm γ _ :=
⟨S.terms.merge_sort (≤)⟩

theorem eval_sort {S : @sterm γ _} :
  S.eval ρ = S.sort.eval ρ :=
begin
  unfold eval, unfold sort,
  apply list.sum_eq_of_perm,
  apply list.perm_map,
  apply list.perm.symm,
  apply list.perm_merge_sort
end

end sterm

def to_sterm : @nterm γ _ → @sterm γ _
| (add x y) := to_sterm x ++ to_sterm y
| (mul x y) :=
  match x with
  | (const a) := y.to_sterm.mul a
  | _         :=
    match y with
    | (const b) := x.to_sterm.mul b
    | _         := ⟨[⟨mul x y, 1⟩]⟩
    end
  end
| x         := ⟨[⟨x, 1⟩]⟩

theorem eval_to_sterm {x : @nterm γ _} :
  nterm.eval ρ x = sterm.eval ρ x.to_sterm :=
begin
  induction x with i c x y ihx ihy x y ihx ihy x n ihx,
  { simp [to_sterm, nterm.eval, sterm.eval, cterm.eval, morph.morph1] },
  { simp [to_sterm, nterm.eval, sterm.eval, cterm.eval, morph.morph1] },
  { unfold to_sterm, unfold eval,
    rw [sterm.eval_add, ihx, ihy] },
  { cases x,
    case const : a {
      simp only [to_sterm, sterm.eval_mul, eval, ihy],
      exact mul_comm (morph.f α a) _
    },
    repeat {
      cases y,
      case const : b {
        simp only [to_sterm, sterm.eval_mul, eval, ihx]
      },
      repeat { simp [to_sterm, nterm.eval, sterm.eval, cterm.eval, morph.morph1] },
    }
  },
  { simp [to_sterm, nterm.eval, sterm.eval, cterm.eval, morph.morph1] }

end

def norm (x : @nterm γ _) : @nterm γ _ :=
x.to_sterm.sort.reduce.to_nterm

theorem correctness {x : @nterm γ _} :
  x.eval ρ = x.norm.eval ρ :=
calc
  x.eval ρ = sterm.eval ρ x.to_sterm             : eval_to_sterm
       ... = sterm.eval ρ x.to_sterm.sort        : sterm.eval_sort
       ... = sterm.eval ρ x.to_sterm.sort.reduce : sterm.eval_reduce
       ... = nterm.eval ρ x.norm                 : sterm.eval_to_nterm
end nterm

@[derive decidable_eq, derive has_reflect]
inductive eterm : Type
| zero : eterm
| one : eterm
| atom : num → eterm
| add : eterm → eterm → eterm
| sub : eterm → eterm → eterm
| mul : eterm → eterm → eterm
| div : eterm → eterm → eterm
| neg : eterm → eterm
| inv : eterm → eterm
| pow : eterm → ℤ → eterm
| const : γ → eterm

namespace eterm

def eval (ρ : dict α) : @eterm γ _ → α
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
| (const r) := morph.f _ r

def to_nterm : @eterm γ _ → @nterm γ _
| zero      := 0
| one       := 1
| (atom i)  := i
| (add x y) := to_nterm x + to_nterm y
| (sub x y) := to_nterm x - to_nterm y
| (mul x y) := to_nterm x * to_nterm y
| (div x y) := to_nterm x / to_nterm y
| (neg x)   := - to_nterm x
| (inv x)   := to_nterm x ^ (-1 : znum)
| (pow x n) := to_nterm x ^ (n : znum)
| (const c) := c

theorem correctness {x : @eterm γ _} :
  x.eval ρ = (to_nterm x).eval ρ :=
begin
    induction x with
      i           --atom
      x y ihx ihy --add
      x y ihx ihy --sub
      x y ihx ihy --mul
      x y ihx ihy --div
      x ihx       --neg
      x ihx       --inv
      x n ihx     --pow
      c;          --const
    unfold to_nterm; unfold eterm.eval,
    repeat { simp },
    repeat { simp [ihx] },
    repeat { simp [ihx, ihy] },
    { simp [fpow_inv] }
end

end eterm

def norm (x : @eterm γ _) : @nterm γ _ :=
(eterm.to_nterm x).norm

theorem correctness {x : @eterm γ _} :
  eterm.eval ρ x = nterm.eval ρ (norm x) :=
calc
  eterm.eval ρ x = nterm.eval ρ (eterm.to_nterm x)      : eterm.correctness
            ... = nterm.eval ρ (eterm.to_nterm x).norm : nterm.correctness
            ... = nterm.eval ρ (norm x)               : rfl

end polya
