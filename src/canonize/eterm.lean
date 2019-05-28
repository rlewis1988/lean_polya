import .pterm

namespace polya

variables {α : Type} [discrete_field α]
variables {γ : Type} [coeff γ]
variables [morph γ α] {ρ : dict α}

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
