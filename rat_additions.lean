import .rat 

meta instance : has_to_format ℤ := ⟨λ z, int.rec_on z (λ k, ↑k) (λ k, "-"++↑(k+1)++"")⟩

meta instance int.reflect : has_reflect int
| (int.of_nat n) := 
       if n = 0 then unchecked_cast `(0 : int)
       else if n = 1 then unchecked_cast `(1 : int)
       else if n % 2 = 0 then unchecked_cast $ `(λ n : int, bit0 n).subst (int.reflect ↑(n / 2))
       else unchecked_cast $ `(λ n : int, bit1 n).subst (int.reflect ↑(n / 2))
| (int.neg_succ_of_nat n) := let rv := int.reflect (int.of_nat (n+1)) in unchecked_cast `(-%%rv : ℤ)

/-meta def f (z : ℤ) : expr := `(z)
set_option pp.all true
run_cmd tactic.trace $ f (-10)-/

def rat_of_int (i : ℤ) : ℚ := ⟦⟨i, 1, zero_lt_one⟩⟧

meta def num_denum.to_expr : rat.num_denum → expr
| (num, ⟨denum, _⟩) := `((rat_of_int %%(int.reflect num)) / (rat_of_int (%%(int.reflect denum)) : ℚ))

meta def num_denum_to_expr_wf : Π a b : rat.num_denum, rat.rel a b → num_denum.to_expr a = num_denum.to_expr b := sorry

meta def rat.to_expr  :=
quot.lift num_denum.to_expr num_denum_to_expr_wf

meta instance rat.reflect : has_reflect rat :=
λ q, unchecked_cast $ q.to_expr


/-set_option pp.all true
run_cmd  tactic.trace $ (↑`(-5 : ℤ) : expr)
meta example (z : ℤ) : reflected z := by apply_instance
-/ 

/-
| n := if n = 0 then unchecked_cast `(0 : nat)
       else if n % 2 = 0 then unchecked_cast $ `(λ n : nat, bit0 n).subst (nat.reflect (n / 2))
       else unchecked_cast $ `(λ n : nat, bit1 n).subst (nat.reflect (n / 2))
-/
-- make this more efficient. Why did it disappear?
--meta instance : has_to_pexpr ℕ := ⟨λ n, nat.rec_on n ``(0) (λ _ k, ``(%%k + 1))⟩

--meta instance : has_to_pexpr ℤ :=
--⟨λ z, int.rec_on z (λ k, ``(%%k)) (λ k, ``(-(%%(k)+1)))⟩


meta def num_denum_format : rat.num_denum → format
| (num, ⟨denum, _⟩) := 
if num = 0 then "0"
--else if denum = 1 then to_fmt num
else to_fmt num ++ "/" ++ to_fmt denum



/-meta def num_denum_quote : rat.num_denum → pexpr
| (num, ⟨denum, _⟩) := ``(%%(to_pexpr num)/%%(to_pexpr denum))-/

meta def num_denum_format_wf : Π a b : rat.num_denum, rat.rel a b → num_denum_format a = num_denum_format b := sorry

--meta def num_denum_quote_wf : Π a b : rat.num_denum, rat.rel a b → num_denum_quote a = num_denum_quote b := sorry

meta instance : has_to_format ℚ :=
⟨quot.lift num_denum_format num_denum_format_wf⟩

/-meta instance : has_to_pexpr ℚ :=
⟨quot.lift num_denum_quote num_denum_quote_wf⟩
-/
