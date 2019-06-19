import data.rat data.nat.gcd tactic.finish algebra.group_power

--meta instance : has_to_format ℤ := ⟨λ z, int.rec_on z (λ k, ↑k) (λ k, "-"++↑(k+1)++"")⟩

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

--def rat_of_int (i : ℤ) : ℚ := --⟦⟨i, 1, zero_lt_one⟩⟧
--{ num := i, denom := 1, 

/-meta def num_denum.to_expr : rat.num_denum → expr
| (num, ⟨denum, _⟩) := `((rat.of_int %%(int.reflect num)) / (rat.of_int (%%(int.reflect denum)) : ℚ))

meta def num_denum_to_expr_wf : Π a b : rat.num_denum, rat.rel a b → num_denum.to_expr a = num_denum.to_expr b := sorry

meta def rat.to_expr  :=
quot.lift num_denum.to_expr num_denum_to_expr_wf

meta instance rat.reflect : has_reflect rat :=
λ q, unchecked_cast $ q.to_expr
-/

--private meta def nat_to_rat_expr : nat → expr | n :=
--if n = 0 then `(0 : ℚ)
--else if n = 1 then `(1 : ℚ)
--else if n % 2 = 0 then `(@bit0 ℚ _ %%(nat_to_rat_expr (n/2)))
--else `(@bit1 ℚ _ _ %%(nat_to_rat_expr (n/2)))
--
--private meta def int_to_rat_expr : int → expr | n :=
--if n = 0 then `(0 : ℚ)
--else if n < 0 then `(-%%(int_to_rat_expr (-n)) : ℚ)
--else if n = 1 then `(1 : ℚ)
--else if n % 2 = 0 then `(@bit0 ℚ _ %%(int_to_rat_expr (n/2)))
--else `(@bit1 ℚ _ _ %%(int_to_rat_expr (n/2)))
--
--meta def rat.to_expr (q : ℚ) : expr :=
--if q.denom = 1 then
--  `(%%(int_to_rat_expr q.num) : ℚ) 
--else 
--  `(%%(int_to_rat_expr q.num) / %%(nat_to_rat_expr q.denom) : ℚ)
----`(rat.mk_nat %%(int.reflect q.num) %%(nat.reflect q.denom))
--
--meta instance rat.reflect : has_reflect rat :=
--λ q, unchecked_cast $ q.to_expr

section
open nat

theorem gcd_ne_zero_right (a : ℕ) {b : ℕ} (hb : b ≠ 0) : gcd a b ≠ 0 :=
assume : gcd a b = 0,
have gcd a b ∣ b, from gcd_dvd_right _ _,
have 0 ∣ b, by cc,
have b = 0, from eq_zero_of_zero_dvd this,
by contradiction

end

def sign {α} [decidable_linear_ordered_comm_ring α] (a : α) : α :=
if a < 0 then (-1) else if a = 0 then 0 else 1
/-
section
open int
def int.gcd : ℤ → ℤ → ℤ 
| (of_nat k1) (of_nat k2) := of_nat (nat.gcd k1 k2)
| (of_nat k1) (neg_succ_of_nat k2) := of_nat (nat.gcd k1 (k2+1))
| (neg_succ_of_nat k1) (of_nat k2) := of_nat (nat.gcd (k1+1) k2)
| (neg_succ_of_nat k1) (neg_succ_of_nat k2) := of_nat (nat.gcd (k1+1) (k2+1))

/-def int.sign : ℤ → ℤ
--| (of_nat 0) := 0
| (of_nat k) := if k = 0 then 0 else 1
| (neg_succ_of_nat _) := -1-/

/-def int.div : ℤ → ℤ → ℤ 
| (of_nat k1) (of_nat k2) := of_nat (k1 / k2)
| (of_nat k1) (neg_succ_of_nat k2) := neg_succ_of_nat (k1 / (k2+1))
| (neg_succ_of_nat k1) (of_nat k2) := neg_succ_of_nat ((k1) / k2)
| (neg_succ_of_nat k1) (neg_succ_of_nat k2) := of_nat ((k1+1) / (k2+1))-/

def int.div (a b : ℤ) : ℤ :=
sign b *
  (match a with
    | of_nat m := of_nat (m / (nat_abs b))
    | -[1+m]   := -[1+ ((m:nat) / (nat_abs b))]
  end)

instance : has_div int := ⟨int.div⟩

theorem int.of_nat_ne_zero_of_ne_zero {n : ℕ} (h : n ≠ 0) : of_nat n ≠ 0 :=
suppose of_nat n = of_nat 0,
by cc

@[ematch]
theorem int_gcd_ne_zero_right : Π (a : ℤ) {b : ℤ} (h : b ≠ 0), int.gcd a b ≠ 0 :=
begin
intros,
induction a, 
all_goals {induction b; apply int.of_nat_ne_zero_of_ne_zero; apply gcd_ne_zero_right; finish}
end

theorem int.gcd_pos_of_ne_right (a : ℤ) {b : ℤ} (h : b ≠ 0) : int.gcd a b > 0 :=
begin
induction a,
all_goals {induction b; unfold int.gcd; apply of_nat_p},


end
/-

variable P : ℕ → Prop
theorem f : Π (h : P 0) (h2 : ∀ n, P n → P (n+1)), Π (n : ℕ), P n
| h h2 0 := sorry --begin try {do n ← decl_name, interactive.clear [n]}; finish end
| h h2 (k+1) := begin apply h2, apply f, apply h, apply h2 end


theorem int_gcd_ne_zero_right' : Π (a : ℤ) {b : ℤ} (h : b ≠ 0), int.gcd a b ≠ 0 :=
begin
intros,
cases a; cases b,
safe [int_gcd_ne_zero_right],
-/

/-| (of_nat k1) (of_nat k2) h := begin safe end
| (of_nat k1) (neg_succ_of_nat k2) h := sorry
| (neg_succ_of_nat k1) (of_nat k2) h := sorry
| (neg_succ_of_nat k1) (neg_succ_of_nat k2) h := sorry
 -/

def num_denum.reduce : rat.num_denum → rat.num_denum | (num, ⟨denum, _⟩) :=
let g := int.gcd num denum in
(num/g, ⟨denum/g, begin end⟩)-/


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


/-meta def num_denum_format : rat.num_denum → format
| (num, ⟨denum, _⟩) := 
if num = 0 then "0"
--else if denum = 1 then to_fmt num
else to_fmt num ++ "/" ++ to_fmt denum
-/


/-meta def num_denum_quote : rat.num_denum → pexpr
| (num, ⟨denum, _⟩) := ``(%%(to_pexpr num)/%%(to_pexpr denum))-/

--meta def num_denum_format_wf : Π a b : rat.num_denum, rat.rel a b → num_denum_format a = num_denum_format b := sorry

--meta def num_denum_quote_wf : Π a b : rat.num_denum, rat.rel a b → num_denum_quote a = num_denum_quote b := sorry

meta def rat.to_string (q : ℚ) : string :=
if q.denom = 1 then
  to_string q.num
else
  to_string q.num ++ " / " ++ to_string q.denom


meta def rat.to_format (q : ℚ) : format :=
/-if q.denom = 1 then
  to_fmt q.num
else
  to_fmt q.num ++ " / " ++ to_fmt q.denom-/
rat.to_string q

/-meta instance : has_to_pexpr ℚ :=
⟨quot.lift num_denum_quote num_denum_quote_wf⟩
-/

def rat.pow (q : ℚ) : ℤ → ℚ
| (int.of_nat n) := q^n
| -[1+n] := 1/(q^(n+1))

--def rat.pow (q : ℚ) (z : ℤ) : ℚ :=
--if q = 1 then q else if z = 1 then q else rat.pow_aux q z

lemma rat.mul_pow_neg_one {q : ℚ} (h : q ≠ 0) : q * (rat.pow q (-1)) = 1 :=
begin
change (-1 : ℤ) with -[1+0],
simp [rat.pow, mul_inv_cancel h]
end

lemma rat.pow_neg_one {q : ℚ} : rat.pow q (-1) = 1 / q :=
begin
change (-1 : ℤ) with -[1+0],
simp [rat.pow]
end

lemma rat.pow_one {q : ℚ} : rat.pow q 1 = q :=
begin
change (1 : ℤ) with int.of_nat 1,
simp [rat.pow]
end

lemma rat.pow_pow (a : ℚ) (z1 z2 : ℤ) : rat.pow (rat.pow a z1) z2 = rat.pow a (z1*z2) := sorry

lemma rat.one_div_pow (q : ℚ) (z : ℤ) : rat.pow (1/q) z = rat.pow q (-z) := sorry

namespace int
open nat
/-protected def div : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := of_nat (m / n)
| (m : ℕ) -[1+ n] := -of_nat (m / succ n)
| -[1+ m] 0       := 0
| -[1+ m] (n+1:ℕ) := -[1+ m / succ n]
| -[1+ m] -[1+ n] := of_nat (succ (m / succ n))

instance : has_div int := ⟨int.div⟩ 

-/
theorem exists_eq_of_nat {z : ℤ} (h : z ≥ 0) : ∃ n : ℕ, z = n :=
match int.le.dest h with
| ⟨n, pr⟩ := ⟨n, by clear _match; finish⟩
end

end int

theorem nat.one_lt_pow_of_one_lt {x n : ℕ} (h : 1 < x) (hn : n > 0) : 1 < nat.pow x n := 
have h : nat.pow 1 n = 1, from nat.one_pow _,
begin
rw ←h, apply nat.pow_lt_pow_of_lt_left, 
repeat {assumption}
end

theorem rat.one_pow : Π (n : ℤ), rat.pow 1 n = 1
| (int.of_nat n) := by simp [rat.pow]
| -[1+n] := by simp [rat.pow, one_inv_eq]

theorem rat.mul_pow (q r : ℚ) : Π (z : ℤ), rat.pow (q*r) z = rat.pow q z * rat.pow r z
| (int.of_nat n) := mul_pow _ _ _
| -[1+n] := begin unfold rat.pow, rw [mul_pow, div_mul_eq_div_mul_one_div] end

theorem rat.mul_pow_rev (q r : ℚ) (z : ℤ) : rat.pow q z * rat.pow r z = rat.pow (q*r) z := by simp [rat.mul_pow]

def rat.order : ℚ → ℚ → ordering :=
λ a b, if a < b then ordering.lt else if a = b then ordering.eq else ordering.gt

def int.order : ℤ → ℤ → ordering :=
λ a b, if a < b then ordering.lt else if a = b then ordering.eq else ordering.gt
