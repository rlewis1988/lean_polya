import .rat_additions tactic.norm_num --comp_val
open tactic

lemma rat_pow_mul (a : ℚ) (e : ℤ) : rat.pow a (e + e) = rat.pow a e * rat.pow a e := sorry

@[simp]
lemma rat.pow_zero (b : ℚ) : rat.pow b 0 = 1 := sorry

attribute [simp] rat.pow_one

meta def pf_by_norm_num : tactic unit :=
do (lhs, rhs) ← target >>= match_eq,
   (lhsv, lhspf) ← norm_num lhs,
   (rhsv, rhspf) ← norm_num rhs,
   to_expr ``(eq.trans %%lhspf (eq.symm %%rhspf)) >>= exact


lemma f1 (a) : rat.pow a ↑(0 : ℕ) = rat.pow a 0 := sorry
lemma f2 (a) : rat.pow a ↑(1 : ℕ) = rat.pow a 1 := sorry
lemma f3 (a b) : rat.pow a ↑(bit1 b : ℕ) = rat.pow a (bit1 ↑b) := sorry
lemma f4 (a b) : rat.pow a ↑(bit0 b : ℕ) = rat.pow a (bit0 ↑b) := sorry


meta def rat_pow_simp_lemmas : tactic simp_lemmas :=
to_simp_lemmas simp_lemmas.mk [`pow_bit0, `pow_bit1, `rat.pow_zero, `rat.pow_one, `f1, `f2, `f3, `f4]

meta def simp_rat_pow : tactic unit := 
rat_pow_simp_lemmas >>= simp_target

--`[simp only [pow_bit0, pow_bit1, rat.pow_zero, rat.pow_one, f1, f2, f3, f4]]


meta def prove_rat_pow : tactic unit :=
simp_rat_pow >>  pf_by_norm_num

--example : rat.pow 5 3 = 125 := by prove_rat_pow

inductive approx_dir
| over | under | none

meta def approx_dir.to_expr : approx_dir → expr
| approx_dir.over := `(@ge rat _)
| approx_dir.under := `(@has_le.le rat _)
| approx_dir.none := `(@eq rat)

meta def correct_offset (A x prec : ℚ) (n : ℤ) : approx_dir → ℚ
| approx_dir.over := if rat.pow x n ≥ A then x else x + prec
| approx_dir.under := if rat.pow x n ≤ A then x else x - prec
| approx_dir.none := x 

meta def round_to_denom (A : ℚ) (denom : ℕ) : ℚ :=
let num_q := (denom*A.num : ℤ) / A.denom in
rat.mk num_q denom

namespace rat

meta def nth_root_aux'' (A : ℚ) (n : ℤ) (prec : ℚ) (dir : approx_dir) : ℚ → ℚ
| guess := 
  let delta_x := (1/(n : ℚ))*((A / rat.pow guess (n - 1)) - guess),
      x := guess + delta_x in
  /-correct_offset A-/ (if abs delta_x < prec then x else nth_root_aux'' x) /-prec n dir-/

meta def nth_root_aux' (A : ℚ) (n : ℤ) (prec : ℚ) (dir : approx_dir) (guess : ℚ) : ℚ :=
correct_offset A (nth_root_aux'' A n prec dir guess) prec n dir

meta def nth_root_aux (A : ℚ) (n : ℤ) (prec guess : ℚ) (dir : approx_dir := approx_dir.none) : ℚ :=
nth_root_aux' A n prec dir guess

/-meta def nth_root_approx (A : ℚ) (n : ℤ) (prec : ℚ) (dir : approx_dir := approx_dir.none) : ℚ :=
nth_root_aux A n prec (A / n) dir-/

meta def nth_root_approx_bin_aux (A : ℚ) (n : ℤ) (prec : ℚ) : ℕ → ℚ → ℚ
| steps guess :=
if steps = 0 then guess
else let v := rat.pow guess n in
if v < A then nth_root_approx_bin_aux (steps/2) (guess + steps*prec)
else if v > A then nth_root_approx_bin_aux (steps/2) (guess - steps*prec)
else guess

meta def nth_root_approx_bin (A : ℚ) (n : ℤ) (prec guess : ℚ) (dir : approx_dir := approx_dir.none) : ℚ :=
let v := nth_root_approx_bin_aux A n prec (ceil (A/4)).nat_abs guess in
correct_offset A v prec n dir



end rat

namespace int
/-def pow (base : ℤ) : ℤ → ℤ
| (of_nat n) := pow_nat base n
| -[1+n] := 

meta def nth_root_aux (A : ℤ) (n : ℤ) (prec : ℚ) : ℤ → ℤ
| guess := 
let delta_x := ((A / pow_int guess (n - 1)) - guess) / n,
    x := guess + delta_x in
if abs delta_x < prec then x else nth_root_aux x

meta def nth_root_approx (A : ℚ) (n : ℤ) (prec : ℚ) : ℚ :=
nth_root_aux A n prec (A / n)-/

-- inl means success, inr means failed with
meta def nth_root_aux (A : ℤ) (n : ℕ) : ℤ → ℤ → ℤ⊕ℤ
| step guess := 
if step = 0 ∨ step = 1 then
 if guess^n = A then sum.inl guess else if (guess+1)^n=A then sum.inl $ guess+1 else if (guess-1)^n=A then sum.inl $ guess-1 else sum.inr guess
else
 if guess^n = A then sum.inl guess
 else if guess^n < A then nth_root_aux ((step+1)/2) (guess+step)
 else nth_root_aux ((step+1)/2) (guess-step)
 
meta def nth_root (A : ℤ) (n : ℕ) : ℤ⊕ℤ :=
nth_root_aux A n ((A+1)/4)  ((A+1)/4)

meta def nth_root_o (A : ℤ) (n : ℕ) : option ℤ :=
match nth_root A n  with
| sum.inl v := some v
| sum.inr _ := none
end

end int

/--- faster to skip first rat approx in non-1 denom case?
meta def nth_root_approx' (dir : approx_dir) : Π (A : ℚ) (n : ℕ) (prec : ℚ), ℚ | A n prec :=
if A.denom = 1 then
 match int.nth_root A.num n with
 | sum.inl v := v
 | sum.inr v := rat.nth_root_aux A n prec (if v = 0 then prec else v) dir
 end
else
  let num_apr := int.nth_root A.num n,
      den_apr := int.nth_root A.denom n in
  match num_apr, den_apr with
  | sum.inl vn, sum.inl vd := (vn : ℚ) / vd
  | sum.inl vn, sum.inr vd := rat.nth_root_aux A n prec (vn / vd) dir --(vn / rat.nth_root_aux A.denom n prec vd) dir
  | sum.inr vn, sum.inl vd := rat.nth_root_aux A n prec (vn / vd) dir --(rat.nth_root_aux A.num n prec vn / vd) dir
  | sum.inr vn, sum.inr vd := rat.nth_root_aux A n prec (vn / vd) dir--(rat.nth_root_aux A.num n prec vn / rat.nth_root_aux A.denom n prec vn) dir
  end
-- rat.nth_root_aux A n prec ((nth_root_approx' A.num n prec) / (nth_root_approx' A.denom n prec)) dir
-/
-- no rounding or direction fixing
meta def nth_root_approx''_a (dir : approx_dir) : Π (A : ℚ) (n : ℕ) (prec : ℚ), ℚ | A n prec :=
if A.denom = 1 then
 match int.nth_root A.num n with
 | sum.inl v := v
 | sum.inr v := (rat.nth_root_aux'' A n prec dir (if v = 0 then prec else v)) --rat.nth_root_aux A n prec (if v = 0 then prec else v) dir
 end
else
  let num_apr := int.nth_root A.num n,
      den_apr := int.nth_root A.denom n in
  match num_apr, den_apr with
  | sum.inl vn, sum.inl vd := (vn : ℚ) / vd
  | sum.inl vn, sum.inr vd := rat.nth_root_aux'' A n prec dir (vn / vd) --(vn / rat.nth_root_aux A.denom n prec vd) dir
  | sum.inr vn, sum.inl vd := rat.nth_root_aux'' A n prec dir (vn / vd) --(rat.nth_root_aux A.num n prec vn / vd) dir
  | sum.inr vn, sum.inr vd := rat.nth_root_aux'' A n prec dir (vn / vd) --(rat.nth_root_aux A.num n prec vn / rat.nth_root_aux A.denom n prec vn) dir
  end

meta def nth_root_approx (dir : approx_dir) (A : ℚ) (n : ℕ) (denom : ℕ) /-(prec : ℚ)-/ : ℚ :=
let av := nth_root_approx''_a dir A n (1/(denom : ℚ)) in
correct_offset A (round_to_denom av denom) (1/(denom : ℚ)) n dir



/-meta def nth_root_approx (A : ℚ) (n : ℕ) (prec : ℚ) (dir : approx_dir := approx_dir.none) : ℚ :=
nth_root_approx' dir A n prec
-/

open tactic
meta def prove_nth_root_approx (A : ℚ) (n : ℕ) (prec : ℕ) (dir : approx_dir) : tactic expr :=
let apprx := nth_root_approx dir A n prec  in
do  apprx_pow ← to_expr ``(rat.pow %%(reflect apprx) %%(reflect n)),
let tgt := dir.to_expr apprx_pow `(A) in 
do (_, e) ← solve_aux tgt (trace_state >> simp_rat_pow >> trace_state >> (try `[norm_num]) >> done),
   return e

--set_option pp.all true

#exit

local attribute [irreducible] rat.pow

example : (0 : ℚ) ≤ 5+1 := 
begin
simp
end

--example : (0 : ℚ) ≤ 500 := by reflexivity

#eval let v := nth_root_approx 10 2 0.5 in v*v

#eval nth_root_approx 2 2 10 approx_dir.under
#eval int.nth_root 2 2
#eval rat.nth_root_aux 2 2 100 0 approx_dir.over
#eval rat.nth_root_aux 2 4 100 0 approx_dir.over

example : (198 : ℚ) / 100 ≤ 2 :=
by norm_num --btrivial

run_cmd do prove_nth_root_approx 2 2 1000 approx_dir.under >>= infer_type >>= trace


/-do trace "hi",
let
    tgt := dir.to_expr `(rat.pow apprx n) A in
failed
-/ 
#exit

set_option profiler true

run_cmd trace $int.nth_root 1934434936 3

run_cmd trace $ nth_root_approx 19344349361234579569400000000000 2 0.0000000000000000000005

run_cmd trace $ nth_root_approx 54354358908309423742342 2 0.0000000000000000000005

run_cmd trace $ nth_root_approx (54354358908309423742342 / 19344349361234579569400000000000) 2 0.0000000000000000000005

run_cmd trace $ nth_root_approx (100/81) 2 0.00005

example : true :=
by do 
trace $ nth_root_approx 1934434936134579569400000000000 2 0.0000000000000000000005,
triv

--run_cmd trace $ int.nth_root 10 2
--run_cmd trace $ rat.nth_root_aux 10 2 0.5 4

#exit

meta def nearest_int (q : ℚ) : ℤ := 
if ↑q.ceil - q < 0.5 then q.ceil else q.floor

meta def find_integer_root (q : ℚ) (n : ℤ) : option ℚ :=
let n_o := nearest_int $ nth_root_approx q n 0.5 in
if rat.pow n_o n = q then some n_o else none



#exit

meta def small_factor_precomp : list ((int × rat) × (rat × expr)) :=
[
((2, 1), (1, `(by prove_rat_pow : rat.pow 1 2 = 1))),
((2, 4), (2, `(by prove_rat_pow  : rat.pow 2 2 = 4))),
((2, 9), (3, `(by prove_rat_pow  : rat.pow 3 2 = 9))),
((2, 16), (4, `(by prove_rat_pow  : rat.pow 4 2 = 16))),
((2, 25), (5, `(by prove_rat_pow  : rat.pow 5 2 = 25))),
((2, 36), (6, `(by prove_rat_pow  : rat.pow 6 2 = 36))),
((2, 49), (7, `(by prove_rat_pow  : rat.pow 7 2 = 49))),
((2, 64), (8, `(by prove_rat_pow  : rat.pow 8 2 = 64))),
((2, 81), (9, `(by prove_rat_pow  : rat.pow 9 2 = 81))),
((2, 100), (10, `(by prove_rat_pow  : rat.pow 10 2 = 100))),
((3, 1), (1, `(by prove_rat_pow  : rat.pow 1 3 = 1))),
((3, 8), (2, `(by prove_rat_pow  : rat.pow 2 3 = 8))),
((3, 27), (3, `(by prove_rat_pow  : rat.pow 3 3 = 27))),
((3, 64), (4, `(by prove_rat_pow  : rat.pow 4 3 = 64))),
((3, 125), (5, `(by prove_rat_pow  : rat.pow 5 3 = 125))),
((3, 216), (6, `(by prove_rat_pow : rat.pow 6 3 = 216))),
((3, 343), (7, `(by prove_rat_pow : rat.pow 7 3 = 343))),
((3, 512), (8, `(by prove_rat_pow : rat.pow 8 3 = 512))),
((3, 729), (9, `(by prove_rat_pow : rat.pow 9 3 = 729))),
((3, 1000), (10, `(by prove_rat_pow : rat.pow 10 3 = 1000))),
((4, 1), (1, `(by prove_rat_pow : rat.pow 1 4 = 1))),
((4, 16), (2, `(by prove_rat_pow : rat.pow 2 4 = 16))),
((4, 81), (3, `(by prove_rat_pow : rat.pow 3 4 = 81))),
((4, 256), (4, `(by prove_rat_pow : rat.pow 4 4 = 256))),
((4, 625), (5, `(by prove_rat_pow : rat.pow 5 4 = 625))),
((4, 1296), (6, `(by prove_rat_pow : rat.pow 6 4 = 1296))),
((4, 2401), (7, `(by prove_rat_pow : rat.pow 7 4 = 2401))),
((4, 4096), (8, `(by prove_rat_pow : rat.pow 8 4 = 4096))),
((4, 6561), (9, `(by prove_rat_pow : rat.pow 9 4 = 6561))),
((4, 10000), (10, `(by prove_rat_pow : rat.pow 10 4 = 10000)))
]

meta def small_factor_map : rb_map (ℤ × ℚ) (ℚ × expr) :=
rb_map.of_list small_factor_precomp

