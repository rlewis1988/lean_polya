import .datatypes
namespace polya

section arith_thms

theorem diseq_sym {lhs rhs c : ℚ} (hc : c ≠ 0) (h : lhs ≠ c*rhs) : rhs ≠ (1/c) * lhs := 
sorry

theorem eq_sym {lhs rhs c : ℚ} (hc : c ≠ 0) (h : lhs = c*rhs) : rhs = (1/c) * lhs :=
sorry

section ineq_sym
variables {lhs rhs c : ℚ}
theorem ineq_sym_le_pos (hc : c > 0) (h : lhs ≤ c*rhs) : rhs ≥ (1/c) * lhs := 
sorry

theorem ineq_sym_lt_pos (hc : c > 0) (h : lhs < c*rhs) : rhs > (1/c) * lhs := 
sorry

theorem ineq_sym_ge_pos (hc : c > 0) (h : lhs ≥ c*rhs) : rhs ≤ (1/c) * lhs := 
sorry

theorem ineq_sym_gt_pos (hc : c > 0) (h : lhs > c*rhs) : rhs < (1/c) * lhs := 
sorry

theorem ineq_sym_le_neg (hc : c < 0) (h : lhs ≤ c*rhs) : rhs ≤ (1/c) * lhs := 
sorry

theorem ineq_sym_lt_neg (hc : c < 0) (h : lhs < c*rhs) : rhs < (1/c) * lhs := 
sorry

theorem ineq_sym_ge_neg (hc : c < 0) (h : lhs ≥ c*rhs) : rhs ≥ (1/c) * lhs := 
sorry

theorem ineq_sym_gt_neg (hc : c < 0) (h : lhs > c*rhs) : rhs > (1/c) * lhs := 
sorry

meta def name_of_comp_pos : comp → name
| comp.le := ``ineq_sym_le_pos
| comp.lt := ``ineq_sym_lt_pos
| comp.ge := ``ineq_sym_ge_pos
| comp.gt := ``ineq_sym_gt_pos

meta def name_of_comp_neg : comp → name
| comp.le := ``ineq_sym_le_neg
| comp.lt := ``ineq_sym_lt_neg
| comp.ge := ``ineq_sym_ge_neg
| comp.gt := ``ineq_sym_gt_neg

meta def name_of_c_and_comp (c : ℚ) (cmp : comp) : name :=
if c ≥ 0 then name_of_comp_pos cmp else name_of_comp_neg cmp

end ineq_sym

theorem ineq_diseq_le {lhs rhs c : ℚ} (hc : lhs ≠ c*rhs) (h : lhs ≤ c*rhs) : lhs < c*rhs :=
or.elim (lt_or_eq_of_le h) (id) (λ hp, absurd hp hc)

theorem ineq_diseq_ge {lhs rhs c : ℚ} (hc : lhs ≠ c*rhs) (h : lhs ≥ c*rhs) : lhs > c*rhs :=
or.elim (lt_or_eq_of_le h) (id) (λ hp, absurd (eq.symm hp) hc)

theorem ineq_diseq_sign_lhs_le {lhs rhs : ℚ} (hc : lhs ≠ 0) (h : lhs ≤ 0*rhs) : lhs < 0*rhs :=
sorry

theorem ineq_diseq_sign_lhs_ge {lhs rhs : ℚ} (hc : lhs ≠ 0) (h : lhs ≥ 0*rhs) : lhs > 0*rhs :=
sorry

theorem ineq_diseq_sign_rhs_le {rhs : ℚ} (hc : rhs ≠ 0) (h : rhs ≤ 0) : rhs < 0 :=
sorry

theorem ineq_diseq_sign_rhs_ge {rhs : ℚ} (hc : rhs > 0) (h : rhs ≥ 0) : rhs < 0 :=
sorry

theorem op_ineq {lhs rhs c : ℚ} (h1 : lhs ≤ c*rhs) (h2 : lhs ≥ c*rhs) : lhs = rhs :=
sorry

section
variables {lhs : ℚ} (rhs : ℚ)
theorem zero_mul_le (h : lhs ≤ 0) : lhs ≤ 0*rhs := by rw zero_mul; assumption
theorem zero_mul_lt (h : lhs < 0) : lhs < 0*rhs := by rw zero_mul; assumption
theorem zero_mul_ge (h : lhs ≥ 0) : lhs ≥ 0*rhs := by rw zero_mul; assumption
theorem zero_mul_gt (h : lhs > 0) : lhs > 0*rhs := by rw zero_mul; assumption

meta def zero_mul_name_of_comp : comp → name
| comp.le := ``zero_mul_le
| comp.lt := ``zero_mul_lt
| comp.ge := ``zero_mul_ge
| comp.gt := ``zero_mul_gt

variable {rhs}
theorem zero_mul_le' (h : lhs ≤ 0*rhs) : lhs ≤ 0 := by rw -(zero_mul rhs); assumption
theorem zero_mul_lt' (h : lhs < 0*rhs) : lhs < 0 := by rw -(zero_mul rhs); assumption
theorem zero_mul_ge' (h : lhs ≥ 0*rhs) : lhs ≥ 0 := by rw -(zero_mul rhs); assumption
theorem zero_mul_gt' (h : lhs > 0*rhs) : lhs > 0 := by rw -(zero_mul rhs); assumption


meta def zero_mul'_name_of_comp : comp → name
| comp.le := ``zero_mul_le'
| comp.lt := ``zero_mul_lt'
| comp.ge := ``zero_mul_ge'
| comp.gt := ``zero_mul_gt'

end

theorem eq_zero_of_eq_mul_zero {lhs rhs : ℚ} (h : lhs = 0*rhs) : lhs = 0 :=
by rw -(zero_mul rhs); assumption

theorem ne_zero_of_ne_mul_zero {lhs rhs : ℚ} (h : lhs ≠ 0*rhs) : lhs ≠ 0 :=
by rw -(zero_mul rhs); assumption

theorem eq_zero_of_two_eqs_rhs {lhs rhs c1 c2 : ℚ} (h : lhs = c1*rhs) (h2 : lhs = c2*rhs) (hc : c1 ≠ c2) : rhs = 0 :=
begin
 rw h at h2,
 note h3 := sub_eq_zero_of_eq h2,
 rw -sub_mul at h3,
 cases eq_zero_or_eq_zero_of_mul_eq_zero h3,
 apply absurd (eq_of_sub_eq_zero a) hc,
 assumption
end

theorem eq_zero_of_two_eqs_lhs {lhs rhs c1 c2 : ℚ} (h : lhs = c1*rhs) (h2 : lhs = c2*rhs) (hc : c1 ≠ c2) : lhs = 0 :=
have hr : rhs = 0, from eq_zero_of_two_eqs_rhs h h2 hc,
begin rw hr at h, rw mul_zero at h, assumption end

section
variables {lhs rhs c : ℚ} (h : lhs = 0)
include h

/-
PUT THEOREMS FOR ineq_of_ineq_and_eq_zero_rhs here
-/

end

section
variables {lhs rhs c d : ℚ} (h : lhs = d*rhs)
include h

-- there are 16 possibilities here!
theorem sub_le_zero_of_le {a b : ℚ} (h : a ≤ b) : a - b ≤ 0 := sorry
theorem sub_lt_zero_of_lt {a b : ℚ} (h : a < b) : a - b < 0 := sorry
theorem sub_ge_zero_of_ge {a b : ℚ} (h : a ≥ b) : a - b ≥ 0 := sorry
theorem sub_gt_zero_of_gt {a b : ℚ} (h : a > b) : a - b > 0 := sorry

theorem le_gt_rhs (h1 : lhs ≤ c*rhs) (h2 : d - c > 0) : rhs ≤ 0 :=
have d*rhs ≤ c*rhs, by rw -h; assumption,
have d*rhs - c*rhs ≤ 0, from sub_le_zero_of_le this,
have (d - c)*rhs ≤ 0, by rw sub_mul; assumption,
show rhs ≤ 0, from nonpos_of_mul_nonpos_left this h2

theorem lt_gt_rhs (h1 : lhs < c*rhs) (h2 : d - c > 0) : rhs < 0 :=
have d*rhs < c*rhs, by rw -h; assumption,
have d*rhs - c*rhs < 0, from sub_lt_zero_of_lt this,
have (d - c)*rhs < 0, by rw sub_mul; assumption,
show rhs < 0, from neg_of_mul_neg_left this (le_of_lt h2)

theorem ge_gt_rhs (h1 : lhs ≥ c*rhs) (h2 : d - c > 0) : rhs ≥ 0 :=
have d*rhs ≥ c*rhs, by rw -h; assumption,
have d*rhs - c*rhs ≥ 0, from sub_ge_zero_of_ge this,
have (d - c)*rhs ≥ 0, by rw sub_mul; assumption,
show rhs ≥ 0, from nonneg_of_mul_nonneg_left this h2

theorem gt_gt_rhs (h1 : lhs > c*rhs) (h2 : d - c > 0) : rhs > 0 :=
have d*rhs > c*rhs, by rw -h; assumption,
have d*rhs - c*rhs > 0, from sub_gt_zero_of_gt this,
have (d - c)*rhs > 0, by rw sub_mul; assumption,
show rhs > 0, from pos_of_mul_pos_left this (le_of_lt h2)

end

theorem gt_self_contr {e : ℚ} (h : e > 1*e) : false :=
begin apply lt_irrefl, rw one_mul at h, assumption end

theorem lt_self_contr {e : ℚ} (h : e < 1*e) : false :=
begin apply lt_irrefl, rw one_mul at h, assumption end

theorem le_gt_contr {e : ℚ} (h1 : e ≤ 0) (h2 : e > 0) : false :=
not_le_of_gt h2 h1

theorem ge_lt_contr {e : ℚ} (h1 : e ≥ 0) (h2 : e < 0) : false :=
not_le_of_gt h2 h1

end arith_thms

open expr tactic diseq_proof

meta def mk_ne_zero_pf (q : ℚ) : tactic expr :=
do qe ← to_expr `(%%(quote q) : ℚ),
   to_expr `(sorry : (%%qe : ℚ) ≠ 0)
   
-- proves that q > 0, q < 0, or q = 0
meta def mk_sign_pf (q : ℚ) : tactic expr :=
do qe ← to_expr `(%%(quote q) : ℚ),
   if q > 0 then to_expr `(sorry : (%%qe : ℚ) > 0)
   else if q < 0 then to_expr `(sorry : (%%qe : ℚ) < 0)
   else to_expr `(sorry : (%%qe : ℚ) = 0)

meta def mk_ne_pf (q1 q2 : ℚ) : tactic expr :=
do q1e ← to_expr `(%%(quote q1) : ℚ),
   q2e ← to_expr `(%%(quote q2) : ℚ),
   to_expr `(sorry : %%q1e ≠ %%q2e)

namespace diseq_proof
private meta def reconstruct_hyp (lhs rhs : expr) (c : ℚ) (pf : expr) : tactic expr :=
do mvc ← mk_mvar,
   pft ← infer_type pf,
   to_expr `(%%lhs ≠ %%mvc * %%rhs) >>= unify pft,
   c' ← eval_expr rat mvc,
   if c = c' then return pf else fail "diseq_proof.reconstruct_hyp failed"

private meta def reconstruct_sym (rc : Π {lhs rhs : expr} {c : ℚ}, diseq_proof lhs rhs c → tactic expr)
        {lhs rhs c} (dp : diseq_proof lhs rhs c) : tactic expr :=
do symp ← rc dp,
   cnep ← mk_ne_zero_pf c,
   mk_mapp ``diseq_sym [none, none, none, cnep, symp] -- why doesn't mk_app work?

meta def reconstruct : Π {lhs rhs : expr} {c : ℚ}, diseq_proof lhs rhs c → tactic expr
| .(_) .(_) .(_) (hyp (lhs) (rhs) (c) e) := reconstruct_hyp lhs rhs c e
| .(_) .(_) .(_) (@sym lhs rhs c dp) := reconstruct_sym @reconstruct dp

end diseq_proof

namespace eq_proof


private meta def reconstruct_hyp (lhs rhs : expr) (c : ℚ) (pf : expr) : tactic expr :=
do mvc ← mk_mvar,
   pft ← infer_type pf,
   to_expr `(%%lhs = %%mvc * %%rhs) >>= unify pft,
   c' ← eval_expr rat mvc,
   if c = c' then return pf else fail "eq_proof.reconstruct_hyp failed"

private meta def reconstruct_sym (rc : Π {lhs rhs : expr} {c : ℚ}, eq_proof lhs rhs c → tactic expr)
        {lhs rhs c} (dp : eq_proof lhs rhs c) : tactic expr :=
do symp ← rc dp,
   cnep ← mk_ne_zero_pf c, -- 5/1 ≠ 0
   infer_type symp >>= trace,
   infer_type cnep >>= trace,
   mk_mapp ``eq_sym [none, none, none, cnep, symp] -- why doesn't mk_app work?

variable iepr_fn : Π {lhs rhs i}, ineq_proof lhs rhs i → tactic expr

private meta def reconstruct_of_opp_ineqs_aux {lhs rhs i} (c : ℚ) (iep : ineq_proof lhs rhs i) 
        (iepr : ineq_proof lhs rhs i.reverse) : tactic expr :=
do guard (bnot i.strict),
   pr1 ← iepr_fn iep, pr2 ← iepr_fn iepr,
   if i.to_comp.is_less then
     mk_mapp ``op_ineq [none, none, none, some pr1, some pr2]
   else
     mk_mapp ``op_ineq [none, none, none, some pr2, some pr1]

meta def reconstruct_aux : Π {lhs rhs : expr} {c : ℚ}, eq_proof lhs rhs c → tactic expr
| .(_) .(_) .(_) (hyp (lhs) (rhs) (c) e) := reconstruct_hyp lhs rhs c e
| .(_) .(_) .(_) (@sym lhs rhs c dp) := reconstruct_sym @reconstruct_aux dp
| .(_) .(_) .(_) (@of_opp_ineqs lhs rhs i c iep iepr) := reconstruct_of_opp_ineqs_aux @iepr_fn c iep iepr

end eq_proof

namespace ineq_proof

meta def guard_is_ineq (lhs rhs : expr) (iq : ineq) (pf : expr) : tactic expr :=
do mvc ← mk_mvar, pft ← infer_type pf,
match iq.to_comp with
| comp.lt := to_expr `(%%lhs < %%mvc * %%rhs) >>= unify pft >> return mvc
| comp.le := to_expr `(%%lhs ≤ %%mvc * %%rhs) >>= unify pft >> return mvc
| comp.gt := to_expr `(%%lhs > %%mvc * %%rhs) >>= unify pft >> return mvc
| comp.ge := to_expr `(%%lhs ≥ %%mvc * %%rhs) >>= unify pft >> return mvc
end

private meta def reconstruct_hyp (lhs rhs : expr) (iq : ineq) (pf : expr) : tactic expr :=
match iq.to_slope with
| slope.horiz  := 
  do tp ← infer_type pf,
     to_expr `( %%(iq.to_comp.to_pexpr) %%rhs 0) >>= unify tp,
     return pf
| slope.some c :=
  do m ← guard_is_ineq lhs rhs iq pf,
     m' ← eval_expr rat m,
     if m' = c then return pf else fail "ineq_proof.reconstruct_hyp failed"
end

section
variable (rc : Π {lhs rhs : expr} {iq : ineq}, ineq_proof lhs rhs iq → tactic expr)
include rc

private meta def reconstruct_sym 
        {lhs rhs iq} (ip : ineq_proof lhs rhs iq) : tactic expr :=
match iq.to_slope with
| slope.horiz  := failed
| slope.some m := 
  do symp ← rc ip, sgnp ← mk_sign_pf m,
     mk_mapp (name_of_c_and_comp m iq.to_comp) [none, none, none, some sgnp, some symp]
end

-- x ≥ 2y and x ≠ 2y implies x > 2y
private meta def reconstruct_ineq_diseq {lhs rhs iq c} (ip : ineq_proof lhs rhs iq) (dp : diseq_proof lhs rhs c) : tactic expr :=
match iq.to_slope with
| slope.horiz := fail "reconstruct_ineq_diseq needs non-horiz slope"
| slope.some m := 
 if bnot (m=c) then
   fail "reconstruct_ineq_diseq found non-matching slopes"
 else if iq.strict then rc ip
 else do ipp ← rc ip, dpp ← dp.reconstruct,
 if iq.to_comp.is_less then
  mk_mapp ``ineq_diseq_le [none, none, none, some dpp, some ipp]
 else 
  mk_mapp ``ineq_diseq_ge [none, none, none, some dpp, some ipp]
end

variable (rcs : Π {e gc}, sign_proof e gc → tactic expr)
include rcs

-- x ≤ 0y and x ≠ 0 implies x < 0y
private meta def reconstruct_ineq_sign_lhs {lhs rhs iq c} (ip : ineq_proof lhs rhs iq) (sp : sign_proof lhs c) : tactic expr :=
if iq.strict || bnot (c = gen_comp.ne) then fail "reconstruct_ineq_sign_lhs assumes a weak ineq and a diseq-0" else
match iq.to_slope with
| slope.horiz := fail "reconstruct_ineq_sign_lhs assumes a 0 slope"
| slope.some m :=
  if m = 0 then do
    ipp ← rc ip, spp ← rcs sp,
    mk_app (if iq.to_comp.is_less then ``ineq_diseq_sign_lhs_le else ``ineq_diseq_sign_lhs_ge) [spp, ipp]    
  else fail "reconstruct_ineq_sign_lhs assumes a 0 slope"
end

private meta def reconstruct_ineq_sign_rhs {lhs rhs iq c} (ip : ineq_proof lhs rhs iq) (sp : sign_proof rhs c) : tactic expr :=
if iq.strict || bnot (c = gen_comp.ne) then fail "reconstruct_ineq_sign_rhs assumes a weak ineq and a diseq-0" else
match iq.to_slope with
| slope.horiz := do ipp ← rc ip, spp ← rcs sp,
    mk_app (if iq.to_comp.is_less then ``ineq_diseq_sign_rhs_le else ``ineq_diseq_sign_rhs_ge) [spp, ipp]
| _ := fail "reconstruct_ineq_sign_rhs assumes a horizontal slope"
end


omit rc

-- x ≥ 0 implies x ≥ 0*y
private meta def reconstruct_zero_comp_of_sign {lhs c} (rhs : expr) (iq : ineq) (sp : sign_proof lhs c) : tactic expr :=
if bnot ((iq.to_comp.to_gen_comp = c) && (iq.is_zero_slope)) then fail "reconstruct_zero_comp_of_sign only produces comps with zero"
else do spp ← rcs sp, mk_app (zero_mul_name_of_comp iq.to_comp) [rhs, spp]

end

meta def reconstruct_aux (rcs : Π {e gc}, sign_proof e gc → tactic expr) :  Π {lhs rhs : expr} {iq : ineq}, ineq_proof lhs rhs iq → tactic expr
| .(_) .(_) .(_) (hyp (lhs) (rhs) (iq) e) := reconstruct_hyp lhs rhs iq e
| .(_) .(_) .(_) (@sym lhs rhs c ip) := reconstruct_sym @reconstruct_aux ip
| .(_) .(_) .(_) (@of_ineq_proof_and_diseq lhs rhs iq c ip dp) := reconstruct_ineq_diseq @reconstruct_aux ip dp
| .(_) .(_) .(_) (@of_ineq_proof_and_sign_lhs lhs rhs iq c ip sp) := reconstruct_ineq_sign_lhs @reconstruct_aux @rcs ip sp
| .(_) .(_) .(_) (@of_ineq_proof_and_sign_rhs lhs rhs iq c ip sp) := reconstruct_ineq_sign_rhs @reconstruct_aux @rcs ip sp
| .(_) .(_) .(_) (@zero_comp_of_sign_proof lhs c rhs iq sp) := reconstruct_zero_comp_of_sign @rcs rhs iq sp

end ineq_proof

namespace sign_proof

private meta def reconstruct_hyp (e : expr) (gc : gen_comp) (pf : expr) : tactic expr :=
let pex := match gc with
| gen_comp.ge := `(%%e ≥ 0)
| gen_comp.gt := `(%%e > 0)
| gen_comp.le := `(%%e ≤ 0)
| gen_comp.lt := `(%%e < 0)
| gen_comp.eq := `(%%e = 0)
| gen_comp.ne := `(%%e ≠ 0)
end in do tp ← infer_type pf, to_expr pex >>= unify tp >> return pf

section
parameter rc : Π {e c}, sign_proof e c → tactic expr
private meta def rci := @ineq_proof.reconstruct_aux @rc
private meta def rce := @eq_proof.reconstruct_aux @rci

-- x ≤ 0*y to x ≤ 0
private meta def reconstruct_ineq_lhs (c : gen_comp) {lhs rhs iqp} (ip : ineq_proof lhs rhs iqp) : tactic expr :=
if bnot ((iqp.to_comp.to_gen_comp = c) && (iqp.is_zero_slope)) then fail "reconstruct_ineq_lhs must take a comparison with 0"
else do ipp ← rci ip, mk_app (zero_mul'_name_of_comp iqp.to_comp) [ipp]

private meta def reconstruct_ineq_rhs (c : gen_comp) {lhs rhs iqp} (ip : ineq_proof lhs rhs iqp) : tactic expr :=
if bnot ((iqp.to_comp.to_gen_comp = c) && (iqp.is_horiz)) then fail "reconstruct_ineq_rhs must take a horiz comp"
else rci ip

private meta def reconstruct_eq_of_two_eqs_lhs {lhs rhs eqp1 eqp2} (ep1 : eq_proof lhs rhs eqp1) (ep2 : eq_proof lhs rhs eqp2) : tactic expr :=
if h : eqp1 = eqp2 then fail "reconstruct_eq_of_two_eqs lhs cannot infer anything from the same equality twice"
else do epp1 ← rce ep1, epp2 ← rce ep2, nep ← mk_ne_pf eqp1 eqp2,
        mk_app ``eq_zero_of_two_eqs_lhs [epp1, epp2, nep]

private meta def reconstruct_eq_of_two_eqs_rhs {lhs rhs eqp1 eqp2} (ep1 : eq_proof lhs rhs eqp1) (ep2 : eq_proof lhs rhs eqp2) : tactic expr :=
if h : eqp1 = eqp2 then fail "reconstruct_eq_of_two_eqs lhs cannot infer anything from the same equality twice"
else do epp1 ← rce ep1, epp2 ← rce ep2, nep ← mk_ne_pf eqp1 eqp2,
        mk_app ``eq_zero_of_two_eqs_rhs [epp1, epp2, nep]

private meta def reconstruct_diseq_of_diseq_zero {lhs rhs} (dp : diseq_proof lhs rhs 0) : tactic expr :=
do dpp ← dp.reconstruct,
   mk_app ``ne_zero_of_ne_mul_zero [dpp]

private meta def reconstruct_eq_of_eq_zero {lhs rhs} (ep : eq_proof lhs rhs 0) : tactic expr :=
do epp ← rce ep,
   mk_app ``eq_zero_of_eq_mul_zero [epp]

-- these are the hard cases. Is this the right place to handle them?
private meta def reconstruct_ineq_of_eq_and_ineq_lhs {lhs rhs iq c} (c' : gen_comp) (ep : eq_proof lhs rhs c) (ip : ineq_proof lhs rhs iq) : tactic expr :=
fail "reconstruct_ineq_of_eq_and_ineq not implemented"

private meta def reconstruct_ineq_of_eq_and_ineq_rhs {lhs rhs iq c} (c' : gen_comp) (ep : eq_proof lhs rhs c) (ip : ineq_proof lhs rhs iq) : tactic expr :=
fail "reconstruct_ineq_of_eq_and_ineq not implemented"

private meta def reconstruct_ineq_of_ineq_and_eq_zero_rhs {lhs rhs iq} (c : gen_comp) (ip : ineq_proof lhs rhs iq) (sp : sign_proof lhs gen_comp.eq) : tactic expr :=
fail "reconstruct_ineq_of_ineq_and_eq_zero not implemented"
   

end

meta def reconstruct : Π {e c}, sign_proof e c → tactic expr
| .(_) .(_) (hyp e c pf) := reconstruct_hyp e c pf
| .(_) .(_) (@ineq_lhs c _ _ _ ip) := reconstruct_ineq_lhs @reconstruct c ip
| .(_) .(_) (@ineq_rhs c _ _ _ ip) := reconstruct_ineq_rhs @reconstruct c ip
| .(_) .(_) (@eq_of_two_eqs_lhs _ _ _ _ ep1 ep2) := reconstruct_eq_of_two_eqs_lhs @reconstruct ep1 ep2
| .(_) .(_) (@eq_of_two_eqs_rhs _ _ _ _ ep1 ep2) := reconstruct_eq_of_two_eqs_rhs @reconstruct ep1 ep2
| .(_) .(_) (@diseq_of_diseq_zero _ _ dp) := reconstruct_diseq_of_diseq_zero dp
| .(_) .(_) (@eq_of_eq_zero _ _ ep) := reconstruct_eq_of_eq_zero @reconstruct ep
| .(_) .(_) (@ineq_of_eq_and_ineq_lhs _ _ _ _ c' ep ip) := reconstruct_ineq_of_eq_and_ineq_lhs c' ep ip
| .(_) .(_) (@ineq_of_eq_and_ineq_rhs _ _ _ _ c' ep ip) := reconstruct_ineq_of_eq_and_ineq_rhs c' ep ip
| .(_) .(_) (@ineq_of_ineq_and_eq_zero_rhs _ _ _ c ip sp) := reconstruct_ineq_of_ineq_and_eq_zero_rhs c ip sp

end sign_proof

meta def ineq_proof.reconstruct := @ineq_proof.reconstruct_aux @sign_proof.reconstruct

meta def eq_proof.reconstruct := @eq_proof.reconstruct_aux @ineq_proof.reconstruct

namespace contrad

private meta def reconstruct_eq_diseq {lhs rhs} (ed : eq_data lhs rhs) (dd : diseq_data lhs rhs) : tactic expr :=
if bnot (ed.c = dd.c) then fail "reconstruct_eq_diseq failed: given different coefficients"
else do ddp ← dd.prf.reconstruct, edp ← ed.prf.reconstruct, return $ ddp.app edp

-- TODO: this is the hard part. Should this be refactored into smaller pieces?
private meta def reconstruct_ineqs {lhs rhs} (ii : ineq_info lhs rhs) (id : ineq_data lhs rhs) : tactic expr :=
failed

private meta def reconstruct_sign_ne_eq {e} (nepr : sign_proof e gen_comp.ne) (eqpr : sign_proof e gen_comp.eq) : tactic expr :=
do neprp ← nepr.reconstruct, eqprp ← eqpr.reconstruct,
   return $ neprp.app eqprp

private meta def reconstruct_sign_le_gt {e} (lepr : sign_proof e gen_comp.le) (gtpr : sign_proof e gen_comp.gt) : tactic expr :=
do leprp ← lepr.reconstruct, gtprp ← gtpr.reconstruct,
   mk_app ``le_gt_contr [leprp, gtprp]

private meta def reconstruct_sign_ge_lt {e} (gepr : sign_proof e gen_comp.ge) (ltpr : sign_proof e gen_comp.lt) : tactic expr :=
do geprp ← gepr.reconstruct, ltprp ← ltpr.reconstruct,
   mk_app ``ge_lt_contr [geprp, ltprp]


private meta def reconstruct_sign {e} : sign_data e → sign_data e → tactic expr
| ⟨gen_comp.ne, prf1⟩ ⟨gen_comp.eq, prf2⟩ := reconstruct_sign_ne_eq prf1 prf2
| ⟨gen_comp.eq, prf1⟩ ⟨gen_comp.ne, prf2⟩ := reconstruct_sign_ne_eq prf2 prf1
| ⟨gen_comp.le, prf1⟩ ⟨gen_comp.gt, prf2⟩ := reconstruct_sign_le_gt prf1 prf2
| ⟨gen_comp.gt, prf1⟩ ⟨gen_comp.le, prf2⟩ := reconstruct_sign_le_gt prf2 prf1
| ⟨gen_comp.lt, prf1⟩ ⟨gen_comp.ge, prf2⟩ := reconstruct_sign_ge_lt prf2 prf1
| ⟨gen_comp.ge, prf1⟩ ⟨gen_comp.lt, prf2⟩ := reconstruct_sign_ge_lt prf1 prf2
| _ _ := fail "reconstruct_sign failed: given non-opposite comps"

private meta def reconstruct_strict_ineq_self {e} (id : ineq_data e e) : tactic expr := 
match id.inq.to_comp, id.inq.to_slope with
| comp.gt, slope.some m := 
  if bnot (m = 1) then fail "reconstruct_strict_ineq_self failed: given non-one slope"
  else do idp ← id.prf.reconstruct,
       mk_app ``gt_self_contr [idp]
| comp.lt, slope.some m := 
  if bnot (m = 1) then fail "reconstruct_strict_ineq_self failed: given non-one slope"
  else do idp ← id.prf.reconstruct,
       mk_app ``lt_self_contr [idp]
| _, _ := fail "reconstruct_strict_ineq_self failed: given non-strict comp or non-one slope"
end

meta def reconstruct : contrad → tactic expr
| none := fail "cannot reconstruct contr: no contradiction is known"
| (@eq_diseq lhs rhs ed dd) := reconstruct_eq_diseq ed dd
| (@ineqs lhs rhs ii id) := reconstruct_ineqs ii id
| (@sign e sd1 sd2) := reconstruct_sign sd1 sd2
| (@strict_ineq_self e id) := reconstruct_strict_ineq_self id

end contrad

end polya

#exit

section tests
open polya tactic expr
parameters x y : ℚ
meta def x' := ```(x)
meta def y' := ```(y)

section diseq
open polya.diseq_proof 
parameter hxy : x ≠ 5*y

meta def dp : diseq_proof _ _ _ := hyp x' y' 5 ```(hxy)
meta def dp2 := sym dp

run_cmd reconstruct dp2 >>= infer_type >>= trace
end diseq

section eq
open polya.eq_proof

parameter hxy : x = 5*y

meta def ep : eq_proof _ _ _ := hyp x' y' 5 ```(hxy)
meta def ep2 := sym ep

run_cmd reconstruct ep2 >>= infer_type >>= trace

end eq

section ineq
open polya.ineq_proof
parameter hxy : x ≤ 5*y
parameter hy : y ≥ 0

meta def ip : ineq_proof _ _ _ := hyp x' y' (ineq.of_comp_and_slope comp.le (slope.some 5)) ```(hxy)
meta def ip2 : ineq_proof _ _ _ := hyp x' y' (ineq.of_comp_and_slope comp.ge (slope.horiz)) ```(hy)
meta def ip3 := sym ip

run_cmd reconstruct ip >>= infer_type >>= trace
run_cmd reconstruct ip2 >>= infer_type >>= trace
run_cmd reconstruct (sym ip3) >>= infer_type >>= trace

meta def ip4 : ineq_proof _ _ _ := of_ineq_proof_and_diseq ip dp

run_cmd reconstruct ip4 >>= infer_type >>= trace

parameter hxy2 : x ≤ 0*y
meta def ip5 : ineq_proof _ _ _ := hyp x' y' (ineq.of_comp_and_slope comp.le (slope.some 0)) ```(hxy2)
end ineq

section sign
open polya.sign_proof

parameter h : x ≠ 0
parameter h2 : x > 0
meta def sp : sign_proof _ _ := hyp x' gen_comp.ne ```(h)
meta def sp2 : sign_proof _ _ := hyp x' gen_comp.gt ```(h2)
meta def ip6 : ineq_proof _ _ _ := ineq_proof.of_ineq_proof_and_sign_lhs ip5 sp
meta def ip7 : ineq_proof _ _ _ := ineq_proof.zero_comp_of_sign_proof y' (ineq.of_comp_and_slope comp.gt (slope.some 0)) sp2

run_cmd reconstruct sp >>= infer_type >>= trace

run_cmd ip6.reconstruct >>= infer_type >>= trace
run_cmd ip7.reconstruct >>= infer_type >>= trace

end sign

end tests
