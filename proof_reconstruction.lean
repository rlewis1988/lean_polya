import .datatypes .sum_form .reconstruction_theorems
namespace polya



open expr tactic diseq_proof

theorem fake_ne_zero_pf (q : ℚ) : q ≠ 0 := sorry
theorem fake_gt_zero_pf (q : ℚ) : q > 0 := sorry
theorem fake_lt_zero_pf (q : ℚ) : q < 0 := sorry
theorem fake_eq_zero_pf (q : ℚ) : q = 0 := sorry
theorem fake_ne_pf (q1 q2 : ℚ) : q1 ≠ q2 := sorry

meta def mk_ne_zero_pf (q : ℚ) : tactic expr :=
do qe ← to_expr ``(%%(quote q) : ℚ),
   to_expr ``(fake_ne_zero_pf (%%qe : ℚ))
   
-- proves that q > 0, q < 0, or q = 0
meta def mk_sign_pf (q : ℚ) : tactic expr :=
do qe ← to_expr `(%%(quote q) : ℚ),
   if q > 0 then to_expr `(fake_gt_zero_pf (%%qe : ℚ))
   else if q < 0 then to_expr `(fake_lt_zero_pf (%%qe : ℚ))
   else to_expr ``(fake_eq_zero_pf (%%qe : ℚ))

meta def mk_ne_pf (q1 q2 : ℚ) : tactic expr :=
do q1e ← to_expr ``(%%(quote q1) : ℚ),
   q2e ← to_expr ``(%%(quote q2) : ℚ),
   to_expr `(fake_ne_pf %%q1e %%q2e)

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

private theorem eq_sub_of_add_eq_facs {c1 c2 e1 e2 : ℚ} (hc1 : c1 ≠ 0) (h : c1 * e1 + c2 * e2 = 0) : e1 = -(c2/c1) * e2 :=
sorry


private meta def reconstruct_of_sum_form_proof (sfpr : Π {sf}, Π (sp : sum_form_proof sf), tactic expr) : expr → expr → ℚ → Π {sf},
       Π (sp : sum_form_proof ⟨sf, spec_comp.eq⟩), tactic expr | lhs rhs c sf sp :=
if rhs.lt lhs then 
  reconstruct_of_sum_form_proof rhs lhs (1/c) sp
else do
  guard $ (sf.contains lhs) && (sf.contains rhs),
  let a := sf.get_coeff lhs in let b := sf.get_coeff rhs in do
  guard $ c = -(b/a),
  pf ← sfpr sp,
  nez ← mk_ne_zero_pf a,
  mk_app ``eq_sub_of_add_eq_facs [nez, pf] 
--  fail "eq_proof.reconstruct_of_sum_proof not implemented yet"

meta def reconstruct_aux (sfpr : Π {sf}, Π (sp : sum_form_proof sf), tactic expr) : Π {lhs rhs : expr} {c : ℚ}, eq_proof lhs rhs c → tactic expr
| .(_) .(_) .(_) (hyp (lhs) (rhs) (c) e) := reconstruct_hyp lhs rhs c e
| .(_) .(_) .(_) (@sym lhs rhs c dp) := reconstruct_sym @reconstruct_aux dp
| .(_) .(_) .(_) (@of_opp_ineqs lhs rhs i c iep iepr) := reconstruct_of_opp_ineqs_aux @iepr_fn c iep iepr
| .(_) .(_) .(_) (@of_sum_form_proof lhs rhs c _ sp) := reconstruct_of_sum_form_proof @sfpr lhs rhs c sp
| .(_) .(_) .(_) (adhoc _ _ _ t) := t

end eq_proof

namespace ineq_proof

meta def guard_is_ineq (lhs rhs : expr) (iq : ineq) (pf : expr) : tactic expr :=
do mvc ← mk_mvar, pft ← infer_type pf, trace "in guard_is_ineq", trace iq.to_comp, trace pft, trace (lhs, rhs), trace pf,
match iq.to_comp with
| comp.lt := to_expr `(%%lhs < %%mvc * %%rhs) >>= unify pft >> return mvc
| comp.le := to_expr `(%%lhs ≤ %%mvc * %%rhs) >>= unify pft >> return mvc
| comp.gt := to_expr `(%%lhs > %%mvc * %%rhs) >>= unify pft >> return mvc
| comp.ge := to_expr `(%%lhs ≥ %%mvc * %%rhs) >>= unify pft >> return mvc
end

private meta def reconstruct_hyp (lhs rhs : expr) (iq : ineq) (pf : expr) : tactic expr :=
match iq.to_slope with
| slope.horiz  := 
  do tp ← infer_type pf, trace "unifying tp in reconstruct_hyp1", trace tp,
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
| slope.horiz  := fail "reconstruct_sym failed on horiz slope"
| slope.some m := 
  do symp ← rc ip, sgnp ← mk_sign_pf m,
     --mk_mapp (name_of_c_and_comp m iq.to_comp) [none, none, none, some sgnp, some symp]
     mk_app (if m < 0 then ``sym_op_neg else ``sym_op_pos) [sgnp, symp]
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

/-
private theorem eq_sub_of_add_eq_facs {c1 c2 e1 e2 : ℚ} (hc1 : c1 ≠ 0) (h : c1 * e1 + c2 * e2 = 0) : e1 = -(c2/c1) * e2 :=
sorry


private meta def reconstruct_of_sum_form_proof (sfpr : Π {sf}, Π (sp : sum_form_proof sf), tactic expr) : expr → expr → ℚ → Π {sf},
       Π (sp : sum_form_proof ⟨sf, spec_comp.eq⟩), tactic expr | lhs rhs c sf sp :=
if rhs.lt lhs then 
  reconstruct_of_sum_form_proof rhs lhs (1/c) sp
else do
  guard $ (sf.contains lhs) && (sf.contains rhs),
  let a := sf.get_coeff lhs in let b := sf.get_coeff rhs in do
  guard $ c = -(b/a),
  pf ← sfpr sp,
  nez ← mk_ne_zero_pf a,
  mk_app ``eq_sub_of_add_eq_facs [nez, pf] 
-/

-- TODO

private meta def reconstruct_of_sum_form_proof  (sfpr : Π {sf}, Π (sp : sum_form_proof sf), tactic expr) :
        expr → expr → ineq → Π {sfc}, sum_form_proof sfc → tactic expr | lhs rhs i sfc sp :=
if rhs.lt lhs then
  reconstruct_of_sum_form_proof rhs lhs i.reverse sp
else match i.to_slope with
| slope.some m := do
  guard $ (sfc.sf.contains lhs) && (sfc.sf.contains rhs),
  guard $ sfc.sf.keys.length = 2,
  let a := sfc.sf.get_coeff lhs in let b := sfc.sf.get_coeff rhs in do
  guard $ m = -(b/a),
  guard $ if a < 0 then sfc.c.to_comp = i.to_comp.reverse else sfc.c.to_comp = i.to_comp,
  rhs' ← to_expr `(%%(quote m) * %%rhs),
  tp ← i.to_comp.to_function lhs rhs',
  to_expr `(sorry : %%tp)
--  fail "ineq_proof.reconstruct_of_sum_proof not implemented yet"
| slope.horiz := fail "ineq_proof.reconstruct_of_sum_proof failed, cannot turn a sum into a horiz slope"
end

meta def reconstruct_aux (rcs : Π {e gc}, sign_proof e gc → tactic expr) (sfpr : Π {sf}, Π (sp : sum_form_proof sf), tactic expr) :
     Π {lhs rhs : expr} {iq : ineq}, ineq_proof lhs rhs iq → tactic expr
| .(_) .(_) .(_) (hyp (lhs) (rhs) (iq) e) := reconstruct_hyp lhs rhs iq e
| .(_) .(_) .(_) (@sym lhs rhs c ip) := reconstruct_sym @reconstruct_aux ip
| .(_) .(_) .(_) (@of_ineq_proof_and_diseq lhs rhs iq c ip dp) := reconstruct_ineq_diseq @reconstruct_aux ip dp
| .(_) .(_) .(_) (@of_ineq_proof_and_sign_lhs lhs rhs iq c ip sp) := reconstruct_ineq_sign_lhs @reconstruct_aux @rcs ip sp
| .(_) .(_) .(_) (@of_ineq_proof_and_sign_rhs lhs rhs iq c ip sp) := reconstruct_ineq_sign_rhs @reconstruct_aux @rcs ip sp
| .(_) .(_) .(_) (@zero_comp_of_sign_proof lhs c rhs iq sp) := reconstruct_zero_comp_of_sign @rcs rhs iq sp
| .(_) .(_) .(_) (@of_sum_form_proof lhs rhs i _ sp) := reconstruct_of_sum_form_proof @sfpr lhs rhs i sp
| .(_) .(_) .(_) (adhoc _ _ _ t) := t

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
parameter sfpr : Π {sf}, Π (sp : sum_form_proof sf), tactic expr
private meta def rci := @ineq_proof.reconstruct_aux @rc @sfpr
private meta def rce := @eq_proof.reconstruct_aux @rci @sfpr

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

-- TODO
private meta def reconstruct_of_sum_form_proof (sfpr : Π {sf}, Π (sp : sum_form_proof sf), tactic expr) (e : expr) (c : gen_comp) {sfc}
        (sp : sum_form_proof sfc) : tactic expr :=
fail "sign_proof.reconstruct_of_sum_form_proof failed, not implemented yet"

meta def reconstruct_aux (sfpr : Π {sf}, Π (sp : sum_form_proof sf), tactic expr) : Π {e c}, sign_proof e c → tactic expr
| .(_) .(_) (hyp e c pf) := reconstruct_hyp e c pf
| .(_) .(_) (@ineq_lhs c _ _ _ ip) := reconstruct_ineq_lhs @reconstruct_aux @sfpr c ip
| .(_) .(_) (@ineq_rhs c _ _ _ ip) := reconstruct_ineq_rhs @reconstruct_aux @sfpr c ip
| .(_) .(_) (@eq_of_two_eqs_lhs _ _ _ _ ep1 ep2) := reconstruct_eq_of_two_eqs_lhs @reconstruct_aux @sfpr ep1 ep2
| .(_) .(_) (@eq_of_two_eqs_rhs _ _ _ _ ep1 ep2) := reconstruct_eq_of_two_eqs_rhs @reconstruct_aux @sfpr ep1 ep2
| .(_) .(_) (@diseq_of_diseq_zero _ _ dp) := reconstruct_diseq_of_diseq_zero dp
| .(_) .(_) (@eq_of_eq_zero _ _ ep) := reconstruct_eq_of_eq_zero @reconstruct_aux @sfpr ep
| .(_) .(_) (@ineq_of_eq_and_ineq_lhs _ _ _ _ c' ep ip) := reconstruct_ineq_of_eq_and_ineq_lhs c' ep ip
| .(_) .(_) (@ineq_of_eq_and_ineq_rhs _ _ _ _ c' ep ip) := reconstruct_ineq_of_eq_and_ineq_rhs c' ep ip
| .(_) .(_) (@ineq_of_ineq_and_eq_zero_rhs _ _ _ c ip sp) := reconstruct_ineq_of_ineq_and_eq_zero_rhs c ip sp
| .(_) .(_) (@of_sum_form_proof e c _ sp) := reconstruct_of_sum_form_proof @sfpr e c sp
| .(_) .(_) (adhoc _ _ t) := t

end sign_proof


namespace sum_form_proof
section  
parameter sfrc : Π {sfc}, sum_form_proof sfc → tactic expr
private meta def sprc := @sign_proof.reconstruct_aux @sfrc
private meta def iprc := @ineq_proof.reconstruct_aux @sprc @sfrc
private meta def eprc := @eq_proof.reconstruct_aux @iprc @sfrc

-- assumes lhs < rhs
private meta def reconstruct_of_ineq_proof  : 
        Π {lhs rhs iq}, ineq_proof lhs rhs iq → tactic expr | lhs rhs iq ip :=
if expr.lt rhs lhs then reconstruct_of_ineq_proof ip.sym else 
match iq.to_slope with
| slope.horiz := 
  do ipp ← iprc ip,
     tactic.mk_app (sum_form_name_of_comp_single iq.to_comp) [ipp]
| slope.some m := 
  do ipp ← iprc ip, trace ("ipp", ip, ipp), infer_type ipp >>= trace,
     tactic.mk_app ((if m = 0 then sum_form_name_of_comp_single else sum_form_name_of_comp) iq.to_comp) [ipp]
end

include sfrc
-- TODO
private meta def reconstruct_of_eq_proof  : 
        Π {lhs rhs c}, eq_proof lhs rhs c → tactic expr | lhs rhs c ep :=
fail "sum_form_proof.reconstruct_of_eq_proof not implemented yet"

-- TODO
private meta def reconstruct_of_sign_proof :
        Π {e c}, sign_proof e c → tactic expr | e c sp :=
fail "sum_form_proof.reconstruct_of_sign_proof not implemented yet"
omit sfrc 

meta def expr_coeff_list_to_expr : list (expr × ℚ) → tactic expr
| [] := to_expr `(0 : ℚ)
| [(e, q)] := to_expr `(%%(quote q)*e)
| ((e, q)::t) := do e' ← expr_coeff_list_to_expr t, h ← to_expr `(%%(quote q)*e), to_expr `(%%h + %%e')

meta def sum_form.to_expr (sf : sum_form) : tactic expr := 
expr_coeff_list_to_expr sf.to_list

--  sum_form_proof ⟨lhs.add_factor rhs m, spec_comp.strongest c1 c2⟩ 
-- wait for algebraic normalizer?
-- TODO
private theorem reconstruct_of_add_factor_aux (P : Prop) {Q R : Prop} (h : Q) (h2 : R) : P := sorry

private meta def reconstruct_of_add_factor_same_comp {lhs rhs c1 c2} (m : ℚ) 
        (sfpl : sum_form_proof ⟨lhs, c1⟩) (sfpr : sum_form_proof ⟨rhs, c2⟩) : tactic expr :=
let sum := lhs + rhs.scale m in
do tp ← sum_form.to_expr sum,
   tp' ← (spec_comp.strongest c1 c2).to_comp.to_function tp ```(0 : ℚ),
   pf1 ← sfrc sfpl, pf2 ← sfrc sfpr,
   mk_mapp ``reconstruct_of_add_factor_aux [some tp', none, none, some pf1, some pf2] --to_expr `(sorry : %%tp)    
--fail "reconstruct_of_add_factor_same_comp failed, not implemented yet"

private theorem reconstruct_of_scale_aux (P : Prop) {Q : Prop} (h : Q) : P := sorry

private meta def reconstruct_of_scale (rct : Π {sfc}, sum_form_proof sfc → tactic expr) 
        {sfc} (m : ℚ) (sfp : sum_form_proof sfc) : tactic expr :=
do tp ← sum_form.to_expr (sfc.sf.scale m),
   tp' ← sfc.c.to_comp.to_function tp ```(0 : ℚ),
   pf ← rct sfp,
   mk_app ``reconstruct_of_scale_aux [tp', pf] -- to_expr `(sorry : %%tp')
   
end 

meta def reconstruct : Π {sfc}, sum_form_proof sfc → tactic expr
| .(_) (@of_ineq_proof _ _ _ ip) := reconstruct_of_ineq_proof @reconstruct ip
| .(_) (@of_eq_proof _ _ _ ep) := reconstruct_of_eq_proof @reconstruct ep
| .(_) (@of_sign_proof _ _ sp) := reconstruct_of_sign_proof @reconstruct sp
| .(_) (@of_add_factor_same_comp _ _ _ _ m sfpl sfpr) := 
  reconstruct_of_add_factor_same_comp @reconstruct m sfpl sfpr 
| .(_) (@of_scale _ m sfp) := reconstruct_of_scale @reconstruct m sfp
| .(_) (@fake sd) := fail "cannot reconstruct a fake proof"




/-meta def reconstruct : Π {sfc}, sum_form_proof sfc → tactic expr | sfc sfp :=
if sfc.sf.keys.length = 0 then do
 ex ← sfc.c.to_comp.to_function ```(0 : ℚ) ```(0 : ℚ),
 to_expr `(sorry : %%ex) else
let sfcd : sum_form_comp_data := ⟨_, sfp, mk_rb_set⟩ in
match sfcd.to_ineq_data with
| option.some ⟨lhs, rhs, id⟩ := do ex ← ineq_data.to_expr id, to_expr `(sorry : %%ex)
| none := trace sfc >> fail "fake sum_form_proof.reconstruct failed, no ineq data"
end-/

end sum_form_proof


meta def sign_proof.reconstruct := @sign_proof.reconstruct_aux @sum_form_proof.reconstruct
meta def ineq_proof.reconstruct := @ineq_proof.reconstruct_aux @sign_proof.reconstruct @sum_form_proof.reconstruct
meta def eq_proof.reconstruct := @eq_proof.reconstruct_aux @ineq_proof.reconstruct @sum_form_proof.reconstruct


meta def ineq_data.to_expr {lhs rhs} (id : ineq_data lhs rhs) : tactic expr :=
match id.inq.to_slope with
| slope.horiz := id.inq.to_comp.to_function rhs ```(0 : ℚ)
| slope.some m := if m = 0 then id.inq.to_comp.to_function lhs ```(0 : ℚ)
                  else do rhs' ← to_expr `(%%(quote m)*%%rhs), id.inq.to_comp.to_function lhs rhs'
end

namespace contrad

private meta def reconstruct_eq_diseq {lhs rhs} (ed : eq_data lhs rhs) (dd : diseq_data lhs rhs) : tactic expr :=
if bnot (ed.c = dd.c) then fail "reconstruct_eq_diseq failed: given different coefficients"
else do ddp ← dd.prf.reconstruct, edp ← ed.prf.reconstruct, return $ ddp.app edp

private meta def reconstruct_two_ineq_data {lhs rhs} (rct : contrad → tactic expr) (id1 id2 : ineq_data lhs rhs) : tactic expr :=
let sfid1 := sum_form_comp_data.of_ineq_data id1,
    sfid2 := sum_form_comp_data.of_ineq_data id2 in
match find_contrad_in_sfcd_list [sfid1, sfid2] with
| some ctr    := trace ("ctr:", ctr) >> rct ctr
| option.none := fail "reconstruct_two_ineq_data failed to find contr"
end

private meta def reconstruct_eq_ineq {lhs rhs} (ed : eq_data lhs rhs) (id : ineq_data lhs rhs) : tactic expr :=
fail "reconstruct_eq_ineq not implemented"

-- TODO: this is the hard part. Should this be refactored into smaller pieces?
private meta def reconstruct_ineqs (rct : contrad → tactic expr) {lhs rhs} (ii : ineq_info lhs rhs) (id : ineq_data lhs rhs) : tactic expr := do trace "ineqs!!",
match ii with
| ineq_info.no_comps := fail "reconstruct_ineqs cannot find a contradiction with no known comps"
| ineq_info.one_comp id2 := reconstruct_two_ineq_data rct id id2
| ineq_info.equal ed := reconstruct_eq_ineq ed id
| ineq_info.two_comps id1 id2 := 
   let sfid  := sum_form_comp_data.of_ineq_data id,
       sfid1 := sum_form_comp_data.of_ineq_data id1,
       sfid2 := sum_form_comp_data.of_ineq_data id2 in
   match find_contrad_in_sfcd_list [sfid, sfid1, sfid2] with
   | some ctr    := rct ctr
   | option.none := fail "reconstruct_ineqs failed to find contr"
   end
end

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

meta def reconstruct_sum_form {sfc} (sfp : sum_form_proof sfc) : tactic expr :=
if sfc.is_contr then do
  zltz ← sfp.reconstruct,
  mk_mapp ``lt_irrefl [option.none, option.none, option.none, some zltz]
else fail "reconstruct_sum_form requires proof of 0 < 0"

meta def reconstruct : contrad → tactic expr
| none := fail "cannot reconstruct contr: no contradiction is known"
| (@eq_diseq lhs rhs ed dd) := reconstruct_eq_diseq ed dd
| (@ineqs lhs rhs ii id) := reconstruct_ineqs reconstruct ii id
| (@sign e sd1 sd2) := reconstruct_sign sd1 sd2
| (@strict_ineq_self e id) := reconstruct_strict_ineq_self id
| (@sum_form _ sfp) := reconstruct_sum_form sfp

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

--run_cmd reconstruct ip4 >>= infer_type >>= trace

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
