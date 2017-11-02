import .datatypes .sum_form .reconstruction_theorems
namespace polya

open expr tactic diseq_proof
--#check mk_nat_val_ne_proof use something like this below?
theorem fake_ne_zero_pf (q : ℚ) : q ≠ 0 := sorry
theorem fake_gt_zero_pf (q : ℚ) : q > 0 := sorry
theorem fake_lt_zero_pf (q : ℚ) : q < 0 := sorry
theorem fake_eq_zero_pf (q : ℚ) : q = 0 := sorry
theorem fake_ne_pf (q1 q2 : ℚ) : q1 ≠ q2 := sorry

meta def mk_ne_zero_pf (q : ℚ) : tactic expr :=
--do qe ← to_expr ``(%%(quote q) : ℚ),
--   to_expr ``(fake_ne_zero_pf (%%qe : ℚ))
return `(fake_ne_zero_pf q) 
  
-- proves that q > 0, q < 0, or q = 0
meta def mk_sign_pf (q : ℚ) : tactic expr :=
/-do qe ← to_expr `(%%(quote q) : ℚ),
   if q > 0 then to_expr `(fake_gt_zero_pf (%%qe : ℚ))
   else if q < 0 then to_expr `(fake_lt_zero_pf (%%qe : ℚ))
   else to_expr ``(fake_eq_zero_pf (%%qe : ℚ))-/
if q > 0 then return `(fake_gt_zero_pf q)
else if q < 0 then return `(fake_lt_zero_pf q)
else return `(fake_eq_zero_pf q)

meta def mk_ne_pf (q1 q2 : ℚ) : tactic expr :=
/-do q1e ← to_expr ``(%%(quote q1) : ℚ),
   q2e ← to_expr ``(%%(quote q2) : ℚ),
   to_expr `(fake_ne_pf %%q1e %%q2e)-/
return `(fake_ne_pf q1 q2)

meta def mk_int_sign_pf (z : ℤ) : tactic expr :=
if z > 0 then return `(sorry : z > 0)
else if z < 0 then return `(sorry : z < 0)
else return `(sorry : z = 0)

-- proves z % 2 = 0 or z % 2 = 1
meta def mk_int_mod_pf (z : ℤ) : tactic expr :=
if z % 2 = 0 then return `(sorry : z % 2 = 0)
else return `(sorry : z % 2 = 1)

namespace diseq_proof
private meta def reconstruct_hyp (lhs rhs : expr) (c : ℚ) (pf : expr) : tactic expr :=
do mvc ← mk_mvar,
   pft ← infer_type pf,
   to_expr ``(%%lhs ≠ %%mvc * %%rhs) >>= unify pft,
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
   to_expr ``(%%lhs = %%mvc * %%rhs) >>= unify pft,
   c' ← eval_expr rat mvc,
   if c = c' then return pf else fail "eq_proof.reconstruct_hyp failed"

private meta def reconstruct_sym (rc : Π {lhs rhs : expr} {c : ℚ}, eq_proof lhs rhs c → tactic expr)
        {lhs rhs c} (dp : eq_proof lhs rhs c) : tactic expr :=
do symp ← rc dp,
   cnep ← mk_ne_zero_pf c, -- 5/1 ≠ 0
--   infer_type symp >>= trace,
--   infer_type cnep >>= trace,
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
if lhs.lt rhs then -- flipped? 
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
do mvc ← mk_mvar, pft ← infer_type pf, 
match iq.to_comp with
| comp.lt := to_expr ``(%%lhs < %%mvc * %%rhs) >>= unify pft >> return mvc
| comp.le := to_expr ``(%%lhs ≤ %%mvc * %%rhs) >>= unify pft >> return mvc
| comp.gt := to_expr ``(%%lhs > %%mvc * %%rhs) >>= unify pft >> return mvc
| comp.ge := to_expr ``(%%lhs ≥ %%mvc * %%rhs) >>= unify pft >> return mvc
end

private meta def reconstruct_hyp (lhs rhs : expr) (iq : ineq) (pf : expr) : tactic expr :=
match iq.to_slope with
| slope.horiz  := 
  do tp ← infer_type pf, --trace "unifying tp in reconstruct_hyp1", trace tp,
     to_expr ``( %%(iq.to_comp.to_pexpr) %%rhs 0) >>= unify tp,
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
--trace ("m", m), trace ("lhs, rhs", lhs, rhs), trace "sgnp", infer_type sgnp >>= trace, trace "symp", trace ip, infer_type symp >>= trace,
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
 /-if iq.to_comp.is_less then
  mk_mapp ``ineq_diseq_le [none, none, none, some dpp, some ipp]
 else 
  mk_mapp ``ineq_diseq_ge [none, none, none, some dpp, some ipp]-/
 mk_app ``ineq_diseq [dpp, ipp]
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
--    mk_app (if iq.to_comp.is_less then ``ineq_diseq_sign_lhs_le else ``ineq_diseq_sign_lhs_ge) [spp, ipp]   
    mk_app ``ineq_diseq_sign_lhs [spp, ipp] 
  else fail "reconstruct_ineq_sign_lhs assumes a 0 slope"
end

-- this might be wrong: should we produce proofs of y < 0?
private meta def reconstruct_ineq_sign_rhs {lhs rhs iq c} (ip : ineq_proof lhs rhs iq) (sp : sign_proof rhs c) : tactic expr :=
if iq.strict || bnot (c = gen_comp.ne) then fail "reconstruct_ineq_sign_rhs assumes a weak ineq and a diseq-0" else
match iq.to_slope with
| slope.horiz := do ipp ← rc ip, spp ← rcs sp,
--    mk_app (if iq.to_comp.is_less then ``ineq_diseq_sign_rhs_le else ``ineq_diseq_sign_rhs_ge) [spp, ipp]
    mk_app ``ineq_diseq_sign_rhs [spp, ipp]
| _ := fail "reconstruct_ineq_sign_rhs assumes a horizontal slope"
end


omit rc

-- x ≥ 0 implies x ≥ 0*y
private meta def reconstruct_zero_comp_of_sign {lhs c} (rhs : expr) (iq : ineq) (sp : sign_proof lhs c) : tactic expr :=
if bnot ((iq.to_comp.to_gen_comp = c) && (iq.is_zero_slope)) then fail "reconstruct_zero_comp_of_sign only produces comps with zero"
--else do spp ← rcs sp, mk_app (zero_mul_name_of_comp iq.to_comp) [rhs, spp]
else do spp ← rcs sp, mk_mapp ``op_zero_mul [none, some rhs, none, none, some spp]

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


private meta def reconstruct_of_sum_form_proof  (sfpr : Π {sf}, Π (sp : sum_form_proof sf), tactic expr) :
        expr → expr → ineq → Π {sfc}, sum_form_proof sfc → tactic expr | lhs rhs i sfc sp :=
if lhs.lt rhs then -- flipped?
  reconstruct_of_sum_form_proof rhs lhs i.reverse sp
else
 (match i.to_slope with
| slope.some m := do {
  guard $ (sfc.sf.contains lhs) && (sfc.sf.contains rhs),
  guard $ sfc.sf.keys.length = 2,
  let a := sfc.sf.get_coeff lhs in let b := sfc.sf.get_coeff rhs in do
  guard $ m = -(b/a),
  guard $ if a < 0 then sfc.c.to_comp = i.to_comp.reverse else sfc.c.to_comp = i.to_comp,
  rhs' ← to_expr ``(%%(↑(rat.reflect m) : expr) * %%rhs), -- better way to do this?
  tp ← i.to_comp.to_function lhs rhs',
  sgnp ← mk_sign_pf a,
  pf ← sfpr sp,
  --trace "have: ", infer_type pf >>= trace, trace ("lhs: ", lhs), trace ("rhs: ", rhs),
  let thnm := if a < 0 then ``op_of_sum_op_zero_neg else ``op_of_sum_op_zero_pos in 
  mk_app thnm [pf, sgnp]}
  --to_expr ``(sorry : %%tp)
--  fail "ineq_proof.reconstruct_of_sum_proof not implemented yet"
| slope.horiz := fail "ineq_proof.reconstruct_of_sum_proof failed, cannot turn a sum into a horiz slope"
end)

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
| gen_comp.ge := ``(%%e ≥ 0)
| gen_comp.gt := ``(%%e > 0)
| gen_comp.le := ``(%%e ≤ 0)
| gen_comp.lt := ``(%%e < 0)
| gen_comp.eq := ``(%%e = 0)
| gen_comp.ne := ``(%%e ≠ 0)
end in do tp ← infer_type pf, to_expr pex >>= unify tp >> return pf

section
parameter rc : Π {e c}, sign_proof e c → tactic expr
parameter sfpr : Π {sf}, Π (sp : sum_form_proof sf), tactic expr
private meta def rci := @ineq_proof.reconstruct_aux @rc @sfpr
private meta def rce := @eq_proof.reconstruct_aux @rci @sfpr

-- x ≤ 0*y to x ≤ 0
private meta def reconstruct_ineq_lhs (c : gen_comp) {lhs rhs iqp} (ip : ineq_proof lhs rhs iqp) : tactic expr :=
if bnot ((iqp.to_comp.to_gen_comp = c) && (iqp.is_zero_slope)) then fail "reconstruct_ineq_lhs must take a comparison with 0"
--else do ipp ← rci ip, mk_app (zero_mul'_name_of_comp iqp.to_comp) [ipp]
else do ipp ← rci ip, mk_app ``op_zero_mul' [ipp]

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

/-
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
-/


private theorem {u} ge_of_not_lt {α : Type u} [linear_order α] {a b : α} (h : ¬ a < b) : (a ≥ b) := le_of_not_gt h

private theorem {u} gt_of_not_le {α : Type u} [linear_order α] {a b : α} (h : ¬ a ≤ b) : (a > b) := lt_of_not_ge h


private meta def neg_op_lemma_name : comp → name
| comp.lt := ``lt_of_not_ge
| comp.le := ``le_of_not_gt
| comp.ge := ``ge_of_not_lt
| comp.gt := ``gt_of_not_le

meta def reconstruct_ineq_of_eq_and_ineq_aux
-- (sfpr : Π {sf : sum_form_comp}, Π (sp : sum_form_proof sf), tactic.{0} (expr tt))
 {lhs rhs iq c} (c' : gen_comp) (ep : eq_proof lhs rhs c) (ip : ineq_proof lhs rhs iq) (pvt : expr) : tactic expr :=
do negt ← c'.to_comp.to_function pvt `(0 : ℚ),
   (_, notpf) ← solve_aux negt (do
     applyc $ neg_op_lemma_name c'.to_comp,
     hypv ← intro `h,
     let sfid := sum_form_comp_data.of_ineq_data ⟨_, ip⟩ in
     let sfed := sum_form_comp_data.of_eq_data ⟨_, ep⟩ in
     let sfsd := sum_form_comp_data.of_sign_data ⟨c'.negate, hyp pvt _ hypv⟩ in
     match find_contrad_sfcd_in_sfcd_list [sfid, sfed, sfsd] with
     | none := fail "reconstruct_ineq_of_eq_and_ineq failed to find proof"
     | some ⟨_, sfp, _⟩ := do ctrp ← sfpr sfp, fp ← mk_mapp ``lt_irrefl [none, none, none, ctrp], apply fp
--applyc ``lt_irrefl, trace "apply3", apply ctrp, trace "apply4"
     end),
   return notpf



--#check @reconstruct_ineq_of_eq_and_ineq_aux
-- these are the hard cases. Is this the right place to handle them?
private meta def reconstruct_ineq_of_eq_and_ineq_lhs {lhs rhs iq c} (c' : gen_comp) (ep : eq_proof lhs rhs c) (ip : ineq_proof lhs rhs iq) : tactic expr :=
reconstruct_ineq_of_eq_and_ineq_aux c' ep ip lhs
--fail "reconstruct_ineq_of_eq_and_ineq not implemented"

private meta def reconstruct_ineq_of_eq_and_ineq_rhs {lhs rhs iq c} (c' : gen_comp) (ep : eq_proof lhs rhs c) (ip : ineq_proof lhs rhs iq) : tactic expr :=
reconstruct_ineq_of_eq_and_ineq_aux c' ep ip rhs
/-do negt ← c'.to_comp.to_function rhs `(0 : ℚ),
   (_, notpf) ← solve_aux negt (do
     applyc $ neg_op_lemma_name c'.to_comp,
     hypv ← intro `h,
     let sfid := sum_form_comp_data.of_ineq_data ⟨_, ip⟩ in
     let sfed := sum_form_comp_data.of_eq_data ⟨_, ep⟩ in
     let sfsd := sum_form_comp_data.of_sign_data ⟨c', hyp rhs _ hypv⟩ in
     match find_contrad_sfcd_in_sfcd_list [sfid, sfed, sfsd] with
     | none := fail "reconstruct_ineq_of_eq_and_ineq_rhs failed to find proof"
     | some ⟨_, sfp, _⟩ := do ctrp ← sfpr sfp, applyc ``lt_irrefl, apply ctrp
     end),
   return notpf-/
--   fail "reconstruct_ineq_of_eq_and_ineq not implemented"

-- TODO
private meta def reconstruct_ineq_of_ineq_and_eq_zero_rhs {lhs rhs iq} (c : gen_comp) (ip : ineq_proof lhs rhs iq) (sp : sign_proof lhs gen_comp.eq) : tactic expr :=
fail "reconstruct_ineq_of_ineq_and_eq_zero not implemented"
   
private meta def reconstruct_diseq_of_strict_ineq {e c} (sp : sign_proof e c) : tactic expr :=
if c.is_strict then do
  spp ← rc sp,
  mk_app ``ne_of_strict_op [spp]
else fail "reconstruct_diseq_of_strict_ineq failed, comp is not strict"

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
| .(_) .(_) (@ineq_of_eq_and_ineq_lhs _ _ _ _ c' ep ip) := reconstruct_ineq_of_eq_and_ineq_lhs @sfpr c' ep ip
| .(_) .(_) (@ineq_of_eq_and_ineq_rhs _ _ _ _ c' ep ip) := reconstruct_ineq_of_eq_and_ineq_rhs @sfpr c' ep ip
| .(_) .(_) (@ineq_of_ineq_and_eq_zero_rhs _ _ _ c ip sp) := reconstruct_ineq_of_ineq_and_eq_zero_rhs c ip sp
| .(_) .(_) (@diseq_of_strict_ineq _ _ sp) := reconstruct_diseq_of_strict_ineq @reconstruct_aux sp
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
if expr.lt lhs rhs then reconstruct_of_ineq_proof ip.sym else 
trace "ipp is:" >> iprc ip >>= infer_type >>= trace >> trace "const is:" >> infer_type ↑`(@polya.mul_lt_of_lt) >>= trace >>
match iq.to_slope with
| slope.horiz := 
  do ipp ← iprc ip, 
     tactic.mk_mapp (sum_form_name_of_comp_single iq.to_comp) [none, none, ipp]
| slope.some m := 
  do ipp ← iprc ip, 
trace ("ipp", ip, ipp), infer_type ipp >>= trace, trace ("comp", iq.to_comp), trace ("iq", iq),
     if m = 0 then
       tactic.mk_mapp (sum_form_name_of_comp_single iq.to_comp) [none, none, ipp]
     else
       tactic.mk_mapp (sum_form_name_of_comp iq.to_comp) [none, none, none, ipp]
--     tactic.mk_mapp ((if m = 0 then sum_form_name_of_comp_single else sum_form_name_of_comp) iq.to_comp) [none, none, ipp]
end
--include sfrc
#check sub_lt_of_gt

private meta def reconstruct_of_eq_proof  : 
        Π {lhs rhs c}, eq_proof lhs rhs c → tactic expr | lhs rhs c ep :=
if expr.lt lhs rhs then reconstruct_of_eq_proof ep.sym else
do ipp ← eprc ep,
   mk_app ``sub_eq_zero_of_eq [ipp]
--fail "sum_form_proof.reconstruct_of_eq_proof not implemented yet"

private meta def reconstruct_of_sign_proof :
        Π {e c}, sign_proof e c → tactic expr | e c sp :=
if c.is_less then sprc sp 
else do spp ← sprc sp,
  trace "spp type is", infer_type spp >>= trace,
  mk_mapp ``rev_op_zero_of_op [none, none, none, some spp]
--fail "sum_form_proof.reconstruct_of_sign_proof not implemented yet"


meta def expr_coeff_list_to_expr : list (expr × ℚ) → tactic expr
| [] := return `(0 : ℚ)
| [(e, q)] := to_expr ``(%%(↑q.reflect : expr)*%%e)
| ((e, q)::t) := do e' ← expr_coeff_list_to_expr t, h ← to_expr ``(%%(q.reflect : expr)*%%e), to_expr ``(%%h + %%e')

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
   tp' ← (spec_comp.strongest c1 c2).to_comp.to_function tp `(0 : ℚ),
   pf1 ← sfrc sfpl, pf2 ← sfrc sfpr,
   mk_mapp ``reconstruct_of_add_factor_aux [some tp', none, none, some pf1, some pf2] --to_expr `(sorry : %%tp)    
--fail "reconstruct_of_add_factor_same_comp failed, not implemented yet"

private theorem reconstruct_of_add_eq_factor_op_comp_aux  (P : Prop) {Q R : Prop} (h : Q) (h2 : R) : P := sorry

/-
m is negative
-/
private meta def reconstruct_of_add_eq_factor_op_comp {lhs rhs c1} (m : ℚ) 
        (sfpl : sum_form_proof ⟨lhs, c1⟩) (sfpr : sum_form_proof ⟨rhs, spec_comp.eq⟩) : tactic expr :=
let sum := lhs + rhs.scale m in
do tp ← sum_form.to_expr sum,
   tp' ← c1.to_comp.to_function tp `(0 : ℚ),
   pf1 ← sfrc sfpl, pf2 ← sfrc sfpr,
   mk_mapp ``reconstruct_of_add_eq_factor_op_comp_aux [some tp', none, none, some pf1, some pf2]
--fail "reconstruct_of_add_eq_factor_op_comp not implemented yet"


private theorem reconstruct_of_scale_aux (P : Prop) {Q : Prop} (h : Q) : P := sorry

private meta def reconstruct_of_scale (rct : Π {sfc}, sum_form_proof sfc → tactic expr) 
        {sfc} (m : ℚ) (sfp : sum_form_proof sfc) : tactic expr :=
do tp ← sum_form.to_expr (sfc.sf.scale m),
   tp' ← sfc.c.to_comp.to_function tp `(0 : ℚ),
   pf ← rct sfp,
   mk_mapp ``reconstruct_of_scale_aux [some tp', none, some pf] -- to_expr `(sorry : %%tp')
   
end 

-- TODO (alg norm)
theorem reconstruct_of_expr_def_aux (P : Prop) : P := sorry

private meta def reconstruct_of_expr_def (e : expr) (sf : sum_form) : tactic expr :=
do tp ← sum_form.to_expr sf,
   tp' ← to_expr ``(%%tp = 0),
--   (_, pf) ← solve_aux tp' (simp >> done),
   mk_app ``reconstruct_of_expr_def_aux [tp']
--   instantiate_mvars pf
--fail "reconstruct_of_expr_def failed, not implemented yet"

meta def reconstruct : Π {sfc}, sum_form_proof sfc → tactic expr
| .(_) (@of_ineq_proof _ _ _ ip) := reconstruct_of_ineq_proof @reconstruct ip
| .(_) (@of_eq_proof _ _ _ ep) := reconstruct_of_eq_proof @reconstruct ep
| .(_) (@of_sign_proof _ _ sp) := reconstruct_of_sign_proof @reconstruct sp
| .(_) (@of_add_factor_same_comp _ _ _ _ m sfpl sfpr) := 
  reconstruct_of_add_factor_same_comp @reconstruct m sfpl sfpr 
| .(_) (@of_add_eq_factor_op_comp _ _ _ m sfpl sfpr) :=
  reconstruct_of_add_eq_factor_op_comp @reconstruct m sfpl sfpr
| .(_) (@of_scale _ m sfp) := reconstruct_of_scale @reconstruct m sfp
| .(_) (@of_expr_def e sf) := reconstruct_of_expr_def e sf
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
| slope.horiz := id.inq.to_comp.to_function rhs `(0 : ℚ)
| slope.some m := if m = 0 then id.inq.to_comp.to_function lhs `(0 : ℚ)
                  else do rhs' ← to_expr ``(%%(m.reflect : expr)*%%rhs), id.inq.to_comp.to_function lhs rhs'
end

namespace contrad

private meta def reconstruct_eq_diseq {lhs rhs} (ed : eq_data lhs rhs) (dd : diseq_data lhs rhs) : tactic expr :=
if bnot (ed.c = dd.c) then fail "reconstruct_eq_diseq failed: given different coefficients"
else do ddp ← dd.prf.reconstruct, edp ← ed.prf.reconstruct, return $ ddp.app edp

private meta def reconstruct_two_ineq_data {lhs rhs} (rct : contrad → tactic expr) (id1 id2 : ineq_data lhs rhs) : tactic expr :=
let sfid1 := sum_form_comp_data.of_ineq_data id1,
    sfid2 := sum_form_comp_data.of_ineq_data id2 in
match find_contrad_in_sfcd_list [sfid1, sfid2] with
| some ctr    := rct ctr
| option.none := fail "reconstruct_two_ineq_data failed to find contr"
end

private meta def reconstruct_eq_ineq {lhs rhs} (ed : eq_data lhs rhs) (id : ineq_data lhs rhs) : tactic expr :=
fail "reconstruct_eq_ineq not implemented"

-- TODO: this is the hard part. Should this be refactored into smaller pieces?
private meta def reconstruct_ineqs (rct : contrad → tactic expr) {lhs rhs} (ii : ineq_info lhs rhs) (id : ineq_data lhs rhs) : tactic expr := --do trace "ineqs!!",
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

private meta def reconstruct_sign_gt_lt {e} (gtpr : sign_proof e gen_comp.gt) (ltpr : sign_proof e gen_comp.lt) : tactic expr :=
do gtprp ← gtpr.reconstruct, ltprp ← ltpr.reconstruct,
   mk_app ``gt_lt_contr [gtprp, ltprp]


private meta def reconstruct_sign {e} : sign_data e → sign_data e → tactic expr
| ⟨gen_comp.ne, prf1⟩ ⟨gen_comp.eq, prf2⟩ := reconstruct_sign_ne_eq prf1 prf2
| ⟨gen_comp.eq, prf1⟩ ⟨gen_comp.ne, prf2⟩ := reconstruct_sign_ne_eq prf2 prf1
| ⟨gen_comp.le, prf1⟩ ⟨gen_comp.gt, prf2⟩ := reconstruct_sign_le_gt prf1 prf2
| ⟨gen_comp.gt, prf1⟩ ⟨gen_comp.le, prf2⟩ := reconstruct_sign_le_gt prf2 prf1
| ⟨gen_comp.lt, prf1⟩ ⟨gen_comp.ge, prf2⟩ := reconstruct_sign_ge_lt prf2 prf1
| ⟨gen_comp.ge, prf1⟩ ⟨gen_comp.lt, prf2⟩ := reconstruct_sign_ge_lt prf1 prf2
| ⟨gen_comp.gt, prf1⟩ ⟨gen_comp.lt, prf2⟩ := reconstruct_sign_gt_lt prf1 prf2
| ⟨gen_comp.lt, prf1⟩ ⟨gen_comp.gt, prf2⟩ := reconstruct_sign_gt_lt prf2 prf1
| s1 s2 := fail "reconstruct_sign failed: given non-opposite comps"

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

namespace prod_form_proof

meta def expr_coeff_list_to_expr : list (expr × ℤ) → tactic expr
| [] := return `(1 : ℚ)
| [(e, z)] := to_expr ``(rat.pow %%e %%(z.reflect : expr))
| ((e, z)::t) := do e' ← expr_coeff_list_to_expr t, h ← to_expr ``(rat.pow %%e %%(z.reflect : expr)), to_expr ``(%%h * %%e')

meta def prod_form.to_expr (sf : prod_form) : tactic expr := 
do trace "in prod_form.to_expr", exp ← expr_coeff_list_to_expr sf.exps.to_list,
   trace "****",
   let cf : expr := sf.coeff.reflect,
   trace "cf, exp", trace (cf, exp),
   to_expr ``(%%cf * %%exp : ℚ)


/-private meta def mk_prod_ne_zero_prf_aux : expr → list (Σ e : expr, sign_proof e gen_comp.ne) → tactic expr
| e [] := return e
| e (⟨e', sp⟩::t) := do ene ← sp.reconstruct, pf ← mk_app ``mul_ne_zero [e, ene], mk_prod_ne_zero_prf_aux pf t

private meta def mk_prod_ne_zero_prf (c : ℚ) : list (Σ e : expr, sign_proof e gen_comp.ne) → tactic expr 
| [] := if c = 0 then fail "mk_prod_ne_zero_prf failed, c = 0" else mk_app ``fake_ne_zero_pf [`(c)]
| (⟨e, sp⟩::t) :=
  if c = 0 then fail "mk_prod_ne_zero_prf failed, c = 0" else
  do cprf ← mk_app ``fake_ne_zero_pf [`(c)],
     hpf ← sp.reconstruct,
     prodprf ← mk_prod_ne_zero_prf_aux hpf t,
     mk_app ``mul_ne_zero [hpf, prodprf]
-/
/-#check spec_comp_and_flipped_of_comp
-- not finished: need to orient c
private meta def reconstruct_of_ineq_proof_pos_lhs {lhs rhs iq} (id : ineq_proof lhs rhs iq)  
        (sp : sign_proof lhs gen_comp.gt) (nzprs : hash_map expr (λ e, sign_proof e gen_comp.ne)) : tactic expr :=
match (spec_comp_and_flipped_of_comp iq.to_comp), iq.to_slope with
| _, slope.horiz := fail "reconstruct_of_ineq_proof_pos_lhs failed, cannot make a prod_form with 0 slope"
| (c, flipped), slope.some m := 
  if m = 0 then fail "reconstruct_of_ineq_proof_pos_lhs failed, cannot make a prod_form with 0 slope"
  else do -- lhs c m*rhs --> 1 c m*(lhs⁻¹*rhs)
     idp ← id.reconstruct,
     spp ← sp.reconstruct,
     opp ← mk_app ``one_op_inv_mul_of_op_of_pos [idp, spp], -- 1 r lhs⁻¹*rhs
     if bnot flipped then 
        return opp
     else do
        mprf ← mk_sign_pf m,
        failed
end-/
        
#print spec_comp
private meta def reconstruct_of_ineq_proof_aux {lhs rhs iq c1 c2} (id : ineq_proof lhs rhs iq)  
        (spl : sign_proof lhs c1) (spr : sign_proof rhs c2) (fail_cond : ℚ → bool) 
        (unflipped_name flipped_name : name) --flipped_lt_name flipped_le_name : name) 
       : tactic expr :=
match (spec_comp_and_flipped_of_comp iq.to_comp), iq.to_slope with
| _, slope.horiz := fail "reconstruct_of_ineq_proof_pos_pos failed, cannot make a prod_form with 0 slope"
| (c, flipped), slope.some m := trace "okay, roipa" >> trace flipped >>
   if fail_cond m then fail "reconstruct_of_ineq_proof_aux failed check" 
   else do
     idp ← id.reconstruct, trace "idp_type:", infer_type idp >>= trace,
     splp ← spl.reconstruct, trace "splp_type:", infer_type splp >>= trace, trace "c1 is:", trace c1, trace spl,
     opp ← mk_app unflipped_name [idp, splp],
     trace "opp", infer_type opp >>= trace,
     if bnot flipped then return opp
     else do
        msgn ← mk_sign_pf m,
        sprp ← spr.reconstruct,
        mk_app flipped_name-- (if c=spec_comp.lt then flipped_lt_name else flipped_le_name) 
               [opp, splp, sprp, msgn]
end

#check one_op_inv_mul_of_op_of_pos

private meta def reconstruct_of_ineq_proof_pos_pos {lhs rhs iq} (id : ineq_proof lhs rhs iq)  
        (spl : sign_proof lhs gen_comp.gt) (spr : sign_proof rhs gen_comp.gt) : tactic expr :=  trace "111" >>
reconstruct_of_ineq_proof_aux id spl spr (λ m, m ≤ 0)
  ``one_op_inv_mul_of_op_of_pos ``one_op_inv_mul_of_lt_of_pos_pos_flipped' -- ``one_le_inv_mul_of_le_of_pos_pos_flipped
/-match (spec_comp_and_flipped_of_comp iq.to_comp), iq.to_slope with
| _, slope.horiz := fail "reconstruct_of_ineq_proof_pos_pos failed, cannot make a prod_form with 0 slope"
| (c, flipped), slope.some m := 
   if m ≤ 0 then fail "reconstruct_of_ineq_proof_pos_pos failed, m ≤ 0"
   else do
     idp ← id.reconstruct,
     splp ← spl.reconstruct,
     opp ← mk_app ``one_op_inv_mul_of_op_of_pos [idp, splp],
     if bnot flipped then return opp
     else do
        msgn ← mk_sign_pf m,
        sprp ← spr.reconstruct,
        mk_app (if c=spec_comp.lt then ``one_lt_inv_mul_of_lt_of_pos_flipped 
                 else ``one_le_inv_mul_of_le_of_pos_flipped) 
               [opp, splp, sprp, msgn]
end-/ 



private meta def reconstruct_of_ineq_proof_pos_neg {lhs rhs iq} (id : ineq_proof lhs rhs iq)  
        (spl : sign_proof lhs gen_comp.gt) (spr : sign_proof rhs gen_comp.lt) : tactic expr := trace "222" >>
reconstruct_of_ineq_proof_aux id spl spr (λ m, m ≥ 0)
  ``one_op_inv_mul_of_op_of_pos ``one_op_inv_mul_of_lt_of_pos_neg_flipped -- ``one_le_inv_mul_of_le_of_pos_neg_flipped



private meta def reconstruct_of_ineq_proof_neg_pos {lhs rhs iq} (id : ineq_proof lhs rhs iq)  
        (spl : sign_proof lhs gen_comp.lt) (spr : sign_proof rhs gen_comp.gt) : tactic expr := trace "333" >>
reconstruct_of_ineq_proof_aux id spl spr (λ m, m ≥ 0)
  ``one_op_inv_mul_of_op_of_neg ``one_op_inv_mul_of_lt_of_neg_pos_flipped -- ``one_le_inv_mul_of_le_of_neg_flipped


private meta def reconstruct_of_ineq_proof_neg_neg {lhs rhs iq} (id : ineq_proof lhs rhs iq)  
        (spl : sign_proof lhs gen_comp.lt) (spr : sign_proof rhs gen_comp.lt) : tactic expr := trace "444" >>
reconstruct_of_ineq_proof_aux id spl spr (λ m, m ≤ 0)
  ``one_op_inv_mul_of_op_of_neg ``one_op_inv_mul_of_lt_of_neg_neg_flipped

/-
pos_neg
cmatch (spec_comp_and_flipped_of_comp iq.to_comp), iq.to_slope with
| _, slope.horiz := fail "reconstruct_of_ineq_proof_pos_pos failed, cannot make a prod_form with 0 slope"
| (c, flipped), slope.some m := 
   if m ≥ 0 then fail "reconstruct_of_ineq_proof_pos_neg failed, m ≥ 0"
   else do
     idp ← id.reconstruct,
     splp ← spl.reconstruct,
     opp ← mk_app ``one_op_inv_mul_of_op_of_pos [idp, splp],
     if bnot flipped then return opp
     else do
        msgn ← mk_sign_pf m,
        sprp ← spr.reconstruct,
        mk_app (if c=spec_comp.lt then ``one_lt_inv_mul_of_lt_of_pos_flipped 
                 else ``one_le_inv_mul_of_le_of_pos_flipped) 
               [opp, splp, sprp, msgn]
end -/

private meta def reconstruct_of_ineq_proof {lhs rhs iq} (id : ineq_proof lhs rhs iq) :
        Π {cl cr}, sign_proof lhs cl → sign_proof rhs cr → tactic expr
| gen_comp.gt gen_comp.gt spl spr := reconstruct_of_ineq_proof_pos_pos id spl spr
| gen_comp.gt gen_comp.lt spl spr := reconstruct_of_ineq_proof_pos_neg id spl spr
| gen_comp.lt gen_comp.gt spl spr := reconstruct_of_ineq_proof_neg_pos id spl spr
| gen_comp.lt gen_comp.lt spl spr := reconstruct_of_ineq_proof_neg_neg id spl spr
| _ _ _ _ := fail "reconstruct_of_ineq_proof failed, need to know signs of components"

/-
-- TODO
private meta def reconstruct_of_ineq_proof_neg_lhs {lhs rhs iq} (id : ineq_proof lhs rhs iq)  
        (sp : sign_proof lhs gen_comp.lt) (nzprs : hash_map expr (λ e, sign_proof e gen_comp.ne)) : tactic expr :=
match iq.to_slope with
| slope.horiz := fail "reconstruct_of_ineq_proof_neg_lhs failed, cannot make a prod_form with 0 slope"
| slope.some m := 
  if m = 0 then fail "reconstruct_of_ineq_proof_pos_lhs failed, cannot make a prod_form with 0 slope"
  else
  failed
end-/

private meta def reconstruct_of_eq_proof {lhs rhs c} (id : eq_proof lhs rhs c) 
        (lhsne : sign_proof lhs gen_comp.ne) : tactic expr :=
if c = 0 then fail "reconstruct_of_eq_proof failed, cannot make a prod_form with 0 slope"
else do
  lhsnep ← lhsne.reconstruct,
  idpf ← id.reconstruct,
  mk_app ``one_eq_div_of_eq [idpf, lhsnep]

theorem reconstruct_of_expr_def_aux (P : Prop) : P := sorry

/-

-- TODO

private meta def reconstruct_of_expr_def (e : expr) (sf : sum_form) : tactic expr :=
do tp ← sum_form.to_expr sf,
   tp' ← to_expr ``(%%tp = 0),
--   (_, pf) ← solve_aux tp' (simp >> done),
   mk_app ``reconstruct_of_expr_def_aux [tp']
--   instantiate_mvars pf
--fail "reconstruct_of_expr_def failed, not implemented yet"
-/

-- TODO (alg_nom)
private meta def reconstruct_of_expr_def (e : expr) (pf : prod_form) : tactic expr :=
do trace "in reconstruct_of_expr_def",
   tp ← prod_form.to_expr pf,
   trace "tp:", trace tp,
   tp' ← to_expr ``(1 = %%tp),
   trace "tp':", trace tp',
--   (_, pf) ← solve_aux tp' (simp >> done),
   mk_app ``reconstruct_of_expr_def_aux [tp']

section
variable (rct : Π {pfc}, prod_form_proof pfc → tactic expr) 

private meta def simp_pow_expr (pf tgt : expr) : tactic expr :=
do sls ← (simp_lemmas.mk.add_simp ``rat.mul_pow_rev) >>= λ t, t.add pf,
   trace "target", trace tgt,
   trace "pf tp", infer_type pf >>= trace,
   (do (_, npf) ← simplify sls [] tgt,-- <|> do rpr ← to_expr ``(eq.refl %%tgt), return (`(()), rpr),
   --(_, npf) ← solve_aux tgt (simp_target sls >> done),
   return npf) <|> to_expr ``(eq.refl %%tgt)


private meta def simp_pow_expr' (tgt : expr) : tactic expr :=
do sls ← (simp_lemmas.mk.add_simp ``rat.mul_pow_rev) >>= (λ s, simp_lemmas.add_simp s ``rat.pow_one) >>= (λ s, simp_lemmas.add_simp s ``rat.pow_neg_one),
   trace "target", trace tgt,
--   trace "pf tp", infer_type pf >>= trace,
--   (do (_, npf) ← simplify sls [] tgt,-- <|> do rpr ← to_expr ``(eq.refl %%tgt), return (`(()), rpr),
   (_, npf) ← solve_aux tgt (simp_target sls >> reflexivity), -- `[simp [rat.mul_pow_rev, rat.pow_one], done],
   return npf

#check @lt_pos_pow'
section
open expr
private meta def reconstruct_of_pow_pos {pfc} (z : ℤ) (pfp : prod_form_proof pfc) : tactic expr :=
if z ≤ 0 then fail "reconstruct_of_pow_pos failed, given negative exponent" else
do zsn ← mk_int_sign_pf z,
   pf1 ← rct pfp,
   trace "here", trace pfc, trace z, infer_type pf1 >>= trace,
   pf2 ← mk_mapp (if pfc.c = spec_comp.lt then ``lt_pos_pow' else ``le_pos_pow') [none, pf1, none, zsn],
   trace "pf2tp", infer_type pf2 >>= trace,
   pf2tp ← infer_type pf2,
   match pf2tp with
   | app (app (app o i) lhs) rhs := do tgt ← prod_form.to_expr (pfc.pf.pow z), pf ← to_expr ``(%%rhs = %%tgt) >>= simp_pow_expr',
    trace "pf2tp", trace pf2tp, trace "pftp", infer_type pf >>= trace,
    trace "o", trace o,
--    trace `(%%o %%lhs %%tgt),
    tgt' ← return $ app (app (app o i) lhs) tgt,--to_expr ``(%%o %%lhs %%tgt),
    trace "new tgt:", trace tgt',
    pf1 ← to_expr ``(eq.symm %%pf),
    (_, pf') ← solve_aux tgt' (rewrite_target pf1 >> apply pf2),
    trace "proved", infer_type pf' >>= trace,
    return pf'
   | _ := failed
   end
--   tgt ← prod_form.to_expr (pfc.pf.pow z),
--   simp_pow_expr pf2 tgt
end

/-private meta def reconstruct_of_pow_neg {pfc} (z : ℤ) (pfp : prod_form_proof pfc) : tactic expr :=
if z ≥ 0 then fail "reconstruct_of_pow_neg failed, given positive exponent" else
failed-/

#check eq_pow

private meta def reconstruct_of_pow_eq {pfc} (z : ℤ) (pfp : prod_form_proof pfc) : tactic expr :=
do trace "pfp is:", trace pfp, pf1 ← rct pfp, trace "reconstructed", infer_type pf1 >>= trace,
   tpf ← mk_app ``eq_pow [pf1, `(z)],
   tpf' ← mk_app ``eq_pow' [tpf],
   tpf_tp ← infer_type tpf',
   tgt ← prod_form.to_expr (pfc.pf.pow z),
   trace "target is:", trace tgt,
   tgt' ← to_expr ``(1 = %%tgt),
   trace "tgt', tpf", trace tgt', infer_type tpf >>= trace,
   (_, pf') ← solve_aux tgt' (assertv `h tpf_tp tpf' >> `[simp only [rat.mul_pow, rat.pow_pow], simp only [rat.mul_pow, rat.pow_pow] at h, apply h] >> done),
   return pf'
--   simp_pow_expr tpf tgt

private meta def reconstruct_of_pow {pfc} (z : ℤ) (pfp : prod_form_proof pfc) : tactic expr :=
if pfc.c = spec_comp.eq then reconstruct_of_pow_eq @rct z pfp else reconstruct_of_pow_pos @rct z pfp

private theorem reconstruct_of_mul_aux (P : Prop) {Q R : Prop} : Q → R → P := sorry

private meta def reconstruct_of_mul (rct : Π {pfc}, prod_form_proof pfc → tactic expr) 
        {lhs rhs c1 c2} (pfp1 : prod_form_proof ⟨lhs, c1⟩) (pfp2 : prod_form_proof ⟨rhs, c2⟩)
        (sgns : list Σ e : expr, sign_proof e gen_comp.ne) : tactic expr :=
let prod := lhs * rhs in
do trace "in reconstruct_of_mul",
   trace prod,
   tp  ← prod_form.to_expr prod,
   trace tp,
   tp' ← (spec_comp.strongest c1 c2).to_comp.to_function `(1 : ℚ) tp,
   trace tp',
   pf1 ← rct pfp1, pf2 ← rct pfp2, trace "**",
   mk_mapp ``reconstruct_of_mul_aux [tp', none, none, pf1, pf2]
/-
let sum := lhs + rhs.scale m in
do tp ← sum_form.to_expr sum,
   tp' ← (spec_comp.strongest c1 c2).to_comp.to_function tp `(0 : ℚ),
   pf1 ← sfrc sfpl, pf2 ← sfrc sfpr,
   mk_mapp ``reconstruct_of_add_factor_aux [some tp', none, none, some pf1, some pf2] 
-/

end
#check @prod_form_proof.of_ineq_proof

meta def reconstruct : Π {pfc}, prod_form_proof pfc → tactic expr
--| .(_) (@of_ineq_proof_pos_lhs _ _ _ id sp nzprs) := reconstruct_of_ineq_proof_pos_lhs id sp nzprs
--| .(_) (@of_ineq_proof_neg_lhs _ _ _ id sp nzprs) := reconstruct_of_ineq_proof_neg_lhs id sp nzprs
| .(_) (@of_ineq_proof _ _ _ _ _ id spl spr) := reconstruct_of_ineq_proof id spl spr
| .(_) (@of_eq_proof _ _ _ id lhsne) := reconstruct_of_eq_proof id lhsne
| .(_) (@of_expr_def e pf) := reconstruct_of_expr_def e pf
| .(_) (@of_pow _ z pfp) := reconstruct_of_pow @reconstruct z pfp
| .(_) (@of_mul _ _ _ _ pfp1 pfp2 sgns) := reconstruct_of_mul @reconstruct pfp1 pfp2 sgns
| .(_) (fake _) := fail "prod_form_proof.reconstruct failed: cannot reconstruct fake"

end prod_form_proof

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
