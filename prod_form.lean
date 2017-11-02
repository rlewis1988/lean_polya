import .datatypes .struct_eta .blackboard .proof_reconstruction .reconstruction_theorems .comp_val

-- TODO: maybe more of this can move to datatypes

namespace polya


meta def mul_state := state (hash_map expr (λ e, sign_data e))
meta instance mul_state.monad : monad mul_state := state.monad _
private meta def inh_sd (e : expr) : inhabited (sign_data e) := ⟨⟨gen_comp.ne, sign_proof.adhoc _ _ (tactic.failed)⟩⟩
local attribute [instance] inh_sd

private meta def si (e : expr) : mul_state (sign_data e) :=
λ hm, (hm.find' e, hm)

private meta def si' (e : expr) : mul_state (option (sign_data e)) :=
λ hm, (hm.find e, hm)

section sign_inference

meta def sign_of_term (pf : prod_form) (e : expr) : mul_state (option gen_comp) :=
match pf.exps.find e with
| some z := 
  do opt  ← si' e,
  match opt with
  | some ⟨gen_comp.lt, _⟩ := return $ some $ if z % 2 = 0 then gen_comp.gt else gen_comp.lt
  | some ⟨gen_comp.le, _⟩ := return $ some $ if z % 2 = 0 then gen_comp.ge else gen_comp.le
  | some ⟨gen_comp.eq, _⟩ := return $ if z > 0 then some gen_comp.eq else none
  | some ⟨c, _⟩ := return $ some c -- gt, ge, ne
  | _ := return none
  end
| none := return none
end

meta def sign_of_prod (l : list gen_comp) : option gen_comp :=
l.mfoldl gen_comp.prod gen_comp.gt

-- get_remaining_sign g s returns the unique g' such that gen_comp.prod g g' = s
meta def get_remaining_sign_aux : gen_comp → spec_comp → option gen_comp
| gen_comp.gt s := s.to_gen_comp
| gen_comp.ge spec_comp.lt := none
| gen_comp.ge s := s.to_gen_comp
| gen_comp.eq _ := none
| gen_comp.le spec_comp.lt := none
| gen_comp.le s := s.to_gen_comp.reverse
| gen_comp.lt s := s.to_gen_comp.reverse
| gen_comp.ne s := none

meta def get_remaining_sign : gen_comp → gen_comp → option gen_comp
| a gen_comp.gt := gen_comp.reverse <$> (get_remaining_sign_aux a spec_comp.lt)
| a gen_comp.ge := gen_comp.reverse <$> (get_remaining_sign_aux a spec_comp.le)
| gen_comp.gt gen_comp.ne := gen_comp.ne
| gen_comp.lt gen_comp.ne := gen_comp.ne
| gen_comp.ne gen_comp.ne := gen_comp.ne
| _ gen_comp.ne := none
| a b := get_remaining_sign_aux a b.to_spec_comp

/-meta def get_unknown_sign_data : prod_form_comp_data → mul_state (option (Σ e, sign_data e))
| ⟨⟨prod_f, c⟩, prf, _⟩ :=
do sds ← prod_f.exps.keys.mmap (sign_of_term prod_f),
   let known_signs := (sds.bfilter option.is_some),
   if known_signs.length = 1 then
     match sign_of_prod (known_signs.map option.iget) with
     | some ks :=
       match get_remaining_sign ks c with
       | some c' := 
         let i := sds.index_of none,
             e := prod_f.exps.keys.inth i,
             pfe := sign_proof.adhoc e c' (tactic.fail "unfinished adhoc") in
         return $ some ⟨e, ⟨_, pfe⟩⟩
         -- e has sign ks
       | none := return none
       end
     | none := return none
     end
   else return none-/

private lemma aux_sign_infer_tac_lemma (P : Prop) : P := sorry

-- TODO
private meta def aux_sign_infer_tac (e : expr) (pf : prod_form) (c : gen_comp) : tactic expr :=
do tp ← c.to_function e `(0 : ℚ),
   tactic.mk_app ``aux_sign_infer_tac_lemma [tp]
/--
 Assumes known_signs.length = pf.length
-/
meta def infer_expr_sign_data_aux (e : expr) (pf : prod_form) (known_signs : list (option gen_comp)) : mul_state (option Σ e', sign_data e') :=
  let prod_sign := 
    (if pf.coeff < 0 then gen_comp.reverse else id) <$> sign_of_prod (known_signs.map option.iget) in
  match prod_sign with
  | some ks :=
    let pfe := sign_proof.adhoc e ks (aux_sign_infer_tac e pf ks)
--(do s ← tactic.pp e, sf ← tactic.pp ks, tactic.fail $ "unfinished adhoc -- infer-expr-sign-data-aux: 0 "  ++ sf.to_string ++ s.to_string) 
in
    return $ some ⟨e, ⟨_, pfe⟩⟩
  | none := return none
  end

/--
 Infers the sign of an expression when the sign of subexpressions is known.
-/
meta def infer_expr_sign_data (e : expr) (pf : prod_form) : mul_state (option Σ e', sign_data e') :=
do sds ← pf.exps.keys.mmap (sign_of_term pf),
   let known_signs := (sds.bfilter option.is_some),
   if pf.exps.keys.length = known_signs.length then
    infer_expr_sign_data_aux e pf known_signs
   else return none

/--
 Tries to infer sign data of variables in expression when the sign of the whole expression is known.
-/
meta def get_unknown_sign_data (e : expr) (sd : option (sign_data e)) (pf : prod_form) : mul_state (option Σ e', sign_data e') :=
do sds ← pf.exps.keys.mmap (sign_of_term pf),
   let known_signs := (sds.bfilter option.is_some),
   let num_vars := pf.exps.keys.length,
   if (known_signs.length = num_vars - 1) && sd.is_some then
     let prod_sign := 
      (if pf.coeff < 0 then gen_comp.reverse else id) <$> sign_of_prod (known_signs.map option.iget) in
     match prod_sign with
     | some ks :=
       match get_remaining_sign ks sd.iget.c with
       | some c' := 
         let i := sds.index_of none,
             e := pf.exps.keys.inth i,
             pfe := sign_proof.adhoc e c' (tactic.fail "unfinished adhoc -- get-unknown-sign-data") in
         return $ some ⟨e, ⟨_, pfe⟩⟩
         -- e has sign ks
       | none := return none
       end
     | none := return none
     end
   else if known_signs.length = num_vars then
     /-let prod_sign := 
      (if pf.coeff < 0 then gen_comp.reverse else id) <$> sign_of_prod (known_signs.map option.iget) in
     match prod_sign with
     | some ks :=
       if sd.c.implies ks then return none else
         let pfe := sign_proof.adhoc e ks (tactic.fail "unfinished adhoc") in
         return $ some ⟨e, ⟨_, pfe⟩⟩
     | none := return none
     end-/
     infer_expr_sign_data_aux e pf known_signs
   else return none

end sign_inference

section sfcd_to_ineq


/- -- assumes lhs < rhs as exprs. cl*lhs + cr*rhs R 0 ==> ineq_data
private meta def mk_ineq_data_of_lhs_rhs (lhs rhs : expr) (cl cr : ℚ) (c : comp) {s} (pf : sum_form_proof s) :
        Σ l r, ineq_data l r :=
let c' := if cl > 0 then c else c.reverse,
    iq := ineq.of_comp_and_slope (c') (slope.some (-cr/cl)) in
⟨lhs, rhs, ⟨iq, ineq_proof.of_sum_form_proof lhs rhs iq pf⟩⟩ --_ _ _ (iq.to_expr lhs rhs pf)⟩⟩ -- TODO
--⟨lhs, rhs, ⟨iq, ineq_proof.hyp _ _ _ ```(0)⟩⟩ -- TODO

-/

--TODO
-- this should be split into two parts, one which makes the ineq and one which proves it.


-- assumes lhs > rhs as exprs. 1 R coeff* lhs^el * rhs^er ==> ineq_data
private meta def mk_ineq_of_lhs_rhs (coeff : ℚ) (lhs rhs : expr) (el er : ℤ) (c : spec_comp) :
        mul_state (option ineq) :=
do ⟨cmpl, _⟩ ← si lhs, ⟨cmpr, _⟩ ← si rhs,
   if cmpl = gen_comp.gt then -- lhs^(-el) c coeff*rhs^(er)
     if (el = -1) && (er = 1) then return $ some $ ineq.of_comp_and_slope c.to_comp (slope.some coeff)
     else if (el = 1) && (er = -1) then return $ some $ ineq.of_comp_and_slope c.to_comp.reverse (slope.some (1/coeff))
     else return none
   else  -- lhs^(-el) 
     return none -- TODO

-- assumes lhs > rhs as exprs. 1 = coeff* lhs^el * rhs^er ==> eq_data (coeff)
-- TODO
private meta def mk_eq_of_lhs_rhs (coeff : ℚ) (lhs rhs : expr) (el er : ℤ) :
        mul_state (option ℚ) :=
do ⟨cmpl, _⟩ ← si lhs, ⟨cmpr, _⟩ ← si rhs,
--   if cmpl = gen_comp.gt then -- lhs^(-el) c coeff*rhs^(er)
     if (el = -1) && (er = 1) then return $ some coeff
     else if (el = 1) && (er = -1) then return $ some (1/coeff)
     else return none
--   else  -- lhs^(-el) 
--     return none -- TODO


section
open tactic
--#check @op_of_one_op_pos
meta def mk_ineq_proof_of_lhs_rhs /-(coeff : ℚ)-/ (lhs /-rhs-/ : expr) (el er : ℤ) /-(c : spec_comp)-/ {s} (pf : prod_form_proof s) : mul_state (tactic expr) :=
do sdl ← si lhs,
match sdl with
| ⟨gen_comp.gt, pf'⟩ := return $ 
   do tactic.trace "in mk_ineq_proof_of_lhs_rhs 1", trace pf, pfr ← pf.reconstruct, trace "1", pfr' ← pf'.reconstruct, trace "reconstructed::", infer_type pfr >>= trace, infer_type pfr' >>= trace,
      tpr ← tactic.mk_mapp ``op_of_one_op_pos [none, none, none, none, none, some pfr', none, none, some pfr],
      if (el = 1) && (er = -1) then tactic.mk_app ``op_of_inv_op_inv_pow [tpr]
      else if (el = -1) && (er = 1) then tactic.mk_app ``op_of_op_pow [tpr]
      else fail "can't handle non-one exponents yet" 
| ⟨gen_comp.lt, pf'⟩ := return $ 
   do tactic.trace "in mk_ineq_proof_of_lhs_rhs 2", pfr ← pf.reconstruct, trace "reconstructed::", infer_type pfr >>= trace, pfr' ← pf'.reconstruct, 
      tactic.mk_mapp ``op_of_one_op_neg [none, none, none, none, none, some pfr', none, none, some pfr]
| _ := return $ tactic.fail "mk_ineq_proof_of_lhs_rhs failed, no sign info for lhs"
end

end

-- assumes lhs > rhs as exprs. 1 R coeff* lhs^el * rhs^er ==> ineq_data
private meta def mk_ineq_data_of_lhs_rhs (coeff : ℚ) (lhs rhs : expr) (el er : ℤ) (c : spec_comp) {s} (pf : prod_form_proof s) :
        mul_state (option Σ l r, ineq_data l r) :=
do iq ← mk_ineq_of_lhs_rhs coeff lhs rhs el er c,
   match iq with
   | none := return none
   | some id := do tac ← mk_ineq_proof_of_lhs_rhs lhs el er pf,
      return $ some ⟨lhs, rhs, ⟨id, ineq_proof.adhoc _ _ id $ 
         tac
--       do t ← id.to_type lhs rhs, tactic.trace "sorrying", tactic.trace t, tactic.to_expr ``(sorry : %%t) --tactic.fail "mk_ineq_data not implemented"
      ⟩⟩ 
   end

-- assumes lhs > rhs as exprs. 1 = coeff* lhs^el * rhs^er ==> eq_data
-- TODO
private meta def mk_eq_data_of_lhs_rhs (coeff : ℚ) (lhs rhs : expr) (el er : ℤ) {s} (pf : prod_form_proof s) :
        mul_state (option Σ l r, eq_data l r) :=
do eqc ← mk_eq_of_lhs_rhs coeff lhs rhs el er,
   match eqc with
   | none := return none
   | some c := do /-tac ← mk_ineq_proof_of_lhs_rhs lhs el er pf,-/ return none
     -- return $ some ⟨lhs, rhs, ⟨id, ineq_proof.adhoc _ _ id $ 
       --  tac
--       do t ← id.to_type lhs rhs, tactic.trace "sorrying", tactic.trace t, tactic.to_expr ``(sorry : %%t) --tactic.fail "mk_ineq_data not implemented"
--      ⟩⟩ -- todo
   end
#print ineq_data
#print ineq

-- pf proves 1 c coeff*e^(-1)
-- returns a proof of 1 c' (1/coeff) * e

-- 1 c coeff * e^exp
private meta def mk_ineq_data_of_single_cmp (coeff : ℚ) (e : expr) (exp : ℤ) (c : spec_comp) {s} (pf : prod_form_proof s) :
        mul_state (option Σ lhs rhs, ineq_data lhs rhs) :=
if exp = 1 then
  let inq := ineq.of_comp_and_slope c.to_comp (slope.some coeff),
      id : ineq_data `(1 : ℚ) e := ⟨inq, ineq_proof.adhoc _ _ _ (do pf' ← pf.reconstruct, tactic.mk_mapp ``one_op_of_op [none, none, none, none, pf'])⟩ in--(tactic.fail "mk_ineq_data_of_single_cmp not implemented")⟩ in
  return $ some ⟨_, _, id⟩
else if exp = -1 then 
  let inq := ineq.of_comp_and_slope c.to_comp.reverse (slope.some coeff).invert,
      id : ineq_data `(1 : ℚ) e := ⟨inq, ineq_proof.adhoc _ _ _ (do pf' ← pf.reconstruct, tactic.mk_mapp ``one_op_of_op_inv [none, none, none, none, pf'])⟩ in--(tactic.fail "mk_ineq_data_of_single_cmp not implemented")⟩ in
  return $ some ⟨_, _, id⟩
else -- TODO
return none


private meta def mk_eq_data_of_single_cmp (coeff : ℚ) (e : expr) (exp : ℤ) {s} (pf : prod_form_proof s) :
        mul_state (option Σ lhs rhs, eq_data lhs rhs) :=
if exp = 1 then
  let id : eq_data `(1 : ℚ) e := ⟨coeff, eq_proof.adhoc _ _ _ (tactic.fail "mk_eq_data_of_single_cmp not implemented")⟩ in
  return $ some ⟨_, _, id⟩
else -- TODO
return none

-- we need a proof constructor for ineq and eq
meta def prod_form_comp_data.to_ineq_data : prod_form_comp_data → mul_state (option (Σ lhs rhs, ineq_data lhs rhs))
| ⟨⟨_, spec_comp.eq⟩, _, _⟩ := return none
| ⟨⟨⟨coeff, exps⟩, c⟩, prf, _⟩ := 
  match exps.to_list with
  | [(rhs, cr), (lhs, cl)] := 
    if rhs.lt lhs then  mk_ineq_data_of_lhs_rhs coeff lhs rhs cl cr c prf
    else mk_ineq_data_of_lhs_rhs coeff rhs lhs cr cl c prf
  | [(rhs, cr)] := mk_ineq_data_of_single_cmp coeff rhs cr c prf
  | _ := return none
  end

meta def prod_form_comp_data.to_eq_data : prod_form_comp_data → mul_state (option (Σ lhs rhs, eq_data lhs rhs))
| ⟨⟨⟨coeff, exps⟩, spec_comp.eq⟩, prf, _⟩ :=
  match exps.to_list with
  | [(rhs, cr), (lhs, cl)] :=     if rhs.lt lhs then  mk_eq_data_of_lhs_rhs coeff lhs rhs cl cr prf
    else mk_eq_data_of_lhs_rhs coeff rhs lhs cr cl prf
  | [(rhs, cr)] := mk_eq_data_of_single_cmp coeff rhs cr prf
  | _ := return none
  end
| _ := return none 



end sfcd_to_ineq

--meta structure sign_storage :=
--(signs : hash_map expr sign_info)

--private meta def inh_sp (e : expr) : inhabited (sign_proof e gen_comp.ne) := ⟨sign_proof.adhoc _ _ (tactic.failed)⟩

meta def ne_pf_of_si {e : expr} (sd : sign_data e) : sign_proof e gen_comp.ne :=
sign_proof.diseq_of_strict_ineq sd.prf

meta def find_cancelled (pf1 pf2 : prod_form) : list expr :=
pf1.exps.fold [] (λ t exp l, if exp + pf2.get_exp t = 0 then t::l else l)

meta def ne_proofs_of_cancelled (pf1 pf2 : prod_form) : mul_state (list Σ e : expr, sign_proof e gen_comp.ne) :=
(find_cancelled pf1 pf2).mmap (λ e, do sd ← si e, return ⟨e, ne_pf_of_si sd⟩) 

meta def prod_form_proof.pfc {pfc} : prod_form_proof pfc → prod_form_comp := λ _, pfc

-- assumes the exponent of pvt in both is nonzero. Does not enforce elim_list preservation
meta def prod_form_comp_data.elim_expr_aux : prod_form_comp_data → prod_form_comp_data → expr → 
     mul_state (option prod_form_comp_data)
| ⟨⟨pf1, comp1⟩, prf1, elim_list1⟩ ⟨⟨pf2, comp2⟩, prf2, elim_list2⟩ pvt :=
let exp1 := pf1.get_exp pvt,
    exp2 := pf2.get_exp pvt in
if exp1 * exp2 < 0 then
 let npow : int := nat.lcm exp1.nat_abs exp2.nat_abs,
     pf1p := prod_form_proof.of_pow (npow/(abs exp1)) prf1,
     pf2p := prod_form_proof.of_pow (npow/(abs exp2)) prf2 in do
 neprfs ← ne_proofs_of_cancelled pf1p.pfc.pf pf2p.pfc.pf,
 let nprf := prod_form_proof.of_mul pf1p pf2p neprfs in
 return $ some ⟨_, nprf, (rb_set.union elim_list1 elim_list2).insert pvt⟩
else if comp1 = spec_comp.eq then
 let pf1p := prod_form_proof.of_pow (-1) prf1 in
 prod_form_comp_data.elim_expr_aux ⟨_, pf1p, elim_list1⟩ ⟨_, prf2, elim_list2⟩ pvt
else if comp2 = spec_comp.eq then
 let pf2p := prod_form_proof.of_pow (-1) prf2 in
 prod_form_comp_data.elim_expr_aux ⟨_, prf1, elim_list1⟩ ⟨_, pf2p, elim_list2⟩ pvt
else return none

meta def prod_form_comp_data.elim_expr (pfcd1 pfcd2 : prod_form_comp_data) (pvt : expr) : 
     mul_state (option prod_form_comp_data) :=
if pfcd1.pfc.pf.get_exp pvt = 0 then return $ some ⟨pfcd1.pfc, pfcd1.prf, pfcd1.elim_list.insert pvt⟩ 
else if pfcd2.pfc.pf.get_exp pvt = 0 then return $ none
else prod_form_comp_data.elim_expr_aux pfcd1 pfcd2 pvt

private meta def compare_coeffs (sf1 sf2 : prod_form) (h : expr) : ordering :=
let c1 := sf1.get_exp h, c2 := sf2.get_exp h in
if c1 < c2 then ordering.lt else if c2 < c1 then ordering.gt else ordering.eq


private meta def compare_coeff_lists (sf1 sf2 : prod_form) : list expr → list expr → ordering
| [] [] := ordering.eq
| [] _ := ordering.lt
| _ [] := ordering.gt
| (h1::t1) (h2::t2) := 
   if h1 = h2 then let ccomp := compare_coeffs sf1 sf2 h1 in
     if ccomp = ordering.eq then compare_coeff_lists t1 t2 else ccomp
   else has_ordering.cmp h1 h2

meta def prod_form.order (sf1 sf2 : prod_form) : ordering :=
compare_coeff_lists sf1 sf2 sf1.exps.keys sf2.exps.keys


meta def prod_form_comp.order : prod_form_comp → prod_form_comp → ordering
| ⟨_, spec_comp.lt⟩ ⟨_, spec_comp.le⟩ := ordering.lt
| ⟨_, spec_comp.lt⟩ ⟨_, spec_comp.eq⟩ := ordering.lt
| ⟨_, spec_comp.le⟩ ⟨_, spec_comp.eq⟩ := ordering.lt
| ⟨sf1, _⟩ ⟨sf2, _⟩ := prod_form.order sf1 sf2 -- need to normalize!

-- TODO: do we need to take elim_vars into account for this order?
meta def prod_form_comp_data.order : prod_form_comp_data → prod_form_comp_data → ordering
| ⟨sfc1, _, _⟩ ⟨sfc2, _, _⟩ := sfc1.order sfc2

meta instance : has_ordering prod_form_comp_data := ⟨prod_form_comp_data.order⟩


meta def prod_form_comp_data.elim_into (sfcd1 sfcd2 : prod_form_comp_data) (pvt : expr)
     (rv : rb_set prod_form_comp_data) : mul_state (rb_set prod_form_comp_data) :=
do elimd ← sfcd1.elim_expr sfcd2 pvt,
   match elimd with
   | none := return rv
   | some sfcd := return $ rv.insert sfcd
   end

private meta def check_elim_lists_aux (sfcd1 sfcd2 : prod_form_comp_data) : bool :=
sfcd1.vars.all (λ e, bnot (sfcd2.elim_list.contains e))

private meta def check_elim_lists (sfcd1 sfcd2 : prod_form_comp_data) : bool :=
check_elim_lists_aux sfcd1 sfcd2 && check_elim_lists_aux sfcd2 sfcd1

meta def prod_form_comp_data.needs_elim_against (sfcd1 sfcd2 : prod_form_comp_data) (e : expr) : bool :=
(check_elim_lists sfcd1 sfcd2) &&
 (((sfcd1.vars.append sfcd2.vars).filter (λ e' : expr, e'.lt e)).length ≤ 2)

namespace prod_form

/--
 Uses sfcd to eliminate the e from all comparisons in cmps, and adds the new comparisons to rv
-/
meta def elim_expr_from_comp_data_filtered (sfcd : prod_form_comp_data) (cmps : rb_set prod_form_comp_data) 
         (e : expr) (rv : rb_set prod_form_comp_data) : mul_state (rb_set prod_form_comp_data) :=
cmps.mfold rv (λ c rv', if sfcd.needs_elim_against c e then sfcd.elim_into c e rv' else return rv')


/--
 Performs all possible eliminations with sfcd on cmps. Returns a set of all new comps, NOT including the old ones.
-/
meta def new_exprs_from_comp_data_set (sfcd : prod_form_comp_data) (cmps : rb_set prod_form_comp_data) : mul_state (rb_set prod_form_comp_data) :=
sfcd.vars.mfoldr (λ e rv, elim_expr_from_comp_data_filtered sfcd cmps e rv) mk_rb_set

meta def elim_list_into_set : rb_set prod_form_comp_data → list prod_form_comp_data → mul_state (rb_set prod_form_comp_data)
| cmps [] := return (trace_val "elim_list_into_set []") >> return cmps
| cmps (sfcd::new_cmps) := return (trace_val "elim_list_into_set cons") >>
   if cmps.contains sfcd then elim_list_into_set cmps new_cmps else
   do new_gen ← new_exprs_from_comp_data_set sfcd cmps,--.keys
      let new_gen := new_gen.keys in 
      elim_list_into_set (cmps.insert sfcd) (new_cmps.append new_gen)

meta def elim_list_set (cmps : list prod_form_comp_data) (start : rb_set prod_form_comp_data := mk_rb_set) : mul_state (rb_set prod_form_comp_data) :=
elim_list_into_set start cmps

meta def elim_list (cmps : list prod_form_comp_data) : mul_state (list prod_form_comp_data) :=
rb_set.to_list <$> elim_list_into_set mk_rb_set cmps

end prod_form
open prod_form


section bb_process

meta def mk_eqs_of_expr_prod_form_pair : expr × prod_form → prod_form_comp_data
| (e, sf) := 
  let sf' := sf * (prod_form.of_expr e).pow (-1) in
  ⟨⟨sf', spec_comp.eq⟩, prod_form_proof.of_expr_def e sf', mk_rb_set⟩

meta def pfcd_of_ineq_data {lhs rhs} (id : ineq_data lhs rhs) : polya_state (option prod_form_comp_data) :=
do sdl ← get_sign_info lhs, sdr ← get_sign_info rhs,
match sdl, sdr with
| some sil, some sir := 
  if sil.c.is_strict && sir.c.is_strict then
    return $ some $ prod_form_comp_data.of_ineq_data id sil.prf sir.prf
  else return none
| _, _ := return (trace_val ("no sign_info", lhs, rhs)) >> return none
end

-- TODO
meta def pfcd_of_eq_data {lhs rhs} (ed : eq_data lhs rhs) : polya_state (option prod_form_comp_data) :=
do sdl ← get_sign_info lhs, sdr ← get_sign_info rhs,
match sdl, sdr with
| some sil, some sir := 
  if sil.c.is_strict && sir.c.is_strict then
    return $ some $ prod_form_comp_data.of_eq_data ed sil.prf.diseq_of_strict_ineq
  else return none
| _, _ := return none
end

private meta def mk_pfcd_list : polya_state (list prod_form_comp_data) :=
do il ← trace_val <$> get_ineq_list, el ← trace_val <$> get_eq_list, dfs ← trace_val <$> get_mul_defs,
   il' ← trace_val <$> reduce_option_list <$> il.mmap (λ ⟨_, _, id⟩, pfcd_of_ineq_data id),
   el' ← trace_val <$> reduce_option_list <$> el.mmap (λ ⟨_, _, ed⟩, pfcd_of_eq_data ed),
   let dfs' := trace_val $ dfs.map mk_eqs_of_expr_prod_form_pair in -- TODO: does this filter ones without sign info?
   return $ ((il'.append el').append dfs').qsort (λ a b, if has_ordering.cmp a b = ordering.lt then tt else ff)

private meta def mk_signed_pfcd_list : polya_state (list (prod_form × Σ e, option (sign_data e))) :=
do mds ← get_mul_defs,
   mds' : list (prod_form × Σ e, sign_info e) ← mds.mmap (λ e_pf, do sd ← get_sign_info e_pf.1, return (e_pf.2, sigma.mk e_pf.1 sd)),
   return mds'
/-   return $ reduce_option_list $ mds'.map 
    (λ pf_sig, 
     match pf_sig.2 with
     | ⟨e, some sd⟩ := some ⟨pf_sig.1, ⟨e, sd⟩⟩
     | ⟨_, none⟩ := none
     end)-/

private meta def mk_sign_data_list : list expr → polya_state (list (Σ e, sign_data e))
| [] := return []
| (h::t) := 
  do si ← get_sign_info h,
  match si with
  | some sd := list.cons ⟨h, sd⟩ <$> mk_sign_data_list t
  | none := mk_sign_data_list t
  end

private meta def mk_mul_state : polya_state (hash_map expr (λ e, sign_data e)) :=
do l ← get_expr_list,
   sds ← mk_sign_data_list l,
   return $ hash_map.of_list sds expr.hash

private meta def gather_new_sign_info_pass_one : polya_state (list Σ e, sign_data e) :=
do  dfs ← mk_signed_pfcd_list,
    ms ← mk_mul_state,
    return $ reduce_option_list $ (dfs.mmap (λ pf_sig : prod_form × Σ e, option (sign_data e), get_unknown_sign_data pf_sig.2.1 pf_sig.2.2 pf_sig.1) ms).1
    
/-
the second pass was originally to handle transitivity, but we can assume this is handled in the additive module

private meta def find_sign_proof_by_trans_eq {unsigned signed : expr} (ed : eq_data unsigned signed) (sd : sign_data signed) : option (Σ e', sign_data e') :=
none

-- assumes sd is not an eq or diseq
private meta def find_sign_proof_by_trans_ineq {unsigned signed : expr} (id : ineq_data unsigned signed) (sd : sign_data signed) : option (Σ e', sign_data e') :=
let su := id.inq.to_comp,
    ss := sd.c.to_comp in
if su.dir = ss.dir && (su.is_strict || ss.is_strict) 
--: ineq_data unsigned signed → sign_data signed → option (Σ e', sign_data e')
--| ⟨inq, prf⟩ ⟨c, prfs⟩ := none
--(id : ineq_data unsigned signed) (sd : sign_data signed) : option (Σ e', sign_data e') :=
--none


meta def find_sign_proof_by_trans (e : expr) : list expr → polya_state (option (Σ e', sign_data e'))
| [] := return none
| (h::t) := 
  do s ← get_sign_info h, ii ← get_ineqs e h,
  match ii, s with
  | _, none := return none
  | ineq_info.no_comps, _ := return none
  | ineq_info.equal ed, some sd := 
     match find_sign_proof_by_trans_eq ed sd with
     | some p := return $ some p
     | none := find_sign_proof_by_trans t
     end
  | ineq_info.one_comp id, some sd :=
    match find_sign_proof_by_trans_ineq id sd with
     | some p := return $ some p
     | none := find_sign_proof_by_trans t
     end
  | ineq_info.two_comps id1 id2, some sd := 
    let o := find_sign_proof_by_trans_ineq id1 sd <|> find_sign_proof_by_trans_ineq id2 sd in
    match o with
     | some p := return $ some p
     | none := find_sign_proof_by_trans t
     end
  end

meta def infer_sign_from_transitivity (e : expr) : polya_state (option (Σ e', sign_data e')) :=
do exs ← get_weak_signed_exprs,
   find_sign_proof_by_trans e exs

private meta def gather_new_sign_info_pass_two : polya_state (list Σ e, sign_data e) :=
do use ← get_unsigned_exprs,
   ose ← use.mmap infer_sign_from_transitivity,
   return $ reduce_option_list ose
-/


lemma rat_pow_pos_of_pos {q : ℚ} (h : q > 0) (z : ℤ) : rat.pow q z > 0 := sorry 

lemma rat_pow_pos_of_neg_even {q : ℚ} (h : q < 0) {z : ℤ} (hz1 : z > 0) (hz2 : z % 2 = 0) : rat.pow q z > 0 := sorry 

lemma rat_pow_neg_of_neg_odd {q : ℚ} (h : q < 0) {z : ℤ} (hz1 : z > 0) (hz2 : z % 2 = 1) : rat.pow q z < 0 := sorry 

lemma rat_pow_nonneg_of_nonneg {q : ℚ} (h : q ≥ 0) (z : ℤ) : rat.pow q z ≥ 0 := sorry 

lemma rat_pow_nonneg_of_nonpos_even {q : ℚ} (h : q ≤ 0) {z : ℤ} (hz1 : z > 0) (hz2 : z % 2 = 0) : rat.pow q z ≥ 0 := sorry 

lemma rat_pow_nonpos_of_nonpos_odd {q : ℚ} (h : q ≤ 0) {z : ℤ} (hz1 : z > 0) (hz2 : z % 2 = 1) : rat.pow q z ≤ 0 := sorry 

lemma rat_pow_zero_of_zero {q : ℚ} (h : q = 0) (z : ℤ) : rat.pow q z = 0 := sorry

lemma rat_pow_zero (q : ℚ) : rat.pow q 0 = 0 := sorry

lemma rat_pow_pos_of_ne_even {q : ℚ} (h : q ≠ 0) {z : ℤ} (hz1 : z > 0) (hz2 : z % 2 = 0) : rat.pow q z > 0 := sorry

lemma rat_pow_ne_of_ne_odd {q : ℚ} (h : q ≠ 0) {z : ℤ} (hz1 : z > 0) (hz2 : z % 2 = 1) : rat.pow q z ≠ 0 := sorry

lemma rat_pow_nonneg_of_pos_even (q : ℚ) {z : ℤ} (hz1 : z > 0) (hz2 : z % 2 = 0) : rat.pow q z ≥ 0 := sorry

-- given a proof that e > 0, proves that rat.pow e z > 0.
private meta def pos_pow_tac (pf : expr) (z : ℤ) : tactic expr :=
tactic.mk_app ``rat_pow_pos_of_pos [pf, `(z)]

private meta def nonneg_pow_tac (pf : expr) (z : ℤ) : tactic expr :=
tactic.mk_app ``rat_pow_nonneg_of_nonneg [pf, `(z)]

-- given a proof that e < 0, proves that rat.pow e z has the right sign
private meta def neg_pow_tac (e pf : expr) (z : ℤ) : tactic expr :=
if z > 0 then
  do zpp ← mk_int_sign_pf z, zmp ← mk_int_mod_pf z,--tactic.to_expr ``(by gen_comp_val : %%(reflect z) > 0),
     tactic.mk_app (if z % 2 = 0 then ``rat_pow_pos_of_neg_even else ``rat_pow_neg_of_neg_odd) [pf, zpp, zmp] 
else if z = 0 then tactic.mk_app ``rat_pow_zero [e]
else tactic.fail "neg_pow_tac failed, neg expr to neg power"

-- given a proof that e ≤ 0, proves that rat.pow e z has the right sign
private meta def nonpos_pow_tac (e pf : expr) (z : ℤ) : tactic expr :=
if z > 0 then
  do zpp ← mk_int_sign_pf z, zmp ← mk_int_mod_pf z,--tactic.to_expr ``(by gen_comp_val : %%(reflect z) > 0),
     tactic.mk_app (if z % 2 = 0 then ``rat_pow_nonneg_of_nonpos_even else ``rat_pow_nonpos_of_nonpos_odd) [pf, zpp, zmp] 
else if z = 0 then tactic.mk_app ``rat_pow_zero [e]
else tactic.fail "neg_pow_tac failed, neg expr to neg power"

private meta def ne_pow_tac (e pf : expr) (z : ℤ) : tactic expr :=
if z > 0 then
  do zpp ← mk_int_sign_pf z, zmp ← mk_int_mod_pf z,--tactic.to_expr ``(by gen_comp_val : %%(reflect z) > 0),
     tactic.mk_app (if z % 2 = 0 then ``rat_pow_pos_of_ne_even else ``rat_pow_ne_of_ne_odd) [pf, zpp, zmp] 
else if z = 0 then tactic.mk_app ``rat_pow_zero [e]
else tactic.fail "neg_pow_tac failed, neg expr to neg power"

private meta def even_pow_tac (e : expr) (z : ℤ) : tactic expr :=
if z > 0 then 
   do zpp ← mk_int_sign_pf z, zmp ← mk_int_mod_pf z,
      tactic.mk_app ``rat_pow_nonneg_of_pos_even [e, zpp, zmp]
else if z = 0 then tactic.mk_app ``rat_pow_zero [e]
else tactic.fail "even_pow_tac failed, cannot handle neg power"

-- assumes pf is the prod form of e and has only one component
private meta def gather_new_sign_info_pass_two_aux (e : expr) (pf : prod_form) : polya_state $ option (Σ e', sign_data e') :=
match pf.exps.to_list with
| [(e', pow)] :=
  do si ← get_sign_info (trace_val ("e'", e')).2,
     match si with
     | some ⟨gen_comp.gt, pf⟩ := return $ some ⟨e, ⟨gen_comp.gt, sign_proof.adhoc _ _ (do pf' ← pf.reconstruct, pos_pow_tac pf' pow)⟩⟩
     | some ⟨gen_comp.ge, pf⟩ := return $ some ⟨e, ⟨gen_comp.ge, sign_proof.adhoc _ _ (do pf' ← pf.reconstruct, nonneg_pow_tac pf' pow)⟩⟩
     | some ⟨gen_comp.lt, pf⟩ := 
       if pow ≥ 0 then 
         let tac : tactic expr := do pf' ← pf.reconstruct, neg_pow_tac e' pf' pow in
         return $ some ⟨e, ⟨(if pow = 0 then gen_comp.eq else if pow % 2 = 0 then gen_comp.gt else gen_comp.lt), sign_proof.adhoc _ _ tac⟩⟩
       else return none
     | some ⟨gen_comp.le, pf⟩ := 
       if pow ≥ 0 then 
         let tac : tactic expr := do pf' ← pf.reconstruct, nonpos_pow_tac e' pf' pow in
         return $ some ⟨e, ⟨(if pow = 0 then gen_comp.eq else if pow % 2 = 0 then gen_comp.gt else gen_comp.lt), sign_proof.adhoc _ _ tac⟩⟩
       else return none
     | some ⟨gen_comp.eq, pf⟩ := return $ some ⟨e, ⟨gen_comp.eq, sign_proof.adhoc _ _ (do pf' ← pf.reconstruct, tactic.mk_app ``rat_pow_zero [pf', `(pow)])⟩⟩
     | some ⟨gen_comp.ne, pf⟩ := 
       if pow ≥ 0 then 
         let tac : tactic expr := do pf' ← pf.reconstruct, ne_pow_tac e' pf' pow in
         return $ some ⟨e, ⟨(if pow = 0 then gen_comp.eq else if pow % 2 = 0 then gen_comp.gt else gen_comp.ne), sign_proof.adhoc _ _ tac⟩⟩
       else return none
     | none := 
       if (pow ≥ 0) && (pow % 2 = 0) then 
          return $ some ⟨e, ⟨if pow = 0 then gen_comp.eq else gen_comp.ge, sign_proof.adhoc _ _ (even_pow_tac e' pow)⟩⟩
       else return none
     end
| _ := return none
end

-- get sign info for power exprs
private meta def gather_new_sign_info_pass_two : polya_state (list Σ e, sign_data e) :=
do exs ← get_mul_defs,
   let exs := (trace_val ("of length one:", exs.filter (λ e, e.2.exps.size = 1))).2,
   reduce_option_list <$> exs.mmap (λ p, gather_new_sign_info_pass_two_aux p.1 p.2)

private meta def gather_new_sign_info : polya_state (list Σ e, sign_data e) :=
do l1 ← gather_new_sign_info_pass_one,
   l2 ← gather_new_sign_info_pass_two,
   return $ l1.append ((trace_val ("THIS IS L2", l2)).2)

private meta def mk_ineq_list (cmps : list prod_form_comp_data) : mul_state (list Σ lhs rhs, ineq_data lhs rhs) :=
do il ← cmps.mmap (λ pfcd, pfcd.to_ineq_data),
   return $ reduce_option_list il

private meta def mk_eq_list (cmps : list prod_form_comp_data) : mul_state (list Σ lhs rhs, eq_data lhs rhs) :=
do il ← cmps.mmap (λ pfcd, pfcd.to_eq_data),
   return $ reduce_option_list il


private meta def mk_ineq_list_of_unelimed (cmps : list prod_form_comp_data) (start : rb_set prod_form_comp_data := mk_rb_set) : mul_state (rb_set prod_form_comp_data × list Σ lhs rhs, ineq_data lhs rhs) :=
do s ← prod_form.elim_list_set cmps start,
   l ← mk_ineq_list s.to_list,
   return (s, l)

meta def prod_form.add_new_ineqs (start : rb_set prod_form_comp_data := mk_rb_set) : polya_state (rb_set prod_form_comp_data) :=
do --new_sign_info ← gather_new_sign_info,
   --new_sign_info.mmap (λ sig, add_sign sig.2),
   is_contr ← contr_found,
   if is_contr then return start else do
   gather_new_sign_info >>= list.mmap (λ sig, add_sign $ trace_val sig.2),
   sfcds ← trace_val <$> mk_pfcd_list,
   ms ← mk_mul_state,
   let ((pfcs, ineqs), _) := mk_ineq_list_of_unelimed sfcds start ms,
   monad.mapm' 
    (λ s : Σ lhs rhs, ineq_data lhs rhs, add_ineq s.2.2)
    ineqs,
   return pfcs -- TODO: FIX RETURN 

end bb_process

end polya

#exit


#exit
section tests
#print instances reflected
--set_option pp.all true
#check `(ℚ) 

variables x y z : ℚ
/-meta def x' : expr := `(x)
meta def y' : expr := `(y)
meta def z' : expr := `(z)-/


open tactic
#print declaration
#check reducibility_hints
include x y z
def aux : ℕ := by do x ← get_local `x, 
match x with
| expr.local_const nm ppnm bi tp :=
 (add_decl $ declaration.defn `x' [] `(expr) `(expr.local_const nm ppnm bi tp) reducibility_hints.abbrev ff) >> apply ↑`(0)
| _ := apply ↑`(0)
end

open tactic polya rb_map
meta def e1 : sum_form := of_list [(x', 3), (y', 2), (z', 1)] -- 3x + 2y + z
meta def e2 : sum_form := of_list [(x', -2), (y',1/2)]
meta def e3 : sum_form := of_list [(y',-5), (z', 4)]
meta def e4 : sum_form := of_list [(x', 10), (y',-1)]
meta def e5 : sum_form := of_list [(z', 1), (y',1)]
meta def e6 : sum_form := of_list [(z', 1)]

meta def c1 : sum_form_comp := ⟨e1, spec_comp.le⟩ -- 3x + 2y + z ≤ 0
meta def c2 : sum_form_comp := ⟨e2.negate, spec_comp.lt⟩
meta def c3 : sum_form_comp := ⟨e3.negate, spec_comp.le⟩
meta def c4 : sum_form_comp := ⟨e4, spec_comp.eq⟩
meta def c5 : sum_form_comp := ⟨e5.negate, spec_comp.lt⟩
meta def c6 : sum_form_comp := ⟨e6, spec_comp.lt⟩

meta def d1 : sum_form_comp_data := ⟨c1, sum_form_proof.fake _, mk_rb_set⟩
meta def d2 : sum_form_comp_data := ⟨c2, sum_form_proof.fake _, mk_rb_set⟩
meta def d3 : sum_form_comp_data := ⟨c3, sum_form_proof.fake _, mk_rb_set⟩
meta def d4 : sum_form_comp_data := ⟨c4, sum_form_proof.fake _, mk_rb_set⟩
meta def d5 : sum_form_comp_data := ⟨c5, sum_form_proof.fake _, mk_rb_set⟩
meta def d6 : sum_form_comp_data := ⟨c6, sum_form_proof.fake _, mk_rb_set⟩

#eval is_inconsistent_list [d1, d3, d5, d6]

run_cmd trace $ d1.elim_expr d2 y'

run_cmd trace $ 
elim_expr_from_comp_data_list 
 (elim_expr_from_comp_data_list [d1, d3,  d5, d6] x')
  y'

run_cmd trace $ 
elim_expr_from_comp_data_list
 (elim_expr_from_comp_data_list 
  (elim_expr_from_comp_data_list [d1, d3,  d5, d6] x')
   y')
  z'


run_cmd trace $
elim_list [d4, d5, d6]


run_cmd trace $
elim_list  [d1, d3, d5] --[d1, d3,  d5, d6]

end tests
