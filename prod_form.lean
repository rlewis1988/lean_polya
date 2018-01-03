import .datatypes .blackboard .proof_reconstruction .reconstruction_theorems .radicals .proof_trace

-- TODO: maybe more of this can move to datatypes

namespace polya

meta def approx_prec := 100


private meta def round_rat_to_prec_over (q : ℚ) (prec : ℕ) : ℚ :=
let z' := ((q.num.nat_abs*prec)/q.denom) + 1 in
rat.mk_nat (if q.num > 0 then z' else -z') prec

-- if pf is an inequality, returns a new, implied inequality where the denominator of coeff is at most prec
meta def prod_form_comp_data.round (pfcd : prod_form_comp_data) (prec : ℕ) : prod_form_comp_data :=
if (pfcd.pfc.pf.coeff.denom ≤ prec) || (pfcd.pfc.c = spec_comp.eq) then pfcd
else let ncoeff := round_rat_to_prec_over pfcd.pfc.pf.coeff prec in
⟨{pfcd.pfc with pf := {pfcd.pfc.pf with coeff := ncoeff}}, prod_form_proof.adhoc _ pfcd.prf.sketch (tactic.fail "pfcd.round not implemented yet"), pfcd.elim_list ⟩



meta def mul_state := state (hash_map expr (λ e, sign_data e) × hash_map expr (λ e, ineq_info e rat_one))
meta instance mul_state.monad : monad mul_state := state.monad _
private meta def inh_sd (e : expr) : inhabited (sign_data e) := ⟨⟨gen_comp.ne, sign_proof.adhoc _ _ (tactic.failed) (tactic.failed)⟩⟩
local attribute [instance] inh_sd

private meta def si (e : expr) : mul_state (sign_data e) :=
λ hm, (hm.1.find' e, hm)

private meta def si' (e : expr) : mul_state (option (sign_data e)) :=
λ hm, (hm.1.find e, hm)

private meta def oi (e : expr) : mul_state (ineq_info e rat_one) :=
λ hm, (/-trace_val $ -/ hm.2.find' e, hm)

-- returns true if the mul_state implies coeff*e c 1
private meta def implies_one_comp (coeff : ℚ) (e : expr) (c : comp) : mul_state bool :=
do ii ← oi e,
   return $ ii.implies_ineq $ ineq.of_comp_and_slope c (slope.some coeff)


private meta def find_comp {lhs rhs} (ii : ineq_info lhs rhs) (m : ℚ) : option gen_comp :=
if ii.implies_eq m then
  some (gen_comp.eq)
else if ii.implies_ineq (ineq.of_comp_and_slope comp.ge (slope.some m)) then
   some (if ii.implies_ineq $ ineq.of_comp_and_slope comp.gt (slope.some m) then gen_comp.gt else gen_comp.ge)
else if ii.implies_ineq (ineq.of_comp_and_slope comp.le (slope.some m)) then
   some (if ii.implies_ineq $ ineq.of_comp_and_slope comp.lt (slope.some m) then gen_comp.lt else gen_comp.le)
else none

-- returns the known comparisons of e with 1 and -1
meta def oc (e : expr) : mul_state (option gen_comp × option gen_comp) :=
do ii ← oi e,
return (find_comp ii 1, find_comp ii (-1))

meta def is_ge_one (e : expr) : mul_state bool :=
do (c, _) ← oc e,
match c with
| some c' := return c'.is_greater_or_eq
| none := return ff
end

meta def is_le_one (e : expr) : mul_state bool :=
do (c, _) ← oc e,
match c with
| some c' := return c'.is_less_or_eq
| none := return ff
end

meta def is_le_neg_one (e : expr) : mul_state bool :=
do (_, c) ← oc e,
match c with
| some c' := return c'.is_less_or_eq
| none := return ff
end

meta def is_ge_neg_one (e : expr) : mul_state bool :=
do (_, c) ← oc e,
match c with
| some c' := return c'.is_greater_or_eq
| none := return ff
end

meta def is_pos_le_one (e : expr) : mul_state bool :=
do ⟨c, _⟩ ← si e,
match c with
| gen_comp.gt := is_le_one e --bnot <$> is_ge_one e
| _ := return ff
end

meta def is_neg_ge_neg_one (e : expr) : mul_state bool :=
do ⟨c, _⟩ ← si e,
match c with
| gen_comp.lt := is_ge_neg_one e-- bnot <$> is_le_neg_one e
| _ := return ff
end

private meta def all_signs : mul_state (hash_map expr sign_data) :=
λ hm, (hm.1, hm)

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

private meta def reduce_sig_opt_list {α} {β : α → Type} : list (Σ a : α, option (β a)) → list (Σ a : α, (β a))
| [] := []
| (⟨a, none⟩::t) := reduce_sig_opt_list t
| (⟨a, some b⟩::t) := ⟨a, b⟩::reduce_sig_opt_list t

private lemma aux_sign_infer_tac_lemma (P : Prop) : P := sorry

-- TODO
private meta def aux_sign_infer_tac (e : expr) (pf : prod_form) (sds : hash_map expr sign_data) (c : gen_comp) : tactic expr :=
let sds' : list ((Σ e, (sign_data e))) := reduce_sig_opt_list $ pf.exps.keys.map (λ e, sigma.mk e (sds.find e)) in
do --sds ← pf.exps.keys.mmap $ λ e, sigma.mk e <$> (si e),
   sds'.mmap (λ a, a.snd.prf.reconstruct),
   tp ← c.to_function e `(0 : ℚ),
   tactic.mk_app ``aux_sign_infer_tac_lemma [tp]

-- TODO : used when only one sign in the middle is unknown
-- proves e C 0 when pf is the prod form of whole
private meta def aux_sign_infer_tac_2 (e whole : expr) (sd : sign_data whole) (pf : prod_form)  (sds : hash_map expr sign_data)  (c : gen_comp) : tactic expr :=
let sds' : list ((Σ e, (sign_data e))) := reduce_sig_opt_list $ pf.exps.keys.map (λ e, sigma.mk e (sds.find e)) in
do --sds ← pf.exps.keys.mmap $ λ e, sigma.mk e <$> (si e),
   sds'.mmap (λ a, a.snd.prf.reconstruct),
   sd.prf.reconstruct,
   tp ← c.to_function e `(0 : ℚ),
   tactic.mk_app ``aux_sign_infer_tac_lemma [tp]


/--
 Assumes known_signs.length = pf.length
-/
meta def infer_expr_sign_data_aux (e : expr) (pf : prod_form) (known_signs : list (option gen_comp)) : mul_state (option Σ e', sign_data e') :=
  let prod_sign := 
    (if pf.coeff < 0 then gen_comp.reverse else id) <$> sign_of_prod (known_signs.map option.iget) in
  match prod_sign with
  | some ks :=
    do sis ← all_signs,
    let pfe  := sign_proof.adhoc e ks (do s ← format_sign e ks, return ⟨s, "inferred from other sign data", []⟩) (aux_sign_infer_tac e pf sis ks) in
--(do s ← tactic.pp e, sf ← tactic.pp ks, tactic.fail $ "unfinished adhoc -- infer-expr-sign-data-aux: 0 "  ++ sf.to_string ++ s.to_string) 
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

private meta def recheck_known_signs_aux (ks : list gen_comp) (es : gen_comp)  (flip_coeff : bool) (i : ℕ): option gen_comp :=
if i ≥ ks.length then none else
let ks' := ks.remove_nth i,
    prod_sign := (if flip_coeff then gen_comp.reverse else id) <$> sign_of_prod ks' in
match prod_sign with
| some sn := get_remaining_sign sn es
| none := none
end

/--
 if we know the sign of e and all of its components, recalculate the sign of each component to check.
-/
meta def recheck_known_signs (e : expr) (sd : option (sign_data e)) (pf : prod_form) (ks : list gen_comp) (flip_coeff : bool) : mul_state (list Σ e', sign_data e') :=
match sd with
| none := return []
| some ⟨es, p⟩ := reduce_option_list <$>
((list.upto ks.length).mmap $ λ i,
  match recheck_known_signs_aux ks es flip_coeff i with
  | some c := 
   do sis ← all_signs,
   let e' := pf.exps.keys.inth i,
   let pfe := sign_proof.adhoc e' c (do s ← format_sign e' c, return ⟨s, "inferred from other sign data", []⟩) (aux_sign_infer_tac_2 e' e ⟨es, p⟩ pf sis c),
   return $ some ⟨e', ⟨_, pfe⟩⟩
  | none := return none
  end)
end

/--
 Tries to infer sign data of variables in expression when the sign of the whole expression is known.
-/
meta def get_unknown_sign_data (e : expr) (sd : option (sign_data e)) (pf : prod_form) : mul_state (list Σ e', sign_data e') :=
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
         do sis ← all_signs,
         let i := sds.index_of none,
         let e' := pf.exps.keys.inth i,
         let sd' := sd.iget,
         let pfe := sign_proof.adhoc e' c' (do s ← format_sign e' c', return ⟨s, "inferred from other sign data", []⟩) (aux_sign_infer_tac_2 e' e sd' pf sis c'),
-- (tactic.fail "unfinished adhoc -- get-unknown-sign-data"),
         return $ [⟨e', ⟨_, pfe⟩⟩]
         -- e has sign ks
       | none := return []
       end
     | none := return []
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
     do k1 ← infer_expr_sign_data_aux e pf known_signs,
        k2 ← recheck_known_signs e sd pf (known_signs.map option.iget) (pf.coeff < 0),
        match k1 with
        | some k1' := return $ k1'::k2
        | none := return k2
        end
   else return []

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

-- assuming 1 r coeff*lhs^el*rhs^er, finds r' such that 1 r coeff*|lhs|^el*|rhs|^er
/-private meta def get_abs_val_comp (lhs rhs : expr) (el er : ℤ)  (coeff : ℚ) : spec_comp → mul_state comp 
| spec_comp.lt := _
| spec_comp.le := _
| spec_comp.eq := _
-/

-- is_junk_comp c lhss rhss checks to see if lhs c rhs is of the form pos > neg, neg < pos, etc
-- we can assume the gen_comps are strict.
private meta def is_junk_comp : comp → gen_comp → gen_comp → bool
| comp.gt gen_comp.gt gen_comp.lt := tt
| comp.ge gen_comp.gt gen_comp.lt := tt
| comp.le gen_comp.lt gen_comp.gt := tt
| comp.lt gen_comp.lt gen_comp.gt := tt
| _ _ _ := ff


-- none if can never lower. some tt if can always lower. some ff if can only lower by even number
private meta def can_lower (e : expr) (ei : ℤ) : mul_state (option bool) :=
do iplo ← is_pos_le_one e,
   if iplo then return $ some tt else  do
   ingno ← is_neg_ge_neg_one e,
   if ingno && (ei % 2 = 0) then return $ some ff else do
   ilno ← is_le_neg_one e,
   if ilno && (ei % 2 = 1) then return $ some ff
   else return none
   
private meta def can_raise (e : expr) (ei : ℤ) : mul_state (option bool) :=
do igo ← is_ge_one e,
   if igo then return $ some tt else  do
   ilno ← is_le_neg_one e,
   if ilno && (ei % 2 = 0) then return $ some ff else do
   ingno ← is_neg_ge_neg_one e,
   if ingno && (ei % 2 = 1) then return $ some ff
   else return none


private meta def can_change_aux (diff_even : bool) : option bool → bool 
| (some tt) := tt
| (some ff) := diff_even
| none := ff

private meta def can_change (ob : option bool) (el er : ℤ) : bool :=
can_change_aux ((el - er) % 2 = 0) ob

-- assuming cmpl and cmpr are the signs of lhs and rhs, tries to find el', er' such that lhs^el*rhs^er ≤ lhs^el'*rhs^er'
private meta def balance_coeffs : expr → expr → ℤ → ℤ → mul_state (list (ℤ × ℤ)) | lhs rhs el er:=
if el = (/-trace_val-/ ("el, -er", lhs, rhs, el, -er)).2.2.2.2 then return $ [(el, er)] else
if (/-trace_val-/ ("el.nat_abs", el.nat_abs)).2 ≤ er.nat_abs then 
  do cll ← /-trace_val <$> -/can_lower lhs el, crl ← /-trace_val <$>-/ can_raise lhs el, clr ← /-trace_val <$> -/can_lower rhs er, crr ← /-trace_val <$>-/ can_raise rhs er,
  return $ 
   if (el < 0) && (er > 0) then 
    (guard (can_change clr el er) >> return (el, -el)) <|> (guard (can_change cll el er) >> return (-er, er))
   else if (el > 0) && (er < 0) then
    (guard (can_change crr el er) >> return (el, -el)) <|> (guard (can_change crl el er) >> return (-er, er))
   else if (el > 0) && (er > 0) then
    (guard (can_change clr el er) >> return (el, -el)) <|> (guard (can_change cll el er) >> return (-er, er))
   else if (el < 0) && (er < 0) then
    (guard (can_change crr el er) >> return (el, -el)) <|> (guard (can_change crl el er) >> return (-er, er))
  else []
else do pro ← balance_coeffs rhs lhs er el,
return $ pro.map (λ p, (p.2, p.1))

/-return $ match clr, crl with
| some br, some bl := if br then el else if (er - el) % 2 = 0 then el else if bl then er else none
| some br, none := if br || ((er - el)%2 = 0) then some el else none
| none, some bl := if bl || ((er - el)%2 = 0) then some er else none
| none, none := none
end
else do cll ← can_lower lhs el, crr ← can_raise rhs er,
return $ match cll, crr with
| some bl, some br := if bl then er else if (el - er) % 2 = 0 then er else if br then el else none
| some bl, none := if bl || ((el - er) % 2 = 0) then some er else none
| none, some br := if br || ((el - er) % 2 = 0) then some el else none
| none, none := none
end-/

-- assumes lhs > rhs as exprs, and el = -er. 1 R coeff*lhs^el*rhs^er ==> ineq
private meta def mk_ineq_of_balanced_lhs_rhs (coeff : ℚ) (lhs rhs : expr) (el er : ℤ) (c : spec_comp) : mul_state ineq :=
if (el % 2 = 0) && (coeff < 0) then -- todo: this is a contradiction
  do ⟨cmpl, _⟩ ← si lhs, return $ (/-trace_val-/ ("GOT A CONTRADICTION HERE", ineq.of_comp_and_slope cmpl.to_comp.reverse (slope.some 0))).2
else 
-- know: 1 c | (root coeff |el|)*lhs^(sign el)*rhs^(sign er) |
do ⟨cmpl, _⟩ ← si lhs, ⟨cmpr, _⟩ ← si rhs,
let coeff_comp := if coeff < 0 then comp.lt else comp.gt,
let prod_sign := (cmpl.to_comp.prod cmpr.to_comp).prod coeff_comp, 
let exp_val := el.nat_abs,
--if prod_sign.is_greater then
-- know: 1 c (root coeff exp_val)*lhs^(sign el)*rhs^(sign er)
  if cmpl.is_greater then -- lhs > 0
    let c' := c.to_comp,
      m  := (if prod_sign.is_greater then (1 : ℚ) else -1) * nth_root_approx approx_dir.over coeff exp_val approx_prec in return $ /-trace_val $-/ 
     if el < 0 then ineq.of_comp_and_slope c' (slope.some m)
    else ineq.of_comp_and_slope c'.reverse (slope.some (1/m))
  else -- x < 0
    let c' := c.to_comp.reverse,
        m  :=  (if prod_sign.is_greater then (1 : ℚ) else -1) * nth_root_approx approx_dir.under coeff exp_val approx_prec in return $ 
    if el < 0 then ineq.of_comp_and_slope c' (slope.some m) 
    else  ineq.of_comp_and_slope c'.reverse (slope.some (1/m))
/-else
-- know: 1 c -(root coeff exp_val)*lhs^(sign el)*rhs^(sign er)
  if cmpl.is_greater then -- lhs > 0
    let c' := c.to_comp, 
        m  := nth_root_approx approx_dir.over coeff exp_val approx_prec in
    if el < 0 then return $ ineq.of_comp_and_slope c' (slope.some (-m))
    else return $ ineq.of_comp_and_slope c'.reverse (slope.some (-1/m))
  else
    let c' := c.to_comp.reverse,
        m  := nth_root_approx approx_dir.under coeff exp_val approx_prec-/
/-if el < 0 then
 let c' := if cmpl.is_less then c.to_comp.reverse else c.to_comp,
     el' := -el in -- lhs^el' c' coeff * rhs^er
 -/

/-if (coeff < 0) && (exp % 2 = 0) then -- 1 ≤ neg. impossible. todo: create contr
  return none
else if coeff < 0 then
  return none
else if exp > 0 then
  let nexp := exp.nat_abs,
      coeff_root_approx := nth_root_approx'' approx_dir.over coeff nexp approx_prec in
  return none
else
  return none-/

-- assumes lhs > rhs as exprs. 1 R coeff* lhs^el * rhs^er ==> ineq_data
private meta def mk_ineq_of_lhs_rhs (coeff : ℚ) (lhs rhs : expr) (el er : ℤ) (c : spec_comp) :
        mul_state (list ineq) :=
do ⟨cmpl, _⟩ ← si lhs, ⟨cmpr, _⟩ ← si rhs,
let cmpl' := cmpl.pow el, 
let cmpr' := cmpr.pow er,
if is_junk_comp (if cmpl' = gen_comp.gt then c.to_comp else c.to_comp.reverse) cmpl' (if coeff > 0 then cmpr' else cmpr'.reverse) then return [] else
do ncs ← balance_coeffs lhs rhs el er,
   ncs.mmap $ λ p, do t ← mk_ineq_of_balanced_lhs_rhs coeff lhs rhs p.1 p.2 c, return (/-trace_val-/ ("got from mk_ineq", ncs.length, lhs, rhs, el, er, p.1, p.2, t)).2.2.2.2.2.2.2.2
/-match ncs with
| none := return none
| some (el', er') := some <$> mk_ineq_of_balanced_lhs_rhs coeff lhs rhs (trace_val ("calling mk_ineq", lhs, rhs, el, er, el')).2.2.2.2.2 er' c
end-/

-- assumes lhs > rhs as exprs. 1 R coeff* lhs^el * rhs^er ==> ineq_data
/-private meta def mk_ineq_of_lhs_rhs (coeff : ℚ) (lhs rhs : expr) (el er : ℤ) (c : spec_comp) :
        mul_state (option ineq) :=
do ⟨cmpl, _⟩ ← si lhs, ⟨cmpr, _⟩ ← si rhs,
let cmpl' := cmpl.pow el, 
let cmpr' := cmpr.pow er,
if is_junk_comp (if cmpl' = gen_comp.gt then c.to_comp else c.to_comp.reverse) cmpl' (if coeff > 0 then cmpr' else cmpr'.reverse) then return none else
   if cmpl = gen_comp.gt then -- lhs^(-el) c coeff*rhs^(er)
     if (el = -1) && (er = 1) then return $ some $ ineq.of_comp_and_slope c.to_comp (slope.some coeff)
     else if (el = 1) && (er = -1) then return $ some $ ineq.of_comp_and_slope c.to_comp.reverse (slope.some (1/coeff))
     else if (el = -1) && (er > 0) then -- lhs c coeff*rhs^er
       
     else return none
   else if cmpl = gen_comp.lt then -- lhs^(-el) -c coeff*rhs^(er)
     if (el = -1) && (er = 1) then return $ some $ ineq.of_comp_and_slope c.to_comp.reverse (slope.some coeff)
     else if (el = 1) && (er = -1) then return $ some $ ineq.of_comp_and_slope c.to_comp (slope.some (1/coeff))
     else if el = -1 then 
       return none
     else return none
   else return none-/

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

private lemma mk_ineq_proof_of_lhs_rhs_aux (P : Prop) {sp old : Prop} (p' : sp) (p : old) : P :=
sorry
#check @mk_ineq_proof_of_lhs_rhs_aux
open tactic
--#check @op_of_one_op_pos
meta def mk_ineq_proof_of_lhs_rhs /-(coeff : ℚ)-/ (lhs rhs : expr) (el er : ℤ) /-(c : spec_comp)-/ {s} (pf : prod_form_proof s) (iq : ineq) : mul_state (tactic expr) :=
do sdl ← si lhs,
match sdl with
| ⟨gen_comp.gt, pf'⟩ := do oil ← oi lhs, oir ← oi rhs, return $ 
   do --tactic.trace "in mk_ineq_proof_of_lhs_rhs 1", 
      pfr ← pf.reconstruct, trace "1", pfr' ← pf'.reconstruct, 
      --trace "reconstructed::", infer_type pfr >>= trace, infer_type pfr' >>= trace, trace pf,
      tpr ← tactic.mk_mapp ``op_of_one_op_pos [none, none, none, none, none, some pfr', none, none, some pfr],
      if (el = 1) && (er = -1) then tactic.mk_app ``op_of_inv_op_inv_pow [tpr]
      else if (el = -1) && (er = 1) then tactic.mk_app ``op_of_op_pow [tpr]
      else 
         do trace "know", infer_type pfr >>= trace, infer_type pfr' >>= trace,
          trace "wts", trace (lhs, rhs, iq), 
         tp ← iq.to_type lhs rhs,
         mk_mapp ``mk_ineq_proof_of_lhs_rhs_aux [tp, none, none, pfr', pfr]
--           fail $ "can't handle non-one exponents yet" ++ to_string el ++ " " ++ to_string er 
| ⟨gen_comp.lt, pf'⟩ := return $ 
   do --tactic.trace "in mk_ineq_proof_of_lhs_rhs 2",
      pfr ← pf.reconstruct,-- trace "reconstructed::", infer_type pfr >>= trace, 
      pfr' ← pf'.reconstruct, 
      tactic.mk_mapp ``op_of_one_op_neg [none, none, none, none, none, some pfr', none, none, some pfr]
| _ := return $ tactic.fail "mk_ineq_proof_of_lhs_rhs failed, no sign info for lhs"
end
end

meta def find_deps_of_pfp : Π {pfc}, prod_form_proof pfc → tactic (list proof_sketch)
| _ (prod_form_proof.of_ineq_proof id _ _) := do id' ← id.sketch, return [id']
| _ (prod_form_proof.of_eq_proof id _) := do id' ← id.sketch, return [id']
| _ (prod_form_proof.of_expr_def e pf) := do s ← to_string <$> (pf.to_expr >>= tactic.pp), return [⟨"1 = " ++ s, "by definition", []⟩]
| _ (prod_form_proof.of_pow _ pfp) := find_deps_of_pfp pfp
| _ (prod_form_proof.of_mul pfp1 pfp2 _) := do ds1 ← find_deps_of_pfp pfp1, ds2 ← find_deps_of_pfp pfp2, return (ds1 ++ ds2)
| _ (prod_form_proof.adhoc _ t _) := do t' ← t, return [t']
| _ (prod_form_proof.fake _) := return []

meta def make_proof_sketch_for_ineq {s} (lhs rhs : expr) (iq : ineq) (pf : prod_form_proof s) : tactic proof_sketch :=
do s' ← format_ineq lhs rhs iq, deps ← find_deps_of_pfp pf,
   return ⟨s', "by multiplicative arithmetic", deps⟩

-- assumes lhs > rhs as exprs. 1 R coeff* lhs^el * rhs^er ==> ineq_data
private meta def mk_ineq_data_of_lhs_rhs (coeff : ℚ) (lhs rhs : expr) (el er : ℤ) (c : spec_comp) {s} (pf : prod_form_proof s) :
        mul_state (list Σ l r, ineq_data l r) :=
do iq ← mk_ineq_of_lhs_rhs coeff lhs rhs el er c,
   iq.mmap $ λ id, do tac ← mk_ineq_proof_of_lhs_rhs lhs rhs el er pf id,
      return $ ⟨lhs, rhs, ⟨id, ineq_proof.adhoc _ _ id (make_proof_sketch_for_ineq lhs rhs id pf) tac⟩⟩
/-   match iq with
   | none := return none
   | some id := do tac ← mk_ineq_proof_of_lhs_rhs lhs rhs el er pf id,
      return $ some ⟨lhs, rhs, ⟨id, ineq_proof.adhoc _ _ id $ 
         tac
--       do t ← id.to_type lhs rhs, tactic.trace "sorrying", tactic.trace t, tactic.to_expr ``(sorry : %%t) --tactic.fail "mk_ineq_data not implemented"
      ⟩⟩ 
   end-/

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

-- pf proves 1 c coeff*e^(-1)
-- returns a proof of 1 c' (1/coeff) * e

-- 1 c coeff * e^exp
private meta def mk_ineq_data_of_single_cmp (coeff : ℚ) (e : expr) (exp : ℤ) (c : spec_comp) {s} (pf : prod_form_proof s) :
        mul_state (option Σ lhs rhs, ineq_data lhs rhs) :=
if exp = 1 then
  let inq := ineq.of_comp_and_slope c.to_comp (slope.some coeff),
      id : ineq_data `(1 : ℚ) e := ⟨inq, ineq_proof.adhoc _ _ _ (make_proof_sketch_for_ineq `(1 : ℚ) e inq pf) (do pf' ← pf.reconstruct, tactic.mk_mapp ``one_op_of_op [none, none, none, none, pf'])⟩ in--(tactic.fail "mk_ineq_data_of_single_cmp not implemented")⟩ in
  return $ some ⟨_, _, id⟩
else if exp = -1 then 
  let inq := ineq.of_comp_and_slope c.to_comp.reverse (slope.some coeff).invert,
       id : ineq_data `(1 : ℚ) e := ⟨inq, ineq_proof.adhoc _ _ _ 
         (make_proof_sketch_for_ineq `(1 : ℚ) e inq pf)
         (do pf' ← pf.reconstruct, 
           tactic.mk_mapp ``one_op_of_op_inv [none, none, none, none, pf'])⟩ in 
  return $ some ⟨_, _, id⟩
else -- TODO
 if exp > 0 then
   if (coeff < 0) && (exp % 2 = 0) then return none -- todo: this is a contradiction 
   else do ⟨es, _⟩ ← si e,
   if es.is_greater then 
     let m := nth_root_approx approx_dir.over coeff exp.nat_abs approx_prec,
         inq := ineq.of_comp_and_slope c.to_comp (slope.some m) in
     return $ some $ ⟨_, _, ⟨inq, ineq_proof.adhoc rat_one e _ 
      (make_proof_sketch_for_ineq rat_one e inq pf)
      (tactic.fail "mk_ineq_data_of_single_cmp not implemented")⟩⟩
   else --todo
    return none
 else return none


private meta def mk_eq_data_of_single_cmp (coeff : ℚ) (e : expr) (exp : ℤ) {s} (pf : prod_form_proof s) :
        mul_state (option Σ lhs rhs, eq_data lhs rhs) :=
if exp = 1 then
  let id : eq_data `(1 : ℚ) e := ⟨coeff, eq_proof.adhoc _ _ _ (tactic.fail "mk_eq_data_of_single_cmp not implemented") (tactic.fail "mk_eq_data_of_single_cmp not implemented")⟩ in
  return $ some ⟨_, _, id⟩
else -- TODO
return none

-- we need a proof constructor for ineq and eq
meta def prod_form_comp_data.to_ineq_data : prod_form_comp_data → mul_state (list (Σ lhs rhs, ineq_data lhs rhs))
| ⟨⟨_, spec_comp.eq⟩, _, _⟩ := return []
| ⟨⟨⟨coeff, exps⟩, c⟩, prf, _⟩ := 
  match exps.to_list with
  | [(rhs, cr), (lhs, cl)] := 
    if rhs.lt lhs then  mk_ineq_data_of_lhs_rhs coeff lhs rhs cl cr c prf
    else mk_ineq_data_of_lhs_rhs coeff rhs lhs cr cl c prf
  | [(rhs, cr)] := do t ← mk_ineq_data_of_single_cmp coeff rhs cr c prf,
       return $ /-trace_val-/ ("in pfcd.toid:", t),
      match t with | some t' := return [t'] | none := return [] end
  | [] := if coeff ≥ 1 then return [] else return [⟨rat_one, rat_one, ⟨ineq.of_comp_and_slope c.to_comp (slope.some coeff), ineq_proof.adhoc _ _ _ (tactic.fail "prod_form_comp_data.to_ineq_data not implemented") (tactic.fail "oops")⟩⟩]
  | _ := return []
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
 return $ some $ prod_form_comp_data.round ⟨_, nprf, (rb_set.union elim_list1 elim_list2).insert pvt⟩ approx_prec
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
else if pfcd2.pfc.pf.get_exp pvt = 0 then return  none
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


meta def prod_form_comp_data.order : prod_form_comp_data → prod_form_comp_data → ordering
| ⟨sfc1, _, ev1⟩ ⟨sfc2, _, ev2⟩ := 
match sfc1.order sfc2 with
| ordering.eq := has_ordering.cmp ev1.keys ev2.keys
| a := a
end

meta instance : has_ordering prod_form_comp_data := ⟨prod_form_comp_data.order⟩


meta def prod_form_comp_data.elim_into (sfcd1 sfcd2 : prod_form_comp_data) (pvt : expr)
     (rv : rb_set prod_form_comp_data) : mul_state (rb_set prod_form_comp_data) :=
do elimd ← /-trace_val <$>-/ sfcd1.elim_expr sfcd2 pvt,
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
cmps.mfold rv (λ c rv', if (/-trace_val-/ (sfcd.needs_elim_against (/-trace_val-/ c) (/-trace_val-/ e) : bool)) = tt then sfcd.elim_into c e rv' else return rv')


/--
 Performs all possible eliminations with sfcd on cmps. Returns a set of all new comps, NOT including the old ones.
-/
meta def new_exprs_from_comp_data_set (sfcd : prod_form_comp_data) (cmps : rb_set prod_form_comp_data) : mul_state (rb_set prod_form_comp_data) :=
sfcd.vars.mfoldr (λ e rv, elim_expr_from_comp_data_filtered sfcd cmps (/-trace_val-/ ("nefcds: ", e)).2 rv) mk_rb_set

meta def elim_list_into_set : rb_set prod_form_comp_data → list prod_form_comp_data → mul_state (rb_set prod_form_comp_data)
| cmps [] := return (/-trace_val-/ "elim_list_into_set []") >> return cmps
| cmps (sfcd::new_cmps) := return (/-trace_val-/ ("elim_list_into_set cons", cmps, sfcd)) >>
   if cmps.contains sfcd then elim_list_into_set cmps new_cmps else
   do new_gen ← new_exprs_from_comp_data_set sfcd cmps,--.keys
      let new_gen := new_gen.keys in 
      elim_list_into_set (cmps.insert sfcd) (new_cmps.append new_gen)

meta def elim_list_set (cmps : list prod_form_comp_data) (start : rb_set prod_form_comp_data := mk_rb_set) : mul_state (rb_set prod_form_comp_data) :=
do s ← elim_list_into_set (/-trace_val-/ ("start:",start)).2 (/-trace_val-/ ("cmps:",cmps)).2,
  return (/-trace_val-/ ("elim_list_set finished:", s)).2

meta def elim_list (cmps : list prod_form_comp_data) : mul_state (list prod_form_comp_data) :=
rb_set.to_list <$> elim_list_into_set mk_rb_set (/-trace_val-/ ("cmps:", cmps)).2

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
| _, _ := return (/-trace_val-/ ("no sign_info", lhs, rhs)) >> return none
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

section
open tactic
private meta def remove_one_from_pfcd_proof (old : prod_form_comp) (new : prod_form) (prf : prod_form_proof old) : tactic expr :=
do `(1*%%old_e) ← { old.pf with coeff := 1}.to_expr,
   `(1*%%new_e) ← { new with coeff := 1}.to_expr,
   prf' ← prf.reconstruct,
   (_, onp) ← tactic.solve_aux `((%%old_e : ℚ) = %%new_e) `[simp only [rat.one_pow, mul_one, one_mul]],
    --tactic.infer_type onp >>= tactic.trace,
    --tactic.infer_type prf' >>= tactic.trace,
   --(l, r) ← infer_type onp >>= match_eq,
   --trace l,
--   `((<) %%l' %%r') ← infer_type prf',
--    trace r',
 --   trace $ (l = r' : bool),
   (ntp, prf'', _) ← infer_type prf' >>= tactic.rewrite onp,
 --   trace ntp,
   --infer_type prf'' >>= trace,
   --return prf''
   mk_app ``eq.mp [prf'', prf']
end
private meta def remove_one_from_pfcd (pfcd : prod_form_comp_data) : prod_form_comp_data :=
match pfcd with
| ⟨⟨⟨coeff, exps⟩, c⟩, prf, el⟩ := 
  if exps.contains rat_one then
    let pf' : prod_form := ⟨coeff, exps.erase rat_one⟩ in
    ⟨⟨pf', c⟩, (prod_form_proof.adhoc _ --prf.sketch
     (do s ← to_string <$> (pf'.to_expr >>= tactic.pp), deps ← find_deps_of_pfp prf,
         return ⟨"1 " ++ (to_string $ to_fmt c) ++ s, "rearranging", deps⟩) 
     (remove_one_from_pfcd_proof pfcd.pfc pf' pfcd.prf)), el⟩
  else pfcd
end

private meta def mk_pfcd_list : polya_state (list prod_form_comp_data) :=
do il ← /-trace_val <$>-/ get_ineq_list, el ← /-trace_val <$>-/ get_eq_list, dfs ← /-trace_val <$> -/ get_mul_defs,
   il' ← /-trace_val <$>-/ reduce_option_list <$> il.mmap (λ ⟨_, _, id⟩, pfcd_of_ineq_data id),
   el' ← /-trace_val <$>-/ reduce_option_list <$> el.mmap (λ ⟨_, _, ed⟩, pfcd_of_eq_data ed),
   let dfs' := /-trace_val $-/ dfs.map mk_eqs_of_expr_prod_form_pair in -- TODO: does this filter ones without sign info?
   return $ list.map remove_one_from_pfcd $ ((il'.append el').append dfs').qsort (λ a b, if has_ordering.cmp a b = ordering.lt then tt else ff)

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
--set_option pp.all true
private meta def mk_one_ineq_info_list : list expr → polya_state (list (Σ e, ineq_info e rat_one))
| [] := return []
| (h::t) := 
  do si ← get_comps_with_one h,
     t' ← mk_one_ineq_info_list t,
     return $ list.cons ⟨h, si⟩ t'

meta def mk_mul_state : polya_state (hash_map expr (λ e, sign_data e) × hash_map expr (λ e, ineq_info e rat_one)) :=
do l ← get_expr_list,
   sds ← mk_sign_data_list l,
   iis ← mk_one_ineq_info_list $ sds.map sigma.fst,
   return (hash_map.of_list sds expr.hash, hash_map.of_list iis expr.hash)

private meta def gather_new_sign_info_pass_one : polya_state (list Σ e, sign_data e) :=
do  dfs ← mk_signed_pfcd_list,
    ms ← mk_mul_state,
    let vv : mul_state (list Σ e, sign_data e) := dfs.mfoldl (λ l (pf_sig : prod_form × Σ e, option (sign_data e)), l.append <$> (get_unknown_sign_data pf_sig.2.1 pf_sig.2.2 pf_sig.1)) [],
    return $ (vv ms).1
--    return $ reduce_option_list $ (dfs.mfoldl (λ (pf_sig : prod_form × Σ e, option (sign_data e)) (l : , l.append (get_unknown_sign_data pf_sig.2.1 pf_sig.2.2 pf_sig.1)) ms).1
    
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
     tactic.mk_mapp (if z % 2 = 0 then ``rat_pow_pos_of_neg_even else ``rat_pow_neg_of_neg_odd) [pf, none, zpp, zmp] 
else if z = 0 then tactic.mk_app ``rat_pow_zero [e]
else tactic.fail "neg_pow_tac failed, neg expr to neg power"

-- given a proof that e ≤ 0, proves that rat.pow e z has the right sign
private meta def nonpos_pow_tac (e pf : expr) (z : ℤ) : tactic expr :=
if z > 0 then
  do zpp ← mk_int_sign_pf z, zmp ← mk_int_mod_pf z,--tactic.to_expr ``(by gen_comp_val : %%(reflect z) > 0),
     tactic.mk_mapp (if z % 2 = 0 then ``rat_pow_nonneg_of_nonpos_even else ``rat_pow_nonpos_of_nonpos_odd) [pf, none, zpp, zmp] 
else if z = 0 then tactic.mk_app ``rat_pow_zero [e]
else tactic.fail "neg_pow_tac failed, neg expr to neg power"

private meta def ne_pow_tac (e pf : expr) (z : ℤ) : tactic expr :=
if z > 0 then
  do zpp ← mk_int_sign_pf z, zmp ← mk_int_mod_pf z,--tactic.to_expr ``(by gen_comp_val : %%(reflect z) > 0),
     tactic.mk_mapp (if z % 2 = 0 then ``rat_pow_pos_of_ne_even else ``rat_pow_ne_of_ne_odd) [pf, none, zpp, zmp] 
else if z = 0 then tactic.mk_app ``rat_pow_zero [e]
else tactic.fail "neg_pow_tac failed, neg expr to neg power"

private meta def even_pow_tac (e : expr) (z : ℤ) : tactic expr :=
if z > 0 then 
   do --tactic.trace "in ept", tactic.trace e, 
      zpp ← mk_int_sign_pf z, zmp ← mk_int_mod_pf z,
      tactic.mk_mapp ``rat_pow_nonneg_of_pos_even [e, none, zpp, zmp]
else if z = 0 then tactic.mk_app ``rat_pow_zero [e]
else tactic.fail "even_pow_tac failed, cannot handle neg power"

-- assumes pf is the prod form of e and has only one component
private meta def gather_new_sign_info_pass_two_aux (e : expr) (pf : prod_form) : polya_state $ option (Σ e', sign_data e') :=
match pf.exps.to_list with
| [(e', pow)] :=
  do si ← get_sign_info (/-trace_val-/ ("e'", e')).2,
     match si with
     | some ⟨gen_comp.gt, pf⟩ := return $ some ⟨e, ⟨gen_comp.gt, sign_proof.adhoc _ _ (do s ← format_sign e' gen_comp.gt, return ⟨s, "inferred from other sign data", []⟩) (do pf' ← pf.reconstruct, pos_pow_tac pf' pow)⟩⟩
     | some ⟨gen_comp.ge, pf⟩ := return $ some ⟨e, ⟨gen_comp.ge, sign_proof.adhoc _ _ (do s ← format_sign e' gen_comp.ge, return ⟨s, "inferred from other sign data", []⟩) (do pf' ← pf.reconstruct, nonneg_pow_tac pf' pow)⟩⟩
     | some ⟨gen_comp.lt, pf⟩ := 
       if pow ≥ 0 then 
         let tac : tactic expr := (do pf' ← pf.reconstruct, neg_pow_tac e' pf' pow),
             c := (if pow = 0 then gen_comp.eq else if pow % 2 = 0 then gen_comp.gt else gen_comp.lt) in
         return $ some ⟨e, ⟨c, sign_proof.adhoc _ _ (do s ← format_sign e c, return ⟨s, "inferred from other sign data", []⟩) tac⟩⟩
       else return none
     | some ⟨gen_comp.le, pf⟩ := 
       if pow ≥ 0 then 
         let tac : tactic expr := (do pf' ← pf.reconstruct, nonpos_pow_tac e' pf' pow),
             c := (if pow = 0 then gen_comp.eq else if pow % 2 = 0 then gen_comp.gt else gen_comp.lt) in
         return $ some ⟨e, ⟨c, sign_proof.adhoc _ _ (do s ← format_sign e c, return ⟨s, "inferred from other sign data", []⟩) tac⟩⟩
       else return none
     | some ⟨gen_comp.eq, pf⟩ := return $ some ⟨e, ⟨gen_comp.eq, sign_proof.adhoc _ _ (do s ← format_sign e gen_comp.eq, return ⟨s, "inferred from other sign data", []⟩) (do pf' ← pf.reconstruct, tactic.mk_app ``rat_pow_zero [pf', `(pow)])⟩⟩
     | some ⟨gen_comp.ne, pf⟩ := 
       if pow ≥ 0 then 
         let tac : tactic expr := (do pf' ← pf.reconstruct, ne_pow_tac e' pf' pow),
             c := (if pow = 0 then gen_comp.eq else if pow % 2 = 0 then gen_comp.gt else gen_comp.ne) in
         return $ some ⟨e, ⟨c, sign_proof.adhoc _ _ (do s ← format_sign e c, return ⟨s, "inferred from other sign data", []⟩) tac⟩⟩
       else return none
     | none := 
       if (pow ≥ 0) && (pow % 2 = 0) then 
          let c := if pow = 0 then gen_comp.eq else gen_comp.ge in
          return $ some ⟨e, ⟨c, sign_proof.adhoc _ _ (do s ← format_sign e c, return ⟨s, "inferred from other sign data", []⟩) (even_pow_tac e' pow)⟩⟩
       else return none
     end
| _ := return none
end

-- get sign info for power exprs
private meta def gather_new_sign_info_pass_two : polya_state (list Σ e, sign_data e) :=
do exs ← get_mul_defs,
   let exs := (/-trace_val-/ ("of length one:", exs.filter (λ e, e.2.exps.size = 1))).2,
   reduce_option_list <$> exs.mmap (λ p, gather_new_sign_info_pass_two_aux p.1 p.2)

private meta def gather_new_sign_info : polya_state (list Σ e, sign_data e) :=
do l1 ← gather_new_sign_info_pass_one,
   l2 ← gather_new_sign_info_pass_two,
   return $ l1.append ((/-trace_val-/ ("THIS IS L2", l2)).2)

private meta def mk_ineq_list (cmps : list prod_form_comp_data) : mul_state (list Σ lhs rhs, ineq_data lhs rhs) :=
do il ← cmps.mmap (λ pfcd, pfcd.to_ineq_data),
   return $ (/-trace_val-/ ("made ineq list: ", il.join)).2

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
   gather_new_sign_info >>= list.mmap (λ sig, add_sign $ /-trace_val-/ sig.2),
   sfcds ← /-trace_val <$>-/ mk_pfcd_list,
   ms ← mk_mul_state,
   let ((pfcs, ineqs), _) := mk_ineq_list_of_unelimed sfcds start ms,
   monad.mapm' 
    (λ s : Σ lhs rhs, ineq_data lhs rhs, add_ineq s.2.2)
    ineqs,
   return pfcs -- TODO: FIX RETURN 

end bb_process

end polya

