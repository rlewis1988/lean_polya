import .datatypes .normalizer

namespace polya
open native

meta structure blackboard : Type :=
( ineqs   : hash_map (expr × expr) (λ p, ineq_info p.1 p.2) )
( diseqs  : hash_map (expr × expr) (λ p, diseq_info p.1 p.2) )
( signs   : hash_map expr sign_info )
( exprs   : rb_set (expr × expr_form) )
( contr   : contrad )
( changed : bool := ff )
( to_refl  : rb_map expr expr := rb_map.mk _ _ )
( to_prove : rb_map expr (list expr) := rb_map.mk _ _ )


namespace blackboard

meta def expr_pair_hash : expr × expr → ℕ
| (e1, e2) := (e1.hash + e2.hash) / 2

meta def mk_empty : blackboard :=
{ ineqs       := mk_hash_map expr_pair_hash,
  diseqs      := mk_hash_map expr_pair_hash,
  signs       := (mk_hash_map expr.hash),--.insert `(1 : ℚ) $ some ⟨gen_comp.gt, sign_proof.adhoc _ _ (tactic.to_expr ``(zero_lt_one : (1 : ℚ) > 0))⟩,
  exprs       := mk_rb_set,--.insert (`(1 : ℚ), expr_form.atom_f `(1 : ℚ)),
  contr       := contrad.none }

section accessors
variables (lhs rhs : expr) (bb : blackboard)

meta def is_changed : bool :=
bb.changed

meta def get_ineqs : ineq_info lhs rhs :=
if h : lhs = rhs then by rw h; exact (ineq_info.equal $ eq_data.refl rhs)
else if expr.lt rhs lhs then bb.ineqs.ifind (lhs, rhs) else (bb.ineqs.ifind (rhs, lhs)).reverse

meta def get_diseqs : diseq_info lhs rhs :=
if expr.lt rhs lhs then bb.diseqs.ifind (lhs, rhs) else (bb.diseqs.ifind (rhs, lhs)).reverse

meta def get_sign_info : sign_info lhs :=
bb.signs.ifind lhs

meta def get_sign_comp : option gen_comp :=
match get_sign_info lhs bb with
| none := none
| some sd := some sd.c
end

meta def has_sign_info : bool :=
match get_sign_info lhs bb with
| some _ := tt
| none := ff
end

meta def has_strict_sign_info : bool :=
match get_sign_info lhs bb with
| some ⟨gen_comp.lt, _⟩ := tt
| some ⟨gen_comp.gt, _⟩ := tt
| _ := ff
end

meta def has_weak_sign_info : bool :=
match get_sign_info lhs bb with
| some ⟨gen_comp.lt, _⟩ := tt
| some ⟨gen_comp.gt, _⟩ := tt
| some ⟨gen_comp.ge, _⟩ := tt
| some ⟨gen_comp.le, _⟩ := tt
| _ := ff
end

meta def get_expr_list : list expr :=
bb.exprs.keys.map prod.fst

meta def get_expr_expr_form_list : list (expr × expr_form) :=
bb.exprs.keys

/-meta def get_sorted_expr_list : list expr :=
bb.exprs.keys.qsort expr.lt-/

meta def contr_found : bool :=
match bb.contr with
| contrad.none := ff
| _ := tt
end

meta def get_contr (bb : blackboard) : contrad :=
bb.contr

private meta def trace_signs : list expr → tactic unit :=
monad.mapm' (λ e, tactic.trace ("expr", e) >> tactic.trace (get_sign_info e bb))

private meta def trace_ineqs : list expr → tactic unit
| [] := tactic.skip
| (h::t) := monad.mapm' (λ e, tactic.trace ("exprs", h, e) >> tactic.trace (get_ineqs h e bb)) t >>  trace_ineqs t

meta def trace : tactic unit :=
trace_ineqs bb bb.get_expr_list >> trace_signs bb bb.get_expr_list

meta def trace_exprs : tactic unit :=
tactic.trace $ bb.get_expr_list

meta def trace_expr_pairs : tactic unit :=
tactic.trace $ bb.get_expr_expr_form_list

end accessors


section manipulators

meta def add_expr (e : expr) (ef : expr_form) (bb : blackboard) : blackboard :=
{bb with exprs := bb.exprs.insert (e, ef), changed := tt}

meta def add_two_exprs (e1 e2 : expr) (ef1 ef2 : expr_form) (bb : blackboard) : blackboard :=
{(bb.add_expr e1 ef1).add_expr e2 ef2 with changed := tt}

meta def insert_sign (e : expr) (si : sign_data e) (bb : blackboard) : blackboard :=
{bb with signs := bb.signs.insert e (some si), changed := tt}

meta def insert_diseq {lhs rhs} (dd : diseq_data lhs rhs) (bb : blackboard) : blackboard :=
let dsq := bb.get_diseqs lhs rhs in
{bb with diseqs := bb.diseqs.insert (lhs, rhs) (dsq.insert dd.c dd), changed := tt}

meta def insert_ineq_info {lhs rhs} (ii : ineq_info lhs rhs) (bb : blackboard) : blackboard :=
{bb with ineqs := bb.ineqs.insert (lhs, rhs) ii, changed := tt}

meta def set_changed (b : bool) (bb : blackboard) : blackboard :=
{bb with changed := b}

end manipulators

meta def insert_hyps (bb : blackboard) (e : expr)
  (mv : expr) (l : list expr) : blackboard :=
{ to_refl := bb.to_refl.insert e mv,
  to_prove := bb.to_prove.insert e l,
  ..bb }

end blackboard

section tactic_state_extension
open monad

meta def polya_state := state blackboard
meta instance : monad polya_state := state_t.monad
meta instance : monad_state blackboard polya_state := state_t.monad_state
meta def skip : polya_state unit := return ()

end tactic_state_extension

section tactics
open state_t

meta def lift_op (f : blackboard → blackboard) : polya_state unit :=
modify f

meta instance tac_coe : has_coe (blackboard → blackboard) (polya_state unit) :=
⟨lift_op⟩

meta def lift_acc {α} (f : blackboard → α) : polya_state α :=
f <$> get

meta instance tac_coe' (α) : has_coe (blackboard → α) (polya_state α) :=
⟨lift_acc⟩

meta def add_expr (e : expr) (ef : expr_form) : polya_state unit :=
blackboard.add_expr e ef

meta def get_diseqs (lhs rhs : expr) : polya_state (diseq_info lhs rhs) :=
blackboard.get_diseqs lhs rhs

meta def get_ineqs (lhs rhs : expr) : polya_state (ineq_info lhs rhs) :=
blackboard.get_ineqs lhs rhs

meta def get_sign_info (e : expr) : polya_state (sign_info e) :=
blackboard.get_sign_info e

meta def has_sign_info (e : expr) : polya_state bool :=
blackboard.has_sign_info e

meta def has_strict_sign_info (e : expr) : polya_state bool :=
blackboard.has_strict_sign_info e

meta def has_weak_sign_info (e : expr) : polya_state bool :=
blackboard.has_weak_sign_info e

meta def assert_contradiction (ctr : contrad) : polya_state unit :=
↑(λ bb : blackboard, if bb.contr_found then bb else {bb with contr := ctr})

meta def get_expr_list : polya_state (list expr) :=
blackboard.get_expr_list

meta def get_unsigned_exprs : polya_state (list expr) :=
get_expr_list >>= mfilter (λ e, bnot <$> has_weak_sign_info e)

meta def get_strict_signed_exprs : polya_state (list expr) :=
get_expr_list >>= mfilter has_strict_sign_info

meta def get_weak_signed_exprs : polya_state (list expr) :=
get_expr_list >>= mfilter has_weak_sign_info

meta def get_expr_expr_form_list : polya_state (list (expr × expr_form)) :=
blackboard.get_expr_expr_form_list

meta def contr_found : polya_state bool :=
blackboard.contr_found

meta def get_contr : polya_state contrad :=
blackboard.get_contr

meta def is_changed : polya_state bool :=
blackboard.is_changed

meta def set_changed (b : bool): polya_state unit :=
blackboard.set_changed b

meta def is_nondeg_slope (id : Σ lhs rhs, ineq_data lhs rhs) : bool :=
match id.2.2.inq.to_slope with
| slope.horiz := ff
| slope.some m := bnot (m = 0)
end

meta def get_ineq_list : polya_state (list Σ lhs rhs, ineq_data lhs rhs) :=
let extract_ineq_info : Π l r, polya_state (list Σ lhs rhs, ineq_data lhs rhs) :=
  (λ l r, if expr.lt l r then return [] else do ii ← get_ineqs l r,
    match ii with
    | ineq_info.one_comp id := return $ [(⟨l, r, id⟩ : Σ _ _, _)].filter (λ i, (is_nondeg_slope i) = tt)
    | ineq_info.two_comps id1 id2 := return $ [(⟨l, r, id1⟩ : Σ _ _, _), ⟨l, r, id2⟩].filter (λ i, (is_nondeg_slope i) = tt)
    | _ := return []
    end),
    inner_fold : Π lhs, Π lst r, polya_state (list Σ lhs rhs, ineq_data lhs rhs) := 
     λ (lhs : expr) lst (r : expr), do nl ← extract_ineq_info lhs r, return $ list.append lst nl
in do exprs ← get_expr_list,
   monad.foldl (λ lst l, monad.foldl (inner_fold l) lst exprs) [] exprs
--extract_ineq_info ```(1) ```(2)

meta def get_eq_list : polya_state (list Σ lhs rhs, eq_data lhs rhs) :=
let extract_eq_info : Π l r, polya_state (option Σ lhs rhs, eq_data lhs rhs) :=
  (λ l r, if expr.lt l r then return none else do ii ← get_ineqs l r,
    match ii with
    | ineq_info.equal ed := return $ some ⟨l, r, ed⟩
    | _ := return none
    end),
    inner_fold : Π lhs, Π lst r, polya_state (list Σ lhs rhs, eq_data lhs rhs) := 
     λ (lhs : expr) lst (r : expr), do nl ← extract_eq_info lhs r, match nl with
      | some ed := return (ed::lst)
      | none := return lst
      end
in do exprs ← get_expr_list,
   monad.foldl (λ lst l, monad.foldl (inner_fold l) lst exprs) [] exprs

meta def get_sign_list : polya_state (list Σ e, sign_data e) :=
do exprs ← get_expr_list,
monad.foldl (λ lst e, do {
  si ← get_sign_info e,
  match si with
  | some sd := return (⟨e, sd⟩::lst)
  | none := return lst
  end
}) [] exprs

private meta def is_sum_form : expr × expr_form → option (expr × sum_form)
| ⟨e, (expr_form.sum_f s)⟩ := some (e, s)
| _ := none

private meta def is_prod_form : expr × expr_form → option (expr × prod_form)
| ⟨e, (expr_form.prod_f s)⟩ := some (e, s)
| _ := none

meta def get_add_defs : polya_state (list (expr × sum_form)) :=
do exprs ← get_expr_expr_form_list,
   return $ list.reduce_option (exprs.map is_sum_form)

meta def get_mul_defs : polya_state (list (expr × prod_form)) :=
do exprs ← get_expr_expr_form_list,
   return $ list.reduce_option (exprs.map is_prod_form)

meta def rat_one : expr := `(1 : ℚ)

meta def get_comps_with_one (e : expr) : polya_state (ineq_info e rat_one) :=
get_ineqs e rat_one


section
variables {lhs rhs : expr}
meta def first_eq_diseq_match (c : ℚ) : list (diseq_data lhs rhs) → option (diseq_data lhs rhs)
| [] := none
| (h::t) := if h.c = c then some h else first_eq_diseq_match t

meta def check_eq_diseq_contr_and_insert (ed : eq_data lhs rhs) : polya_state unit :=
do di ← get_diseqs lhs rhs,
match di.find ed.c with
| none := blackboard.insert_ineq_info $ ineq_info.equal ed
| some dd := assert_contradiction $ contrad.eq_diseq ed dd
end

meta def add_zero_ineqs_aux (add_ineq : Π l r, ineq_data l r → polya_state unit) 
        {e} (sd : sign_data e) : polya_state unit :=
match sd.c with
| gen_comp.eq := skip
| gen_comp.ne := skip
| c :=
  let y : ℚ := if c.is_less then 1 else -1,
      inq : ineq := ⟨c.is_strict, 0, y⟩ in
  get_expr_list >>= 
   monad.mapm' (λ rhs, add_ineq e rhs ⟨inq, ineq_proof.zero_comp_of_sign_proof _ _ sd.prf⟩)
  
end

private meta def add_sign_aux (add_ineq : Π l r, ineq_data l r → polya_state unit) 
        {e} : sign_data e → polya_state unit | sd :=
do si ← get_sign_info e, 
--return $ trace_val ("si:", si),
match si with
| none := lift_op (blackboard.insert_sign e sd) >> set_changed tt >> add_zero_ineqs_aux add_ineq sd
| some osd := 
  if osd.c.implies sd.c then skip
  else if sd.c.implies osd.c then modify (blackboard.insert_sign e sd) >> set_changed tt >> add_zero_ineqs_aux add_ineq sd
  else if h : (sd.c = gen_comp.ge) ∧ (osd.c = gen_comp.le) then
    add_sign_aux ⟨_, sign_proof.eq_of_le_of_ge (by rw ←h.right; exact osd.prf) (by rw ←h.left; exact sd.prf)⟩
  else if h : (sd.c = gen_comp.le) ∧ (osd.c = gen_comp.ge) then 
    add_sign_aux ⟨_, sign_proof.eq_of_le_of_ge (by rw ←h.left; exact sd.prf) (by rw ←h.right; exact osd.prf)⟩
  else if sd.c.contr osd.c then
   let ctr := contrad.sign sd osd in
       assert_contradiction (trace_val ("found contr in add_sign_aux", ctr)).2 
  else skip
end


/--
 If id is nonstrict and a disequality is known, return the strict version of id.
 Else, return id.
-/
meta def strengthen_ineq_if_implied (id : ineq_data lhs rhs) : polya_state (ineq_data lhs rhs) :=
if id.inq.strict then return id else
match id.inq.to_slope with
| slope.horiz  := 
  do si ← get_sign_info rhs,
  match si with
  | none := return id
  | some sd := return $ id.strengthen_from_sign_rhs sd
  end
| slope.some m := 
  if m = 0 then do
    si ← get_sign_info lhs,
    match si with
    | none := return id
    | some sd := return $ id.strengthen_from_sign_lhs sd
    end
  else do
    di ← get_diseqs lhs rhs,
    match di.find m with
    | none := return id
    | some dd := return $ id.strengthen_from_diseq dd
    end
end

/--
 Assumes that nid.inq.to_slope = oid.inq.to_slope,
 there are no equalities known yet between lhs and rhs,
 and nid constitutes new and non-contradictory information.
 It could be stronger than oid, or imply an equality.

TODO
-/
meta def add_ineq_one_comp_matching_slopes (nid oid : ineq_data lhs rhs) : polya_state unit :=
skip

/--
 Assumes there are no equalities known between lhs and rhs,
 and that the new ineq data constitutes new and non-contradictory information.
-/
meta def add_ineq_no_comps (id : ineq_data lhs rhs) : polya_state unit :=
do nid ← strengthen_ineq_if_implied id,
   blackboard.insert_ineq_info $ ineq_info.one_comp nid

/--
 Assumes there are no equalities known between lhs and rhs,
 and that the new ineq data constitutes new and non-contradictory information.
-/
meta def add_ineq_one_comp (nid oid : ineq_data lhs rhs) : polya_state unit :=
if nid.inq.to_slope = oid.inq.to_slope then
 add_ineq_one_comp_matching_slopes nid oid
 --blackboard.insert_ineq_info $ ineq_info.one_comp nid
else do nid' ← strengthen_ineq_if_implied nid,
 let nii := if nid'.inq.clockwise_of oid.inq 
            then ineq_info.two_comps oid nid' 
            else ineq_info.two_comps nid' oid in
 blackboard.insert_ineq_info nii

/--
 Assumes there are no equalities known between lhs and rhs,
 and that the new ineq data constitutes new and non-contradictory information.

TODO : equal slopes cases are wrong!
-/
meta def add_ineq_two_comps (nid oid1 oid2 : ineq_data lhs rhs) : polya_state unit :=
if nid.inq.to_slope = oid1.inq.to_slope then
 blackboard.insert_ineq_info $ ineq_info.two_comps nid oid2
else if nid.inq.to_slope = oid2.inq.to_slope then
 blackboard.insert_ineq_info $ ineq_info.two_comps oid1 nid
else do nid' ← strengthen_ineq_if_implied nid,
 let nii := if nid'.inq.clockwise_of oid1.inq && nid'.inq.clockwise_of oid2.inq 
            then ineq_info.mk_two_comps oid1 nid'
            else if oid1.inq.clockwise_of nid'.inq && oid2.inq.clockwise_of nid'.inq
            then ineq_info.mk_two_comps nid' oid2
            else ineq_info.mk_two_comps oid1 oid2 in -- this last case shouldn't happen
 blackboard.insert_ineq_info nii


private meta def add_implied_signs_from_eq_and_ineq_aux (as : Π {e}, sign_data e → polya_state unit) {lhs rhs} 
         (ed : eq_data lhs rhs) (id : ineq_data lhs rhs) : polya_state unit :=
do (si1, si2) ← return $ ed.get_implied_sign_info_from_ineq id,
   match si1, si2 with
   | some sd1, some sd2 := as sd1 >> as sd2
   | some sd1, none     := as sd1
   | none, some sd2     := as sd2
   | none, none         := skip
   end

/-
TODO: This is wrong, not always a contradiction. Could just be sign info
-/
meta def add_self_ineq (id : ineq_data lhs lhs) : polya_state unit :=
if id.inq.strict && bnot (id.inq.is_axis) then assert_contradiction $ contrad.strict_ineq_self id
else skip

open ineq_info
meta def add_ineq : Π {lhs rhs}, ineq_data lhs rhs → polya_state unit | lhs rhs id :=
--if (/-trace_val ("in add_ineq", id, lhs, rhs)).2.1.inq ≠ id.inq then skip else
if expr.lt lhs rhs then add_ineq id.reverse else
if h : lhs = rhs then @add_self_ineq lhs (by rw ←h at id; apply id) else
do ii ← get_ineqs lhs rhs,
   if ( ("implies", ii, id, ii.implies id)).2.2.2 then skip
   else if ii.implies_ineq id.inq.negate then assert_contradiction $ contrad.ineqs ii id
   else match ii with
   | no_comps := add_ineq_no_comps id
   | one_comp id1 := add_ineq_one_comp id id1
   | two_comps id1 id2 := add_ineq_two_comps id id1 id2
   | equal ed := add_implied_signs_from_eq_and_ineq_aux (@add_sign_aux @add_ineq) ed id
   end

meta def add_zero_ineq := @add_zero_ineqs_aux @add_ineq

meta def add_sign := @add_sign_aux @add_ineq 

meta def add_implied_signs_from_eq_and_ineq := @add_implied_signs_from_eq_and_ineq_aux @add_sign

meta def check_ineq_for_diseq_update (id : ineq_data lhs rhs) (dd : diseq_data lhs rhs) :
         polya_state unit :=
match id.inq.to_slope with
| slope.some c :=
  if (c = dd.c) && bnot (id.inq.strict) then 
    let prf := ineq_proof.of_ineq_proof_and_diseq id.prf dd.prf in
    add_ineq ⟨id.inq.strengthen, prf⟩
  else skip
| _ := skip
end

meta def update_ineqs_and_insert_diseq (dd : diseq_data lhs rhs) : polya_state unit :=
do ei ← get_ineqs lhs rhs,
match ei with
| no_comps := blackboard.insert_diseq dd
| one_comp id1 := do check_ineq_for_diseq_update id1 dd, blackboard.insert_diseq dd
| two_comps id1 id2 :=
  do check_ineq_for_diseq_update id1 dd, check_ineq_for_diseq_update id2 dd, blackboard.insert_diseq dd
| equal ed := 
  if ed.c = dd.c then 
    assert_contradiction $ contrad.eq_diseq ed dd 
  else blackboard.insert_diseq dd
end

meta def add_eq : Π {lhs rhs}, eq_data lhs rhs → polya_state unit 
| lhs rhs ed :=
if lhs.lt rhs then add_eq ed.reverse else
if h : ed.c = 0 then
 let prf := sign_proof.eq_of_eq_zero (begin rw ←h, apply ed.prf end) in
 add_sign ⟨_, prf⟩
else
 do ei ← get_ineqs lhs rhs,
 match ei with
 | no_comps := check_eq_diseq_contr_and_insert ed
 | one_comp id1 := add_implied_signs_from_eq_and_ineq ed id1 >>
                      check_eq_diseq_contr_and_insert ed
 | two_comps id1 id2 := add_implied_signs_from_eq_and_ineq ed id1 >>
                          add_implied_signs_from_eq_and_ineq ed id2 >>
                            check_eq_diseq_contr_and_insert ed
 | equal ⟨c, prf⟩ := 
    if c = ed.c then skip 
    else 
     let sdl : sign_data lhs := ⟨gen_comp.eq, sign_proof.eq_of_two_eqs_lhs ed.prf prf⟩,
         sdr : sign_data rhs := ⟨gen_comp.eq, sign_proof.eq_of_two_eqs_rhs ed.prf prf⟩
     in add_sign sdl >> add_sign sdr
 end

/-
TODO: check for lhs = rhs
-/
meta def add_diseq : Π {lhs rhs}, diseq_data lhs rhs → polya_state unit
| lhs rhs dd :=
if lhs.lt rhs then add_diseq dd.reverse else
if h : dd.c = 0 then
 let prf := sign_proof.diseq_of_diseq_zero (begin rw ←h, apply dd.prf end) in
 add_sign ⟨_, prf⟩
else
 do di ← get_diseqs lhs rhs,
 match di.find dd.c with
 | none := update_ineqs_and_insert_diseq dd
 | some _ := skip
 end



end


meta def add_old_sign_info_to_new_ineq (new_e : expr) {old_e : expr} : sign_data old_e → polya_state unit
| ⟨gen_comp.ne, prf⟩ := skip
| ⟨gen_comp.eq, prf⟩ := skip
| ⟨c, prf⟩ := 
  let y : ℚ := if c.is_less then 1 else -1,
      inq : ineq := ⟨c.is_strict, 0, y⟩,
      --inq' := if old_e.lt new_e then inq.reverse else inq in
      ip := ineq_proof.zero_comp_of_sign_proof new_e inq prf in
  add_ineq $ /-trace_val-/ ⟨_, ip⟩--⟨inq', ineq_proof.zero_comp_of_sign_proof new_e _ prf⟩

meta def add_expr_and_update_ineqs (e : expr) (ef : expr_form) : polya_state unit :=
do es ← get_expr_list,
   if e ∈ es then skip else do
   add_expr (/-trace_val-/ ("adding expr and updating:", e)).2 ef,
   es.mmap' (λ e',
    do si ← get_sign_info e',
    match si with
    | some sd := add_old_sign_info_to_new_ineq e (/-trace_val-/ ("adding old sign info to:", e, sd)).2.2
    | none := skip
    end)

/-meta def process_expr : expr → expr_form → polya_state unit :=
λ e ef, add_expr e ef >>
match e with
| `(%%lhs + %%rhs) := process_expr lhs >> process_expr rhs
| `(%%lhs * %%rhs) := process_expr lhs >> process_expr lhs
| _ := skip
end-/

--meta def mk_neg : expr → expr

/-meta def get_sum_components : expr → list expr
| `(%%lhs + %%rhs) := rhs::(get_sum_components lhs)
--| `(%%lhs - %%rhs) := mk_neg rhs::(get_sum_components lhs)
| a := [a]

meta def get_prod_components : expr → list expr
| `(%%lhs * %%rhs) := rhs::(get_prod_components lhs)
| a := [a]

meta def is_sum (e : expr) : bool :=
e.is_app_of ``has_add.add

meta def is_prod (e : expr) : bool :=
e.is_app_of ``has_mul.mul || e.is_app_of ``rat.pow

open tactic
meta def get_comps_of_mul (e : expr) : tactic (expr × ℚ) := match e with
| `(%%lhs * %%rhs) := (do c ← eval_expr ℚ lhs, return (rhs, c)) <|> return (e, 1)
| f := return (f, 1)
end

meta def get_comps_of_exp (e : expr) : tactic (expr × ℤ) := match e with
| `(rat.pow %%base %%exp) := (do z ← eval_expr ℤ exp, return (base, z)) <|> return (e, 1)
| f := return (f, 1)
end-/

meta def process_expr_tac : blackboard → expr → tactic blackboard | bb e := 
if is_sum e then 
  let scs := get_sum_components e in do
  sum_components ← monad.mapm get_comps_of_mul scs,
  let sf : sum_form := rb_map.of_list sum_components,
  let (_, bb') := (add_expr_and_update_ineqs e (expr_form.sum_f sf)).run bb, 
  monad.foldl process_expr_tac bb' (sum_components.map prod.fst)
else if is_prod e then 
  --trace "is_prod:" >> trace e >>
  let scs := get_prod_components e in do
  --trace ("scs", scs),
  prod_components ← monad.mapm get_comps_of_exp scs,
  let sf : prod_form := ⟨1, rb_map.of_list prod_components⟩,
  let (_, bb') := (add_expr_and_update_ineqs e (expr_form.prod_f sf)).run bb,
  monad.foldl process_expr_tac bb' (prod_components.map prod.fst)--scs 
else do /-trace "atom", trace e,-/ return $ prod.snd $ (add_expr_and_update_ineqs e (expr_form.atom_f e)).run bb

meta def tac_add_eq {lhs rhs} (bb : blackboard) (ed : eq_data lhs rhs) : tactic blackboard :=
do bb' ← monad.foldl process_expr_tac bb [lhs, rhs],
   return ((add_eq ed).run bb').2

meta def tac_add_diseq {lhs rhs} (bb : blackboard) (ed : diseq_data lhs rhs) : tactic blackboard :=
do bb' ← monad.foldl process_expr_tac bb [lhs, rhs],
   return ((add_diseq ed).run bb').2

meta def tac_add_ineq {lhs rhs} (bb : blackboard) (ed : ineq_data lhs rhs) : tactic blackboard :=
do bb' ← monad.foldl process_expr_tac bb [lhs, rhs],
   return ((add_ineq ed).run bb').2

meta def tac_add_sign {e} (bb : blackboard) (sd : sign_data e) : tactic blackboard :=
do bb' ← process_expr_tac bb e,
   return ((add_sign sd).run bb').2

/-
TODO: rename?
-/
open tactic
meta def add_proof_to_blackboard (b : blackboard) (e : expr) : tactic blackboard :=
--infer_type e >>= trace >>
do
  infer_type e >>= trace,
  (mv, l, e) ← canonize_hyp e,
  let b := b.insert_hyps e mv l,

  tp ← infer_type e,
  --trace tp,
  (do (x, y, ie1) ← expr_to_ineq tp,
  --    trace x, trace y, trace ie1,
      id ← return $ ineq_data.mk ie1 (ineq_proof.hyp x y _ e),
      --return (add_ineq id b).2)
      tac_add_ineq b id)
  <|>
  (do (x, y, ie1) ← expr_to_eq tp,
      id ← return $ eq_data.mk ie1 (eq_proof.hyp x y _ e),
      --return (add_eq id b).2)
      tac_add_eq b id)
  <|>
  (do (x, c) ← expr_to_sign tp,
      cf ← coeff_of_expr x,
      match cf with
      | (none, e') := do
      sd ← return $ sign_data.mk c (sign_proof.hyp x _ e),
  --    trace "calling tac-add-sign",
      bb ← tac_add_sign b sd,
  --    trace "tac_add_sign done",
      return bb
      | (some q, e') :=
      do trace q, trace e', sd ← return $ trace_val $ sign_data.mk (if q > 0 then c else c.reverse) (sign_proof.scaled_hyp e' _ e q),
        tac_add_sign b sd
      end)
  <|>
  (do (x, y, ie1) ← expr_to_diseq tp,
      sd ← return $ diseq_data.mk ie1 (diseq_proof.hyp x y _ e),
      tac_add_diseq b sd)
  <|>
  trace "failed" >> trace e >> fail "add_comp_to_blackboard failed"

meta def add_proofs_to_blackboard (b : blackboard) (l : list expr) : tactic blackboard :=
monad.foldl add_proof_to_blackboard b l

/- assumes the second input is the type of prf
meta def process_comp (prf : expr) : expr → polya_state unit
| ```(%%lhs ≥ %%rhs) := process_expr lhs >> process_expr rhs >> 
    add_ineq ⟨ineq.of_comp_and_slope , ineq_proof.hyp lhs rhs _ prf⟩
| _ := skip-/

end tactics
end polya
