import .datatypes
namespace polya

meta structure blackboard :=
(ineqs : hash_map (expr×expr) (λ p, ineq_info p.1 p.2))
--(eqs : hash_map (expr×expr) (λ p, eq_info p.1 p.2))
(diseqs : hash_map (expr×expr) (λ p, diseq_info p.1 p.2))
(signs : hash_map expr (λ e, sign_info e))
(exprs : rb_set expr)
(contr : contrad)

namespace blackboard

meta def expr_pair_hash : expr × expr → ℕ
| (e1, e2) := (e1.hash + e2.hash) / 2

meta def mk_empty : blackboard :=
⟨mk_hash_map expr_pair_hash, mk_hash_map expr_pair_hash, mk_hash_map expr.hash, mk_rb_set, contrad.none⟩

section accessors
variables (lhs rhs : expr) (bb : blackboard)

meta def get_ineqs : ineq_info lhs rhs :=
if expr.lt lhs rhs then bb.ineqs.find' (lhs, rhs) else (bb.ineqs.find' (rhs, lhs)).reverse

meta def get_diseqs : diseq_info lhs rhs :=
if expr.lt lhs rhs then bb.diseqs.find' (lhs, rhs) else (bb.diseqs.find' (rhs, lhs)).reverse

meta def get_sign_info : sign_info lhs :=
bb.signs.find' lhs

meta def get_sign_comp : option gen_comp :=
match get_sign_info lhs bb with
| none := none
| some sd := some sd.c
end

meta def get_expr_list : list expr :=
bb.exprs.keys

meta def get_sorted_expr_list : list expr :=
bb.exprs.keys.qsort expr.lt

meta def contr_found : bool :=
match bb.contr with
| contrad.none := ff
| _ := tt
end

end accessors

section manipulators

meta def add_expr (e : expr) (bb : blackboard) : blackboard :=
{bb with exprs := bb.exprs.insert e}

meta def add_two_exprs (e1 e2 : expr) (bb : blackboard) : blackboard :=
(bb.add_expr e1).add_expr e2

meta def insert_sign (e : expr) (si : sign_data e) (bb : blackboard) : blackboard :=
{bb.add_expr e with signs := bb.signs.insert e (some si)}

meta def insert_diseq {lhs rhs} (dd : diseq_data lhs rhs) (bb : blackboard) : blackboard :=
let dsq := bb.get_diseqs lhs rhs in
{bb.add_two_exprs lhs rhs with diseqs := bb.diseqs.insert (lhs, rhs) (dsq.insert dd.c dd)}

meta def insert_ineq_info {lhs rhs} (ii : ineq_info lhs rhs) (bb : blackboard) : blackboard :=
{bb.add_two_exprs lhs rhs with ineqs := bb.ineqs.insert (lhs, rhs) ii}

end manipulators

end blackboard

section tactic_state_extension
open monad

meta def polya_state := state blackboard
meta instance : monad polya_state := state.monad _
meta def skip : polya_state unit := return ()

end tactic_state_extension

section tactics
open state

meta def lift_op (f : blackboard → blackboard) : polya_state unit :=
λ bb, ((), f bb)

meta instance tac_coe : has_coe (blackboard → blackboard) (polya_state unit) :=
⟨lift_op⟩

meta def lift_acc {α} (f : blackboard → α) : polya_state α :=
λ bb, (f bb, bb)

meta instance tac_coe' (α) : has_coe (blackboard → α) (polya_state α) :=
⟨lift_acc⟩

meta def add_expr (e : expr) : polya_state unit :=
blackboard.add_expr e

meta def get_diseqs (lhs rhs : expr) : polya_state (diseq_info lhs rhs) :=
blackboard.get_diseqs lhs rhs

meta def get_ineqs (lhs rhs : expr) : polya_state (ineq_info lhs rhs) :=
blackboard.get_ineqs lhs rhs

meta def get_sign_info (e : expr) : polya_state (sign_info e) :=
blackboard.get_sign_info e

meta def assert_contradiction (ctr : contrad) : polya_state unit :=
↑(λ bb : blackboard, if bb.contr_found then bb else {bb with contr := (trace_val ("contr:", ctr)).2})

meta def get_expr_list : polya_state (list expr) :=
blackboard.get_expr_list

meta def contr_found : polya_state bool :=
blackboard.contr_found

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

meta def add_zero_ineqs (add_ineq : Π l r, ineq_data l r → polya_state unit) 
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
        {e} (sd : sign_data e) : polya_state unit :=
do si ← get_sign_info e, 
return $ trace_val ("si:", si),
match si with
| none := ((λ bb, bb.insert_sign e sd) : polya_state unit) >> add_zero_ineqs add_ineq sd
| some osd := 
  if osd.c.implies sd.c then skip
  else if sd.c.implies osd.c then ((λ bb, bb.insert_sign e sd) : polya_state unit) >> add_zero_ineqs add_ineq sd
  else let ctr := contrad.sign sd osd in
       assert_contradiction ctr 
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
 blackboard.insert_ineq_info $ ineq_info.one_comp nid
else do nid' ← strengthen_ineq_if_implied nid,
 let nii := if nid'.inq.clockwise_of oid.inq 
            then ineq_info.two_comps oid nid' 
            else ineq_info.two_comps nid' oid in
 blackboard.insert_ineq_info nii

/--
 Assumes there are no equalities known between lhs and rhs,
 and that the new ineq data constitutes new and non-contradictory information.
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
   | some sd1, some sd2 := as (trace_val sd1) >> as sd2
   | some sd1, none     := as sd1
   | none, some sd2     := as sd2
   | none, none         := skip
   end


meta def add_self_ineq (id : ineq_data lhs lhs) : polya_state unit :=
if id.inq.strict && bnot (id.inq.is_axis) then assert_contradiction $ contrad.strict_ineq_self id
else skip

open ineq_info
meta def add_ineq : Π {lhs rhs}, ineq_data lhs rhs → polya_state unit | lhs rhs id :=
if expr.lt rhs lhs then add_ineq id.reverse else
if h : lhs = rhs then @add_self_ineq lhs (by rw -h at id; apply id) else
do ii ← get_ineqs lhs rhs,
   if ii.implies id then skip
   else if ii.implies_ineq id.inq.negate then assert_contradiction $ contrad.ineqs ii id
   else match ii with
   | no_comps := add_ineq_no_comps id
   | one_comp id1 := add_ineq_one_comp id id1
   | two_comps id1 id2 := add_ineq_two_comps id id1 id2
   | equal ed := add_implied_signs_from_eq_and_ineq_aux (@add_sign_aux @add_ineq) ed id
   end

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
if rhs.lt lhs then add_eq ed.reverse else
if h : ed.c = 0 then
 let prf := sign_proof.eq_of_eq_zero (begin rw -h, apply ed.prf end) in
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

meta def add_diseq : Π {lhs rhs}, diseq_data lhs rhs → polya_state unit
| lhs rhs dd :=
if rhs.lt lhs then add_diseq dd.reverse else
if h : dd.c = 0 then
 let prf := sign_proof.diseq_of_diseq_zero (begin rw -h, apply dd.prf end) in
 add_sign ⟨_, prf⟩
else
 do di ← get_diseqs lhs rhs,
 match di.find dd.c with
 | none := update_ineqs_and_insert_diseq dd
 | some _ := skip
 end

end

meta def process_expr : expr → polya_state unit :=
λ e, add_expr e >>
match e with
| ```(%%lhs + %%rhs) := process_expr lhs >> process_expr rhs
| ```(%%lhs * %%rhs) := process_expr lhs >> process_expr lhs
| _ := skip
end

/- assumes the second input is the type of prf
meta def process_comp (prf : expr) : expr → polya_state unit
| ```(%%lhs ≥ %%rhs) := process_expr lhs >> process_expr rhs >> 
    add_ineq ⟨ineq.of_comp_and_slope , ineq_proof.hyp lhs rhs _ prf⟩
| _ := skip-/

end tactics
end polya
