import .datatypes
namespace polya

meta structure blackboard :=
(ineqs : hash_map (expr×expr) (λ p, ineq_info p.1 p.2))
(eqs : hash_map (expr×expr) (λ p, eq_info p.1 p.2))
(diseqs : hash_map (expr×expr) (λ p, diseq_info p.1 p.2))
(signs : hash_map expr (λ e, sign_info e))
(exprs : rb_set expr)
(contr : contrad)

namespace blackboard

section accessors
variables (lhs rhs : expr) (bb : blackboard)

meta def get_ineqs : ineq_info lhs rhs :=
if expr.lt lhs rhs then bb.ineqs.find' (lhs, rhs) else (bb.ineqs.find' (rhs, lhs)).reverse

meta def get_eq : eq_info lhs rhs :=
if expr.lt lhs rhs then bb.eqs.find' (lhs, rhs) else (bb.eqs.find' (rhs, lhs)).reverse

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

meta def insert_eq {lhs rhs} (ei : eq_data lhs rhs) (bb : blackboard) : blackboard :=
{bb with eqs := bb.eqs.insert (lhs, rhs) (some ei)}

meta def remove_eq (lhs rhs : expr) (bb : blackboard) : blackboard :=
{bb with eqs := bb.eqs.erase (lhs, rhs)}

meta def insert_sign (e : expr) (si : sign_data e) (bb : blackboard) : blackboard :=
{bb with signs := bb.signs.insert e (some si)}

meta def insert_diseq {lhs rhs} (dd : diseq_data lhs rhs) (bb : blackboard) : blackboard :=
let dsq := bb.get_diseqs lhs rhs in
{bb with diseqs := bb.diseqs.insert (lhs, rhs) (dsq.insert dd.c dd)}

meta def insert_ineq_info {lhs rhs} (ii : ineq_info lhs rhs) (bb : blackboard) : blackboard :=
{bb with ineqs := bb.ineqs.insert (lhs, rhs) ii}

end manipulators

end blackboard

section tactic_state_extension
open monad

meta def polya_state := state blackboard
meta instance : monad polya_state := state.monad _
meta def skip : polya_state unit := return ()
/-meta instance : has_monad_lift tactic polya_tactic := 
⟨λ _, state_t.lift⟩

meta instance (α : Type) : has_coe (tactic α) (polya_tactic α) :=
⟨monad_lift⟩-/

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

meta def get_eq (lhs rhs : expr) : polya_state (eq_info lhs rhs) :=
blackboard.get_eq lhs rhs

meta def get_diseqs (lhs rhs : expr) : polya_state (diseq_info lhs rhs) :=
blackboard.get_diseqs lhs rhs

meta def get_ineqs (lhs rhs : expr) : polya_state (ineq_info lhs rhs) :=
blackboard.get_ineqs lhs rhs

meta def get_sign_info (e : expr) : polya_state (sign_info e) :=
blackboard.get_sign_info e

meta def remove_eq (lhs rhs : expr) : polya_state unit :=
λ bb, bb.remove_eq lhs rhs

meta def assert_contradiction (ctr : contrad) : polya_state unit :=
↑(λ bb : blackboard, if bb.contr_found then bb else {bb with contr := ctr})

meta def get_expr_list : polya_state (list expr) :=
blackboard.get_expr_list

section
variables {lhs rhs : expr}
meta def first_eq_diseq_match (c : ℚ) : list (diseq_data lhs rhs) → option (diseq_data lhs rhs)
| [] := none
| (h::t) := if h.c = c then some h else first_eq_diseq_match t

meta def check_eq_contr_and_insert (ed : eq_data lhs rhs) : polya_state unit :=
do di ← get_diseqs lhs rhs,
match di.find ed.c with
| none := blackboard.insert_eq ed
| some dd := assert_contradiction $ contrad.eq_diseq ed dd
end

meta def add_zero_ineqs (add_ineq : Π l r, ineq_data l r → polya_state unit) 
        {e} (sd : sign_data e) : polya_state unit :=
match sd.c with
| gen_comp.eq := skip
| gen_comp.ne := skip
| c :=
  let x : ℚ := if c.is_less then -1 else 1,
      inq : ineq := ⟨c.is_strict, x, 0⟩ in
  get_expr_list >>= 
   monad.mapm' (λ rhs, add_ineq e rhs ⟨⟨c.is_strict, x, 0⟩, ineq_proof.zero_comp_of_sign_proof _ _ sd.prf⟩)
  
end

private meta def add_sign_aux (add_ineq : Π l r, ineq_data l r → polya_state unit) 
        {e} (sd : sign_data e) : polya_state unit :=
do si ← get_sign_info e, 
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

/-
The following three functions assume there are no equalities known between lhs and rhs,
and that the new ineq data constitutes new and non-contradictory information.
-/
meta def add_ineq_no_comps (id : ineq_data lhs rhs) : polya_state unit :=
do nid ← strengthen_ineq_if_implied id,
   blackboard.insert_ineq_info $ ineq_info.one_comp nid

meta def add_ineq_one_comp (nid oid : ineq_data lhs rhs) : polya_state unit :=
if nid.inq.to_slope = oid.inq.to_slope then
 blackboard.insert_ineq_info $ ineq_info.one_comp nid
else do nid' ← strengthen_ineq_if_implied nid,
 let nii := if nid'.inq.clockwise_of oid.inq 
            then ineq_info.two_comps oid nid' 
            else ineq_info.two_comps nid' oid in
 blackboard.insert_ineq_info nii

meta def add_ineq_two_comps (nid oid1 oid2 : ineq_data lhs rhs) : polya_state unit :=
if nid.inq.to_slope = oid1.inq.to_slope then
 blackboard.insert_ineq_info $ ineq_info.two_comps nid oid2
else if nid.inq.to_slope = oid2.inq.to_slope then
 blackboard.insert_ineq_info $ ineq_info.two_comps oid1 nid
else do nid' ← strengthen_ineq_if_implied nid,
 let nii := if nid'.inq.clockwise_of oid1.inq && nid'.inq.clockwise_of oid2.inq 
            then ineq_info.two_comps oid1 nid'
            else if oid1.inq.clockwise_of nid'.inq && oid2.inq.clockwise_of nid'.inq
            then ineq_info.two_comps nid' oid2
            else ineq_info.two_comps oid1 oid2 in -- this last case shouldn't happen
 blackboard.insert_ineq_info nii

-- TODO
/--
 If an equality is known between lhs and rhs, the inequality is redundant, but
 we may be able to infer sign information.
-/
meta def add_ineq_with_eq_data (id : ineq_data lhs rhs) (ed : eq_data lhs rhs) : polya_state unit :=
do sil ← get_sign_info lhs,
sir ← get_sign_info rhs,
match sil, sir with
| none, none := skip
| _, _ := skip
end

meta def add_self_ineq (id : ineq_data lhs lhs) : polya_state unit :=
if id.inq.strict then assert_contradiction $ contrad.strict_ineq_self id
else skip

end
open ineq_info
meta def add_ineq : Π {lhs rhs}, ineq_data lhs rhs → polya_state unit | lhs rhs id :=
if expr.lt rhs lhs then add_ineq id.reverse else
if h : lhs = rhs then @add_self_ineq lhs (by rw -h at id; apply id) else
do ii ← get_ineqs lhs rhs,
if ii.implies id then skip
else if ii.implies_ineq id.inq.negate then assert_contradiction $ contrad.ineqs ii id
else do ei ← get_eq lhs rhs,
match ei with
| some ed := add_ineq_with_eq_data id ed
| none :=
  match ii with
  | no_comps := add_ineq_no_comps id
  | one_comp id1 := add_ineq_one_comp id id1
  | two_comps id1 id2 := add_ineq_two_comps id id1 id2
  end
end

section
variables {lhs rhs : expr}

meta def add_sign := @add_sign_aux @add_ineq 

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
end

meta def check_diseq_eq_contr_and_insert (dd : diseq_data lhs rhs) : polya_state unit :=
do ei ← get_eq lhs rhs,
match ei with
| none := blackboard.insert_diseq dd
| some ed :=
  if ed.c = dd.c then assert_contradiction $ contrad.eq_diseq ed dd 
  else blackboard.insert_diseq dd
end

meta def add_eq (ed : eq_data lhs rhs) : polya_state unit :=
if h : ed.c = 0 then
 let prf := sign_proof.eq_of_eq_zero (begin rw -h, apply ed.prf end) in
 add_sign ⟨_, prf⟩
else
 do ei ← get_eq lhs rhs,
 match ei with
 | none := check_eq_contr_and_insert ed
 | some ⟨c, prf⟩ := 
    if c = ed.c then skip 
    else 
     let sdl : sign_data lhs := ⟨gen_comp.eq, sign_proof.eq_of_two_eqs_lhs ed.prf prf⟩,
         sdr : sign_data rhs := ⟨gen_comp.eq, sign_proof.eq_of_two_eqs_rhs ed.prf prf⟩
     in do add_sign sdl, add_sign sdr, remove_eq lhs rhs
 end

meta def add_diseq (dd : diseq_data lhs rhs) : polya_state unit :=
if h : dd.c = 0 then
 let prf := sign_proof.diseq_of_diseq_zero (begin rw -h, apply dd.prf end) in
 add_sign ⟨_, prf⟩
else
 do di ← get_diseqs lhs rhs,
 match di.find dd.c with
 | none := check_diseq_eq_contr_and_insert dd
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

end tactics
end polya
