import data.hash_map

namespace hash_map
def {u v} find' {α : Type u} {β : α → Type v} [decidable_eq α] (m : hash_map α β) (a : α) [inhabited (β a)] : β a :=
match m.find a with
| none := default _
| some b := b
end

end hash_map

namespace polya

inductive rat : Type
instance : decidable_linear_ordered_comm_ring rat := sorry
def div : rat → rat → rat.
instance : has_div rat := ⟨div⟩
notation `ℚ` := rat
instance : has_ordering ℚ :=
⟨λ a b, if a = b then ordering.eq else if a < b then ordering.lt else ordering.gt⟩

inductive comp
| le | lt | ge | gt

inductive gen_comp
| le | lt | ge | gt | eq | ne

namespace comp
instance : decidable_eq comp := by tactic.mk_dec_eq_instance

def reverse : comp → comp
| le := ge
| lt := gt
| ge := le
| gt := lt

def negate : comp → comp
| le := gt
| lt := ge
| ge := lt
| gt := le

def strengthen : comp → comp
| le := lt
| ge := gt
| a  := a

def is_strict : comp → bool
| lt := tt
| gt := tt
| _  := ff

def is_less : comp → bool
| lt := tt
| le := tt
| _  := ff

def implies (c1 c2 : comp) : bool :=
(is_less c1 = is_less c2) && (is_strict c1 || bnot (is_strict c2))

end comp

namespace gen_comp
instance : decidable_eq gen_comp := by tactic.mk_dec_eq_instance

def implies_aux : gen_comp → gen_comp → bool
| lt le := tt
| gt ge := tt
| eq le := tt
| eq ge := tt
| lt ne := tt
| gt ne := tt
| _ _   := ff

def implies (c1 c2 : gen_comp) : bool :=
(c1 = c2) || implies_aux c1 c2 
end gen_comp

/--
 This does not represent the traditional slope, but (x/y) if (x, y) is a point on the line
-/
inductive slope
| horiz : slope
| some : rat → slope

instance slope.decidable_eq : decidable_eq slope := by tactic.mk_dec_eq_instance

/--
 An inequality (str, a, b) represents the halfplane counterclockwise from the vector (a, b).
 If str is true, it is strict (ie, it doesn't include the line bx-ay=0).
-/
structure ineq :=
(strict : bool)
(x y : ℚ)

namespace ineq
open comp slope
def to_comp (i : ineq) : comp := -- DOUBLE CHECK THIS
if i.x ≥ 0 then
  if i.y > 0 then
    if i.strict then lt else le
  else 
    if i.strict then gt else ge
else
  if i.y > 0 then
    if i.strict then lt else le
  else
    if i.strict then gt else ge

def to_slope (i : ineq) : slope :=
if i.y = 0 then slope.horiz else slope.some (i.x / i.y) 

def equiv (i1 i2 : ineq) : bool :=
to_slope i1 = to_slope i2

def of_comp_and_slope (c : comp) : slope → ineq
| horiz    := if is_less c then ⟨is_strict c, -1, 0⟩ else ⟨is_strict c, 1, 0⟩
| (some v) :=
  if v > 0 then 
    if is_less c then ⟨is_strict c, v, 1⟩ else ⟨is_strict c, -v, -1⟩
  else
    if is_less c then ⟨is_strict c, v, 1⟩ else ⟨is_strict c, -v, -1⟩


/--
 Turns a < 3b into a > 3b
-/
def flip (i : ineq) : ineq :=
⟨i.strict, -i.x, -i.y⟩

/--
 Turns a < 3b into a ≥ 3b
-/
def negate (i : ineq) : ineq :=
⟨bnot i.strict, -i.x, -i.y⟩

/--
 Turns a < 3b into b > 1/3 a.
 This is equivalent to reflecting over the identity line and flipping
-/
def reverse (i : ineq) : ineq :=
⟨i.strict, -i.y, -i.x⟩

/--
 Turns a ≤ 3b into a < 3b.
-/
def strengthen (i : ineq) : ineq :=
{i with strict := tt}

def implies (i1 i2 : ineq) : bool :=
(i1.to_slope = i2.to_slope) && (i1.strict || bnot (i2.strict))


def clockwise_of (i1 i2 : ineq) : bool :=
i1.x*i2.y - i1.y*i2.x > 0

/--
 True if the conjunction of i1 and i2 implies ninq
-/
def two_imply (i1 i2 : ineq) (ninq : ineq) : bool :=
(ninq.clockwise_of i1 && i2.clockwise_of ninq) || (i1.implies ninq) || (i2.implies ninq)

end ineq


meta inductive diseq_proof : expr → expr → ℚ → Type
| hyp : Π lhs rhs c, expr → diseq_proof lhs rhs c
| sym : Π {lhs rhs c}, Π (dp : diseq_proof lhs rhs c), diseq_proof rhs lhs (1/c)

meta inductive ineq_proof : expr → expr → ineq → Type--(lhs rhs : expr) (r : comp) (c : ℚ)
| hyp : Π lhs rhs i, expr → ineq_proof lhs rhs i
| sym : Π {lhs rhs i}, ineq_proof lhs rhs i → ineq_proof rhs lhs (i.reverse)
| of_ineq_proof_and_diseq : Π {lhs rhs i c}, 
    ineq_proof lhs rhs i → diseq_proof lhs rhs c → ineq_proof rhs lhs (i.strengthen)

meta structure ineq_data (lhs rhs : expr) :=
(inq : ineq)
(prf : ineq_proof lhs rhs inq)

meta def ineq_data.reverse {lhs rhs : expr} (id : ineq_data lhs rhs) : ineq_data rhs lhs :=
⟨id.inq.reverse, id.prf.sym⟩

/--
 In the two_comps case, we maintain the invariant that the defining ray of the first is 
 counterclockwise to that of the second.
-/
meta inductive ineq_info (lhs rhs : expr)
| no_comps {}  : ineq_info
| one_comp {}  : ineq_data lhs rhs → ineq_info
| two_comps {} : ineq_data lhs rhs → ineq_data lhs rhs → ineq_info
open ineq_info

meta instance ineq_info.inhabited (lhs rhs) : inhabited (ineq_info lhs rhs) :=
⟨no_comps⟩

meta def ineq_info.reverse {lhs rhs : expr} : ineq_info lhs rhs → ineq_info rhs lhs
| no_comps            := no_comps
| (one_comp id1)      := one_comp id1.reverse
| (two_comps id1 id2) := two_comps id1.reverse id2.reverse

meta inductive eq_proof : expr → expr → ℚ → Type
| hyp : Π lhs rhs c, expr → eq_proof lhs rhs c
| sym : Π {lhs rhs c}, Π (ep : eq_proof lhs rhs c), eq_proof rhs lhs (1/c)

meta structure eq_data (lhs rhs : expr) :=
(c   : ℚ)
(prf : eq_proof lhs rhs c)

meta def eq_data.reverse {lhs rhs : expr} (ei : eq_data lhs rhs) : eq_data rhs lhs :=
⟨(1/ei.c), ei.prf.sym⟩

meta def eq_info (lhs rhs : expr) := option (eq_data lhs rhs)

meta instance eq_info.inhabited (lhs rhs) : inhabited (eq_info lhs rhs) :=
⟨none⟩


meta def eq_info.reverse {lhs rhs : expr} : eq_info lhs rhs → eq_info rhs lhs
| none      := none
| (some ei) := some (ei.reverse)


meta structure diseq_data (lhs rhs : expr) :=
(c : ℚ)
(prf : diseq_proof lhs rhs c)

meta def diseq_data.reverse {lhs rhs : expr} (di : diseq_data lhs rhs) : diseq_data rhs lhs :=
⟨(1/di.c), di.prf.sym⟩

--meta def diseq_info (lhs rhs : expr) := list (diseq_data lhs rhs)
meta def diseq_info (lhs rhs : expr) := rb_map ℚ (diseq_data lhs rhs)

meta instance diseq_info.inhabited (lhs rhs) : inhabited (diseq_info lhs rhs) :=
⟨mk_rb_map⟩

meta def diseq_info.reverse {lhs rhs : expr} : diseq_info lhs rhs → diseq_info rhs lhs :=
rb_map.map diseq_data.reverse

meta inductive sign_proof : expr → gen_comp → Type
| hyp  : Π e c, expr → sign_proof e c
| ineq_lhs : Π c, Π {lhs rhs iqp}, ineq_proof lhs rhs iqp → sign_proof lhs c
| ineq_rhs : Π c, Π {lhs rhs iqp}, ineq_proof lhs rhs iqp → sign_proof rhs c
| eq_of_two_eqs_lhs : Π {lhs rhs eqp1 eqp2}, 
    eq_proof lhs rhs eqp1 → eq_proof lhs rhs eqp2 → sign_proof lhs gen_comp.eq
| eq_of_two_eqs_rhs : Π {lhs rhs eqp1 eqp2}, 
    eq_proof lhs rhs eqp1 → eq_proof lhs rhs eqp2 → sign_proof rhs gen_comp.eq
| diseq_of_diseq_zero : Π {lhs rhs}, diseq_proof lhs rhs 0 → sign_proof lhs gen_comp.ne
| eq_of_eq_zero : Π {lhs rhs}, eq_proof lhs rhs 0 → sign_proof lhs gen_comp.eq

meta structure sign_data (e : expr) :=
(c : gen_comp)
(prf : sign_proof e c)

meta def sign_info (e : expr) := option (sign_data e)

meta instance sign_info.inhabited (lhs) : inhabited (sign_info lhs) :=
⟨none⟩

section two_var_ineqs
meta def ineq_info.implies {lhs rhs : expr} : ineq_info lhs rhs → ineq_data lhs rhs → bool
| (one_comp ⟨inq1, _⟩) ⟨ninq, _⟩ := inq1.implies ninq
| (two_comps ⟨inq1, _⟩ ⟨inq2, _⟩) ⟨ninq, _⟩ := ineq.two_imply inq1 inq1 ninq
| _ _ := ff

end two_var_ineqs

meta inductive contrad
| none : contrad
| eq_diseq : Π {lhs rhs}, eq_data lhs rhs → diseq_data lhs rhs → contrad
| ineqs : Π {lhs rhs}, ineq_info lhs rhs → ineq_data lhs rhs → contrad
| sign : Π {e}, sign_data e → sign_data e → contrad

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
| some sd := some (sd.c)
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

meta def insert_eq {lhs rhs : expr} (ei : eq_data lhs rhs) (bb : blackboard) : blackboard :=
{bb with eqs := bb.eqs.insert (lhs, rhs) (some ei)}

meta def remove_eq (lhs rhs : expr) (bb : blackboard) : blackboard :=
{bb with eqs := bb.eqs.erase (lhs, rhs)}

meta def insert_sign (e : expr) (si : sign_data e) (bb : blackboard) : blackboard :=
{bb with signs := bb.signs.insert e (some si)}

meta def insert_diseq {lhs rhs : expr} (dd : diseq_data lhs rhs) (bb : blackboard) : blackboard :=
let dsq := bb.get_diseqs lhs rhs in
{bb with diseqs := bb.diseqs.insert (lhs, rhs) (dsq.insert dd.c dd)}

end manipulators

end blackboard

section tactic_state_extension
open tactic monad

meta def polya_tactic := state_t blackboard tactic
meta instance : monad polya_tactic := state_t.monad _ _

meta instance : has_monad_lift tactic polya_tactic := 
⟨λ _, state_t.lift⟩

meta instance (α : Type) : has_coe (tactic α) (polya_tactic α) :=
⟨monad_lift⟩

end tactic_state_extension

section tactics
open tactic

meta def lift_op (f : blackboard → blackboard) : polya_tactic unit :=
λ bb, return ((), f bb)

meta instance tac_coe : has_coe (blackboard → blackboard) (polya_tactic unit) :=
⟨lift_op⟩

meta def lift_acc {α} (f : blackboard → α) : polya_tactic α :=
λ bb, return (f bb, bb)

meta instance tac_coe' (α) : has_coe (blackboard → α) (polya_tactic α) :=
⟨lift_acc⟩

meta def add_expr (e : expr) : polya_tactic unit :=
blackboard.add_expr e

meta def get_eq (lhs rhs : expr) : polya_tactic (eq_info lhs rhs) :=
blackboard.get_eq lhs rhs

meta def get_diseqs (lhs rhs : expr) : polya_tactic (diseq_info lhs rhs) :=
blackboard.get_diseqs lhs rhs

meta def get_ineqs (lhs rhs : expr) : polya_tactic (ineq_info lhs rhs) :=
blackboard.get_ineqs lhs rhs

meta def get_sign_info (e : expr) : polya_tactic (sign_info e) :=
blackboard.get_sign_info e

meta def remove_eq (lhs rhs : expr) : polya_tactic unit :=
λ bb, bb.remove_eq lhs rhs

meta def assert_contradiction (ctr : contrad) : polya_tactic unit :=
↑(λ bb : blackboard, if bb.contr_found then bb else {bb with contr := ctr})

meta def add_sign {e} (sd : sign_data e) : polya_tactic unit :=
do si ← get_sign_info e, 
match si with
| none := (λ bb, bb.insert_sign e sd)
| some osd := 
  if osd.c.implies sd.c then skip
  else if sd.c.implies osd.c then (λ bb, bb.insert_sign e sd)
  else let ctr := contrad.sign sd osd in
       assert_contradiction ctr 
end

meta def first_eq_diseq_match {lhs rhs} (c : ℚ) : list (diseq_data lhs rhs) → option (diseq_data lhs rhs)
| [] := none
| (h::t) := if h.c = c then some h else first_eq_diseq_match t

meta def check_eq_contr_and_insert {lhs rhs} (ed : eq_data lhs rhs) : polya_tactic unit :=
do di ← get_diseqs lhs rhs,
match di.find ed.c with
| none := blackboard.insert_eq ed
| some dd := assert_contradiction $ contrad.eq_diseq ed dd
end

meta def add_ineq_no_comps {lhs rhs} (id : ineq_data lhs rhs) : polya_tactic unit :=
failed

meta def add_ineq_one_comp {lhs rhs} (nid oid : ineq_data lhs rhs) : polya_tactic unit :=
failed

meta def add_ineq_two_comps {lhs rhs} (nid oid1 oid2 : ineq_data lhs rhs) : polya_tactic unit :=
failed

meta def add_ineq {lhs rhs} (id : ineq_data lhs rhs) : polya_tactic unit :=
do ii ← get_ineqs lhs rhs,
match ii with
| no_comps := add_ineq_no_comps id
| one_comp id1 := add_ineq_one_comp id id1
| two_comps id1 id2 := add_ineq_two_comps id id1 id2
end

meta def check_ineq_for_diseq_update {lhs rhs} (id : ineq_data lhs rhs) (dd : diseq_data lhs rhs) :
         polya_tactic unit :=
match id.inq.to_slope with
| slope.some c :=
  if (c = dd.c) && bnot (id.inq.strict) then 
    let prf := ineq_proof.of_ineq_proof_and_diseq id.prf dd.prf in
    add_ineq ⟨id.inq.strengthen, prf⟩
  else skip
| _ := skip
end

meta def update_ineqs_and_insert_diseq {lhs rhs} (dd : diseq_data lhs rhs) : polya_tactic unit :=
do ei ← get_ineqs lhs rhs,
match ei with
| no_comps := blackboard.insert_diseq dd
| one_comp id1 := do check_ineq_for_diseq_update id1 dd, blackboard.insert_diseq dd
end

meta def check_diseq_eq_contr_and_insert {lhs rhs} (dd : diseq_data lhs rhs) : polya_tactic unit :=
do ei ← get_eq lhs rhs,
match ei with
| none := blackboard.insert_diseq dd
| some ed :=
  if ed.c = dd.c then assert_contradiction $ contrad.eq_diseq ed dd 
  else blackboard.insert_diseq dd
end

meta def add_eq {lhs rhs} (ed : eq_data lhs rhs) : polya_tactic unit :=
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

meta def add_diseq {lhs rhs} (dd : diseq_data lhs rhs) : polya_tactic unit :=
if h : dd.c = 0 then
 let prf := sign_proof.diseq_of_diseq_zero (begin rw -h, apply dd.prf end) in
 add_sign ⟨_, prf⟩
else
 do di ← get_diseqs lhs rhs,
 match di.find dd.c with
 | none := check_diseq_eq_contr_and_insert dd
 | some _ := skip
 end

meta def process_expr : expr → polya_tactic unit :=
λ e, (lift_acc $ add_expr e) >>
match e with
| ```(%%lhs + %%rhs) := process_expr lhs >> process_expr rhs
| ```(%%lhs * %%rhs) := process_expr lhs >> process_expr lhs
| _ := skip
end

end tactics
end polya
