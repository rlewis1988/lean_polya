import datatypes norm_num-- blackboard
namespace polya

section aux
#check expr.is_numeral

meta def is_num : expr → bool
| `(bit0 %%e) := is_num e
| `(bit1 %%e) := is_num e
| `(@has_zero.zero _ _) := tt
| `(@has_one.one _ _) := tt
| `(-%%a) := is_num a
| `(%%a / %%b) := is_num a && is_num b
| _ := ff

meta def mk_neg : expr → expr
| `((-%%lhs) * %%rhs) := `(%%lhs * %%rhs : ℚ)
| `(%%lhs * %%rhs) := `((-%%lhs) * %%rhs : ℚ)
| a := `((-1 : ℚ)*%%a)

meta def get_sum_components : expr → list expr
| `(%%lhs + %%rhs) := rhs::(get_sum_components lhs)
| `(%%lhs - %%rhs) := mk_neg rhs::(get_sum_components lhs)
| a := [a]

meta def get_prod_components : expr → list expr
| `(%%lhs * %%rhs) := rhs::(get_prod_components lhs)
| a := [a]

meta def is_sum (e : expr) : bool :=
e.is_app_of ``has_add.add || e.is_app_of ``has_sub.sub

meta def is_prod (e : expr) : bool :=
e.is_app_of ``has_mul.mul || e.is_app_of ``rat.pow

open tactic
meta def get_comps_of_mul (e : expr) : tactic (expr × ℚ) := match e with
| `(%%lhs * %%rhs) := (do c ← eval_expr ℚ lhs, return (rhs, c)) <|> return (e, 1)
| `(%%num / %%denom) := (do c ← eval_expr ℚ denom, return (num, 1/c)) <|> return (e, 1)
| f := return (f, 1)
end

meta def get_comps_of_exp (e : expr) : tactic (expr × ℤ) := match e with
| `(rat.pow %%base %%exp) := (do z ← eval_expr ℤ exp, return (base, z)) <|> return (e, 1)
| f := return (f, 1)
end


end aux

/-meta mutual inductive sterm, term
with sterm : Type
| scaled : ℚ → term → sterm
with term : Type
| add_term : list sterm → term
| mul_term : list (term × ℤ) → term
| atom : expr → term-/
meta inductive term : Type
| add_term : rb_map term ℚ → term
| mul_term : rb_map term ℤ → term
| atom : expr → term

namespace term
meta def order : term → term → ordering
| (add_term m) (add_term n) := @has_ordering.cmp _ (@list.has_ordering _ ⟨order⟩) m.keys n.keys
| (add_term _) _ := ordering.gt
| _ (add_term _) := ordering.lt
| (mul_term m) (mul_term n) := @has_ordering.cmp _ (@list.has_ordering _ ⟨order⟩) m.keys n.keys
| (mul_term _) (atom _) := ordering.gt
| (atom _) (mul_term _) := ordering.lt
| (atom e1) (atom e2) := has_ordering.cmp e1 e2

meta instance : has_ordering term := ⟨order⟩ 

meta def add_term_empty : term :=
add_term mk_rb_map

meta def mul_term_empty : term :=
mul_term mk_rb_map
end term

meta structure sterm :=
(coeff : ℚ) (body : term)

private meta def add_term_coeff_pair (map : rb_map term ℚ) (st : term × ℚ) : rb_map term ℚ :=
match map.find st.1 with
| none := map.insert st.1 st.2
| some c := map.insert st.1 (st.2 + c)
end

private meta def add_term_coeff_pair_list (map : rb_map term ℚ) (l : list (term × ℚ)) : rb_map term ℚ :=
l.foldl add_term_coeff_pair map

private meta def add_sterm (map : rb_map term ℚ) (st : sterm) : rb_map term ℚ :=
add_term_coeff_pair map (st.body, st.coeff)

meta def add_term_of_sterm_list (l : list sterm) : term :=
term.add_term $ l.foldl add_sterm mk_rb_map

private meta def pow_term_exp (map : rb_map term ℤ) (pr : term × ℤ) : rb_map term ℤ :=
match map.find pr.1 with
| none := map.insert pr.1 pr.2
| some c := map.insert pr.1 (pr.2 + c)
end

private meta def pow_term_exp_list (map : rb_map term ℤ) (l : list (term × ℤ)) : rb_map term ℤ :=
l.foldl pow_term_exp map

meta def mul_term_of_term_exp_list (l : list (term × ℤ)) : term :=
term.mul_term $ l.foldl pow_term_exp mk_rb_map

meta def term.is_zero : term → bool
| (term.add_term m) := m.size = 0
| _ := ff

meta def sterm.is_zero (st : sterm) : bool :=
st.body.is_zero || (st.coeff = 0)

meta def term.scale (q : ℚ) (t : term) : sterm :=
⟨q, t⟩

meta def sterm.scale (q : ℚ) (st : sterm) : sterm :=
{ st with coeff := st.coeff * q }

meta def sterm.of_pair (pr : term × ℚ) : sterm :=
⟨pr.2, pr.1⟩


open tactic

private meta def expr.to_term_aux (tst : expr → tactic sterm) : expr → tactic term | e := 
if is_sum e then
  let scs := get_sum_components e in
  add_term_of_sterm_list <$> scs.mmap tst
else if is_prod e then 
  let scs := get_prod_components e in
  do scs' ← scs.mmap get_comps_of_exp,
     mul_term_of_term_exp_list <$> scs'.mmap (λ pr, do tm ← expr.to_term_aux pr.1, return (tm, pr.2))
else return $ term.atom e
          
private meta def split_num_nonnum_prod_comps : list expr → list expr × list expr
| [] := ([], [])
| (e::l) :=
   let (t1, t2) := split_num_nonnum_prod_comps l in
   if is_num e then (e::t1, t2) else (t1, e::t2)


private meta def fold_op_app_aux (op : pexpr) : expr → list expr → tactic expr
| h [] := return h
| h (h'::t) := do h'' ← to_expr ``(%%op %%h %%h'), fold_op_app_aux h'' t

private meta def fold_op_app (op : pexpr) (dflt : expr) : list expr → tactic expr
| [] := return dflt
| (h::t) := fold_op_app_aux op h t

meta def expr.to_sterm : expr → tactic sterm | e :=
if is_num e then
  do q ← eval_expr ℚ e,
     return ⟨q, (term.atom `(1 : ℚ))⟩
else if is_prod e then
 let scs := get_prod_components e,
     (numcs, nnumcs) := split_num_nonnum_prod_comps scs in
 do  numcs' ← numcs.mmap (eval_expr ℚ),
 let q := numcs'.foldl (*) 1,
     sterm.mk q <$> ((fold_op_app ``((*)) `(1 : ℚ) nnumcs) >>= expr.to_term_aux expr.to_sterm)
else sterm.mk 1 <$> expr.to_term_aux expr.to_sterm e

/-match e with
| `(%%c*%%t) := 
  if is_num c then
    do q ← eval_expr ℚ c,
       sterm.scale q <$> expr.to_sterm t
  else sterm.mk 1 <$> expr.to_term_aux expr.to_sterm e
| t := sterm.mk 1 <$> expr.to_term_aux expr.to_sterm t
end       -/

meta def expr.to_term : expr → tactic term := expr.to_term_aux expr.to_sterm



private meta def term.to_expr_aux (ste : sterm → tactic expr) : term → tactic expr
| (term.add_term l) :=
 if l.size = 0 then return `(0 : ℚ) else
 do l' ← l.to_list.mmap (λ pr, ste (sterm.of_pair pr)),
     fold_op_app ``((+)) `(0 : ℚ) l'
| (term.mul_term l) :=
  if l.size = 0 then return `(1 : ℚ) else
  do l' ← l.to_list.mmap (λ pr, do e' ← term.to_expr_aux pr.1, return (e', pr.2)),
  let l'' := l'.map (λ pr, `(rat.pow %%(pr.1) %%(pr.2.reflect))),
     fold_op_app ``((*)) `(1 : ℚ) l''
| (term.atom e) := return e
    

meta def sterm.to_expr : sterm → tactic expr
| ⟨c, t⟩ :=
  if t.is_zero || (c = 0) then return `(0 : ℚ) else
  do t' ← term.to_expr_aux sterm.to_expr t,
     return `(%%(c.reflect)*%%t' : ℚ)

meta def term.to_expr : term → tactic expr := term.to_expr_aux sterm.to_expr

meta def term.to_tactic_format (e : term) : tactic format :=
do ex ← e.to_expr,
   tactic_format_expr ex

meta def sterm.to_tactic_format (e : sterm) : tactic format :=
do ex ← e.to_expr,
   tactic_format_expr ex

meta instance term.has_to_tactic_format : has_to_tactic_format term :=
⟨term.to_tactic_format⟩

meta instance sterm.has_to_tactic_format : has_to_tactic_format sterm :=
⟨sterm.to_tactic_format⟩



section canonize

private meta def coeff_and_terms_of_sterm_z_list : list (sterm × ℤ) → ℚ × list (term × ℤ)
| [] := (1, [])
| ((⟨c, tm⟩, z)::t) :=
   let (q, l) := coeff_and_terms_of_sterm_z_list  t in
  (q * rat.pow c z, (tm, z)::l)

/-private meta def coeff_and_terms_of_sterm_z_list : ℚ → list (term × ℤ) → list (sterm × ℤ) → ℚ × list (term × ℤ)
| acc l [] := (acc, l)
| acc l ((sterm.scaled c tm, z)::t) := (tm, z)::coeff_and_terms_of_sterm_z_list (acc*rat.pow c z) t-/

-- only applies to add_term
private meta def term.leading_coeff : term → ℚ
| (term.add_term l) := 
  match l.to_list with
  | [] := 1
  | ((_, c)::t) := c
  end
| _ := 1

-- only applies to add_term
private meta def term.scale_coeffs (c : ℚ) : term → term
| (term.add_term l) := term.add_term $ l.map (λ c', c*c')
| a := a

-- doesn't flatten
private meta def term.canonize_aux (stc : sterm → tactic sterm) : term → tactic sterm
| (term.add_term l) :=
  do l' ← add_term_of_sterm_list <$> l.to_list.mmap (λ pr, stc (sterm.of_pair pr)),
     let c := term.leading_coeff l',
     return ⟨c, term.scale_coeffs (1/c) l'⟩
/-  do l' : list (sterm × expr) ← l.to_list.mmap (λ st, do st' ← stc (sterm.of_pair st), e ← st'.to_expr, return (st', e)),
  let l' := (l'.qsort (λ pr1 pr2 : sterm × expr, pr2.2.lt pr1.2)).map prod.fst,
  match l' with
  | [] := return $ sterm.mk 1 term.add_term_empty
  | [st] := return st
  | (⟨c, tm⟩)::t := 
    if c = 1 then return $ sterm.mk 1 (add_term_of_sterm_list l')
    else return $ sterm.mk c (add_term_of_sterm_list (l'.map (sterm.scale (1/c))))
  end-/
| (term.mul_term l) := 
  do l' ←  l.to_list.mmap (λ pr, do t' ← term.canonize_aux pr.1, return (t', pr.2)),
     let (q, l'') := coeff_and_terms_of_sterm_z_list l',
     return ⟨q, mul_term_of_term_exp_list l''⟩
 /- do l' ← l.to_list.mmap (λ pr, do t' ← term.canonize_aux pr.1, e ← t'.to_expr, return ((t', pr.2), e)),
    let l' := (l'.qsort (λ pr1 pr2 : (sterm × ℤ) × expr, pr2.2.lt pr1.2)),
    let l' := l'.map prod.fst,
    let (q, l'') := coeff_and_terms_of_sterm_z_list l',
    return $ sterm.mk q (mul_term_of_term_exp_list l'')-/
| (term.atom e) := return $ sterm.mk 1 (term.atom e)

-- doesn't flatten
private meta def sterm.canonize_aux : sterm → tactic sterm 
| ⟨c, t⟩ := 
  do sterm.mk c' t' ← term.canonize_aux sterm.canonize_aux t,
  return $ sterm.mk (c*c') t'

/-private meta def flatten_sum_list : list (term × ℚ) → list (term × ℚ)
| [] := []
| ((term.add_term tm, c)::t) := 
  (tm.to_list.map (λ pr : term × ℚ, (pr.1, pr.2*c))).append (flatten_sum_list t)
| (h::t) := h::flatten_sum_list t

private meta def flatten_prod_list : list (term × ℤ) → list (term × ℤ)
| [] := []
| ((term.mul_term l, z)::t) := (l.to_list.map (λ pr : term × ℤ, (pr.1, pr.2*z))).append (flatten_prod_list t)
| (h::t) := h::flatten_prod_list t-/


private meta def scale_list {α} [has_mul α] (l : list (term × α)) (q : α) : list (term × α) :=
l.map (λ pr, {pr with snd := pr.snd * q})

private meta def flatten_sum_term_aux (t : term) (coeff : ℚ) (map : rb_map term ℚ) : rb_map term ℚ :=
match t with
| term.add_term l := add_term_coeff_pair_list map (scale_list l.to_list coeff)
| _ := map.insert t coeff
end

private meta def flatten_sum_term (map : rb_map term ℚ) : rb_map term ℚ :=
map.fold mk_rb_map flatten_sum_term_aux 

private meta def flatten_mul_term_aux (t : term) (exp : ℤ) (map : rb_map term ℤ) : rb_map term ℤ :=
match t with
| term.mul_term l := pow_term_exp_list map (scale_list l.to_list exp)
| _ := map.insert t exp
end

private meta def flatten_mul_term (map : rb_map term ℤ) : rb_map term ℤ :=
map.fold mk_rb_map flatten_mul_term_aux

private meta def term.flatten : term → term
| (term.add_term l) := term.add_term $ flatten_sum_term l --$ rb_map.of_list (flatten_sum_list l.to_list)
| (term.mul_term l) := term.mul_term $ flatten_mul_term l --$ rb_map.of_list (flatten_prod_list l.to_list)
| a := a

private meta def sterm.flatten : sterm → sterm 
| (sterm.mk c t) := sterm.mk c (term.flatten t)

meta def sterm.canonize : sterm → tactic sterm :=
sterm.canonize_aux ∘ sterm.flatten

meta def term.canonize (t : term) : tactic sterm :=
term.canonize_aux sterm.canonize (term.flatten t)

meta def expr.canonize (e : expr) : tactic sterm :=
match e with
| `(0 : ℚ) := return $ sterm.mk 0 (term.add_term_empty)
| _ := expr.to_sterm e >>= sterm.canonize
end

meta def expr.canonize_to_expr (e : expr) : tactic expr :=
match e with 
| `(0 : ℚ) := return e
| _ := expr.to_sterm e >>= sterm.canonize >>= sterm.to_expr
end

theorem canonized_inequality {P : Prop} (h : P) (canP : Prop) : canP := sorry

meta def prove_inequality (lhs rhs pf : expr) (op : gen_comp) : tactic expr :=
do sterm.mk clhs tlhs ← expr.canonize lhs, 
   --trace "tlhs", trace tlhs,
   srhs ← expr.canonize rhs,
   --trace "srhs", trace srhs,
   elhs ← tlhs.to_expr,
   if clhs = 0 then
     do erhs ← srhs.to_expr,
        tp ← op.reverse.to_function erhs elhs,
        mk_app ``canonized_inequality [pf, tp]
   else 
     do erhs ← (srhs.scale (1/clhs)).to_expr,
        tp ← ((if clhs < 0 then gen_comp.reverse else id) op).to_function elhs erhs, --to_expr ``(%%op %%elhs %%erhs),
        mk_app ``canonized_inequality [pf, tp]

meta def canonize_hyp : expr → tactic expr | e :=
do tp ← infer_type e, match tp with
/-| `(0 > %%e) := do ce ← expr.canonize e,
  mk_app ``canonized_inequality [e, `(0 > %%ce)]
| `(0 ≥ %%e) := do ce ← expr.canonize e,
  mk_app ``canonized_inequality [e, `(0 ≥ %%ce)]
| `(0 < %%e) := do ce ← expr.canonize e,
  mk_app ``canonized_inequality [e, `(0 < %%ce)]
| `(0 ≤ %%e) := do ce ← expr.canonize e,
  mk_app ``canonized_inequality [e, `(0 ≤ %%ce)]
| `(%%e > 0) := do ce ← expr.canonize e,
  mk_app ``canonized_inequality [e, `(%%ce > 0)]
| `(%%e ≥ 0) := do ce ← expr.canonize e,
  mk_app ``canonized_inequality [e, `(%%ce ≥ 0)]
| `(%%e < 0) := do ce ← expr.canonize e,
  mk_app ``canonized_inequality [e, `(%%ce < 0)]
| `(%%e ≤ 0) := do ce ← expr.canonize e,
  mk_app ``canonized_inequality [e, `(%%ce ≤ 0)]-/
| `(%%lhs ≤ %%rhs) := prove_inequality lhs rhs e gen_comp.le
| `(%%lhs < %%rhs) := prove_inequality lhs rhs e gen_comp.lt
| `(%%lhs ≥ %%rhs) := prove_inequality lhs rhs e gen_comp.ge
| `(%%lhs > %%rhs) := prove_inequality lhs rhs e gen_comp.gt
| `(%%lhs = %%rhs) := prove_inequality lhs rhs e gen_comp.eq
| `(%%lhs ≠ %%rhs) := prove_inequality lhs rhs e gen_comp.ne
| _ := /-trace e >>-/ do s ← to_string <$> pp e, fail $ "didn't recognize " ++ s
end

end canonize



constants a b c u v w z y x: ℚ
run_cmd (expr.to_term `(1*a + 3*(b + c) + 5*b)) >>= term.canonize >>= trace
run_cmd expr.canonize `(rat.pow (1*u + (2*rat.pow (1*rat.pow v 2 + 23*1) 3) + 1*z) 3) >>= trace

end polya
