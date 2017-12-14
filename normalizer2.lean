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

meta def get_sum_components : expr → list expr
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
end


end aux

meta mutual inductive sterm, term
with sterm : Type
| scaled : ℚ → term → sterm
with term : Type
| add_term : list sterm → term
| mul_term : list (term × ℤ) → term
| atom : expr → term

meta def term.is_zero : term → bool
| (term.add_term []) := tt
| _ := ff

meta def sterm.is_zero : sterm → bool
| (sterm.scaled c t) := t.is_zero || (c = 0)

meta def term.scale (q : ℚ) (t : term) : sterm :=
sterm.scaled q t

meta def sterm.term : sterm → term
| (sterm.scaled _ t) := t

meta def sterm.coeff : sterm → ℚ
| (sterm.scaled q _) := q

meta def sterm.scale (q : ℚ) : sterm → sterm
| (sterm.scaled q' t) := sterm.scaled (q*q') t

open tactic

private meta def expr.to_term_aux (tst : expr → tactic sterm) : expr → tactic term | e := 
if is_sum e then
  let scs := get_sum_components e in
  term.add_term <$> scs.mmap tst
else if is_prod e then 
  let scs := get_prod_components e in
  do scs' ← scs.mmap get_comps_of_exp,
     term.mul_term <$> scs'.mmap (λ pr, do tm ← expr.to_term_aux pr.1, return (tm, pr.2))
else return $ term.atom e
          
meta def expr.to_sterm : expr → tactic sterm | e :=
match e with
| `(%%c*%%t) := 
  if is_num c then
    do q ← eval_expr ℚ c,
       sterm.scale q <$> expr.to_sterm t
  else sterm.scaled 1 <$> expr.to_term_aux expr.to_sterm e
| t := sterm.scaled 1 <$> expr.to_term_aux expr.to_sterm t
end       

meta def expr.to_term : expr → tactic term := expr.to_term_aux expr.to_sterm


private meta def fold_op_app_aux (op : pexpr) : expr → list expr → tactic expr
| h [] := return h
| h (h'::t) := do h'' ← to_expr ``(%%op %%h %%h'), fold_op_app_aux h'' t

private meta def fold_op_app (op : pexpr) (dflt : expr) : list expr → tactic expr
| [] := return dflt
| (h::t) := fold_op_app_aux op h t


private meta def term.to_expr_aux (ste : sterm → tactic expr) : term → tactic expr
| (term.add_term []) := return `(0 : ℚ)
| (term.add_term l) :=
  do l' ← l.mmap ste,
     fold_op_app ``((+)) `(0 : ℚ) l'
| (term.mul_term []) := return `(1 : ℚ)
| (term.mul_term l) :=
  do l' ← l.mmap (λ pr, do e' ← term.to_expr_aux pr.1, return (e', pr.2)),
  let l'' := l'.map (λ pr, `(rat.pow %%(pr.1) %%(pr.2.reflect))),
     fold_op_app ``((*)) `(1 : ℚ) l''
| (term.atom e) := return e
    

meta def sterm.to_expr : sterm → tactic expr
| (sterm.scaled c t) :=
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
| ((sterm.scaled c tm, z)::t) :=
   let (q, l) := coeff_and_terms_of_sterm_z_list  t in
  (q * rat.pow c z, (tm, z)::l)

/-private meta def coeff_and_terms_of_sterm_z_list : ℚ → list (term × ℤ) → list (sterm × ℤ) → ℚ × list (term × ℤ)
| acc l [] := (acc, l)
| acc l ((sterm.scaled c tm, z)::t) := (tm, z)::coeff_and_terms_of_sterm_z_list (acc*rat.pow c z) t-/

-- doesn't flatten
private meta def term.canonize_aux (stc : sterm → tactic sterm) : term → tactic sterm
| (term.add_term l) :=
  do l' : list (sterm × expr) ← l.mmap (λ st, do st' ← stc st, e ← st'.to_expr, return (st', e)),
  let l' := (l'.qsort (λ pr1 pr2 : sterm × expr, pr2.2.lt pr1.2)).map prod.fst,
  match l' with
  | [] := return $ sterm.scaled 1 (term.add_term [])
  | [st] := return st
  | (sterm.scaled c tm)::t := 
    if c = 1 then return $ sterm.scaled 1 (term.add_term l')
    else return $ sterm.scaled c (term.add_term (l'.map (sterm.scale (1/c))))
  end
| (term.mul_term l) := 
  do l' ← l.mmap (λ pr, do t' ← term.canonize_aux pr.1, e ← t'.to_expr, return ((t', pr.2), e)),
    let l' := (l'.qsort (λ pr1 pr2 : (sterm × ℤ) × expr, pr2.2.lt pr1.2)),
    let l' := l'.map prod.fst,
    let (q, l'') := coeff_and_terms_of_sterm_z_list l',
    return $ sterm.scaled q (term.mul_term l'')
| (term.atom e) := return $ sterm.scaled 1 (term.atom e)

-- doesn't flatten
private meta def sterm.canonize_aux : sterm → tactic sterm 
| (sterm.scaled c t) := 
  do sterm.scaled c' t' ← term.canonize_aux sterm.canonize_aux t,
  return $ sterm.scaled (c*c') t'

private meta def flatten_sum_list : list sterm → list sterm
| [] := []
| (sterm.scaled c (term.add_term l)::t) := 
  (l.map (sterm.scale c)).append (flatten_sum_list t)
| (h::t) := h::flatten_sum_list t

private meta def flatten_prod_list : list (term × ℤ) → list (term × ℤ)
| [] := []
| ((term.mul_term l, z)::t) := (l.map (λ pr : term × ℤ, (pr.1, pr.2*z))).append (flatten_prod_list t)
| (h::t) := h::flatten_prod_list t

private meta def term.flatten : term → term
| (term.add_term l) := term.add_term (flatten_sum_list l)
| (term.mul_term l) := term.mul_term (flatten_prod_list l)
| a := a

private meta def sterm.flatten : sterm → sterm 
| (sterm.scaled c t) := sterm.scaled c (term.flatten t)

meta def sterm.canonize : sterm → tactic sterm :=
sterm.canonize_aux ∘ sterm.flatten

meta def term.canonize (t : term) : tactic sterm :=
term.canonize_aux sterm.canonize (term.flatten t)

meta def expr.canonize (e : expr) : tactic sterm :=
match e with
| `(0 : ℚ) := return $ sterm.scaled 0 (term.add_term [])
| _ := expr.to_sterm e >>= sterm.canonize
end

meta def expr.canonize_to_expr (e : expr) : tactic expr :=
match e with 
| `(0 : ℚ) := return e
| _ := expr.to_sterm e >>= sterm.canonize >>= sterm.to_expr
end

theorem canonized_inequality {P : Prop} (h : P) (canP : Prop) : canP := sorry

meta def prove_inequality (lhs rhs pf : expr) (op : gen_comp) : tactic expr :=
do sterm.scaled clhs tlhs ← expr.canonize lhs, 
   trace "tlhs", trace tlhs,
   srhs ← expr.canonize rhs,
   trace "srhs", trace srhs,
   elhs ← tlhs.to_expr,
   erhs ← (srhs.scale (1/clhs)).to_expr,
   tp ← op.to_function elhs erhs, --to_expr ``(%%op %%elhs %%erhs),
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
| _ := trace e >> fail "didn't recognize e"
end

end canonize



constants a b c u v w z y x: ℚ
--run_cmd (expr.to_term `(1*a + 3*(b + c) + 5*b)) >>= term.canonize >>= trace
run_cmd expr.canonize `(rat.pow (1*u + (1*rat.pow (1*rat.pow v 2 + 23*1) 3) + 1*z) 3) >>= trace

end polya
