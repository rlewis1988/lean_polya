import .tactic

open polya tactic

constants u v w x y z : ℝ
constants (h1 : x ≠ 0) (h2 : z ≠ 0) (h3 : x + y ≠ 0)

/- benchmak -/
set_option profiler true

def i : num := 0
def j : num := 1
def t1 : @nterm ℚ _ := i * (1 / 10 : ℚ) + i * (1 / 10 : ℚ) - i * (1 / 5 : ℚ)
def t2 : @nterm ℚ _ := i - i

def e1 : @eterm ℚ _ := eterm.div (eterm.atom i) (eterm.atom i)
def e2 : @eterm ℚ _ := eterm.mul
  (eterm.div (eterm.atom i) (eterm.atom i))
  (eterm.div (eterm.atom j) (eterm.atom j))

theorem foo : norm_hyps e1 = [@nterm.atom ℚ _ i] := rfl
theorem bar : norm_hyps e2 = [@nterm.atom ℚ _ i, @nterm.atom ℚ _ j] := rfl

--lemma slow : t1.norm = 0 := rfl
lemma fast : t2.norm = 0 := rfl

theorem ex1 : x * (1 / 10 : ℚ) + x * (1 / 10 : ℚ) - x * (1 / 5 : ℚ) = 0 :=
begin
  field1,
end

theorem ex2 :
  (x + y) ^ 2 / (x + y) ^ 2 * x * y / x
  = y * (z + 2 * y * x - x * y * 2) * z⁻¹:=
begin
  field1,
  { exact h2 },
  { exact h1 },
  { exact h3 },
end

theorem ex3 :
  x * ((y * w) * (z * (u * z) * v) * w)
  = w^2 * v * z^2 * u * y * x :=
begin
  field1,
end

theorem ex4 : x / x = (x / x) ^ 0 :=
begin
  field1,
  { exact h1 },
end

theorem ex5 : y * (y / y) = (x * y) / x :=
begin
  field1,
  { exact h1 },
end
