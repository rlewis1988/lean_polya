import .tactic

open polya tactic

constants u v w x y z : ℝ
constants
  (h1 : x ≠ 0)
  (h2 : z ≠ 0)
  (h3 : x + y ≠ 0)

/- benchmak -/
set_option profiler true

lemma ex1 : x * (1 / 10 : ℚ) + x * (1 / 10 : ℚ) - x * (1 / 5 : ℚ) = 0 :=
begin
  field1,
end

theorem ex2 :
  (x + y) ^ 2 / (x + y) ^ 2 * x * y / x
  = y * (z + 2 * y * x - x * y * 2) * z⁻¹:=
begin
  field1,
  { exact h1 },
  { exact h3 },
  { exact h2 },
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
