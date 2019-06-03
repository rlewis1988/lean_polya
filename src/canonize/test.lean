import .tactic

open polya

constants u v w x y z : ℝ
constants
  (h1 : x ≠ 0)
  (h2 : y ≠ 0)
  (h3 : x + y ≠ 0)
  (h4 : z ≠ 0)

/- benchmak -/
set_option profiler true

example : x * (1 / 10 : ℚ) + x * (1 / 10 : ℚ) - x * (1 / 5 : ℚ) = 0 :=
by field1

example : (x + y) ^ 2 / (x + y) ^ 2 * x * y / x = y * (z + 2 * y * x - x * y * 2) * z⁻¹:=
begin
  field1,
  exact h1,
  exact h3,
  exact h4,
end

example : x * ((y * w) * (z * (u * z) * v) * w) = w^2 * v * z^2 * u * y * x :=
by field1

example : x / x = (x / x) ^ 0 :=
begin
  field1,
  exact h1,
end

example : y * (y / y) = (x * y) / x :=
begin
  field1,
  exact h1,
end
