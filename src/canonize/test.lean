import .tactic

open polya

constants u v w x y z : ℝ

/- benchmak -/
set_option profiler true

example : x * (1 / 10 : ℚ) + x * (1 / 10 : ℚ) - x * (1 / 5 : ℚ) = 0 :=
by field1

example : (x + y) ^ 2 / (x + y) ^ 2 * x * y / x = y * (z + 2 * y * x - x * y * 2) * z⁻¹:=
by field1

example : x * ((y * w) * (z * (u * z) * v) * w) = w^2 * v * z^2 * u * y * x :=
by field1

example : x / x = (x / x) ^ 0 :=
by field1

example : y * (y / y) = (x * y) / x :=
by field1
