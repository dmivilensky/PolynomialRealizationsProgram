import polyak.General.Parameters

/-! Article: eq:Hr, eq:E and Appendix D lem:cubic.
The source cubic and its two equivalent lag-one representations. -/
namespace polyak.General
noncomputable section
namespace Tuning

def Xi (q : Tuning) (c : ℝ) : ℝ :=
  (q.B^2-(1-q.beta)^2-q.A^2+2*q.A*(1+q.beta)*c-4*q.beta*c^2) /
    (2*q.B*(1-q.beta))

def L (q : Tuning) (c : ℝ) : ℝ :=
  4*q.beta*c^2 + 2*(q.y-1-2*q.beta-q.beta^2+q.beta*q.x)*c +
    (2-2*q.x+q.x*q.y+2*q.beta^2-2*q.beta*q.y)

def H (q : Tuning) (r c : ℝ) : ℝ :=
  -4*q.beta*r^3*c^3 -
  2*r^2*(r^2*q.y-r^2-q.beta*r^2+q.beta*q.x-3*q.beta-q.beta^2)*c^2 -
  r*(r^4+r^2*q.x*q.y-2*r^2*q.x-2*r^2*q.y+3*r^2+q.beta^2*r^2+3*q.beta^2-
    q.beta*r^2*q.x-q.beta*r^2*q.y+2*q.beta*r^2-q.beta*q.x-q.beta*q.y+2*q.beta)*c +
  r^4*(1+q.y-q.x)+r^2*(1-q.x)*(1-q.y)-2*q.beta*r^2*q.y+q.beta^2*r^2+q.beta^2

theorem H_one (q : Tuning) (c : ℝ) : q.H 1 c = (1-c)*q.L c := by
  dsimp [H,L]; ring

theorem L_eq_Xi (q : Tuning) (c : ℝ) :
    q.L c = (q.y-q.x)*(1-q.beta)*(1+c-q.Xi c) := by
  have hB := q.B_ne_zero
  have hb : 1-q.beta ≠ 0 := ne_of_gt (sub_pos.2 q.beta_lt_one)
  dsimp [Xi]
  field_simp
  dsimp [L,A,B] at *
  ring

theorem L_neg_one (q : Tuning) : q.L (-1) = (2+2*q.beta-q.x)*(2+2*q.beta-q.y) := by
  dsimp [L]; ring
theorem L_one (q : Tuning) : q.L 1 = 2*(1-q.beta)*(q.y-q.x)+q.x*q.y := by
  dsimp [L]; ring
theorem L_neg_one_pos (q : Tuning) : 0 < q.L (-1) := by
  rw [q.L_neg_one]
  apply mul_pos <;> linarith [q.x_lt_y,q.y_lt]
theorem L_one_pos (q : Tuning) : 0 < q.L 1 := by
  rw [q.L_one]
  positivity [q.x_pos, q.y_pos, q.x_lt_y, q.beta_lt_one]

theorem GTD_identity (q : Tuning) (c : ℝ) :
    q.x^2-2*(q.beta-c+(q.x/q.y)*(1-q.beta*c))*q.x+
      2*(q.x/q.y)*(1-c)*(1+q.beta^2-2*q.beta*c)=(q.x/q.y)*q.L c := by
  dsimp [L]
  field_simp [ne_of_gt q.y_pos]
  ring

end Tuning
end
end polyak.General
