import jacobi.Fredholm.Euler
import jacobi.Elliptic.ClippedUniqueness

/-!
Article: jacobi, Theorem D.7.
The proved normal multipliers determine the switching level and amplitude.
The original continuous optimizing density and its genuine Green diagonal
satisfy the printed autonomous equation and its exact zero first integral.
No profile equation or asymptotic condition is an additional premise.
Source: the actual Fredholm KKT optimizer, Gel'fand--Dikii and proved free diagonal limits.
Use: the true first integral and normalized profile are derived from this literal operator quantity.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual optimizing inverse Green diagonal.
Use: the true first integral and normalized profile are derived from this literal operator quantity.
Article: jacobi, Theorem D.7.
-/
def Optimizer.g {s M d : ℝ} (P : Optimizer s M d) (hs : 0≤s) : ℝ → ℝ := P.density.greenDiagonal s hs P.pole

/-- The switching level obtained from the actual upper-mass normal multiplier.
Use: separates the compact support and full support optimizer branches.
Article: jacobi, Theorem D.7.
-/
def Optimizer.edge {s M d : ℝ} (P : Optimizer s M d) : ℝ := (1/2:ℝ)+P.ell/(2*P.mu*s)

/-- The true amplitude determined by the actual determinant normal multiplier.
Use: the autonomous first integral is the actual optimizing Green equation.
Article: jacobi, Theorem D.7.
-/
def Optimizer.A {s M d : ℝ} (P : Optimizer s M d) : ℝ := (4/3:ℝ)*P.mu*s*sqrt (2*s)

/-- The actual normal multipliers put the Green switching level and amplitude in their full geometric range.
Use: the turning and profile classification require no guessed coefficient signs.
Article: jacobi, Theorem D.7.
Proof: the mass multiplier is nonnegative and the determinant multiplier and coupling are strictly positive. -/
theorem Optimizer.parameter_signs {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    (1/2:ℝ)≤P.edge ∧ 0<P.A := by
  have hden : 0<2*P.mu*s := mul_pos (mul_pos (by norm_num) P.mu_pos) hs
  exact ⟨le_add_of_nonneg_right (div_nonneg P.ell_nonneg hden.le),
    mul_pos (mul_pos (mul_pos (by norm_num) P.mu_pos) hs) (sqrt_pos.mpr (by positivity))⟩

/-- The original optimizing density has its exact continuous positive-part-square Green formula.
Use: closes the actual autonomous diagonal equation and profile quadratures.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: retain the actual normal Euler identity and factor its positive
2*mu*s coefficient out of the positive part. The actual square root of
2*s fixes the amplitude normalization exactly. -/
theorem Optimizer.density_formula {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) (x : ℝ) :
    2*s*P.density.value x=P.A^2*(max (P.g hs.le x-P.edge) 0)^2 := by
  -- This formula describes the genuine minimizer, not a prescribed stationary candidate.
  have he := congrFun (P.euler hs.le) x
  have hcoef : 0≤2*P.mu*s := le_of_lt (mul_pos (mul_pos (by norm_num) P.mu_pos) hs)
  have hinside : P.mu*s*(2*P.g hs.le x-1)-P.ell=(2*P.mu*s)*(P.g hs.le x-P.edge) := by
    unfold Optimizer.edge
    field_simp [P.mu_pos.ne',hs.ne']
    ring
  have hmax : max ((2*P.mu*s)*(P.g hs.le x-P.edge)) 0=
      (2*P.mu*s)*max (P.g hs.le x-P.edge) 0 := by
    rw [mul_max_of_nonneg _ _ hcoef,mul_zero]
  change P.density.value x=(4/9:ℝ)*(max (P.mu*s*(2*P.g hs.le x-1)-P.ell) 0)^2 at he
  rw [he,hinside,hmax]
  unfold Optimizer.A
  have hsq := sq_sqrt (show 0≤2*s by positivity)
  nlinarith [congrArg (fun r : ℝ => ((4/3:ℝ)*P.mu*s)^2*(max (P.g hs.le x-P.edge) 0)^2*r) hsq]

/-- The actual optimizing diagonal satisfies the classical Gel'fand--Dikii equation with its proved autonomous density.
Use: the source's conserved energy follows without an assumed weak-to-classical upgrade.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: apply the previously verified actual diagonal identity to the
continuous genuine minimizing density, then substitute its proved exact Euler formula. -/
theorem Optimizer.gd {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) (x : ℝ) :
    2*P.g hs.le x*deriv (deriv (P.g hs.le)) x-(deriv (P.g hs.le) x)^2-
      4*(1-P.A^2*(max (P.g hs.le x-P.edge) 0)^2)*(P.g hs.le x)^2+1=0 := by
  have hh := P.density.gelfand_dikii P.continuous hs.le P.pole x
  change 2*P.g hs.le x*deriv (deriv (P.g hs.le)) x-(deriv (P.g hs.le) x)^2-
    4*(1-2*s*P.density.value x)*(P.g hs.le x)^2+1=0 at hh
  rwa [P.density_formula hs x] at hh

/-- The genuine optimizing Green diagonal has the exact printed zero first integral.
Use: its true turning value, strict shape and all normalized quadratures are derived from this identity.
Article: jacobi, Theorem D.7.
Proof: the actual continuous density supplies a C2 Green diagonal bounded
below by one half and tending to one half at infinity. Apply the proved
conservation and mean-value argument to its genuine autonomous diagonal equation. -/
theorem Optimizer.first_integral {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) (x : ℝ) :
    (deriv (P.g hs.le) x)^2=phase P.A P.edge (P.g hs.le x) := by
  -- Every regularity and limit premise is discharged for the actual inverse diagonal.
  have hc : ContDiff ℝ 2 (P.g hs.le) := P.density.greenDiagonal_contDiff P.continuous hs.le P.pole
  exact green_first_integral P.A P.edge (P.parameter_signs hs).1
    (fun t => (hc.differentiable (by norm_num) t).hasDerivAt)
    (fun t => hc.differentiable_deriv_two t)
    (fun t => (by norm_num : (0:ℝ)<1/2).trans_le (P.density.fredholmGreen_diagonal hs.le P.pole t).1)
    (P.gd hs) (green_diagonal_limits P.density hs.le P.pole).1 x

end
end jacobi.Fredholm
