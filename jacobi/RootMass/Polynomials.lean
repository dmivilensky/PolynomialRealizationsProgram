import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-!
Article: jacobi, Theorem D.8.
The literal scalar polynomials and inverse-profile coordinate are analyzed
on their whole stated parameter range a>-2*sqrt(3). Their denominators are
proved positive, and the exact positive derivative gives strict monotonicity.
Source: polynomial algebra and the real mean value theorem.
Use: defines the inverse coordinate and every root-mass quadrature.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The root-mass profile polynomial p(n)=3*n²+a*n+1.
Use: defines the inverse coordinate and every root-mass quadrature.
Article: jacobi, Theorem D.8.
-/
def p (a n : ℝ) : ℝ := 3*n^2+a*n+1

/-- The second positive root-mass polynomial q(n)=n²+a*n+3.
Use: its positivity controls the inverse coordinate derivative and the quadrature denominators.
Article: jacobi, Theorem D.8.
-/
def q (a n : ℝ) : ℝ := n^2+a*n+3

/-- The literal increasing root-mass coordinate psi.
Use: its inverse parametrizes the compact optimizing profile and the fixed-interval quadratures.
Article: jacobi, Theorem D.8.
-/
def psi (a n : ℝ) : ℝ := n^3*(n^2-1)/(p a n)^2

/-- The exact derivative of the root-mass coordinate, written with its positive factors.
Use: inverse-function regularity and all genuine profile Jacobians use this same derivative.
Article: jacobi, Theorem D.8.
-/
def psiSlope (a n : ℝ) : ℝ := n^2*(3*n^2-1)*q a n/(p a n)^3

/-- The source parameter range implies a>-4 and a²<12 whenever a is negative.
Use: supplies elementary coercive estimates for the two literal profile polynomials.
Article: jacobi, Theorem D.8.
Proof: sqrt(3)<2 and sqrt(3)²=3; squaring the negative-side bound is then legitimate. -/
theorem parameter_bounds {a : ℝ} (ha : -2*sqrt 3<a) : -4<a ∧ (a<0 → a^2<12) := by
  have hs := sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hp := sqrt_nonneg (3:ℝ)
  have hlt : sqrt (3:ℝ)<2 := by nlinarith
  constructor
  · linarith
  · intro hn
    nlinarith

/-- The actual p polynomial has the source's positive lower bound on the full profile domain.
Use: every coordinate and quadrature denominator is genuinely nonzero.
Article: jacobi, Theorem D.8.
Proof: factor p(n)-p(1)=(n-1)*(3*(n+1)+a) and use a>-4. -/
theorem p_bounds {a n : ℝ} (ha : -2*sqrt 3<a) (hn : 1≤n) :
    0<4+a ∧ 4+a≤p a n ∧ 0<6*n+a := by
  have hab := (parameter_bounds ha).1
  have hh := mul_nonneg (sub_nonneg.mpr hn) (by linarith : 0≤3*(n+1)+a)
  unfold p
  exact ⟨by linarith,by nlinarith,by linarith⟩

/-- The actual q polynomial is positive on the entire stated parameter and profile domain.
Use: proves the strict sign of psi' without imposing an artificial stronger parameter restriction.
Article: jacobi, Appendix D.5 (root-mass coordinate and inverse).
Proof: if a>=-2 compare with q(1); otherwise complete the square and use a²<12. -/
theorem q_pos {a n : ℝ} (ha : -2*sqrt 3<a) (hn : 1≤n) : 0<q a n := by
  have hab := (parameter_bounds ha).1
  unfold q
  by_cases hh : -2≤a
  · have hp := mul_nonneg (sub_nonneg.mpr hn) (by linarith : 0≤n+1+a)
    nlinarith
  · have hs := (parameter_bounds ha).2 (by linarith)
    nlinarith [sq_nonneg (n+a/2)]

/-- The literal inverse-profile coordinate has its exact positive-factor derivative.
Use: establishes actual differentiability before invoking inverse-function and substitution theorems.
Article: jacobi, Theorem D.8.
Proof: differentiate the actual rational function and compare polynomial coefficients after clearing the nonzero p denominator. -/
theorem psi_hasDerivAt {a n : ℝ} (hp : p a n≠0) : HasDerivAt (psi a) (psiSlope a n) n := by
  -- The rational identity is verified in the field of real numbers, not numerically sampled.
  have hP : HasDerivAt (p a) (6*n+a) n := by
    convert (((hasDerivAt_id n).pow 2).const_mul 3).add ((hasDerivAt_id n).const_mul a) |>.add_const 1 using 1
    · rfl
    · norm_num
      ring
  convert (((hasDerivAt_id n).pow 3).mul (((hasDerivAt_id n).pow 2).sub_const 1)).div (hP.pow 2) (pow_ne_zero 2 hp) using 1
  · rfl
  · dsimp only [psiSlope,Pi.pow_apply,Pi.mul_apply,id_eq]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub]
    field_simp [hp]
    unfold p q
    ring

/-- The rational coordinate is smooth at every point with nonzero p denominator.
Use: the actual inverse coordinate is smooth also at its n=1 endpoint.
Article: jacobi, Theorem D.8.
Proof: quotient of polynomial smooth maps with a proved nonzero denominator. -/
theorem psi_contDiffAt {a n : ℝ} (hp : p a n≠0) : ContDiffAt ℝ ⊤ (psi a) n := by
  have hP : ContDiff ℝ ⊤ (p a) := by unfold p; fun_prop
  have hN : ContDiff ℝ ⊤ (fun n : ℝ => n^3*(n^2-1)) := by fun_prop
  exact hN.contDiffAt.div (hP.pow 2).contDiffAt (pow_ne_zero 2 hp)

/-- The coordinate derivative is strictly positive throughout the actual closed profile domain.
Use: makes psi injective and licenses its smooth inverse, including at the lower endpoint.
Article: jacobi, Theorem D.8.
Proof: every numerator factor and the actual denominator is strictly positive. -/
theorem psiSlope_pos {a n : ℝ} (ha : -2*sqrt 3<a) (hn : 1≤n) : 0<psiSlope a n := by
  obtain ⟨ha0,hp,_⟩ := p_bounds ha hn
  have hpn : 0<p a n := ha0.trans_le hp
  have hn0 : 0<n := zero_lt_one.trans_le hn
  exact div_pos (mul_pos (mul_pos (sq_pos_of_pos hn0) (by nlinarith)) (q_pos ha hn)) (pow_pos hpn 3)

/-- The actual rational coordinate is strictly increasing on its full stated profile domain.
Use: the quadrature inverse and its unique parameter are genuine mathematical inverses.
Article: jacobi, Theorem D.8.
Proof: the proved smooth rational function is continuous on the interval;
its actual derivative is strictly positive, so the mean value theorem applies. -/
theorem psi_strictMono {a : ℝ} (ha : -2*sqrt 3<a) : StrictMonoOn (psi a) (Ici (1:ℝ)) := by
  -- No monotonicity certificate is assumed for the inverse used later.
  have hp (n : ℝ) (hn : 1≤n) : p a n≠0 := ((p_bounds ha hn).1.trans_le (p_bounds ha hn).2.1).ne'
  apply strictMonoOn_of_deriv_pos (convex_Ici 1)
  · exact fun n hn => (psi_contDiffAt (hp n hn)).continuousAt.continuousWithinAt
  · intro n hn
    have hni : 1≤n := interior_subset hn
    rw [(psi_hasDerivAt (hp n hni)).deriv]
    exact psiSlope_pos ha hni

/-- The lower profile endpoint has coordinate zero exactly.
Use: fixes the boundary value of the actual inverse coordinate.
Article: jacobi, Theorem D.8.
Proof: the factor n²-1 in the literal numerator vanishes. -/
theorem psi_one (a : ℝ) : psi a 1=0 := by simp [psi]

end
end jacobi.RootMass
