import jacobi.Jacobi.QuadraticTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: jacobi, Proposition A.1.
Source: DLMF 18.7.15--18.7.16 and Kindermann's residual formula as
stated in jacobi. No convergence theorem about the original iterates
is assumed in proving the polynomial identities.
Use: brakhage_residual and nesterov_square_formula identify the actual source residuals, including the odd linear factor.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial Complex jacobi.Jacobi

/-- The original endpoint-normalized Gegenbauer polynomial has the exact quadratic Jacobi form for either parity.
Use: brakhage_residual and nesterov_square_formula identify the actual source residuals, including the odd linear factor.
Article: jacobi, Proposition A.1.
Proof: normalize the original Gegenbauer function by its nonzero endpoint value and apply the proved polynomial quadratic transformation. -/
theorem gegenbauer_quadratic {g : ℝ} (hg : 0<g) {e : ℕ} (he : e≤1)
    (m : ℕ) (z : ℂ) :
    gegenbauer (g:ℂ) (2*m+e) z/gegenbauer (g:ℂ) (2*m+e) 1=
      z^e*normalized ((g:ℂ)-1/2) ((e:ℂ)-1/2) m (2*z^2-1) := by
  rw [gegenbauer_normalized (by simpa using hg)]
  convert quadratic_transform_complex (a := g-1/2) (by linarith) he m z using 1 <;>
    push_cast <;> rfl

/-- Brakhage's original even Gegenbauer residual is exactly the normalized Jacobi factor at every real physical argument.
Use: applies the already verified Jacobi fibre and hard-edge theory to the nu-method terminal residual without a new polynomial family.
Article: jacobi, Proposition A.1.
Proof: the even quadratic identity has no remaining square-root factor; the genuine nonnegative square root squares to 1-lambda. -/
theorem brakhage_residual {v : ℝ} (hv : 0<v) (m : ℕ) {l : ℝ} (hl : l≤1) :
    gegenbauer ((2*v:ℝ):ℂ) (2*m) (Real.sqrt (1-l):ℂ)/
      gegenbauer ((2*v:ℝ):ℂ) (2*m) 1=
        aeval (l:ℂ) (shiftedPolynomial (2*v-1/2) (-1/2) m) := by
  -- The normalization and polynomial are the original Jacobi objects.
  have h := gegenbauer_quadratic (g := 2*v) (by positivity) (e := 0) (by omega)
    m (Real.sqrt (1-l):ℂ)
  have hs : (Real.sqrt (1-l):ℂ)^2=1-(l:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0≤1-l)
  rw [hs] at h
  rw [shiftedPolynomial_aeval]
  have hx : 2*(1-(l:ℂ))-1=1-2*(l:ℂ) := by ring
  rw [hx] at h
  norm_num at h ⊢
  exact h

/-- The genuine Jacobi factor in the two parity cases of the Nesterov residual.
Use: nesterovResidual appends the source's Landweber factor to this already verified Jacobi family.
Article: jacobi, Proposition A.1.
-/
def nesterovFactor (b : ℝ) (m e : ℕ) : Polynomial ℝ :=
  shiftedPolynomial (b/2) ((e:ℝ)-1/2) m

/-- The literal Nesterov polynomial after extracting its integer Landweber power.
Use: nesterov_square_formula and nesterov_sqrt_formula identify it with the source residual; its hard-edge and ordered zeros are then proved for this same object.
Article: jacobi, Proposition A.1.
-/
def nesterovResidual (b : ℝ) (m e : ℕ) : Polynomial ℝ :=
  (1-X)^(m+1+e)*nesterovFactor b m e

/-- The original factorized Nesterov polynomial equals Kindermann's Gegenbauer expression in the square coordinate throughout the complex plane.
Use: nesterov_sqrt_formula restores the printed real square-root expression, while the complex polynomial form supplies the genuine entire hard-edge limit.
Article: jacobi, Proposition A.1.
Proof: the quadratic transformation gives z^e times the Jacobi factor. The two integer powers of z combine to exactly the polynomial Landweber exponent. -/
theorem nesterov_square_formula {b : ℝ} (hb : -1<b) {e : ℕ} (he : e≤1)
    (m : ℕ) (z : ℂ) :
    aeval (1-z^2) (nesterovResidual b m e)=
      z^(2*m+2+e)*(gegenbauer (((b+1)/2:ℝ):ℂ) (2*m+e) z/
        gegenbauer (((b+1)/2:ℝ):ℂ) (2*m+e) 1) := by
  -- The square coordinate avoids every square-root branch restriction.
  rw [gegenbauer_quadratic (by linarith : 0<(b+1)/2) he]
  simp only [nesterovResidual,nesterovFactor,map_mul,map_pow,map_sub,map_one,
    aeval_X,shiftedPolynomial_aeval,sub_sub_cancel]
  have ha : (((b+1)/2:ℝ):ℂ)-1/2=((b/2:ℝ):ℂ) := by push_cast; ring
  have hc : (((e:ℝ)-1/2:ℝ):ℂ)=(e:ℂ)-1/2 := by push_cast; rfl
  rw [ha,hc]
  have hx : 1-2*(1-z^2)=2*z^2-1 := by ring
  rw [hx,← mul_assoc,← pow_add,← pow_mul]
  congr 2
  omega

/-- The literal polynomial has exactly the printed real-power square-root residual formula, including lambda=1.
Use: the later entire hard-edge limit and complete small-zero limit concern the original Nesterov residual, rather than an unconnected polynomial surrogate.
Article: jacobi, Proposition A.1.
Proof: the real-power prefactor equals the integer power of the nonnegative square root. Substitute its actual square into the complex polynomial identity. -/
theorem nesterov_sqrt_formula {b : ℝ} (hb : -1<b) {e : ℕ} (he : e≤1)
    (m : ℕ) {l : ℝ} (hl : l≤1) :
    aeval (l:ℂ) (nesterovResidual b m e)=
      ((1-l)^(((2*m+2+e:ℕ):ℝ)/2):ℝ)*
        (gegenbauer (((b+1)/2:ℝ):ℂ) (2*m+e) (Real.sqrt (1-l):ℂ)/
          gegenbauer (((b+1)/2:ℝ):ℂ) (2*m+e) 1) := by
  have hs : (Real.sqrt (1-l):ℂ)^2=1-(l:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0≤1-l)
  have hp := Real.rpow_div_two_eq_sqrt (x := 1-l) ((2*m+2+e:ℕ):ℝ) (by linarith)
  rw [Real.rpow_natCast] at hp
  rw [hp,Complex.ofReal_pow]
  simpa only [hs,sub_sub_cancel] using nesterov_square_formula hb he m (Real.sqrt (1-l):ℂ)

/-- The literal Nesterov residual has value one at the normalization origin in both parities.
Use: its terminal realization and hard-edge limit preserve the original residual normalization.
Article: jacobi, Proposition A.1.
Proof: the Jacobi factor is endpoint-normalized and the Landweber factor is one at zero. -/
theorem nesterovResidual_zero (b : ℝ) (m e : ℕ) :
    (nesterovResidual b m e).eval 0=1 := by
  simp [nesterovResidual,nesterovFactor,shiftedPolynomial_zero]

/-- The integer Jacobi and Landweber stage lengths add to the exact source iteration count, including the zero-degree factor.
Use: the fixed-operator terminal realization has exactly k applications, rather than only an asymptotic count.
Article: jacobi, Proposition A.1.
Proof: associativity of natural-number addition gives the exact count. -/
theorem nesterov_stage_count (m e : ℕ) : m+(m+1+e)=2*m+1+e := by omega

end
end jacobi.Applications
