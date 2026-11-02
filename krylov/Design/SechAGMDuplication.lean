import krylov.Design.SquareLambertDifference
import krylov.Design.HyperbolicNomeParameters
import krylov.Design.EllipticAGM

/-!
Article: main_krylov, apC:lem:poisson, actual hyperbolic AGM duplication.
Use: derive both genuine arithmetic-geometric coordinates from the proved
integer convolutions and the proved signed Lambert rearrangement. Iterating
them preserves the actual elliptic integral and evaluates it at infinity.
Source: genuine sech products, actual Fubini, and the earlier Landen integral proof.
-/

namespace krylov.Design
noncomputable section
open Real Filter Set jacobi.Young chebyshev1.SineJacobi
open scoped Topology

/-- The genuine alternating sech mass has the exact squared geometric duplication identity.
Article: main_krylov, apC:lem:poisson, the critical elliptic product. -/
theorem latticeSechAlternatingMass_duplication_sq {θ : ℝ} (hθ : 0 < θ) :
    latticeSechAlternatingMass (2 * θ) ^ 2 = latticeSechMass θ * latticeSechAlternatingMass θ := by
  have h2θ : 0 < 2 * θ := mul_pos (by norm_num) hθ
  rw [latticeSechAlternatingMass_square h2θ, latticeSechMass_mul_alternating hθ,
    latticeSechSquaredAlternatingMass_eq hθ,
    latticeSechSquaredMass_eq h2θ, latticeSechSquaredMass_eq hθ]
  have h := sampledSechSquared_duplication_difference hθ
  linarith

/-- The actual positive alternating mass is the true geometric mean at doubled spacing.
Article: main_krylov, apC:lem:poisson, the second genuine AGM coordinate. -/
theorem latticeSechAlternatingMass_duplication {θ : ℝ} (hθ : 0 < θ) :
    latticeSechAlternatingMass (2 * θ) = sqrt (latticeSechMass θ * latticeSechAlternatingMass θ) := by
  rw [← latticeSechAlternatingMass_duplication_sq hθ,
    Real.sqrt_sq (latticeSechAlternatingMass_pos (mul_pos (by norm_num) hθ)).le]

/-- The actual homogeneous elliptic integral is preserved by doubling the true hyperbolic spacing.
Article: main_krylov, apC:lem:poisson, the real integral-preserving elliptic nome iteration. -/
theorem gaussIntegral_latticeSech_step {θ : ℝ} (hθ : 0 < θ) :
    gaussIntegral (latticeSechMass θ) (latticeSechAlternatingMass θ) =
      gaussIntegral (latticeSechMass (2 * θ)) (latticeSechAlternatingMass (2 * θ)) := by
  have hd := latticeSechMass_strict_domain hθ
  rw [gaussIntegral_agm_step (hd.1.trans hd.2) hd.1 hd.2.le,
    ← latticeSechMass_duplication hθ, ← latticeSechAlternatingMass_duplication hθ]

/-- The genuine homogeneous elliptic integral of the actual hyperbolic masses is pi/2.
Article: main_krylov, apC:lem:poisson.
Proof: actual spacing doublings preserve the real integral, and both actual
mass coordinates converge to one as the doubled spacing tends to infinity. -/
theorem gaussIntegral_latticeSech_eq {θ : ℝ} (hθ : 0 < θ) :
    gaussIntegral (latticeSechMass θ) (latticeSechAlternatingMass θ) = π / 2 := by
  let T : ℕ → ℝ := fun n => θ * (2 : ℝ) ^ n
  have hp (n : ℕ) : 0 < T n := mul_pos hθ (pow_pos (by norm_num) n)
  have hi (n : ℕ) : gaussIntegral (latticeSechMass (T n)) (latticeSechAlternatingMass (T n)) =
      gaussIntegral (latticeSechMass θ) (latticeSechAlternatingMass θ) := by
    induction n with
    | zero => simp only [T, pow_zero, mul_one]
    | succ n ih =>
      rw [show T (n + 1) = 2 * T n by dsimp [T]; rw [pow_succ]; ring]
      exact (gaussIntegral_latticeSech_step (hp n)).symm.trans ih
  have ht : Tendsto T atTop atTop :=
    Filter.Tendsto.const_mul_atTop hθ (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have ha := latticeSechMass_tendsto_one.comp ht
  have hb := latticeSechAlternatingMass_tendsto_one.comp ht
  have hg := gaussIntegral_tendsto ha hb (by norm_num : (0 : ℝ) < 1)
  simp only [Function.comp_def, hi, mul_one] at hg
  exact tendsto_nhds_unique tendsto_const_nhds hg

/-- The actual complete elliptic integral at the genuine hyperbolic modulus is pi times the true sech mass divided by two.
Article: main_krylov, apC:lem:poisson, the substantive elliptic-integral reformulation.
Every transformation and limit is derived from the original integral and actual series. -/
theorem ellipticK_sechModulus {θ : ℝ} (hθ : 0 < θ) :
    ellipticK (sechModulus θ) = π / 2 * latticeSechMass θ := by
  have h := gaussIntegral_latticeSech_eq hθ
  change ellipticK (sechModulus θ) / latticeSechMass θ = π / 2 at h
  have hp := latticeSechMass_strict_domain hθ
  exact (div_eq_iff (hp.1.trans hp.2).ne').mp h

end
end krylov.Design
