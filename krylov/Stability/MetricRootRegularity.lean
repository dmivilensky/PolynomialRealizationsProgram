import krylov.Stability.CanonicalContinuity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Article: main_krylov, lem:U, true joint positive metric-root regularity.
Use: discharge the actual variable-base root and inverse-root regularity
in canonical method families at every finite order, C-infinity and real analyticity.
Source: the standard Sylvester derivative of squaring, the positive finite
spectral theorem and mathlib's C-r inverse function theorem. The actual CFC
root is identified with the local inverse by its genuine continuity and square identity.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Topology krylov.Secant chebyshev1
open scoped MatrixOrder Matrix.Norms.L2Operator ContDiff
variable {n : ℕ}

/-- The genuine linear Sylvester map at a real matrix, X mapped to RX plus XR.
Use: The genuine linear Sylvester map at a real matrix, X mapped to RX plus XR.
Article: main_krylov, lem:U.
Proof: Both multiplication operations are real linear. -/
def sylvesterLinear (R : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun X := R*X+X*R
  map_add' X Y := by noncomm_ring
  map_smul' c X := by simp only [Matrix.mul_smul,Matrix.smul_mul,smul_add,RingHom.id_apply]

/-- The genuine Sylvester map at a positive definite matrix is injective on the full physical matrix space.
Use: The genuine Sylvester map at a positive definite matrix is injective on the full physical matrix space.
Article: main_krylov, lem:U.
Proof: In the actual spectral basis each coordinate is multiplied by the strictly positive sum of two genuine eigenvalues. -/
theorem sylvesterLinear_injective (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosDef) :
    Function.Injective (sylvesterLinear R) := by
  -- In genuine spectral coordinates no eigenvalue sum vanishes, including the empty matrix case.
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro X hX
  have hz : R*X+X*R=0 := hX
  let B := SpectralBasis.ofHermitian R hR.1
  apply B.coordinates_injective
  have hdiag : B.coordinates R=diagonal B.eigenvalues := B.diagonalize
  have hc : B.coordinates (R*X+X*R)=B.coordinates (R*X)+B.coordinates (X*R) := by
    simp only [SpectralBasis.coordinates,Matrix.mul_add,Matrix.add_mul]
  have he := congrArg B.coordinates hz
  rw [hc,B.coordinates_mul,B.coordinates_mul,hdiag] at he
  have hp (i : Fin n) : 0<B.eigenvalues i := hR.eigenvalues_pos i
  have hz0 : B.coordinates (0 : Matrix (Fin n) (Fin n) ℝ)=0 := by simp [SpectralBasis.coordinates]
  rw [hz0] at he ⊢
  ext i j
  have hij := congrFun (congrFun he i) j
  simp only [Matrix.add_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.zero_apply] at hij
  have hsum : B.eigenvalues i+B.eigenvalues j≠0 := (add_pos (hp i) (hp j)).ne'
  exact (mul_eq_zero.mp (show (B.eigenvalues i+B.eigenvalues j)*B.coordinates X i j=0 by nlinarith)).resolve_left hsum

/-- The true Sylvester map at a positive definite matrix is a continuous linear equivalence.
Use: The true Sylvester map at a positive definite matrix is a continuous linear equivalence.
Article: main_krylov, lem:U.
Proof: Actual injectivity implies surjectivity in the same finite-dimensional space; the genuine linear equivalence is continuous. -/
def sylvesterEquiv (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosDef) :
    Matrix (Fin n) (Fin n) ℝ ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (LinearEquiv.ofBijective (sylvesterLinear R)
    ⟨sylvesterLinear_injective R hR, (LinearMap.injective_iff_surjective).mp (sylvesterLinear_injective R hR)⟩).toContinuousLinearEquiv

/-- The derivative of the actual physical matrix squaring map is its genuine Sylvester equivalence.
Use: The derivative of the actual physical matrix squaring map is its genuine Sylvester equivalence.
Article: main_krylov, lem:U.
Proof: Use the noncommutative product derivative at the real matrix. -/
theorem square_hasFDerivAt (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosDef) :
    HasFDerivAt (fun X : Matrix (Fin n) (Fin n) ℝ => X*X) (sylvesterEquiv R hR).toContinuousLinearMap R := by
  convert! (hasFDerivAt_id R).mul' (hasFDerivAt_id R) using 1


/-- The actual CFC metric root of a positive definite physical base is itself positive definite.
Use: The actual CFC metric root of a positive definite physical base is itself positive definite.
Article: main_krylov, lem:U.
Proof: It is positive semidefinite and its actual determinant is a unit. -/
theorem metricRoot_posDef (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) :
    (metricRoot base).PosDef := by
  apply (CFC.sqrt_nonneg base).posSemidef.posDef_iff_isUnit.mpr
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (metricRoot_det_unit base hb)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual CFC positive metric root preserves every genuine local C-r regularity order on positive physical base families.
Use: The actual CFC positive metric root preserves every genuine local C-r regularity order on positive physical base families.
Article: main_krylov, lem:U.
Proof: The actual root is continuous on the true positive family. The standard inverse function theorem for squaring gives a genuine C-r local inverse since the real Sylvester derivative is invertible. Actual continuity and the true root-square identity identify the actual root with that local inverse; order zero uses its genuine continuous neighborhood. -/
theorem metricRoot_contDiffAt (base : X → Matrix (Fin n) (Fin n) ℝ) (x : X)
    {r : WithTop ℕ∞} (hbase : ContDiffAt ℝ r base x)
    (hpos : ∀ᶠ p in 𝓝 x, (base p).PosDef) :
    ContDiffAt ℝ r (fun p => metricRoot (base p)) x := by
  -- Work with the actual positive family, rather than asserting smoothness off the symmetric cone.
  have hb := hpos.self_of_nhds
  have hroot : ContinuousAt (fun p => metricRoot (base p)) x := by
    let S := {p | (base p).PosDef}
    have hw : ContinuousWithinAt (fun p => metricRoot (base p)) S x :=
      (CFC.continuousOn_sqrt (base x) hb.posSemidef.nonneg).comp
        hbase.continuousAt.continuousWithinAt (fun p (hp : (base p).PosDef) => hp.posSemidef.nonneg)
    exact hw.continuousAt hpos
  rcases eq_or_ne r 0 with rfl|hr
  · obtain ⟨U,hU,hcont⟩ := contDiffAt_zero.mp hbase
    refine contDiffAt_zero.mpr ⟨U∩{p | (base p).PosDef},Filter.inter_mem hU hpos,?_⟩
    exact CFC.continuousOn_sqrt.comp (hcont.mono Set.inter_subset_left)
      (fun p hp => hp.2.posSemidef.nonneg)
  · let R := metricRoot (base x)
    let f := fun M : Matrix (Fin n) (Fin n) ℝ => M*M
    have hf : ContDiffAt ℝ r f R := (contDiff_id.mul contDiff_id).contDiffAt
    have hd : HasFDerivAt f (sylvesterEquiv R (metricRoot_posDef _ hb)).toContinuousLinearMap R :=
      square_hasFDerivAt R (metricRoot_posDef _ hb)
    let invf := hf.localInverse hd hr
    have hinv : ContDiffAt ℝ r invf (base x) := by
      have h := hf.to_localInverse hd hr
      change ContDiffAt ℝ r invf (R*R) at h
      simpa only [R,metricRoot_square _ hb] using h
    -- Continuity selects the true positive branch of the local square inverse.
    have heq : (fun p => metricRoot (base p))=ᶠ[𝓝 x] (fun p => invf (base p)) := by
      have hl := (hf.hasStrictFDerivAt' hd hr).eventually_left_inverse
      filter_upwards [hroot.tendsto.eventually hl,hpos] with p hp hpPos
      change invf (metricRoot (base p)*metricRoot (base p))=metricRoot (base p) at hp
      rw [metricRoot_square _ hpPos] at hp
      exact hp.symm
    exact (hinv.comp x hbase).congr_of_eventuallyEq heq


/-- The genuine inverse positive metric root preserves actual local C-r regularity.
Use: The genuine inverse positive metric root preserves actual local C-r regularity.
Article: main_krylov, lem:U.
Proof: The true root determinant is a unit, so the analytic actual ring inverse composes with the proved genuine root regularity. -/
theorem metricRoot_inverse_contDiffAt (base : X → Matrix (Fin n) (Fin n) ℝ) (x : X)
    {r : WithTop ℕ∞} (hbase : ContDiffAt ℝ r base x)
    (hpos : ∀ᶠ p in 𝓝 x, (base p).PosDef) :
    ContDiffAt ℝ r (fun p => (metricRoot (base p))⁻¹) x := by
  have hu : IsUnit (metricRoot (base x)) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (metricRoot_det_unit _ hpos.self_of_nhds)
  have hi := contDiffAt_ringInverse (n := r) ℝ hu.unit
  rw [hu.unit_spec] at hi
  simpa only [Function.comp_def,← Matrix.nonsing_inv_eq_ringInverse] using hi.comp x (metricRoot_contDiffAt base x hbase hpos)

/-- Genuine spectral-matrix C-r regularity transfers to its actual Euclidean operator.
Use: Genuine spectral-matrix C-r regularity transfers to its actual Euclidean operator.
Article: main_krylov, lem:U.
Proof: The real matrix/operator algebra identification is a continuous linear map on finite-dimensional spaces. -/
theorem matrixOperator_contDiffAt (M : X → Matrix (Fin n) (Fin n) ℝ) (x : X)
    {r : WithTop ℕ∞} (hM : ContDiffAt ℝ r M x) :
    ContDiffAt ℝ r (fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (M p)) x := by
  let L := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap.toContinuousLinearMap
  exact L.contDiff.contDiffAt.comp x hM

end
end krylov.Stability
