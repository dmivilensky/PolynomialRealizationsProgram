import krylov.Secant.Correction
import krylov.LinearAlgebra.CorrectionAsymptotics

/-!
Article: main_krylov, apA:galerkin(a), actual finite-matrix correction orders.
Use: connect the generic Banach/Hilbert estimates to the genuine physical model
solve and its actual positive-root canonical gradient.
Source: reuse the proved canonical normal equation and correction asymptotic calculus.
-/

namespace krylov.Secant
noncomputable section
open Matrix Filter Asymptotics Topology krylov.LinearAlgebra
open scoped Matrix Matrix.Norms.L2Operator
variable {α : Type*} {n : ℕ} {f : Filter α}

/-- Matrix-to-Hilbert operator identification preserves actual spectral asymptotic bounds.
Use: no entrywise matrix norm enters the correction-order transfer to actual residual vectors.
Article: main_krylov, apA:galerkin(a).
Proof: the already fixed spectral matrix norm equals its genuine Euclidean operator norm. -/
theorem matrix_bigO_toEuclideanCLM (M : α → Matrix (Fin n) (Fin n) ℝ) (s : α → ℝ)
    (hM : M =O[f] s) : (fun x => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (M x)) =O[f] s := by
  apply IsBigO.of_norm_left
  simpa only [Matrix.cstar_norm_def] using hM.norm_left

/-- An actual matrix model that tends to I through first-order errors is nonsingular eventually.
Use: discharges the small-perturbation inverse domain before any asymptotic correction solve.
Article: main_krylov, apA:galerkin(a), Ĵ=I+O(ω).
Source: openness of the unit group of a complete normed algebra.
Proof: the genuine model tends to I, and units form an open neighborhood of I. -/
theorem near_identity_eventually_nonsingular (J : α → Matrix (Fin n) (Fin n) ℝ) (s : α → ℝ)
    (hs : Tendsto s f (𝓝 0)) (hJ : (fun x => J x - 1) =O[f] s) :
    ∀ᶠ x in f, IsUnit (J x).det := by
  have ht : Tendsto J f (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using (hJ.trans_tendsto hs).add_const (1 : Matrix (Fin n) (Fin n) ℝ)
  have hu := ht.eventually (Units.isOpen.mem_nhds isUnit_one)
  exact hu.mono fun x hx => (Matrix.isUnit_iff_isUnit_det _).mp hx

/-- The actual inverse matrix correction operator has its quadratic spectral remainder.
Use: instantiate the generic inverse expansion with actual finite matrix inverses.
Article: main_krylov, apA:galerkin(a), E Ĵ⁻¹=L+O(ω²).
Proof: the nonsingular matrix inverse is the actual Banach-algebra ring inverse. -/
theorem matrix_correction_operator_order (J E L : α → Matrix (Fin n) (Fin n) ℝ) (s : α → ℝ)
    (hs : Tendsto s f (𝓝 0)) (hJ : (fun x => J x - 1) =O[f] s)
    (hE : (fun x => E x - L x) =O[f] (fun x => s x^2)) (hL : L =O[f] s) :
    (fun x => E x * (J x)⁻¹ - L x) =O[f] (fun x => s x^2) := by
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using correction_operator_order J E L s hs hJ hE hL

/-- The actual finite-matrix canonical correction has the printed leading residual and order.
Use: the generic operator estimate is applied to the actual matrix model and Euclidean residual.
Article: main_krylov, apA:galerkin(a), ĝ₊=−Lr+O(ω^(p+2)).
Proof: transfer the proved actual spectral matrix remainder through the isometric
operator identification, then apply the proved actual residual action estimate. -/
theorem matrix_correction_vector_order (J E L : α → Matrix (Fin n) (Fin n) ℝ)
    (g r : α → EuclideanSpace ℝ (Fin n)) (s : α → ℝ) (p : ℕ)
    (hs : Tendsto s f (𝓝 0)) (hJ : (fun x => J x - 1) =O[f] s)
    (hE : (fun x => E x - L x) =O[f] (fun x => s x^2)) (hL : L =O[f] s)
    (hg : (fun x => g x - r x) =O[f] (fun x => s x^(p+1)))
    (hr : r =O[f] (fun x => s x^p)) :
    (fun x => -(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E x * (J x)⁻¹) (g x)) +
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (L x) (r x)) =O[f] (fun x => s x^(p+2)) := by
  have ht := matrix_bigO_toEuclideanCLM _ _ (matrix_correction_operator_order J E L s hs hJ hE hL)
  simp only [map_sub] at ht
  exact correction_vector_order _ _ g r s p hs ht (matrix_bigO_toEuclideanCLM L s hL) hg hr

/-- The actual canonical gradient uses the fixed genuine inverse positive metric root.
Use: connect physical model solves to the Euclidean residuals in every asymptotic estimate.
Article: main_krylov, apA:galerkin(a), ĝ=A⁻¹/²g. -/
def canonicalGradient (base : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 ((metricRoot base)⁻¹ *ᵥ g)

/-- The true physical square-window correction has the stated canonical asymptotic remainder.
Use: the expansion concerns the actual coefficient solve and corrected physical gradient,
not an assumed normalized update or an abstract substitute trajectory.
Article: main_krylov, apA:galerkin(a), first-order correction conclusion.
Proof: the proved actual matrix estimate applies to the true canonical model and
error; the exact physical canonical normal equation identifies its left-hand residual eventually. -/
theorem physical_correction_order (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (U H B : α → Matrix (Fin n) (Fin n) ℝ) (g : α → Fin n → ℝ)
    (r : α → EuclideanSpace ℝ (Fin n)) (L : α → Matrix (Fin n) (Fin n) ℝ) (s : α → ℝ) (p : ℕ)
    (hU : ∀ᶠ x in f, IsUnit (U x).det) (hH : ∀ᶠ x in f, IsUnit (H x).det)
    (hs : Tendsto s f (𝓝 0))
    (hJ : (fun x => relativeOperator base (inverseCongruence (U x) (H x)) - 1) =O[f] s)
    (hE : (fun x => relativeOperator base (B x - inverseCongruence (U x) (H x)) - L x) =O[f]
      (fun x => s x^2)) (hL : L =O[f] s)
    (hg : (fun x => canonicalGradient base (g x) - r x) =O[f] (fun x => s x^(p+1)))
    (hr : r =O[f] (fun x => s x^p)) :
    (fun x => canonicalGradient base
      (correctedGradient (U x) (B x) (g x) (correctionCoefficients (U x) (H x) (g x))) +
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (L x) (r x)) =O[f] (fun x => s x^(p+2)) := by
  have ht := matrix_correction_vector_order
    (fun x => relativeOperator base (inverseCongruence (U x) (H x)))
    (fun x => relativeOperator base (B x - inverseCongruence (U x) (H x))) L
    (fun x => canonicalGradient base (g x)) r s p hs hJ hE hL hg hr
  apply ht.congr' ?_ (Filter.EventuallyEq.refl _ _)
  -- Identify the true output only on the actual neighborhood where both physical solves exist.
  filter_upwards [hU, hH] with x hxU hxH
  have hc := canonical_corrected_gradient (U x) (H x) (B x) base hxU hxH hbase (g x)
  rw [neg_mulVec] at hc
  have he := congrArg (WithLp.toLp 2) hc
  exact congrArg (fun v : EuclideanSpace ℝ (Fin n) =>
    v + Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (L x) (r x)) he.symm

/-- The actual normalized matrix corrections, iterated with their actual inverse models.
Use: the repeated-correction expansion concerns a constructed residual recurrence.
Article: main_krylov, apA:galerkin(a), ĝ^(t). -/
def normalizedCorrectionRun (J E : ℕ → α → Matrix (Fin n) (Fin n) ℝ)
    (g : α → EuclideanSpace ℝ (Fin n)) : ℕ → α → EuclideanSpace ℝ (Fin n) :=
  correctionRun (fun j x => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E j x * (J j x)⁻¹)) g

/-- Every fixed finite number of actual matrix corrections has the exact printed signed leading product.
Use: closes the matrix specialization of the repeated-correction asymptotic claim.
Article: main_krylov, apA:galerkin(a), eq:correction-product.
Proof: apply each proved genuine matrix operator remainder in the finite
correction induction, then identify the explicitly constructed leading ordered product. -/
theorem matrix_repeated_correction_order (J E L : ℕ → α → Matrix (Fin n) (Fin n) ℝ)
    (g r : α → EuclideanSpace ℝ (Fin n)) (s : α → ℝ) (p t : ℕ)
    (hs : Tendsto s f (𝓝 0)) (hJ : ∀ j < t, (fun x => J j x - 1) =O[f] s)
    (hE : ∀ j < t, (fun x => E j x - L j x) =O[f] (fun x => s x^2))
    (hL : ∀ j < t, L j =O[f] s)
    (hg : (fun x => g x - r x) =O[f] (fun x => s x^(p+1))) (hr : r =O[f] (fun x => s x^p)) :
    (fun x => normalizedCorrectionRun J E g t x - ((-1 : ℝ)^t) •
      (chebyshev1.orderedProduct
        (fun j => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (L j x)) t) (r x)) =O[f]
      (fun x => s x^(p+t+1)) := by
  let T := fun j x => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E j x * (J j x)⁻¹)
  let Lc := fun j x => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (L j x)
  have ht : ∀ j < t, (fun x => T j x - Lc j x) =O[f] (fun x => s x^2) := by
    intro j hj
    have h := matrix_bigO_toEuclideanCLM _ _
      (matrix_correction_operator_order (J j) (E j) (L j) s hs (hJ j hj) (hE j hj) (hL j hj))
    simpa only [map_sub] using h
  have hc := repeated_correction_order T Lc g r s p t hs ht
    (fun j hj => matrix_bigO_toEuclideanCLM _ _ (hL j hj)) hg hr
  -- The leading recurrence is the already proved ordered product with newest factors leftmost.
  exact hc.congr_left fun x => congrArg (fun z => correctionRun T g t x - z)
    (correctionRun_orderedProduct Lc r t x)

end
end krylov.Secant
