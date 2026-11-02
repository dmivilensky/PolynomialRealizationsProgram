import krylov.Reference.JacobiFunctionalWindow
import krylov.Reference.JacobiOrientation
import krylov.Reference.JacobiPivotLimit
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), genuine measure-derived Nevai CG limits.
Use: derive actual residual-orientation spectral forms and true common CG coefficient limits from the original probability measure and its stated Jacobi recurrence data.
Source: the original integral Gaussian support theorem, actual alternating conjugacy and the proved genuine determinant-pivot stability theorem.
-/

namespace krylov.Reference
noncomputable section
open Matrix Filter chebyshev1 krylov.LinearAlgebra
open scoped Topology

/-- The original compact spectral measure supplies both actual physical shifted forms for every genuine residual-orientation Gaussian Jacobi prefix.
Use: The original compact spectral measure supplies both actual physical shifted forms for every genuine residual-orientation Gaussian Jacobi prefix.
Article: main_krylov, prop:phi(c), genuine measure-derived Nevai CG limits.
Proof: First derive the true positive-edge Gauss node window from original support, then conjugate by the genuine first-site-preserving orthogonal sign map. -/
theorem jacobiMeasure_residual_window (J : JacobiData) (hJ : ∀ n,0≤J.aSq n)
    (hpos : ∀ n,0<n → 0<J.aSq n) (sigma : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure sigma] (I : SpectralInterval)
    (hI : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L)
    (ho : ∀ m q,q.natDegree<m → measurePolynomialIntegral sigma I hI (J.leading m*q)=0)
    (N : ℕ) :
    (jacobiPrefix J.b (fun n => Real.sqrt (J.aSq (n+1))) N-I.mu • 1).PosSemidef ∧
    (I.L • (1 : Matrix (Fin N) (Fin N) ℝ)-jacobiPrefix J.b (fun n => Real.sqrt (J.aSq (n+1))) N).PosSemidef := by
  have hw := jacobiMeasure_window J hJ hpos sigma I hI ho N
  rw [← jacobiData_matrix_orientation J N] at hw
  exact ⟨alternating_conjugate_lower _ I.mu hw.1,alternating_conjugate_upper _ I.L hw.2⟩

/-- The genuine common line and recurrence coefficient sequences of the original Gaussian rules converge to the printed heavy-ball parameters from actual Nevai recurrence limits.
Use: The genuine common line and recurrence coefficient sequences of the original Gaussian rules converge to the printed heavy-ball parameters from actual Nevai recurrence limits.
Article: main_krylov, prop:phi(c), genuine measure-derived Nevai CG limits.
Proof: Use measure-derived finite spectral domains to prove the true principal-pivot limit, then apply continuity of reciprocal and squared physical edge ratios. -/
theorem jacobiMeasure_nevai_coefficients (J : JacobiData) (hJ : ∀ n,0≤J.aSq n)
    (hpos : ∀ n,0<n → 0<J.aSq n) (sigma : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure sigma] (I : SpectralInterval)
    (hI : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L)
    (ho : ∀ m q,q.natDegree<m → measurePolynomialIntegral sigma I hI (J.leading m*q)=0)
    (hA : Tendsto J.b atTop (𝓝 ((I.L+I.mu)/2)))
    (hB : Tendsto (fun n => Real.sqrt (J.aSq (n+1))) atTop (𝓝 ((I.L-I.mu)/4))) :
    let d := jacobiPivot J.b (fun n => Real.sqrt (J.aSq (n+1)))
    Tendsto (fun n => (d n)⁻¹) atTop (𝓝 (HeavyBallParameters.pivot I)⁻¹) ∧
    Tendsto (fun n => (Real.sqrt (J.aSq (n+1))/d n)^2) atTop (𝓝 ((HeavyBallParameters.ratio I)^2)) := by
  -- Original support supplies every actual finite pivot domain before limits of the genuine measured CG coefficient sequence are taken.
  dsimp only
  have hBp (n : ℕ) : 0<Real.sqrt (J.aSq (n+1)) := Real.sqrt_pos.mpr (hpos (n+1) (by omega))
  have hw := jacobiMeasure_residual_window J hJ hpos sigma I hI ho
  have hd := jacobiPivot_nevai_limit J.b (fun n => Real.sqrt (J.aSq (n+1))) I hBp
    (fun N => (hw N).1) (fun N => (hw N).2) hA hB
  have hdn := (HeavyBallParameters.pivot_pos I).ne'
  refine ⟨hd.inv₀ hdn,?_⟩
  have he : (I.L-I.mu)/4/HeavyBallParameters.pivot I=HeavyBallParameters.ratio I := by
    rw [← HeavyBallParameters.edge, mul_div_cancel_left₀ _ hdn]
  simpa only [Pi.div_apply,he] using (hB.div hd hdn).pow 2
end
end krylov.Reference
