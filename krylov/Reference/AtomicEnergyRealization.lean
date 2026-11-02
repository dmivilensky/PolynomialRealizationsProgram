import krylov.Reference.Exhaustion
import krylov.Reference.CGMomentInvariance
import krylov.Nonlinear.MetricCoordinates
import krylov.LinearAlgebra.NormOrder

/-!
Article: main_krylov, apC:lem:natoms and the FC/design supremum dictionary.
Use: realize every genuine positive finite energy measure by an actual
positive diagonal matrix and initial gradient, with its full actual CG error
profile. Source: Hestenes--Stiefel energy minimization and the existing finite
Christoffel minimum, using explicit diagonal polynomial evaluation.
-/
namespace krylov.Reference
noncomputable section
open Matrix Polynomial jacobi.Finite krylov.Nonlinear krylov.Secant
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {N : ℕ}

/-- Root-normalized polynomial actions preserve the actual primal polynomial
vector, for every polynomial and positive reference. Article: apC:lem:natoms. -/
theorem canonicalPolynomial_metric_initial
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef)
    (v : EuclideanSpace ℝ (Fin N)) (p : ℝ[X]) :
    canonicalPolynomial A (metricCoordinates A hA v) p=CG.polynomialAction (cgOperator A) v p := by
  let S := metricCoordinates A hA
  let Q := cgOperator A
  have hsq : Q=S.toContinuousLinearMap*S.toContinuousLinearMap := by
    change cgOperator A=cgOperator (metricRoot A)*cgOperator (metricRoot A)
    simp only [cgOperator,←map_mul,metricRoot_square A hA]
  have hcomm (x : EuclideanSpace ℝ (Fin N)) : Q (S x)=S (Q x) := by rw [hsq]; rfl
  have hpoly : CG.polynomialAction Q (S v) p=S (CG.polynomialAction Q v p) := by
    induction p using Polynomial.induction_on with
    | C a => simp [CG.polynomialAction,map_smul]
    | add p q ihp ihq => simp only [map_add,ihp,ihq]
    | monomial j a ih =>
      have hx : C a*X^(j+1)=X*(C a*X^j) := by ring
      rw [hx,CG.polynomialAction_X_mul,CG.polynomialAction_X_mul,ih,hcomm]
  change S.symm (CG.polynomialAction Q (S v) p)=_
  rw [hpoly,S.symm_apply_apply]

/-- The actual diagonal reference acts by weighted pointwise polynomial
evaluation. Article: main_krylov, apC:lem:natoms. -/
theorem diagonal_polynomialAction (M : DiscreteMeasure N) (p : ℝ[X]) :
    CG.polynomialAction (cgOperator (diagonal M.node)) (M.evaluate 1) p=M.evaluate p := by
  induction p using Polynomial.induction_on with
  | C a =>
    ext i
    simp [CG.polynomialAction,DiscreteMeasure.evaluate,mul_comm]
  | add p q ihp ihq =>
    rw [map_add,ihp,ihq]
    ext i
    simp [DiscreteMeasure.evaluate,Polynomial.eval_add,mul_add]
  | monomial j a ih =>
    have hx : C a*X^(j+1)=X*(C a*X^j) := by ring
    rw [hx,CG.polynomialAction_X_mul,ih]
    ext i
    simp only [cgOperator,DiscreteMeasure.evaluate,Matrix.toEuclideanCLM_toLp,mulVec_diagonal,
      eval_mul,eval_X]
    ring

/-- Every original finite energy measure has an explicit genuine positive
reference, with initial canonical norm one, all atoms active, the original
spectral interval and the exact complete Christoffel error profile.
Article: main_krylov, apC:lem:natoms, converse spectral realization. -/
theorem atomic_energy_reference_realization (M : DiscreteMeasure N)
    (μ L : ℝ) (hμ : 0<μ) (hM : ∀ i, M.node i∈Set.Icc μ L) :
    ∃ A : Matrix (Fin N) (Fin N) ℝ, ∃ hA : A.PosDef, ∃ g : EuclideanSpace ℝ (Fin N),
      g≠0 ∧ referenceAtomCount A hA g=N ∧
      (∀ i, μ≤hA.1.eigenvalues i ∧ hA.1.eigenvalues i≤L) ∧
      ‖cgCanonicalError A g 0‖=1 ∧
      ∀ m : ℕ, ‖cgCanonicalError A g m‖^2=finiteChristoffelValue M m := by
  let A := diagonal M.node
  have hA : A.PosDef := posDef_diagonal_iff.mpr (fun i=>hμ.trans_le (hM i).1)
  let v := M.evaluate 1
  let g := metricCoordinates A hA v
  have hvnorm : ‖v‖^2=1 := by
    rw [←real_inner_self_eq_norm_sq]
    change inner ℝ (M.evaluate 1) (M.evaluate 1)=1
    rw [M.inner_evaluate]
    simpa only [eval_one,one_mul,mul_one] using M.probability
  have hv : v≠0 := by intro hz; rw [hz,norm_zero,zero_pow (by omega : (2:ℕ)≠0)] at hvnorm; norm_num at hvnorm
  have hg : g≠0 := by
    intro hz
    apply hv
    have hh := congrArg (metricCoordinates A hA).symm hz
    simpa only [g,ContinuousLinearEquiv.symm_apply_apply,map_zero] using hh
  have he (p : ℝ[X]) : canonicalPolynomial A g p=M.evaluate p :=
    (canonicalPolynomial_metric_initial A hA v p).trans (diagonal_polynomialAction M p)
  have hinit : cgCanonicalError A g 0=v := by
    change (metricCoordinates A hA).symm ((cgRun (cgOperator A) g 0).gradient)=v
    change (metricCoordinates A hA).symm (metricCoordinates A hA v)=v
    exact (metricCoordinates A hA).symm_apply_apply v
  have hcount : referenceAtomCount A hA g=N := by
    have hle : referenceAtomCount A hA g≤N := by
      unfold referenceAtomCount activeSpectralValues
      exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin N))
    by_contra hn
    have hlt : referenceAtomCount A hA g<N := lt_of_le_of_ne hle hn
    let m := referenceAtomCount A hA g
    let p := CG.residualPolynomial (cgOperator A) g m
    have hp : p.natDegree<N := (CG.polynomial_degree (cgOperator A) g m).1.trans_lt hlt
    have hz : M.evaluate p=0 := by
      rw [←he,canonicalPolynomial_residual]
      change (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N) (metricRoot A)⁻¹)
        (CG.gradient (cgOperator A) g (referenceAtomCount A hA g))=0
      rw [cg_terminates A hA g,map_zero]
    have hzero := M.evaluate_eq_zero hp hz
    have h0 := CG.residualPolynomial_zero (cgOperator A) g m
    change p.eval 0=1 at h0
    rw [hzero,eval_zero] at h0
    norm_num at h0
  have hband : ∀ i, μ≤hA.1.eigenvalues i ∧ hA.1.eigenvalues i≤L := by
    let B := chebyshev1.SpectralBasis.ofHermitian A hA.1
    have hl : ((-μ) • (1 : Matrix (Fin N) (Fin N) ℝ)+A).PosSemidef := by
      have hh : (-μ) • (1 : Matrix (Fin N) (Fin N) ℝ)+A=diagonal (fun i=>M.node i-μ) := by
        ext i j
        by_cases hij : i=j <;> simp [A,hij]; ring
      rw [hh,posSemidef_diagonal_iff]
      intro i; exact sub_nonneg.mpr (hM i).1
    have hu : (L • (1 : Matrix (Fin N) (Fin N) ℝ)-A).PosSemidef := by
      have hh : L • (1 : Matrix (Fin N) (Fin N) ℝ)-A=diagonal (fun i=>L-M.node i) := by
        ext i j
        by_cases hij : i=j <;> simp [A,hij]
      rw [hh,posSemidef_diagonal_iff]
      intro i; exact sub_nonneg.mpr (hM i).2
    have hl' := (krylov.LinearAlgebra.coordinates_posSemidef_iff B _).mpr hl
    have hu' := (krylov.LinearAlgebra.coordinates_posSemidef_iff B _).mpr hu
    rw [krylov.LinearAlgebra.coordinates_lower_shift,posSemidef_diagonal_iff] at hl'
    rw [krylov.LinearAlgebra.coordinates_upper_shift,posSemidef_diagonal_iff] at hu'
    intro i
    change μ≤B.eigenvalues i ∧ B.eigenvalues i≤L
    exact ⟨by linarith only [hl' i],sub_nonneg.mp (hu' i)⟩
  refine ⟨A,hA,g,hg,hcount,hband,?_,?_⟩
  · rw [hinit]
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa only [one_pow] using hvnorm)
  · intro m
    by_cases hm : m<N
    · rw [finiteChristoffelValue,ite_eq_left hm]
      have hCG := cg_energy_minimum A hA g (by omega : m≤referenceAtomCount A hA g)
        (christoffelPolynomial_admissible M m 0).1 (christoffelPolynomial_admissible M m 0).2
      rw [he,christoffelPolynomial_norm M hm 0] at hCG
      have hFin := (christoffel_minimum_unique M hm 0
        (CG.polynomial_degree (cgOperator A) g m).1 (CG.residualPolynomial_zero (cgOperator A) g m)).1
      rw [←he,canonicalPolynomial_residual] at hFin
      exact le_antisymm hCG hFin
    · rw [finiteChristoffelValue,ite_eq_right hm]
      have hz := (cg_stopping_iff A hA g m).mpr (by omega)
      simp only [cgCanonicalError,hz,map_zero,norm_zero,zero_pow (by omega : (2:ℕ)≠0)]

end
end krylov.Reference
