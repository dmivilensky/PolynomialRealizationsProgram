import krylov.OneGradient.AtomicProbability
import krylov.LinearAlgebra.PositiveGaussNodes
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), uniqueness of actual finite principal representations.
Use: identify supported measures from their original low polynomial moments.
Source: classical Lagrange cardinal polynomials and the genuine finite-support
Dirac decomposition, with positivity used to recover every actual spectral node.
-/

namespace krylov.OneGradient
noncomputable section
open Polynomial MeasureTheory jacobi.Finite krylov.LinearAlgebra
open scoped BigOperators ENNReal
variable {N : ℕ}

/-- Almost everywhere assertions on a genuine positive atomic probability measure
hold at every original node.
Use: convert an endpoint localizing-square equality into the actual Radau support.
Article: main_krylov, s5:moment(b).
Proof: every real spectral weight is strictly positive, so its Dirac summand
has the same null sets as its node mass. -/
theorem discrete_atomic_ae_iff (M : DiscreteMeasure N) (P : ℝ → Prop) :
    (∀ᵐ x ∂discreteAtomicMeasure M,P x) ↔ ∀ i,P (M.node i) := by
  rw [discreteAtomicMeasure,ae_finsetSum_measure_iff]
  constructor
  · intro h i
    have hi := (Measure.ae_ennreal_smul_measure_iff
      (ENNReal.ofReal_pos.mpr (M.positive i)).ne').mp (h i (Finset.mem_univ i))
    simpa only [ae_dirac_eq,Filter.eventually_pure] using hi
  · intro h i _
    apply Measure.ae_smul_measure
    simpa only [ae_dirac_eq,Filter.eventually_pure] using h i

/-- The normalized actual Lagrange cardinal polynomial at a true spectral node.
Use: its genuine integral isolates the mass at that node for every supported measure.
Article: main_krylov, s5:moment(b). -/
def normalizedCardinal (M : DiscreteMeasure N) (i : Fin N) : ℝ[X] :=
  ((spectralCardinalPolynomial M.node i).eval (M.node i))⁻¹ • spectralCardinalPolynomial M.node i

/-- The actual normalized cardinal polynomial is the node singleton indicator
on every original distinct spectral node.
Use: finite moment equality determines genuine singleton masses.
Article: main_krylov, s5:moment(b).
Proof: cancel the nonzero own-node product; every other node has its actual vanishing factor. -/
theorem normalized_cardinal_eval (M : DiscreteMeasure N) (i j : Fin N) :
    (normalizedCardinal M i).eval (M.node j)=if j=i then 1 else 0 := by
  unfold normalizedCardinal
  rw [Polynomial.eval_smul,smul_eq_mul]
  split_ifs with h
  · subst j
    exact inv_mul_cancel₀ (spectralCardinal_self_ne_zero M.node M.distinct i)
  · rw [spectralCardinal_other M.node i j h,mul_zero]

/-- An actual finite spectral support determines every finite measure from
its polynomial integrals below the number of nodes.
Use: prove uniqueness of the original principal endpoint representations,
including among non-atomic candidate measures before support is derived.
Article: main_krylov, s5:moment(b).
Proof: normalized Lagrange polynomials have the original degree bound and
are node indicators almost everywhere. Their integrals determine every actual
singleton mass; the true finite-support Dirac decomposition determines the measure. -/
theorem supported_atomic_unique (M : DiscreteMeasure N) (sigma : Measure ℝ)
    [IsFiniteMeasure sigma]
    (hs : ∀ᵐ x ∂sigma,x∈Finset.univ.image M.node)
    (hm : ∀ p : ℝ[X],p.natDegree<N →
      (∫ x,p.eval x ∂sigma)=discretePolynomialIntegral M p) :
    sigma=discreteAtomicMeasure M := by
  have hmass (i : Fin N) : sigma {M.node i}=discreteAtomicMeasure M {M.node i} := by
    let p := normalizedCardinal M i
    have hdeg : p.natDegree<N := by
      apply (Polynomial.natDegree_smul_le _ _).trans_lt
      rw [spectralCardinal_degree]
      have hi := i.isLt
      omega
    have hval (j : Fin N) : p.eval (M.node j)=({M.node i} : Set ℝ).indicator 1 (M.node j) := by
      rw [normalized_cardinal_eval]
      by_cases h : j=i
      · subst j
        simp
      · have hne : M.node j≠M.node i := fun he => h (M.distinct he)
        simp [h,hne]
    have hfirst : (∫ x,p.eval x ∂sigma)=sigma.real {M.node i} := by
      rw [← integral_indicator_one (measurableSet_singleton (M.node i))]
      apply integral_congr_ae
      filter_upwards [hs] with x hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
      exact hval j
    have hsecond : discretePolynomialIntegral M p=(discreteAtomicMeasure M).real {M.node i} := by
      rw [← discrete_atomic_polynomial_integral,← integral_indicator_one (measurableSet_singleton (M.node i))]
      apply integral_congr_ae
      exact (discrete_atomic_ae_iff M _).mpr hval
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top sigma _) (measure_ne_top _ _)).mp
    exact hfirst.symm.trans ((hm p hdeg).trans hsecond)
  have hsM : ∀ᵐ x ∂discreteAtomicMeasure M,x∈Finset.univ.image M.node := by
    apply (discrete_atomic_ae_iff M _).mpr
    intro i
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  rw [Measure.ae_mem_finset_iff.mp hs,Measure.ae_mem_finset_iff.mp hsM]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  rw [hmass i]

end
end krylov.OneGradient
