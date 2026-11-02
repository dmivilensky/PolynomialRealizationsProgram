import krylov.XR.ConditionalObservation
import krylov.Secant.RelativeMetric

/-!
Article: main_krylov, prop:cond, original two-dimensional realizations.
Use: realize the attaining completion matrices by actual positive bases,
actual own-time secant observations and the original physical increments.
The step window is literally the identity, so changing the hidden base
does not change the physical steps. Source: positive diagonal congruence
and the original chronological observation/flag identities.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant
open scoped Matrix.Norms.L2Operator MatrixOrder

/-- An actual positive diagonal physical base root. Article: prop:cond. -/
def conditionalPhysicalRoot (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := diagonal (![1,r] : Fin 2 → ℝ)

/-- The physical operator sequence generating the original two secant
pairs and its fresh output operator. Article: main_krylov, prop:cond. -/
def conditionalPhysicalSequence (r y δ k : ℝ) (E : Matrix (Fin 2) (Fin 2) ℝ)
    (j : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let R := conditionalPhysicalRoot r
  if j=0 then R*R else
    if j=1 then R*(1+conditionalMatrix y δ k)*R
    else R*(1+conditionalMatrix y δ k)*R+R*E*R

/-- Actual own-time observed pairings, on the fixed identity step window.
Article: main_krylov, prop:cond. -/
def conditionalPhysicalObservation (r y δ k : ℝ) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ := observed (conditionalPhysicalSequence r y δ k E)

/-- The physical base root is truly symmetric. Article: prop:cond. -/
theorem conditionalPhysicalRoot_isSymm (r : ℝ) : (conditionalPhysicalRoot r).IsSymm := by
  simp only [conditionalPhysicalRoot,IsSymm,diagonal_transpose]

/-- Every nonzero physical scale gives the actual inverse domain.
Article: main_krylov, prop:cond. -/
theorem conditionalPhysicalRoot_det_unit (r : ℝ) (hr : r≠0) : IsUnit (conditionalPhysicalRoot r).det := by
  simpa [conditionalPhysicalRoot,Matrix.det_fin_two] using isUnit_iff_ne_zero.mpr hr

/-- The actual positive diagonal root is the canonical positive square
root of its physical base. Article: main_krylov, prop:cond. -/
theorem conditionalPhysicalRoot_canonical (r : ℝ) (hr : 0≤r) :
    metricRoot (conditionalPhysicalRoot r*conditionalPhysicalRoot r)=conditionalPhysicalRoot r := by
  apply CFC.sqrt_mul_self
  apply Matrix.PosSemidef.nonneg
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i <;> simp [hr]

/-- The constructed physical base is genuinely positive definite.
Article: main_krylov, prop:cond. -/
theorem conditionalPhysicalBase_posDef (r : ℝ) (hr : r≠0) :
    (conditionalPhysicalRoot r*conditionalPhysicalRoot r).PosDef := by
  have hu := (isUnit_iff_isUnit_det _).mpr (conditionalPhysicalRoot_det_unit r hr)
  have hh := Matrix.PosDef.one.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
  simpa only [conjTranspose_eq_transpose_of_trivial,(conditionalPhysicalRoot_isSymm r).eq,
    Matrix.mul_one] using hh

/-- The canonical old and fresh increment budgets are exactly the
original true matrix norms, with no artificial relaxation.
Article: main_krylov, prop:cond, physical budget realization. -/
theorem conditionalPhysical_budget (r : ℝ) (hr : r≠0) (X : Matrix (Fin 2) (Fin 2) ℝ)
    (hX : X.IsSymm) :
    relativeBudget (conditionalPhysicalRoot r*conditionalPhysicalRoot r)
      (conditionalPhysicalRoot r*X*conditionalPhysicalRoot r)=‖X‖ := by
  have hh := relativeBudget_congruence (1 : Matrix (Fin 2) (Fin 2) ℝ) X
    (conditionalPhysicalRoot r) Matrix.PosDef.one hX (conditionalPhysicalRoot_det_unit r hr)
  simp only [(conditionalPhysicalRoot_isSymm r).eq,Matrix.mul_one] at hh
  rw [hh]
  change ‖(metricRoot (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹*X*
    (metricRoot (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹‖=‖X‖
  simp [metricRoot,CFC.sqrt_one]

/-- The original second segment operator is genuinely positive under
the original strict old-budget assumption. Article: prop:cond. -/
theorem conditionalPhysicalOld_posDef (r y δ k ω : ℝ) (hr : r≠0) (hω : ω<1)
    (hbudget : ‖conditionalMatrix y δ k‖≤ω) :
    (conditionalPhysicalRoot r*(1+conditionalMatrix y δ k)*conditionalPhysicalRoot r).PosDef := by
  have hh := (krylov.LinearAlgebra.strict_shifted_posDef (conditionalMatrix y δ k)
    (conditionalMatrix_isSymm y δ k) (hbudget.trans_lt hω)).2
  simp only [one_smul] at hh
  have hu := (isUnit_iff_isUnit_det _).mpr (conditionalPhysicalRoot_det_unit r hr)
  have hc := hh.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
  simpa only [conjTranspose_eq_transpose_of_trivial,(conditionalPhysicalRoot_isSymm r).eq] using hc

/-- The literal own-time secant observations have exactly the compressed
entries in the source proof; neither hidden y nor fresh E is observed.
Article: main_krylov, prop:cond. -/
theorem conditionalPhysicalObservation_formula (r y δ k : ℝ) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    conditionalPhysicalObservation r y δ k E=!![1,r*δ;0,r^2*(1+k)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conditionalPhysicalObservation,observed,conditionalPhysicalSequence,conditionalPhysicalRoot,
      Matrix.mul_apply,Fin.sum_univ_two,conditionalMatrix] <;> ring

/-- This is precisely the original identity-step matrix observation
dictionary, rather than an independent synthetic data record.
Article: main_krylov, prop:cond. -/
theorem conditionalPhysicalObservation_pairs (r y δ k : ℝ) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ*pairImages 1 (conditionalPhysicalSequence r y δ k E)=
      conditionalPhysicalObservation r y δ k E := by
  rw [←observed_compression]
  simp only [transpose_one,Matrix.one_mul,Matrix.mul_one,conditionalPhysicalObservation]

/-- The actual hidden model error has exactly its old rank-one term and
fresh congruent matrix term. Article: main_krylov, prop:cond. -/
theorem conditionalPhysical_model_error (r y δ k : ℝ) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    conditionalPhysicalSequence r y δ k E 2-latest (conditionalPhysicalObservation r y δ k E)=
      conditionalPhysicalRoot r*(conditionalHiddenError y+E)*conditionalPhysicalRoot r := by
  rw [conditionalPhysicalObservation_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conditionalPhysicalSequence,conditionalPhysicalRoot,conditionalHiddenError,latest,
      Matrix.mul_apply,Fin.sum_univ_two,conditionalMatrix] <;> ring

/-- The original physical C-normalized model-error norm is exactly the
attained conditional objective already optimized above.
Article: main_krylov, prop:cond. -/
theorem conditionalPhysical_model_radius (r y δ k : ℝ) (hr : r≠0)
    (E : Matrix (Fin 2) (Fin 2) ℝ) (hE : E.IsSymm) :
    relativeBudget (conditionalPhysicalRoot r*conditionalPhysicalRoot r)
      (conditionalPhysicalSequence r y δ k E 2-latest (conditionalPhysicalObservation r y δ k E))=
      ‖conditionalHiddenError y+E‖ := by
  rw [conditionalPhysical_model_error]
  exact conditionalPhysical_budget r hr _ ((conditionalHiddenError_isSymm y).add hE)

/-- Every explanation of the signed normalized data is realized by the
same physical identity steps and exactly the same observed matrix,
while its hidden positive base varies. Article: prop:cond(b). -/
theorem conditionalPhysical_fixed_observation (δobs k y : ℝ) (hk : 0<1+k)
    (E : Matrix (Fin 2) (Fin 2) ℝ) :
    conditionalPhysicalObservation (Real.sqrt (1+k))⁻¹ y (observedConditionalCross δobs k) k E=
      normalizedConditionalObservation δobs := by
  rw [conditionalPhysicalObservation_formula]
  have hs : Real.sqrt (1+k)≠0 := (Real.sqrt_pos.mpr hk).ne'
  have hsq := Real.sq_sqrt hk.le
  have hc : (Real.sqrt (1+k))⁻¹*observedConditionalCross δobs k=δobs := by
    unfold observedConditionalCross
    field_simp
  have hd : ((Real.sqrt (1+k))⁻¹)^2*(1+k)=1 := by
    calc
      _ = ((Real.sqrt (1+k))⁻¹)^2*(Real.sqrt (1+k))^2 :=
        congrArg (fun t : ℝ=>((Real.sqrt (1+k))⁻¹)^2*t) hsq.symm
      _ = _ := by field_simp
  rw [hc,hd]
  rfl

end
end krylov.XR
