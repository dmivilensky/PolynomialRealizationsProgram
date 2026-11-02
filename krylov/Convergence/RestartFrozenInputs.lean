import krylov.Convergence.RestartFrozenModel
import krylov.Convergence.RestartedFC

/-!
Article: main_krylov, thm:D, genuine frozen full FC model inputs.
Use: prove actual model error, full column independence and bounded inverse
from primitive scalar objective data and a compact full reference family.
No conditioning or closeness of the measured model is assumed.
Source: native query localization, genuine finite FC operator homogeneity,
and the proved compact full-model regularity on the true CG basis.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Nonlinear krylov.Functions krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- An actually invertible full ambient model entails an actually
independent complete observed column window. Article: thm:D. -/
theorem fcFrozenColumns_unit_of_model_unit
    {n : ℕ} (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (hM : IsUnit (fcFrozenMatrix A g).det) :
    IsUnit (windowMatrix (fcFrozenColumns A g)).det := by
  rw [isUnit_iff_ne_zero] at hM ⊢
  intro hz
  apply hM
  simp only [fcFrozenMatrix,inverseCongruence,det_mul,det_nonsing_inv,det_transpose,
    Ring.inverse_eq_inv,hz,_root_.inv_zero,zero_mul]

/-- The original full model formed after real FC queries has an actual
first-order error and a uniform inverse domain and inverse bound.
Article: main_krylov, thm:D, final frozen corrections. -/
theorem nativeFC_frozen_model_bounds
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z,‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K,∀ i<k+1,CG.gradient (cgOperator base) g i≠0)
    (R : ℝ) (hR : 0<R) :
    ∃ ep Cm J : ℝ,0<ep ∧0<Cm ∧0<J ∧∀ ε : ℝ,0<ε → ε<ep →
      ∀ u,‖u‖≤R →cgOperator base u∈K →
      let A := metricFCOperator T f G H fullMemory r (ε • u)
      let M := fcFrozenMatrix A (G (ε • u))
      IsUnit (windowMatrix (fcFrozenColumns A (G (ε • u)))).det ∧
        IsUnit M.det ∧‖M-base‖≤Cm*ε ∧‖M⁻¹‖≤J := by
  obtain ⟨em,Cm,hem,hCm,hmodel⟩ := compact_fcFrozenMatrix_first_order base hb K hK hpre
  obtain ⟨ed,J,hed,hJ,hdomains⟩ := compact_fcFrozenMatrix_domains base hb K hK hpre
  obtain ⟨ei,D,hei,hD,hinput⟩ := metricFCInput_bound T hT f G H (cgOperator base)
    hr hG₀ hH₀ hHc₀ hLr hH hF hG R hR
  refine ⟨min ei (min em ed/(D+1)),Cm*D,J,by positivity,by positivity,hJ,?_⟩
  intro ε hε he u hu hKu
  let A := metricFCOperator T f G H fullMemory r (ε • u)
  let I := metricFCInput T f G H (cgOperator base) r ε u (k+1)
  let Af := fcFiniteOperatorPath (cgOperator base) (k+1) I.2
  have hI : ‖I‖≤D*ε := (hinput ε hε (he.trans_le (min_le_left _ _)) u hu).2 (k+1)
  have hsmall : ‖I‖≤min em ed := by
    have hh := (lt_div_iff₀ (by positivity : 0<D+1)).mp (he.trans_le (min_le_right _ _))
    exact hI.trans (by nlinarith only [hh,hε])
  have hAf : ∀ i<k+1,Af i=A i := by
    intro i hi
    simp only [Af,fcFiniteOperatorPath,hi,dite_true,I,metricFCInput,A,add_sub_cancel]
  have hg : cgOperator base u+I.1=ε⁻¹ • G (ε • u) := by
    dsimp only [I,metricFCInput]
    abel
  have hM : fcFrozenMatrix Af (cgOperator base u+I.1)=fcFrozenMatrix A (G (ε • u)) := by
    rw [hg,fcFrozenMatrix_congr_prefix Af A _ hAf,
      fcFrozenMatrix_scalar A (G (ε • u)) ε⁻¹ (inv_ne_zero hε.ne')]
  have hm := hmodel (cgOperator base u) hKu I.1 I.2 (hsmall.trans (min_le_left _ _))
  obtain ⟨_,hunit,hinv⟩ := hdomains (cgOperator base u) hKu I.1 I.2 (hsmall.trans (min_le_right _ _))
  rw [hM] at hm hunit hinv
  refine ⟨fcFrozenColumns_unit_of_model_unit A _ hunit,hunit,?_,hinv⟩
  exact hm.trans ((mul_le_mul_of_nonneg_left hI hCm.le).trans_eq (by ring))

end
end krylov.Convergence
