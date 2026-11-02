import krylov.Functions.RFCOwnTensor
import krylov.Functions.NativeRFCOwnPhysical

/-!
Article: main_krylov, thm:Htransfer, genuine own-reference source drift.
Use: bound the actual first search secant and independently observed
normalized initial gradient directly from scalar objective derivatives.
Source: the native RFC bootstrap and genuine gradient Taylor remainder.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Correction
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The actual first-secant matrix and true normalized initial gradient have
uniform first-order drift from the minimizer-Hessian reference.
Article: main_krylov, thm:Htransfer, original reference source bound. -/
theorem nativeRFC_own_reference_drift
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1))))
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (R : ℝ) (hR : 0<R) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      ‖(physicalOperatorMatrix (rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0)-base,
        ε⁻¹ • G (ε • u)-cgOperator base u)‖≤C*ε := by
  let Q := cgOperator base
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  obtain ⟨ep,M,D,Cp,hep,hM,hD,_,hprefix⟩ := nativeRFC_compact_prefix T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos (k+1) K hK (fun g hg i hi=>hpre g hg i (by omega)) R hR
  let P : ℝ := (((‖T.toContinuousLinearMap‖₊^3*L : ℝ≥0) : ℝ))
  let Dg := P/2*R^2
  let Dt := Dg+D+1
  have hP : 0≤P := NNReal.coe_nonneg _
  have hDg : 0≤Dg := by dsimp only [Dg]; positivity
  have hDt : 0<Dt := by dsimp only [Dt]; positivity
  let ε₀ := min ep (r/(‖T.toContinuousLinearMap‖*R+1))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,Dt,hε₀,hDt,?_⟩
  intro ε hε he u hu hKu
  have hp := hprefix ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  let x₀ := ε • u
  let A := rfcFunctionSearchOperator T f G H fullMemory r x₀
  have hx₀ : ‖T x₀‖≤r := by
    have hh := (lt_div_iff₀ (by positivity : 0<‖T.toContinuousLinearMap‖*R+1)).mp
      (he.trans_le (min_le_right _ _))
    have hn := T.toContinuousLinearMap.le_opNorm x₀
    rw [show x₀=ε • u from rfl,norm_smul,Real.norm_of_nonneg hε.le] at hn
    have hmul := mul_le_mul_of_nonneg_left hu (by positivity : 0≤‖T.toContinuousLinearMap‖*ε)
    change ‖T x₀‖≤_ at hn
    nlinarith only [hn,hmul,hh,hε]
  let v := ε⁻¹ • G x₀-Q u
  have hv : ‖v‖≤Dg*ε := by
    have hh := metric_gradient_quadratic_error T G H Q hr.le hG₀ hH₀ hH hG x₀ hx₀
    have heq : v=ε⁻¹ • (G x₀-Q x₀) := by
      dsimp only [v,x₀]
      rw [smul_sub,map_smul,smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
    rw [heq,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
    have hs : ‖u‖^2≤R^2 := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hu
    rw [show x₀=ε • u from rfl,norm_smul,Real.norm_of_nonneg hε.le] at hh
    calc
      _ ≤ ε⁻¹*(P/2*(ε*‖u‖)^2) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hε.le)
      _ = P/2*‖u‖^2*ε := by field_simp
      _ ≤ Dg*ε := by
        dsimp only [Dg]
        nlinarith only [mul_le_mul_of_nonneg_left hs (by positivity : 0≤P/2*ε)]
  have hbase : physicalOperatorMatrix (A 0)-base=physicalOperatorMatrix (A 0-Q) := by
    rw [physicalOperatorMatrix_sub]
    congr 1
    exact ((Matrix.toEuclideanCLM (n:=Fin (k+1)) (𝕜:=ℝ)).symm_apply_apply base).symm
  change ‖(physicalOperatorMatrix (A 0)-base,v)‖≤Dt*ε
  rw [Prod.norm_def,max_le_iff,hbase,physicalOperatorMatrix_norm]
  exact ⟨(hp.2 0 (by omega)).1.trans (mul_le_mul_of_nonneg_right (by dsimp only [Dt]; linarith only [hDg]) hε.le),
    hv.trans (mul_le_mul_of_nonneg_right (by dsimp only [Dt]; linarith only [hD]) hε.le)⟩

end
end krylov.Functions
