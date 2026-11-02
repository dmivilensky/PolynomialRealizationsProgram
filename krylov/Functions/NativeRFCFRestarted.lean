import krylov.Functions.NativeRFCFCubic
import krylov.Functions.NativeRFCFStationary

/-!
Article: main_krylov, prop:Fcycle(ii), actual restarted RFC-F cycles.
Use: derive cycle order at least three for the real recursive value-informed
executor under the article's compact nondegeneracy and convergence hypotheses.
Source: the primitive-function compact cubic error theorem and exact stationary
execution. Each restart clears the genuine observed history and executes the
unchanged ordinary RFC prefix followed by its actual value-informed last solve.
-/
namespace krylov.Functions
noncomputable section
open Set Filter Topology Metric krylov.Methods krylov.Reference krylov.Nonlinear
  chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual RFC-F restart points, with a fresh full-memory cycle at every restart.
Article: main_krylov, prop:Fcycle(ii). -/
def rfcFRestartedPoints (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (k : ℕ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | c+1 => rfcFPoint T f G r (rfcFRestartedPoints T f G r k x₀ c) k

variable {k : ℕ}
set_option maxHeartbeats 800000 in
/-- Actual restarted RFC-F has cycle order at least three, uniformly on the
compact nondegenerate reference family, including exact stationary tails.
Article: main_krylov, prop:Fcycle(ii).
Convergence puts every sufficiently late active cycle in the same proved
native neighborhood. Its actual metric error is the scale in the genuine
single-cycle theorem; zero-error cycles use exact stationary execution. -/
theorem restarted_nativeRFCF_cubic
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D₃ : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hD₃ : HasFDerivAt H D₃ 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1))))
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (U : Set (EuclideanSpace ℝ (Fin (k+1)))) (hU : IsCompact U)
    (hpre : ∀ u∈U, ∀ i≤k, CG.gradient (cgOperator base) (cgOperator base u) i≠0)
    (x₀ : EuclideanSpace ℝ (Fin (k+1))) :
    let x := rfcFRestartedPoints T f G r k x₀
    let e := fun c=>‖T (x c)‖
    (∀ c, 0<e c → (e c)⁻¹ • x c∈U) → Tendsto e atTop (𝓝 0) →
    ∃ C : ℝ, 0<C ∧ ∀ᶠ c in atTop, e (c+1)≤C*(e c)^3 := by
  let x := rfcFRestartedPoints T f G r k x₀
  let e := fun c=>‖T (x c)‖
  dsimp only
  intro hdirs hconv
  let K := cgOperator base '' U
  have hK : IsCompact K := hU.image (cgOperator base).continuous
  have hKpre g (hg : g∈K) : ∀ i≤k, CG.gradient (cgOperator base) g i≠0 := by
    obtain ⟨u,hu,rfl⟩ := hg
    exact hpre u hu
  let R := ‖T.symm.toContinuousLinearMap‖+1
  obtain ⟨ε₀,C,hε₀,hC,hcycle⟩ := nativeRFCF_error_cubic base hb hk T hT f G H
    D₃ hD₃ hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hKpre R (by dsimp only [R]; positivity)
  refine ⟨C,hC,?_⟩
  filter_upwards [hconv.eventually (gt_mem_nhds hε₀)] with c hc
  change e (c+1)≤C*(e c)^3
  by_cases he : 0<e c
  · let u := (e c)⁻¹ • x c
    have hdecomp : e c • u=x c := by
      dsimp only [u]; rw [smul_smul,mul_inv_cancel₀ he.ne',one_smul]
    have hunit : ‖T u‖=1 := by
      dsimp only [u]
      rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr he.le)]
      change (e c)⁻¹*e c=1
      exact inv_mul_cancel₀ he.ne'
    have hu : ‖u‖≤R := by
      have hn := T.symm.toContinuousLinearMap.le_opNorm (T u)
      simp only [ContinuousLinearEquiv.coe_coe,T.symm_apply_apply,hunit,mul_one] at hn
      exact hn.trans (by dsimp only [R]; linarith)
    have hKu : cgOperator base u∈K := ⟨u,hdirs c he,rfl⟩
    have hout := hcycle (e c) he hc u hu hKu
    rw [hdecomp] at hout
    exact hout
  · have he₀ : e c=0 := le_antisymm (by linarith only [he]) (norm_nonneg _)
    have hx : x c=0 := by
      apply T.injective
      simpa only [map_zero] using norm_eq_zero.mp he₀
    have hnext : e (c+1)=0 := by
      change ‖T (rfcFPoint T f G r (x c) k)‖=0
      rw [hx,rfcFPoint_stationary T f G r 0 hG₀ k,map_zero,norm_zero]
    rw [hnext,he₀]
    positivity

end
end krylov.Functions
