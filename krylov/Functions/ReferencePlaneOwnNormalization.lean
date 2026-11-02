import krylov.Functions.ReferencePlaneSharpSources
import krylov.Functions.SharpCoefficientNormalization

/-!
Article: main_krylov, prop:Fcycle(iii), literal own-reference sharpness.
Use: replace the construction reference by the actual first-segment secant,
and normalize by the genuine true-minimizer initial error. Every matrix,
vector and error below is computed from the original scalar source.
Source: actual segment-average positivity and drift, genuine critical-point
localization, primitive two-metric regularity and sharp quartic absorption.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Reference krylov.Nonlinear krylov.Tensor.BinaryCubic chebyshev1.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual first-segment secant of the literal original source.
Article: main_krylov, prop:Fcycle(iii). -/
def referencePlaneObservedMatrix (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (t : krylov.Tensor.BinaryCubic) :=
  metricHilbertPlaneFirstSecant A hA (referencePlaneFirst A g) (referencePlaneLast A hA g)
    (ε*‖canonicalCGStep A g 0‖) (referencePlaneRatio A hA g) t (ε • canonicalCGStep A g 0)

/-- The actual true-minimizer Hessian of the original source.
Article: main_krylov, prop:Fcycle(iii). -/
def referencePlaneTrueHessian (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (t : krylov.Tensor.BinaryCubic)
    (z : EuclideanSpace ℝ (Fin n)) :=
  metricHilbertPlaneTrueHessian A (referencePlaneFirst A g) (referencePlaneLast A hA g)
    (ε*‖canonicalCGStep A g 0‖) (referencePlaneRatio A hA g) t z

/-- The actual initial error measured in the true source Hessian.
Article: main_krylov, prop:Fcycle(iii). -/
def referencePlaneTrueInitialError (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (t : krylov.Tensor.BinaryCubic)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  referenceMetricSize (referencePlaneTrueHessian A hA g ε t z) (-(metricCoordinates A hA).symm z)

/-- The literal normalized sharp coefficient of this source's own first
secant and genuine true initial error. Article: prop:Fcycle(iii). -/
def referencePlaneOwnCoefficient (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (t : krylov.Tensor.BinaryCubic)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  referenceTwoMetricFibreCoefficient (referencePlaneObservedMatrix A hA g ε t)
    (referencePlaneTrueHessian A hA g ε t z) g
    ((-ε⁻¹) • (metricCoordinates A hA).symm z) (referenceAtomCount A hA g-1)

set_option maxHeartbeats 1000000 in
/-- The actual source normalization preserves the sharp coefficient in the
printed own-reference metric, with relative factor 1-O(e_c). The inputs are
the actual critical localization, true-Hessian drift and SC realization,
all constructed by `referencePlane_sharp_actual_sources`.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlane_own_normalization
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (a U D M E : ℝ) (ha : 0<a) (hU : 0<U) (hD : 0<D) (hM : 0<M) (hE : 0≤E) :
    ∃ ep Cκ C c : ℝ, 0<ep ∧ 0<Cκ ∧ 0<C ∧ 0<c ∧
      ∀ ε : ℝ, 0<ε → ε<ep → ∀ α : ℝ, 0≤α → α≤U →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall → ∀ z : Plane,
      ‖z-planeOfPair (ε*‖canonicalCGStep A g 0‖,referencePlaneRatio A hA g*(ε*‖canonicalCGStep A g 0‖))‖≤
        M*(ε*‖canonicalCGStep A g 0‖)^2 →
      let τ := scaleBinaryCubic α t
      let zf := hilbertPlaneEmbed (referencePlaneFirst A g) (referencePlaneLast A hA g) z+
        ε • referencePlaneComplement A hA g
      ReferencePlaneTrueMetricRealization A hA g ε a τ zf →
      ‖referencePlaneTrueHessian A hA g ε τ zf-A‖≤
        ‖(metricCoordinates A hA).toContinuousLinearMap‖^2*D*‖canonicalCGStep A g 0‖*ε →
      let ec := referencePlaneTrueInitialError A hA g ε τ zf
      (referencePlaneObservedMatrix A hA g ε τ).PosDef ∧ c*ε≤ec ∧
      |referencePlaneOwnCoefficient A hA g ε τ zf/
        referenceTwoMetricFibreCoefficient A A g (referencePlaneInitialError A hA g)
          (referenceAtomCount A hA g-1)-1|≤Cκ*ec ∧
      (1-C*ec)*a^2*referencePlaneOwnCoefficient A hA g ε τ zf*ec^3≤
        a^2*referenceFibreCoefficient A g (referenceAtomCount A hA g-1)*ε^3-E*ε^4 := by
  let p := ‖canonicalCGStep A g 0‖
  let r := referencePlaneRatio A hA g
  let e := referencePlaneFirst A g
  let h := referencePlaneLast A hA g
  let u₀ := referencePlaneInitialError A hA g
  let k := referenceAtomCount A hA g-1
  obtain ⟨hp,_,he,hh,heh,_,_⟩ := referencePlane_sample_lines A hA g hN
  change 0<p at hp
  have hg : g≠0 := by
    have hn := cg_nonstagnation A hA g 0 (by omega)
    simpa only [CG.gradient,cgRun] using hn
  have hu₀ : u₀≠0 := referencePlaneInitialError_ne_zero A hA g hg
  have hpre (j : ℕ) (hj : j≤k) : CG.gradient (cgOperator A) g j≠0 :=
    cg_nonstagnation A hA g j (by dsimp only [k] at hj; omega)
  obtain ⟨L,hL,hLt⟩ := planeTerminal_uniform_bounds r
  let J := U*p*(1/2+L+‖planeOfPair (1,r)‖)
  have hJ : 0<J := by dsimp only [J]; positivity
  let S := ‖(metricCoordinates A hA).toContinuousLinearMap‖^2*J+
    ‖(metricCoordinates A hA).toContinuousLinearMap‖^2*D*p+
    ‖(metricCoordinates A hA).symm.toContinuousLinearMap‖*M*p^2+1
  have hS : 0<S := by dsimp only [S]; positivity
  obtain ⟨epN,CN,c,hepN,hCN,hc,hNrm⟩ := reference_primitive_normalization A hA g u₀ hu₀ k hpre S hS
  have hK := (referenceFibre_domains A hA g k hpre).2.2.2.2
  obtain ⟨epL,C,hepL,hC,hTransfer⟩ := sharp_coefficient_true_error_transfer
    (referenceFibreCoefficient A g k) a CN E c hK ha hCN hE hc
  let ep := min epN (min epL (1/(2*(J+1))))
  refine ⟨ep,CN/c,C,c,lt_min hepN (lt_min hepL (by positivity)),div_pos hCN hc,hC,hc,?_⟩
  intro ε hε heps α hα hαU t ht z hz
  dsimp only
  intro hreal hH
  let τ := scaleBinaryCubic α t
  let zf := hilbertPlaneEmbed e h z+ε • referencePlaneComplement A hA g
  let B := referencePlaneObservedMatrix A hA g ε τ
  let H := referencePlaneTrueHessian A hA g ε τ zf
  let v := (-ε⁻¹) • (metricCoordinates A hA).symm zf
  let ec := referencePlaneTrueInitialError A hA g ε τ zf
  have hJ0 : 0≤‖(metricCoordinates A hA).toContinuousLinearMap‖^2*J := by positivity
  have hH0 : 0≤‖(metricCoordinates A hA).toContinuousLinearMap‖^2*D*p := by positivity
  have hv0 : 0≤‖(metricCoordinates A hA).symm.toContinuousLinearMap‖*M*p^2 := by positivity
  have hJS : ‖(metricCoordinates A hA).toContinuousLinearMap‖^2*J≤S := by
    dsimp only [S]; linarith only [hH0,hv0]
  have hHS : ‖(metricCoordinates A hA).toContinuousLinearMap‖^2*D*p≤S := by
    dsimp only [S]; linarith only [hJ0,hv0]
  have hvS : ‖(metricCoordinates A hA).symm.toContinuousLinearMap‖*M*p^2≤S := by
    dsimp only [S]; linarith only [hJ0,hH0]
  have hB : ‖B-A‖≤S*ε := by
    have hb := metricHilbertPlaneFirstSecant_scaled_drift A hA e h he hh heh (canonicalCGStep A g 0) r U ε α hε.le hα hαU ht
    have hj : U*p*(1/2+‖planeTerminalOperator r t‖+‖planeOfPair (1,r)‖)≤J := by
      exact mul_le_mul_of_nonneg_left (by linarith only [(hLt t ht).1]) (mul_nonneg hU.le hp.le)
    exact hb.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj (sq_nonneg _)) hε.le).trans
      (mul_le_mul_of_nonneg_right hJS hε.le))
  have hH' : ‖H-A‖≤S*ε := hH.trans (mul_le_mul_of_nonneg_right hHS hε.le)
  have hv : ‖v-u₀‖≤S*ε :=
    (referencePlane_normalized_initial_error A hA g hN hε z hz).trans (mul_le_mul_of_nonneg_right hvS hε.le)
  have hn := hNrm ε hε (heps.trans_le (min_le_left _ _)) B H v hB hH' hv
  have hcan : ‖averagedDerivative (hilbertPlaneHessian e h (ε*p) r τ) 0 (ε • canonicalCGStep A g 0)-
      ContinuousLinearMap.id ℝ _‖≤1/2 := by
    have hb := hilbertPlaneFirstSecant_scaled_drift e h he hh heh (canonicalCGStep A g 0) r U ε α hε.le hα hαU ht
    have hj : U*p*(1/2+‖planeTerminalOperator r t‖+‖planeOfPair (1,r)‖)≤J :=
      mul_le_mul_of_nonneg_left (by linarith only [(hLt t ht).1]) (mul_nonneg hU.le hp.le)
    have hsmall := (lt_div_iff₀ (by positivity : 0<2*(J+1))).mp
      (heps.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact (hb.trans (mul_le_mul_of_nonneg_right hj hε.le)).trans (by nlinarith only [hsmall,hε])
  have hBP : B.PosDef := metricHilbertPlaneFirstSecant_posDef A hA e h (ε*p) r τ _ hcan
  obtain ⟨_,hHP,_,_,_,_⟩ := hreal
  have hec : ec=ε*referenceMetricSize H v := by
    have hs : ε • v=-(metricCoordinates A hA).symm zf := by
      dsimp only [v]
      rw [smul_smul,mul_neg,mul_inv_cancel₀ hε.ne',neg_one_smul]
    change referenceMetricSize H (-(metricCoordinates A hA).symm zf)=_
    rw [←hs,referenceMetricSize_positive_scalar H hHP v hε.le]
  have hecL : c*ε≤ec := by rw [hec]; exact hn.1
  have hsz : 0<referenceMetricSize H v := by
    by_contra hsz
    have hh := mul_nonpos_of_nonneg_of_nonpos hε.le (le_of_not_gt hsz)
    exact (not_lt_of_ge hh) ((mul_pos hc hε).trans_le hn.1)
  have hκ : |referencePlaneOwnCoefficient A hA g ε τ zf/
      referenceTwoMetricFibreCoefficient A A g u₀ k-1|≤CN/c*ec := by
    have hb : CN*ε≤CN/c*ec := by
      have hh := mul_le_mul_of_nonneg_left hecL (div_nonneg hCN.le hc.le)
      exact (show CN*ε=CN/c*(c*ε) by field_simp).le.trans hh
    exact hn.2.1.trans hb
  have hcancel : referencePlaneOwnCoefficient A hA g ε τ zf*ec^3=referenceFibreCoefficient B g k*ε^3 := by
    change (referenceFibreCoefficient B g k/(referenceMetricSize H v)^3)*ec^3=_
    rw [hec,mul_pow]
    field_simp [hsz.ne']
  refine ⟨hBP,hecL,hκ,?_⟩
  have hl := hTransfer ε ec (referenceFibreCoefficient B g k) hε
    (heps.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hecL hn.2.2
  convert! hl using 1
  calc
    _ = (1-C*ec)*a^2*(referencePlaneOwnCoefficient A hA g ε τ zf*ec^3) := by ring
    _ = _ := by rw [hcancel]; ring

end
end krylov.Functions
