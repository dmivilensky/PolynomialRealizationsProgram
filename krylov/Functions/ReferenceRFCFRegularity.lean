import krylov.Functions.ReferenceFibreNormalization
import krylov.Tensor.BinaryRFCRegularity

/-!
Article: main_krylov, thm:Fplanar, true-reference stability of C_Y.
Use: retain the exact RFC-F leading constant after genuine true-minimizer
Hessian, gradient and metric-error normalization. Source: actual CG energy
regularity, true metric quadratic forms and the proved full-ball C_Y bound.
-/
namespace krylov.Functions
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Reference krylov.Correction krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual RFC-F reference coefficient c_0 sqrt(c_last) C_Y(r).
Article: main_krylov, thm:Fplanar, B_delta C_Y. -/
def referenceRFCFCoefficient (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  cgEnergy base g 0*Real.sqrt (cgEnergy base g k)*
    krylov.Tensor.BinaryCubic.modelMetricCoefficient (referenceFibreRatio base g k)

/-- The genuine RFC-F coefficient is strictly positive at every active
first/last reference. Article: main_krylov, thm:Fplanar. -/
theorem referenceRFCFCoefficient_pos (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hpre : ∀ j≤k, CG.gradient (cgOperator base) g j≠0) :
    0<referenceRFCFCoefficient base g k := by
  have hd := referenceFibre_domains base hb g k hpre
  have hCY := (krylov.Tensor.BinaryCubic.modelMetricCoefficient_bounds hd.2.2.1.le).1
  have hpos : 0<krylov.Tensor.BinaryCubic.modelMetricCoefficient (referenceFibreRatio base g k) := by
    nlinarith only [hCY,hd.2.2.1]
  exact mul_pos (mul_pos hd.1 (Real.sqrt_pos.mpr hd.2.1)) hpos

/-- The full RFC-F coefficient has first-order variation in the actual CG
reference even though its true supremum need only be locally Lipschitz.
Article: main_krylov, thm:Fplanar, actual reference replacement. -/
theorem referenceRFCFCoefficient_order (base : X → Matrix (Fin n) (Fin n) ℝ)
    (g : X → EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hb : AnalyticAt ℝ base 0) (hg : AnalyticAt ℝ g 0) (hpos : (base 0).PosDef)
    (hpre : ∀ j≤k, CG.gradient (cgOperator (base 0)) (g 0) j≠0) :
    (fun z=>referenceRFCFCoefficient (base z) (g z) k-referenceRFCFCoefficient (base 0) (g 0) k)
      =O[𝓝 (0 : X)] (fun z=>‖z‖) := by
  let rho := fun z=>referenceFibreRatio (base z) (g z) k
  let pref := fun z=>cgEnergy (base z) (g z) 0*Real.sqrt (cgEnergy (base z) (g z) k)
  let CY := krylov.Tensor.BinaryCubic.modelMetricCoefficient
  have hr := (referenceFibre_fields_contDiffAt base g 0 k hb hg hpos hpre).1
  have h0 := (cgEnergy_variable_analyticAt base g 0 0 hb hg hpos (fun j hj=>hpre j (by omega))).contDiffAt (n:=1)
  have hk := (cgEnergy_variable_analyticAt base g 0 k hb hg hpos hpre).contDiffAt (n:=1)
  have hp : ContDiffAt ℝ 1 pref 0 := h0.mul (hk.sqrt (referenceFibre_domains (base 0) hpos (g 0) k hpre).2.1.ne')
  have hro : (fun z=>rho z-rho 0)=O[𝓝 (0 : X)] (fun z=>‖z‖) := by
    simpa only [sub_zero] using (hr.differentiableAt one_ne_zero).isBigO_sub.norm_right
  have hpo : (fun z=>pref z-pref 0)=O[𝓝 (0 : X)] (fun z=>‖z‖) := by
    simpa only [sub_zero] using (hp.differentiableAt one_ne_zero).isBigO_sub.norm_right
  let R := |rho 0|+1
  have hR : 0≤R := by dsimp only [R]; positivity
  have hR0 : |rho 0|≤R := by dsimp only [R]; linarith
  have hnear : ∀ᶠ z in 𝓝 (0 : X), |rho z|≤R := by
    filter_upwards [hr.continuousAt (Metric.ball_mem_nhds (rho 0) (by norm_num : (0:ℝ)<1))] with z hz
    have hz' : rho z∈Metric.ball (rho 0) 1 := hz
    have hh : |rho z-rho 0|<1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hz'
    have ht := abs_add_le (rho z-rho 0) (rho 0)
    rw [sub_add_cancel] at ht
    dsimp only [R]
    linarith
  have hCo : (fun z=>CY (rho z)-CY (rho 0))=O[𝓝 (0 : X)] (fun z=>rho z-rho 0) := by
    apply IsBigO.of_bound (2*Real.sqrt (1+R^2)+2*R)
    filter_upwards [hnear] with z hz
    simpa only [Real.norm_eq_abs] using
      krylov.Tensor.BinaryCubic.modelMetricCoefficient_lipschitz_on R hR (rho z) (rho 0) hz hR0
  have hCb : (fun z=>CY (rho z))=O[𝓝 (0 : X)] (fun _=>(1:ℝ)) := by
    apply IsBigO.of_bound (2*R*Real.sqrt (1+R^2))
    filter_upwards [hnear] with z hz
    have hrho : 0≤rho z := Real.sqrt_nonneg _
    have hb := (krylov.Tensor.BinaryCubic.modelMetricCoefficient_bounds hrho).2
    have hnonneg := (krylov.Tensor.BinaryCubic.modelMetricCoefficient_bounds hrho).1
    rw [Real.norm_eq_abs,abs_of_nonneg (by nlinarith only [hnonneg,hrho]),norm_one,mul_one]
    have hpR : rho z≤R := (le_abs_self _).trans hz
    have hs : (rho z)^2≤R^2 := by simpa only [pow_two] using mul_self_le_mul_self hrho hpR
    exact hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left hpR (by norm_num : (0:ℝ)≤2))
      (Real.sqrt_le_sqrt (by linarith only [hs])) (Real.sqrt_nonneg _) (by positivity))
  have hprod : (fun z=>(pref z-pref 0)*CY (rho z))=O[𝓝 (0 : X)] (fun z=>‖z‖) := by
    simpa only [mul_one] using hpo.mul hCb
  have hh := hprod.add ((hCo.trans hro).const_mul_left (pref 0))
  convert! hh using 1
  ext z
  dsimp only [referenceRFCFCoefficient,pref,CY,rho]
  ring

/-- Uniform first-order control for arbitrary actual reference perturbations.
Article: main_krylov, thm:Fplanar, genuine true-minimizer replacement. -/
theorem referenceRFCFCoefficient_variation (base : Matrix (Fin n) (Fin n) ℝ)
    (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hpre : ∀ j≤k, CG.gradient (cgOperator base) g j≠0) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ Δ : Matrix (Fin n) (Fin n) ℝ,
      ∀ v : EuclideanSpace ℝ (Fin n), ‖(Δ,v)‖≤δ →
      |referenceRFCFCoefficient (base+Δ) (g+v) k-referenceRFCFCoefficient base g k|≤C*‖(Δ,v)‖ := by
  have ho := referenceRFCFCoefficient_order
    (fun z : Matrix (Fin n) (Fin n) ℝ × EuclideanSpace ℝ (Fin n)=>base+z.1)
    (fun z : Matrix (Fin n) (Fin n) ℝ × EuclideanSpace ℝ (Fin n)=>g+z.2) k
    (analyticAt_const.add analyticAt_fst) (analyticAt_const.add analyticAt_snd)
    (by simpa only [Prod.fst_zero,add_zero] using hb)
    (by simpa only [Prod.fst_zero,Prod.snd_zero,add_zero] using hpre)
  obtain ⟨C,hC,hev⟩ := isBigO_iff'.mp ho
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ/2,C,by positivity,hC,?_⟩
  intro Δ v hv
  have hh := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hv.trans_lt (by linarith : δ/2<δ))
  simpa only [Prod.fst_zero,Prod.snd_zero,add_zero,Real.norm_eq_abs,abs_norm,Set.mem_ofPred_eq] using hh

end
end krylov.Functions
