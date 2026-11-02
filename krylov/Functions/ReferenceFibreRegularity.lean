import krylov.Correction.ReferenceRegularity
import krylov.Stability.ReferenceErrorRegularity
import krylov.Tensor.BinaryFibreRegularity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Article: main_krylov, prop:Fcycle(iii), true-reference parameter transfer.
Use: compare actual CG energies, the first/last step ratio and the complete
function-value minimax coefficient when the real Hessian and initial gradient
move. The coefficient is built from the genuine computed CG recurrence.
Source: actual joint CG analyticity, smooth positive square roots and the
proved local Lipschitz theorem for the exact all-chord minimax M_F.
-/
namespace krylov.Functions
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Reference krylov.Correction krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual first/last energy ratio of a genuine reference.
Article: main_krylov, prop:Fcycle(iii), r=sqrt(c_last/c_0). -/
def referenceFibreRatio (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ := Real.sqrt (cgEnergy base g k/cgEnergy base g 0)

/-- The positive reference factor multiplying the exact all-chord coefficient.
Article: main_krylov, prop:Fcycle(iii). -/
def referenceFibrePrefactor (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  cgEnergy base g 0*Real.sqrt (cgEnergy base g k)*referenceFibreRatio base g k*
    Real.sqrt (1+4*(referenceFibreRatio base g k)^2)

/-- The complete genuine CG reference coefficient in the value-information lower bound.
Article: main_krylov, prop:Fcycle(iii). -/
def referenceFibreCoefficient (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  referenceFibrePrefactor base g k*krylov.Tensor.BinaryCubic.fibreMinimax (referenceFibreRatio base g k)

/-- The true physical energy of an actual active CG step is jointly analytic.
Article: main_krylov, prop:Fcycle(iii), actual energy parameter regularity. -/
theorem cgEnergy_variable_analyticAt (base : X → Matrix (Fin n) (Fin n) ℝ)
    (g : X → EuclideanSpace ℝ (Fin n)) (x : X) (k : ℕ)
    (hb : AnalyticAt ℝ base x) (hg : AnalyticAt ℝ g x) (hpos : (base x).PosDef)
    (hpre : ∀ j≤k, CG.gradient (cgOperator (base x)) (g x) j≠0) :
    AnalyticAt ℝ (fun z=>cgEnergy (base z) (g z) k) x := by
  have hQ := (matrixOperator_contDiffAt base x hb.contDiffAt).analyticAt
  have hp := cgOperator_positive (base x) hpos
  have hs := referenceStep_analyticAt (fun z=>cgOperator (base z)) g x hQ hg hp.1 hp.2 k hpre
  exact analytic_inner hs (analytic_operator_apply hQ hs)

/-- Nonstagnation supplies every positive square-root and ratio denominator.
Article: main_krylov, prop:Fcycle(iii), actual reference domains. -/
theorem referenceFibre_domains (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hpre : ∀ j≤k, CG.gradient (cgOperator base) g j≠0) :
    0<cgEnergy base g 0 ∧ 0<cgEnergy base g k ∧ 0<referenceFibreRatio base g k ∧
      0<referenceFibrePrefactor base g k ∧ 0<referenceFibreCoefficient base g k := by
  have hc (j : ℕ) (hj : j≤k) : 0<cgEnergy base g j := by
    rw [cgEnergy_eq_norm_sq base hb]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
      (canonicalCGStep_ne_zero base hb g j (fun i hi=>hpre i (hi.trans hj))))
  have h0 := hc 0 (Nat.zero_le k)
  have hk := hc k le_rfl
  have hr : 0<referenceFibreRatio base g k := Real.sqrt_pos.mpr (div_pos hk h0)
  have hp : 0<referenceFibrePrefactor base g k := by
    dsimp only [referenceFibrePrefactor]; positivity
  have hm : 0<krylov.Tensor.BinaryCubic.fibreMinimax (referenceFibreRatio base g k) := by
    have hs := krylov.Tensor.BinaryCubic.fibreMinimax_shear 0 (referenceFibreRatio base g k)
    rw [krylov.Tensor.BinaryCubic.fibreMinimax_zero] at hs
    have hn := (krylov.Tensor.BinaryCubic.fibreMinimax_bounds (referenceFibreRatio base g k)).1
    by_contra hh
    have hz : krylov.Tensor.BinaryCubic.fibreMinimax (referenceFibreRatio base g k)=0 := by linarith
    rw [hz,mul_zero] at hs
    norm_num at hs
  exact ⟨h0,hk,hr,hp,mul_pos hp hm⟩

/-- Actual first/last reference ratios and their smooth positive prefactors
are C-one in the genuine base and observed gradient.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referenceFibre_fields_contDiffAt (base : X → Matrix (Fin n) (Fin n) ℝ)
    (g : X → EuclideanSpace ℝ (Fin n)) (x : X) (k : ℕ)
    (hb : AnalyticAt ℝ base x) (hg : AnalyticAt ℝ g x) (hpos : (base x).PosDef)
    (hpre : ∀ j≤k, CG.gradient (cgOperator (base x)) (g x) j≠0) :
    ContDiffAt ℝ 1 (fun z=>referenceFibreRatio (base z) (g z) k) x ∧
      ContDiffAt ℝ 1 (fun z=>referenceFibrePrefactor (base z) (g z) k) x := by
  have h0 := (cgEnergy_variable_analyticAt base g x 0 hb hg hpos (fun j hj=>hpre j (hj.trans (Nat.zero_le k)))).contDiffAt (n:=1)
  have hk := (cgEnergy_variable_analyticAt base g x k hb hg hpos hpre).contDiffAt (n:=1)
  have hd := referenceFibre_domains (base x) hpos (g x) k hpre
  have hr : ContDiffAt ℝ 1 (fun z=>referenceFibreRatio (base z) (g z) k) x :=
    (hk.div h0 hd.1.ne').sqrt (ne_of_gt (div_pos hd.2.1 hd.1))
  refine ⟨hr,?_⟩
  exact ((h0.mul (hk.sqrt hd.2.1.ne')).mul hr).mul
    ((contDiffAt_const.add (contDiffAt_const.mul (hr.pow 2))).sqrt (by positivity))


/-- The full actual minimax coefficient has first-order variation in the
primitive moving reference, although M_F need only be locally Lipschitz.
Article: main_krylov, prop:Fcycle(iii), true-minimizer reference replacement. -/
theorem referenceFibreCoefficient_order (base : X → Matrix (Fin n) (Fin n) ℝ)
    (g : X → EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hb : AnalyticAt ℝ base 0) (hg : AnalyticAt ℝ g 0) (hpos : (base 0).PosDef)
    (hpre : ∀ j≤k, CG.gradient (cgOperator (base 0)) (g 0) j≠0) :
    (fun z=>referenceFibreCoefficient (base z) (g z) k-referenceFibreCoefficient (base 0) (g 0) k)
      =O[𝓝 (0 : X)] (fun z=>‖z‖) := by
  let rho := fun z=>referenceFibreRatio (base z) (g z) k
  let pref := fun z=>referenceFibrePrefactor (base z) (g z) k
  let MF := krylov.Tensor.BinaryCubic.fibreMinimax
  obtain ⟨hr,hp⟩ := referenceFibre_fields_contDiffAt base g 0 k hb hg hpos hpre
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
  have hMo : (fun z=>MF (rho z)-MF (rho 0))=O[𝓝 (0 : X)] (fun z=>rho z-rho 0) := by
    apply IsBigO.of_bound (48*(1+R)*(1+6*R))
    filter_upwards [hnear] with z hz
    simpa only [Real.norm_eq_abs] using krylov.Tensor.BinaryCubic.fibreMinimax_abs_sub_le (rho z) (rho 0) R hR hz hR0
  have hMb : (fun z=>MF (rho z))=O[𝓝 (0 : X)] (fun _=>(1:ℝ)) := by
    apply IsBigO.of_bound (4*(1+R))
    filter_upwards [hnear] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (krylov.Tensor.BinaryCubic.fibreMinimax_bounds (rho z)).1,norm_one,mul_one]
    exact (krylov.Tensor.BinaryCubic.fibreMinimax_bounds (rho z)).2.trans (by linarith)
  have hprod : (fun z=>(pref z-pref 0)*MF (rho z))=O[𝓝 (0 : X)] (fun z=>‖z‖) := by
    simpa only [mul_one] using hpo.mul hMb
  have hh := hprod.add ((hMo.trans hro).const_mul_left (pref 0))
  convert! hh using 1
  ext z
  dsimp only [referenceFibreCoefficient,pref,MF,rho]
  ring


/-- Every true reference perturbation in one common ball changes the genuine
minimax coefficient by at most a fixed multiple of its primitive drift.
The perturbed family need not have an analytic parameterization.
Article: main_krylov, prop:Fcycle(iii), actual true-Hessian normalization. -/
theorem referenceFibreCoefficient_variation (base : Matrix (Fin n) (Fin n) ℝ)
    (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hpre : ∀ j≤k, CG.gradient (cgOperator base) g j≠0) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ Δ : Matrix (Fin n) (Fin n) ℝ,
      ∀ v : EuclideanSpace ℝ (Fin n), ‖(Δ,v)‖≤δ →
      |referenceFibreCoefficient (base+Δ) (g+v) k-referenceFibreCoefficient base g k|≤C*‖(Δ,v)‖ := by
  have ho := referenceFibreCoefficient_order
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

/-- The positive sharp coefficient changes by a relative O(drift), with all
constants chosen before the actual perturbed reference.
Article: main_krylov, prop:Fcycle(iii), preservation of the printed leading constant. -/
theorem referenceFibreCoefficient_relative_variation (base : Matrix (Fin n) (Fin n) ℝ)
    (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hpre : ∀ j≤k, CG.gradient (cgOperator base) g j≠0) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ Δ : Matrix (Fin n) (Fin n) ℝ,
      ∀ v : EuclideanSpace ℝ (Fin n), ‖(Δ,v)‖≤δ →
      |referenceFibreCoefficient (base+Δ) (g+v) k/referenceFibreCoefficient base g k-1|≤C*‖(Δ,v)‖ := by
  obtain ⟨δ,C,hδ,hC,hvar⟩ := referenceFibreCoefficient_variation base hb g k hpre
  have hK := (referenceFibre_domains base hb g k hpre).2.2.2.2
  refine ⟨δ,C/referenceFibreCoefficient base g k,hδ,div_pos hC hK,?_⟩
  intro Δ v hv
  rw [div_sub_one hK.ne',abs_div,abs_of_pos hK]
  exact (div_le_div_of_nonneg_right (hvar Δ v hv) hK.le).trans_eq (by ring)

end
end krylov.Functions
