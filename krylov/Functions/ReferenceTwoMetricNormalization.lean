import krylov.Functions.ReferenceFibreNormalization

/-!
Article: main_krylov, prop:Fcycle(iii), true error normalization.
Use: preserve the exact sharp coefficient after recentering the cubic at
its true critical point and using its true Hessian metric. Both energy and
error normalizations are derived from the actual matrices and vectors.
Source: the positive-root square identity, smooth positive quadratic forms
and the genuine locally Lipschitz minimax reference coefficient.
-/
namespace krylov.Functions
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Reference krylov.Secant krylov.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The sharp coefficient per cube of the true initial metric error.
Article: main_krylov, prop:Fcycle(iii), q_0² q_last normalization. -/
def referenceTwoMetricFibreCoefficient (base errorBase : Matrix (Fin n) (Fin n) ℝ)
    (g u : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  referenceFibreCoefficient base g k/(referenceMetricSize errorBase u)^3

/-- The full error-normalized sharp coefficient has first-order variation,
including independent observed-reference, true-Hessian, gradient and minimizer displacement.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referenceTwoMetricFibreCoefficient_order
    (base errorBase : X → Matrix (Fin n) (Fin n) ℝ) (g u : X → EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hb : AnalyticAt ℝ base 0) (he : AnalyticAt ℝ errorBase 0) (hg : AnalyticAt ℝ g 0) (hu : AnalyticAt ℝ u 0)
    (hpos : (base 0).PosDef) (herror : (errorBase 0).PosDef) (hne : u 0≠0)
    (hpre : ∀ j≤k, CG.gradient (cgOperator (base 0)) (g 0) j≠0) :
    (fun z=>referenceTwoMetricFibreCoefficient (base z) (errorBase z) (g z) (u z) k-
      referenceTwoMetricFibreCoefficient (base 0) (errorBase 0) (g 0) (u 0) k)
      =O[𝓝 (0 : X)] (fun z=>‖z‖) := by
  let F := fun z=>referenceFibreCoefficient (base z) (g z) k
  let I := fun z=>((referenceMetricSize (errorBase z) (u z))^3)⁻¹
  have hF : (fun z=>F z-F 0)=O[𝓝 (0 : X)] (fun z=>‖z‖) :=
    referenceFibreCoefficient_order base g k hb hg hpos hpre
  have hI : ContDiffAt ℝ 1 I 0 :=
    ((referenceMetricSize_contDiffAt errorBase u 0 he hu herror hne).pow 3).inv
      (pow_ne_zero _ (referenceMetricSize_pos (errorBase 0) herror (u 0) hne).ne')
  have hIb := hI.continuousAt.tendsto.isBigO_one ℝ
  have hIo : (fun z=>I z-I 0)=O[𝓝 (0 : X)] (fun z=>‖z‖) := by
    simpa only [sub_zero] using (hI.differentiableAt one_ne_zero).isBigO_sub.norm_right
  have hp : (fun z=>(F z-F 0)*I z)=O[𝓝 (0 : X)] (fun z=>‖z‖) := by
    simpa only [mul_one] using hF.mul hIb
  have hh := hp.add (hIo.const_mul_left (F 0))
  convert! hh using 1
  ext z
  dsimp only [referenceTwoMetricFibreCoefficient,F,I]
  rw [div_eq_mul_inv,div_eq_mul_inv]
  ring

/-- A common primitive source neighborhood controls the true sharp coefficient
when the observed first secant and the true minimizer Hessian vary independently.
Article: main_krylov, prop:Fcycle(iii), genuine two-metric normalization. -/
theorem referenceTwoMetricFibreCoefficient_variation
    (base errorBase : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (he : errorBase.PosDef)
    (g u : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hu : u≠0)
    (hpre : ∀ j≤k, CG.gradient (cgOperator base) g j≠0) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ Δ Λ : Matrix (Fin n) (Fin n) ℝ,
      ∀ v w : EuclideanSpace ℝ (Fin n), ‖((Δ,Λ),(v,w))‖≤δ →
      |referenceTwoMetricFibreCoefficient (base+Δ) (errorBase+Λ) (g+v) (u+w) k/
        referenceTwoMetricFibreCoefficient base errorBase g u k-1|≤C*‖((Δ,Λ),(v,w))‖ := by
  let Z := (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) ×
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
  have ho := referenceTwoMetricFibreCoefficient_order
    (fun z : Z=>base+z.1.1) (fun z : Z=>errorBase+z.1.2)
    (fun z : Z=>g+z.2.1) (fun z : Z=>u+z.2.2) k
    (analyticAt_const.add (analyticAt_fst.comp analyticAt_fst))
    (analyticAt_const.add (analyticAt_snd.comp analyticAt_fst))
    (analyticAt_const.add (analyticAt_fst.comp analyticAt_snd))
    (analyticAt_const.add (analyticAt_snd.comp analyticAt_snd))
    (by simpa only [Prod.fst_zero,Prod.snd_zero,add_zero] using hb)
    (by simpa only [Prod.fst_zero,Prod.snd_zero,add_zero] using he)
    (by simpa only [Prod.fst_zero,Prod.snd_zero,add_zero] using hu)
    (by simpa only [Prod.fst_zero,Prod.snd_zero,add_zero] using hpre)
  obtain ⟨C,hC,hev⟩ := isBigO_iff'.mp ho
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  have hK : 0<referenceTwoMetricFibreCoefficient base errorBase g u k :=
    div_pos (referenceFibre_domains base hb g k hpre).2.2.2.2 (pow_pos (referenceMetricSize_pos errorBase he u hu) 3)
  refine ⟨δ/2,C/referenceTwoMetricFibreCoefficient base errorBase g u k,by positivity,div_pos hC hK,?_⟩
  intro Δ Λ v w hv
  have hh := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hv.trans_lt (by linarith : δ/2<δ))
  have hh' : |referenceTwoMetricFibreCoefficient (base+Δ) (errorBase+Λ) (g+v) (u+w) k-
      referenceTwoMetricFibreCoefficient base errorBase g u k|≤C*‖((Δ,Λ),(v,w))‖ := by
    simpa only [Prod.fst_zero,Prod.snd_zero,add_zero,Real.norm_eq_abs,abs_norm,Set.mem_ofPred_eq] using hh
  rw [div_sub_one hK.ne',abs_div,abs_of_pos hK]
  exact (div_le_div_of_nonneg_right hh' hK.le).trans_eq (by ring)

end
end krylov.Functions
