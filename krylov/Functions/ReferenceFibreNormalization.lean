import krylov.Functions.ReferenceFibreRegularity
import krylov.Nonlinear.MetricCoordinates

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

/-- The actual Hessian-metric size, written without a parameter-dependent root.
Article: main_krylov, prop:Fcycle(iii). -/
def referenceMetricSize (base : Matrix (Fin n) (Fin n) ℝ)
    (u : EuclideanSpace ℝ (Fin n)) : ℝ := Real.sqrt (inner ℝ u (cgOperator base u))

/-- The true positive-root error norm equals its original quadratic-form size.
Article: main_krylov, prop:Fcycle(iii), actual metric dictionary. -/
theorem referenceMetricSize_eq_norm (base : Matrix (Fin n) (Fin n) ℝ)
    (hb : base.PosDef) (u : EuclideanSpace ℝ (Fin n)) :
    referenceMetricSize base u=‖metricCoordinates base hb u‖ := by
  have hs : (cgOperator (metricRoot base)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr (metricRoot_isSymm base))
  have hsq : inner ℝ u (cgOperator base u)=‖metricCoordinates base hb u‖^2 := by
    rw [metricCoordinates_apply,←real_inner_self_eq_norm_sq]
    calc
      _ = inner ℝ u (cgOperator (metricRoot base) (cgOperator (metricRoot base) u)) := by
        simp only [cgOperator,←mul_apply_eq_comp,←map_mul,metricRoot_square base hb]
      _ = _ := (hs u (cgOperator (metricRoot base) u)).symm
  rw [referenceMetricSize,hsq,Real.sqrt_sq (norm_nonneg _)]

/-- The actual metric error is positive at every nonzero reference displacement.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referenceMetricSize_pos (base : Matrix (Fin n) (Fin n) ℝ)
    (hb : base.PosDef) (u : EuclideanSpace ℝ (Fin n)) (hu : u≠0) :
    0<referenceMetricSize base u :=
  Real.sqrt_pos.mpr ((cgOperator_positive base hb).2 u hu)

/-- True metric error has C-one dependence on primitive Hessian and position
at every positive nonzero reference. Article: main_krylov, prop:Fcycle(iii). -/
theorem referenceMetricSize_contDiffAt (base : X → Matrix (Fin n) (Fin n) ℝ)
    (u : X → EuclideanSpace ℝ (Fin n)) (x : X) (hb : AnalyticAt ℝ base x)
    (hu : AnalyticAt ℝ u x) (hpos : (base x).PosDef) (hne : u x≠0) :
    ContDiffAt ℝ 1 (fun z=>referenceMetricSize (base z) (u z)) x := by
  have hQ := (krylov.Stability.matrixOperator_contDiffAt base x hb.contDiffAt).analyticAt
  exact (krylov.Stability.analytic_inner hu (krylov.Stability.analytic_operator_apply hQ hu)).contDiffAt.sqrt
    ((cgOperator_positive (base x) hpos).2 (u x) hne).ne'

/-- The sharp coefficient per cube of the true initial metric error.
Article: main_krylov, prop:Fcycle(iii), q_0² q_last normalization. -/
def referenceNormalizedFibreCoefficient (base : Matrix (Fin n) (Fin n) ℝ)
    (g u : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  referenceFibreCoefficient base g k/(referenceMetricSize base u)^3

/-- The full error-normalized sharp coefficient has first-order variation,
including simultaneous true-Hessian, gradient and minimizer displacement.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referenceNormalizedFibreCoefficient_order
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g u : X → EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hb : AnalyticAt ℝ base 0) (hg : AnalyticAt ℝ g 0) (hu : AnalyticAt ℝ u 0)
    (hpos : (base 0).PosDef) (hne : u 0≠0)
    (hpre : ∀ j≤k, CG.gradient (cgOperator (base 0)) (g 0) j≠0) :
    (fun z=>referenceNormalizedFibreCoefficient (base z) (g z) (u z) k-
      referenceNormalizedFibreCoefficient (base 0) (g 0) (u 0) k)
      =O[𝓝 (0 : X)] (fun z=>‖z‖) := by
  let F := fun z=>referenceFibreCoefficient (base z) (g z) k
  let I := fun z=>((referenceMetricSize (base z) (u z))^3)⁻¹
  have hF : (fun z=>F z-F 0)=O[𝓝 (0 : X)] (fun z=>‖z‖) :=
    referenceFibreCoefficient_order base g k hb hg hpos hpre
  have hI : ContDiffAt ℝ 1 I 0 :=
    ((referenceMetricSize_contDiffAt base u 0 hb hu hpos hne).pow 3).inv
      (pow_ne_zero _ (referenceMetricSize_pos (base 0) hpos (u 0) hne).ne')
  have hIb := hI.continuousAt.tendsto.isBigO_one ℝ
  have hIo : (fun z=>I z-I 0)=O[𝓝 (0 : X)] (fun z=>‖z‖) := by
    simpa only [sub_zero] using (hI.differentiableAt one_ne_zero).isBigO_sub.norm_right
  have hp : (fun z=>(F z-F 0)*I z)=O[𝓝 (0 : X)] (fun z=>‖z‖) := by
    simpa only [mul_one] using hF.mul hIb
  have hh := hp.add (hIo.const_mul_left (F 0))
  convert! hh using 1
  ext z
  dsimp only [referenceNormalizedFibreCoefficient,F,I]
  rw [div_eq_mul_inv,div_eq_mul_inv]
  ring

/-- A common primitive reference neighborhood preserves the sharp coefficient
relative to the actual initial error, for arbitrary actual perturbations.
Article: main_krylov, prop:Fcycle(iii), true-minimizer normalization. -/
theorem referenceNormalizedFibreCoefficient_variation
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g u : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hu : u≠0)
    (hpre : ∀ j≤k, CG.gradient (cgOperator base) g j≠0) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ Δ : Matrix (Fin n) (Fin n) ℝ,
      ∀ v w : EuclideanSpace ℝ (Fin n), ‖(Δ,(v,w))‖≤δ →
      |referenceNormalizedFibreCoefficient (base+Δ) (g+v) (u+w) k/
        referenceNormalizedFibreCoefficient base g u k-1|≤C*‖(Δ,(v,w))‖ := by
  have ho := referenceNormalizedFibreCoefficient_order
    (fun z : Matrix (Fin n) (Fin n) ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))=>base+z.1)
    (fun z : Matrix (Fin n) (Fin n) ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))=>g+z.2.1)
    (fun z : Matrix (Fin n) (Fin n) ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))=>u+z.2.2) k
    (analyticAt_const.add analyticAt_fst)
    (analyticAt_const.add (analyticAt_fst.comp analyticAt_snd))
    (analyticAt_const.add (analyticAt_snd.comp analyticAt_snd))
    (by simpa only [Prod.fst_zero,add_zero] using hb)
    (by simpa only [Prod.snd_zero,add_zero] using hu)
    (by simpa only [Prod.fst_zero,Prod.snd_zero,add_zero] using hpre)
  obtain ⟨C,hC,hev⟩ := isBigO_iff'.mp ho
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  have hK : 0<referenceNormalizedFibreCoefficient base g u k :=
    div_pos (referenceFibre_domains base hb g k hpre).2.2.2.2 (pow_pos (referenceMetricSize_pos base hb u hu) 3)
  refine ⟨δ/2,C/referenceNormalizedFibreCoefficient base g u k,by positivity,div_pos hC hK,?_⟩
  intro Δ v w hv
  have hh := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hv.trans_lt (by linarith : δ/2<δ))
  have hh' : |referenceNormalizedFibreCoefficient (base+Δ) (g+v) (u+w) k-
      referenceNormalizedFibreCoefficient base g u k|≤C*‖(Δ,(v,w))‖ := by
    simpa only [Prod.fst_zero,Prod.snd_zero,add_zero,Real.norm_eq_abs,abs_norm,Set.mem_ofPred_eq] using hh
  rw [div_sub_one hK.ne',abs_div,abs_of_pos hK]
  exact (div_le_div_of_nonneg_right hh' hK.le).trans_eq (by ring)

end
end krylov.Functions
