import krylov.Functions.ReferenceTwoMetricNormalization

/-!
Article: main_krylov, prop:Fcycle(iii), primitive actual-reference normalization.
Use: absorb independently derived drifts of the observed matrix, true Hessian
and normalized minimizer into one sharp coefficient neighborhood. No analytic
parameterization of the actual sources is required. Source: the proved joint
coefficient variation and continuity of the genuine positive metric error.
-/
namespace krylov.Functions
noncomputable section
open Matrix Filter Topology krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true metric size stays uniformly separated from zero on a primitive
neighborhood of a positive nonzero reference. Article: prop:Fcycle(iii). -/
theorem referenceMetricSize_primitive_lower (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (u : EuclideanSpace ℝ (Fin n)) (hu : u≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ H : Matrix (Fin n) (Fin n) ℝ,
      ∀ v : EuclideanSpace ℝ (Fin n), ‖(H-A,v-u)‖≤δ →
      referenceMetricSize A u/2≤referenceMetricSize H v := by
  let Z := Matrix (Fin n) (Fin n) ℝ × EuclideanSpace ℝ (Fin n)
  have hc := (referenceMetricSize_contDiffAt (fun z : Z=>A+z.1) (fun z : Z=>u+z.2) 0
    (analyticAt_const.add analyticAt_fst) (analyticAt_const.add analyticAt_snd)
    (by simpa only [Prod.fst_zero,add_zero] using hA)
    (by simpa only [Prod.snd_zero,add_zero] using hu)).continuousAt
  have hp := referenceMetricSize_pos A hA u hu
  have he : ∀ᶠ z : Z in 𝓝 0, referenceMetricSize A u/2<referenceMetricSize (A+z.1) (u+z.2) := by
    apply hc.preimage_mem_nhds
    apply isOpen_Ioi.mem_nhds
    change referenceMetricSize A u/2<referenceMetricSize (A+(0 : Z).1) (u+(0 : Z).2)
    simpa only [Prod.fst_zero,Prod.snd_zero,add_zero] using (half_lt_self hp)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro H v hv
  have hh := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hv.trans_lt (by linarith : δ/2<δ))
  change referenceMetricSize A u/2<referenceMetricSize (A+(H-A)) (u+(v-u)) at hh
  simpa only [add_sub_cancel] using hh.le

/-- Independently bounded actual source drifts imply a common first-order
sharp normalization in the true error metric and a positive true error scale.
Article: main_krylov, prop:Fcycle(iii). -/
theorem reference_primitive_normalization
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g u : EuclideanSpace ℝ (Fin n)) (hu : u≠0) (k : ℕ)
    (hpre : ∀ j≤k, CG.gradient (cgOperator A) g j≠0) (S : ℝ) (hS : 0<S) :
    ∃ ep C c : ℝ, 0<ep ∧ 0<C ∧ 0<c ∧
      ∀ ε : ℝ, 0<ε → ε<ep → ∀ B H : Matrix (Fin n) (Fin n) ℝ,
      ∀ v : EuclideanSpace ℝ (Fin n),
      ‖B-A‖≤S*ε → ‖H-A‖≤S*ε → ‖v-u‖≤S*ε →
      c*ε≤ε*referenceMetricSize H v ∧
      |referenceTwoMetricFibreCoefficient B H g v k/referenceTwoMetricFibreCoefficient A A g u k-1|≤C*ε ∧
      |referenceFibreCoefficient B g k-referenceFibreCoefficient A g k|≤C*ε := by
  obtain ⟨δ₀,hδ₀,hsz⟩ := referenceMetricSize_primitive_lower A hA u hu
  obtain ⟨δ₁,C₁,hδ₁,hC₁,hκ⟩ := referenceTwoMetricFibreCoefficient_variation A A hA hA g u k hu hpre
  obtain ⟨δ₂,C₂,hδ₂,hC₂,hρ⟩ := referenceFibreCoefficient_variation A hA g k hpre
  let δ := min δ₀ (min δ₁ δ₂)
  let ep := δ/(S+1)
  have hδ : 0<δ := lt_min hδ₀ (lt_min hδ₁ hδ₂)
  refine ⟨ep,(C₁+C₂)*S,referenceMetricSize A u/2,div_pos hδ (by linarith),by positivity,
    half_pos (referenceMetricSize_pos A hA u hu),?_⟩
  intro ε hε heps B H v hB hH hv
  have hsmall : S*ε≤δ := by
    have hh := (lt_div_iff₀ (by linarith : 0<S+1)).mp heps
    nlinarith only [hh,hε]
  have hb₀ : ‖(H-A,v-u)‖≤δ₀ := by
    rw [Prod.norm_def]
    exact (max_le hH hv).trans (hsmall.trans (min_le_left _ _))
  have hb₁ : ‖((B-A,H-A),((0 : EuclideanSpace ℝ (Fin n)),v-u))‖≤S*ε := by
    simp only [Prod.norm_def,norm_zero]
    exact max_le (max_le hB hH) (max_le (by positivity) hv)
  have hb₂ : ‖(B-A,(0 : EuclideanSpace ℝ (Fin n)))‖≤S*ε := by
    rw [Prod.norm_def,norm_zero]
    exact max_le hB (by positivity)
  refine ⟨by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hsz H v hb₀) hε.le,?_,?_⟩
  · have hh := hκ (B-A) (H-A) 0 (v-u)
      (hb₁.trans (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))))
    simp only [add_sub_cancel,add_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hb₁ hC₁.le).trans (by nlinarith only [mul_nonneg hC₂.le (mul_nonneg hS.le hε.le)]))
  · have hh := hρ (B-A) 0
      (hb₂.trans (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))))
    simp only [add_sub_cancel,add_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hb₂ hC₂.le).trans (by nlinarith only [mul_nonneg hC₁.le (mul_nonneg hS.le hε.le)]))

end
end krylov.Functions
