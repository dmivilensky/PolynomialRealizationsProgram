import polyak.ModeLocking.Analysis.JetBounds
import Mathlib.Topology.Compactness.Compact

/-! Uniform quadratic Taylor limits over a compact parameter space.
The remainder estimate is derived from the actual second derivative and
Lagrange's remainder, with one frequency radius for every parameter. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Set Filter
open scoped Topology

private theorem abs_le_of_uIcc_zero {y δ : ℝ} (hy : y∈uIcc (0:ℝ) δ) : |y|≤|δ| := by
  by_cases hδ : 0≤δ
  · rw [uIcc_of_le hδ] at hy
    rw [abs_of_nonneg hy.1,abs_of_nonneg hδ]
    exact hy.2
  · have hδ' := le_of_not_ge hδ
    rw [uIcc_of_ge hδ'] at hy
    rw [abs_of_nonpos hy.2,abs_of_nonpos hδ']
    exact neg_le_neg hy.1

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem uniform_second_difference (F : X→ℝ→ℝ)
    (hF : ∀ x,ContinuousAt (fun p:X×ℝ=>deriv^[2] (F p.1) p.2) (x,0))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ x,|deriv^[2] (F x) t-deriv^[2] (F x) 0|<ε := by
  have hh := isCompact_univ.eventually_forall_of_forall_eventually
    (P := fun t x=>|deriv^[2] (F x) t-deriv^[2] (F x) 0|<ε) (fun x _=>by
      have h₁ := ContinuousAt.comp (f := fun p:ℝ×X=>(p.2,p.1))
        (g := fun p:X×ℝ=>deriv^[2] (F p.1) p.2) (x := (0,x)) (hF x)
        (continuousAt_snd.prodMk continuousAt_fst)
      have h₂ := ContinuousAt.comp (f := fun p:ℝ×X=>(p.2,(0:ℝ)))
        (g := fun p:X×ℝ=>deriv^[2] (F p.1) p.2) (x := (0,x)) (hF x)
        (continuousAt_snd.prodMk continuousAt_const)
      have hc : ContinuousAt (fun p:ℝ×X=>deriv^[2] (F p.2) p.1-deriv^[2] (F p.2) 0) (0,x) := by
        simpa only [Function.comp_def,Pi.sub_def] using h₁.sub h₂
      have he := hc.abs.eventually (eventually_lt_nhds (show
          |deriv^[2] (F x) 0-deriv^[2] (F x) 0|<ε by simpa only [sub_self,abs_zero] using hε))
      exact he)
  exact hh.mono (fun t ht x=>ht x (mem_univ x))

theorem uniform_quadratic_taylor (F : X→ℝ→ℝ) {r : ℝ} (hr : 0<r)
    (hsmooth : ∀ x t,|t|<r → AnalyticAt ℝ (F x) t)
    (hsecond : ∀ x,ContinuousAt (fun p:X×ℝ=>deriv^[2] (F p.1) p.2) (x,0))
    (hzero : ∀x,F x 0=0) (hslope : ∀x,deriv (F x) 0=0)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ δ in 𝓝[≠] (0:ℝ), ∀x,
      |F x δ/δ^2-deriv^[2] (F x) 0/2|<ε := by
  obtain ⟨d,hd,hbound⟩ := Metric.eventually_nhds_iff.mp (uniform_second_difference F hsecond hε)
  have hevent : ∀ᶠ δ in 𝓝 (0:ℝ),|δ|<min r d := by
    exact Metric.eventually_nhds_iff.mpr ⟨min r d,lt_min hr hd,fun {y} hy=>by
      simpa only [Real.dist_eq,sub_zero] using hy⟩
  filter_upwards [hevent.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with δ hδ hz x
  have hδ0 : δ≠0 := hz
  have hf (y) (hy : y∈uIcc (0:ℝ) δ) : ContDiffAt ℝ 2 (F x) y := by
    have hab : |y|≤|δ| := by simpa only [sub_zero] using abs_le_of_uIcc_zero hy
    exact (hsmooth x y (hab.trans_lt (hδ.trans_le (min_le_left _ _)))).contDiffAt
  obtain ⟨y,hy,hyform⟩ := ModeLocking.Analysis.quadratic_taylor hf left_mem_uIcc right_mem_uIcc
    (Ne.symm hδ0) (hzero x) (hslope x)
  have hab : |y|≤|δ| := by
    simpa only [sub_zero] using abs_le_of_uIcc_zero (Ioo_subset_Icc_self hy)
  have hybound := hbound (show dist y (0:ℝ)<d by
    simpa only [Real.dist_eq,sub_zero] using hab.trans_lt (hδ.trans_le (min_le_right _ _))) x
  have hidentity : F x δ/δ^2-deriv^[2] (F x) 0/2=
      (deriv^[2] (F x) y-deriv^[2] (F x) 0)/2 := by
    rw [hyform]
    simp only [sub_zero,iteratedDeriv_eq_iterate]
    field_simp [hδ0]
  rw [hidentity,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

end polyak.FareyPlateau.FanAnalysis
