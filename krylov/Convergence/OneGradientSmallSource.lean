import krylov.Convergence.OneGradientNormalLower

/-!
Article: main_krylov, thm:LB, source scale chosen before the policy.
Use: derive all genuine cubic smallness and uniform perturbation-denominator
conditions from a sufficiently small positive forcing h. Constants are
fixed before any M1 last query, which may depend arbitrarily on h.
Source: true quadratic minimizer homogeneity and elementary continuity of
the explicit polynomial majorants already proved for clipped cubics.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Filter Topology krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The genuine quadratic minimizer scales exactly with the true force.
Article: main_krylov, thm:LB. -/
theorem oneGradientQuadraticMinimizer_smul
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (g : E) (h : ℝ) :
    oneGradientQuadraticMinimizer A (h • g)=h • oneGradientQuadraticMinimizer A g := by
  simp only [oneGradientQuadraticMinimizer,map_smul,smul_neg]

/-- All scalar source conditions hold uniformly at small positive h,
independently of a method, its last query, and its output. The explicit
majorant is exactly the original clipped-source relative denominator.
Article: main_krylov, thm:LB. -/
theorem oneGradient_small_source_scalars
    (M c m δ η ξ R Y N : ℝ) (hM : 0<M) (_hc : 0<c) (_hm : 0<m) (hδ : 0<δ)
    (hR : 0<R) (hB0 : c^2*δ<η) (hξ : δ<ξ) :
    ∃ s : ℝ,0<s ∧∀ h : ℝ,0<h → h<s →
      h*|Y|≤δ/M ∧2*M*(2/m)^2*(h*N)≤1 ∧2*(2/m)*(h*N)≤R ∧
      c^2*(M*(h*|Y|)+δ)+M*c^4/4*(h*|Y|)*(M*(h*|Y|)+2*δ)≤η ∧
      δ+2*M*(2/m)*(h*N)≤ξ := by
  let B := fun h : ℝ=>c^2*(M*(h*|Y|)+δ)+M*c^4/4*(h*|Y|)*(M*(h*|Y|)+2*δ)
  have h1 : ∀ᶠ h : ℝ in 𝓝 0,h*|Y|<δ/M := by
    have hc : ContinuousAt (fun h : ℝ=>h*|Y|) 0 := by fun_prop
    exact hc.eventually (gt_mem_nhds (by simpa only [zero_mul] using div_pos hδ hM))
  have h2 : ∀ᶠ h : ℝ in 𝓝 0,2*M*(2/m)^2*(h*N)<1 := by
    have hc : ContinuousAt (fun h : ℝ=>2*M*(2/m)^2*(h*N)) 0 := by fun_prop
    exact hc.eventually (gt_mem_nhds (by simp only [zero_mul,mul_zero];norm_num))
  have h3 : ∀ᶠ h : ℝ in 𝓝 0,2*(2/m)*(h*N)<R := by
    have hc : ContinuousAt (fun h : ℝ=>2*(2/m)*(h*N)) 0 := by fun_prop
    exact hc.eventually (gt_mem_nhds (by simpa only [zero_mul,mul_zero] using hR))
  have h4 : ∀ᶠ h : ℝ in 𝓝 0,B h<η := by
    have hc : ContinuousAt B 0 := by dsimp only [B];fun_prop
    exact hc.eventually (gt_mem_nhds (by simpa only [B,zero_mul,mul_zero,add_zero,zero_add] using hB0))
  have h5 : ∀ᶠ h : ℝ in 𝓝 0,δ+2*M*(2/m)*(h*N)<ξ := by
    have hc : ContinuousAt (fun h : ℝ=>δ+2*M*(2/m)*(h*N)) 0 := by fun_prop
    exact hc.eventually (gt_mem_nhds (by simpa only [zero_mul,mul_zero,add_zero] using hξ))
  have hgood : ∀ᶠ h : ℝ in 𝓝 0,h*|Y|≤δ/M ∧2*M*(2/m)^2*(h*N)≤1 ∧2*(2/m)*(h*N)≤R ∧B h≤η ∧
      δ+2*M*(2/m)*(h*N)≤ξ := by
    filter_upwards [h1,h2,h3,h4,h5] with h hh1 hh2 hh3 hh4 hh5
    exact ⟨hh1.le,hh2.le,hh3.le,hh4.le,hh5.le⟩
  obtain ⟨s,hs,hbound⟩ := Metric.eventually_nhds_iff.mp hgood
  refine ⟨s,hs,?_⟩
  intro h hh hhsmall
  exact hbound (by simpa only [dist_zero_right,Real.norm_of_nonneg hh.le] using hhsmall)

end
end krylov.Convergence
