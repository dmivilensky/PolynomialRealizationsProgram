import polyak.Spectral.CompactDual

/-!
Article: Appendix A, analyticity of the limiting normalized dual symbol.
Use: holomorphy survives the entire compact convex construction, uniformly in u.
Proof: continuous linear evaluation, the closed convex holomorphic class and Weierstrass.
-/

namespace polyak.Spectral
noncomputable section
open Set
open scoped Topology OnePoint

/-- Article: the complex window has connected interior. -/
theorem convex_lagWindow (s : ℝ) : Convex ℝ (lagWindow s) := by
  have hstrip := (convex_Icc (-s/2) (s/2)).linear_preimage Complex.imCLM.toLinearMap
  have he : {z : ℂ | |z.im| ≤ s/2} = Complex.imCLM ⁻¹' Icc (-s/2) (s/2) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Complex.imCLM_apply, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  exact (convex_closedBall (0 : ℂ) (Real.pi+1)).inter (he.symm ▸ hstrip)

/-- Article: finite normalized lag restrictions are holomorphic in the full window interior. -/
theorem holomorphic_complexLagMap (u s δ : ℝ) (n : ℕ) :
    DifferentiableOn ℂ (windowExtension (complexLagMap u s δ n)) (interior (lagWindow s)) := by
  apply (differentiable_complexLag u s δ n).differentiableOn.congr
  intro z hz
  simp only [windowExtension,dite_eq_left (interior_subset hz),complexLagMap,ContinuousMap.coe_mk]

/-- Article: the limiting minimizer restriction is holomorphic in the window interior. -/
theorem holomorphic_complexGapMap (u s : ℝ) :
    DifferentiableOn ℂ (windowExtension (complexGapMap u s)) (interior (lagWindow s)) := by
  apply (differentiable_complexGap u).differentiableOn.congr
  intro z hz
  simp only [windowExtension,dite_eq_left (interior_subset hz),complexGapMap,ContinuousMap.coe_mk]

/-- Article: every compactified generator is holomorphic after exact twist evaluation. -/
theorem generator_holomorphic {s : ℝ} (hs : 0 < s) (u : ℝ)
    {d : DualCoefficient s} (hd : d ∈ dualGenerators s hs) :
    DifferentiableOn ℂ (windowExtension (evaluateDual u d)) (interior (lagWindow s)) := by
  have hfamily (δ : ℝ) (hδ : |δ| ≤ 1) (l : OnePoint ℕ) :
      DifferentiableOn ℂ (windowExtension (evaluateDual u (coefficientFamily s δ hs hδ l)))
        (interior (lagWindow s)) := by
    induction l using OnePoint.rec with
    | infty => rw [evaluateDual_coefficient_infty]; exact holomorphic_complexGapMap u s
    | coe n => rw [evaluateDual_coefficient_coe]; exact holomorphic_complexLagMap u s δ n
  rcases hd with ⟨l,rfl⟩ | ⟨l,rfl⟩
  · exact hfamily 1 (by norm_num) l
  · exact hfamily (-1) (by norm_num) l

/-- Article: the actual limiting dual symbol is holomorphic around the entire physical interval. -/
theorem dualHull_holomorphic {s : ℝ} (hs : 0 < s) (u : ℝ) {d : DualCoefficient s}
    (hd : d ∈ dualHull s hs) :
    DifferentiableOn ℂ (windowExtension (evaluateDual u d)) (interior (lagWindow s)) := by
  let L := evaluateDualCLM (s := s) u
  have hconv := convex_holomorphic_window.linear_preimage L.toLinearMap
  have hclosed := isClosed_holomorphic_window.preimage L.continuous
  exact (closure_minimal (hconv.convexHull_subset_iff.mpr (fun g hg => generator_holomorphic hs u hg))
    hclosed) hd

end
end polyak.Spectral
