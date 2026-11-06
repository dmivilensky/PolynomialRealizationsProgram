import nesterov.Attainment.Trace

/-! The common compact hull preserves holomorphy of the actual polynomial
symbols on a fixed complex neighbourhood, also when the exponent moves. -/
noncomputable section
open Set
open scoped Topology OnePoint
namespace nesterov.Attainment

theorem holomorphic_restriction_of_entire {lo hi : ℝ} {d : DualPoint lo hi}
    (s : LagParameter lo hi) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (he : ∀ z : LagWindow lo, d.2 (s,z) = f z) :
    DifferentiableOn ℂ (polyak.Spectral.windowExtension (restrictSymbolCLM lo hi s d))
      (interior (LagWindow lo)) := by
  apply hf.differentiableOn.congr
  intro z hz
  rw [polyak.Spectral.windowExtension, dite_eq_left (interior_subset hz)]
  exact he ⟨z,interior_subset hz⟩

theorem polynomial_generator_holomorphic (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) {d : DualPoint lo hi}
    (hd : d ∈ dualGenerators lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ)) :
    DifferentiableOn ℂ (polyak.Spectral.windowExtension (restrictSymbolCLM lo hi s d))
      (interior (LagWindow lo)) := by
  obtain ⟨⟨b,l⟩,rfl⟩ := hd
  let δ : ℝ := if b then -1 else 1
  change DifferentiableOn ℂ (polyak.Spectral.windowExtension (restrictSymbolCLM lo hi s
    (dualFamily lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ) δ l))) _
  induction l using OnePoint.rec with
  | infty =>
    rw [dualFamily_infty]
    exact holomorphic_restriction_of_entire s (gapEntire u p (σ*s))
      (differentiable_gapEntire u p (σ*s)) (fun _ => rfl)
  | coe n =>
    let f : ℂ → ℂ := fun z => gapEntire u p (σ*s) z*cosineKernel s n z-
      (2*δ : ℝ) • (skewEntire u p (σ*s) z*sineKernel s n z)
    apply holomorphic_restriction_of_entire s f
    · dsimp [f, gapEntire, skewEntire, amplitude, cosineKernel, sineKernel]
      fun_prop
    · intro z
      rfl

/-- The limiting symbol is analytic on the common open frequency window. -/
theorem polynomial_dualHull_holomorphic (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) {d : DualPoint lo hi}
    (hd : d ∈ dualHull lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ)) :
    DifferentiableOn ℂ (polyak.Spectral.windowExtension (restrictSymbolCLM lo hi s d))
      (interior (LagWindow lo)) := by
  let L := restrictSymbolCLM lo hi s
  have hconv := polyak.Spectral.convex_holomorphic_window.linear_preimage L.toLinearMap
  have hclosed := polyak.Spectral.isClosed_holomorphic_window.preimage L.continuous
  exact (closure_minimal (hconv.convexHull_subset_iff.mpr
    (fun g hg => polynomial_generator_holomorphic u p lo hi σ hlo s hg)) hclosed) hd

end nesterov.Attainment
