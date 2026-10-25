import polyak.Boundary.P2.Differential

/-! Article: inverse-coordinate calculus for the actual rational P₂ branch. -/
namespace polyak.Boundary.P2
noncomputable section
open Spectral Filter
open scoped Topology

/-- Article: the source closed arc lies in the common sign interval. -/
private theorem parameter_arc_mem {z : ℝ} (hz : z∈Set.Icc zeta1 zetaA) : z∈parameterInterval := by
  constructor <;> linarith [hz.1,hz.2,zeta1_bounds.1,zetaA_bounds.2]

/-- Article: the actual boundary has the stated derivative within the whole closed arc,
including the one-sided derivatives at the two switches. -/
theorem hasDerivWithinAt_of_branch (F : ℝ → ℝ)
    (hbranch : ∀ z∈Set.Icc zeta1 zetaA,∀ s : ℝ,Real.cosh s=G z → F s=Real.arsinh (u z))
    {z t : ℝ} (hz : z∈Set.Icc zeta1 zetaA)
    (ht : Real.cosh t=G z) : HasDerivWithinAt F (boundaryDerivative z t) exponentArc t := by
  have hm:=parameter_arc_mem hz
  have hg:=hasStrictDerivAt_G hm
  have hn: GDerivative z≠0 := (GDerivative_neg hm).ne
  let inv := hg.localInverse G (GDerivative z) z hn
  have hi : HasDerivAt inv (GDerivative z)⁻¹ (G z) := hg.to_localInverse hn |>.hasDerivAt
  have hleft : inv (G z)=z := (hg.eventually_left_inverse hn).self_of_nhds
  have hi' : HasDerivAt inv (GDerivative z)⁻¹ (Real.cosh t) := by rw [ht]; exact hi
  have hit : inv (Real.cosh t)=z := by rw [ht]; exact hleft
  have hd := ((hasDerivAt_u hm).comp_of_eq t (hi'.comp t (Real.hasDerivAt_cosh t)) hit.symm).arsinh
  have hder : HasDerivAt (fun s => Real.arsinh (u (inv (Real.cosh s)))) (boundaryDerivative z t) t := by
    convert hd using 1
    · simp only [Function.comp_apply]
    · dsimp [boundaryDerivative]
      rw [hit]
      field_simp
  have hnear : ∀ᶠ s in 𝓝 t, inv (Real.cosh s)∈parameterInterval ∧ G (inv (Real.cosh s))=Real.cosh s := by
    have hc : ContinuousAt (fun s => inv (Real.cosh s)) t := hi'.continuousAt.comp (Real.continuous_cosh.continuousAt)
    have hio : ∀ᶠ s in 𝓝 t, inv (Real.cosh s)∈Set.Ioo (3391/2000) (1699/1000) := by
      apply hc (Ioo_mem_nhds ?_ ?_)
      · change 3391/2000 < inv (Real.cosh t)
        rw [hit]; exact (arc_mem_interior hz).1
      · change inv (Real.cosh t) < 1699/1000
        rw [hit]; exact (arc_mem_interior hz).2
    have hr : ∀ᶠ s in 𝓝 t,G (inv (Real.cosh s))=Real.cosh s := by
      have hr0 := hg.eventually_right_inverse hn
      rw [←ht] at hr0
      exact Real.continuous_cosh.continuousAt.eventually hr0
    filter_upwards [hio,hr] with s hs he
    exact ⟨⟨hs.1.le,hs.2.le⟩,he⟩
  have heq : F =ᶠ[𝓝[exponentArc] t] (fun s => Real.arsinh (u (inv (Real.cosh s)))) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hs hsa
    have hlo : zeta1 ≤ inv (Real.cosh s) := by
      by_contra hh
      have ho:=G_strictAntiOn hs.1 zeta1_mem (lt_of_not_ge hh)
      rw [G_zeta1,hs.2] at ho
      exact (not_lt_of_ge hsa.2) ho
    have hhi : inv (Real.cosh s) ≤ zetaA := by
      by_contra hh
      have ho:=G_strictAntiOn zetaA_mem hs.1 (lt_of_not_ge hh)
      rw [hs.2] at ho
      exact (not_lt_of_ge hsa.1) ho
    exact hbranch _ ⟨hlo,hhi⟩ s hs.2.symm
  apply hder.hasDerivWithinAt.congr_of_eventuallyEq heq
  rw [hit]
  exact hbranch z hz t ht


end
end polyak.Boundary.P2
