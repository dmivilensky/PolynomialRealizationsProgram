import polyak.Spectral.HullAnalytic
import polyak.Spectral.HullEndpoint
import polyak.Spectral.NormalizedCertificate

/-!
Article: Appendix A, finite-support lemma, the zero set of the limiting symbol.
Use: a single compact convex dual symbol has finitely many physical zeros,
all strictly inside the cosine interval.
Proof: holomorphy on a connected neighborhood and the uniform strict endpoint sign.
-/

namespace polyak.Spectral
noncomputable section
open Set
open scoped Topology

/-- Article: the actual zero set in the source cosine coordinate. -/
def dualZeros {s : ℝ} (hs : 0 < s) (u : ℝ) (d : DualCoefficient s) : Set Frequency :=
  {c | evaluateDual u d (dualAngle s hs c)=0}

/-- Article: strict endpoint sign gives a nonzero symbol at either end. -/
theorem dualHull_endpoint_ne_zero {s : ℝ} (hs : 0 < s) {u : ℝ} (hu : 0 < u)
    (ω : ℝ) (hω : ω=0 ∨ ω=Real.pi) (z : lagWindow s) (hz : (z : ℂ)=(ω : ℂ))
    {d : DualCoefficient s} (hd : d ∈ dualHull s hs) : evaluateDual u d z ≠ 0 := by
  intro hzero
  have he := dualHull_endpoint_le hs u ω hω z hz hd
  rw [hzero,Complex.zero_re] at he
  have hb := (lagRadial_bounds hs 0).2.2
  have hp : 0 < (1-Real.exp (-s))/(1+Real.exp (-s)) := div_pos (by linarith) (by positivity)
  nlinarith [mul_pos (sq_pos_of_pos hu) hp]

/-- Article: analytic finite zero set on all physical frequencies. -/
theorem dualZeros_finite {s : ℝ} (hs : 0 < s) {u : ℝ} (hu : 0 < u)
    {d : DualCoefficient s} (hd : d ∈ dualHull s hs) : (dualZeros hs u d).Finite := by
  let f := windowExtension (evaluateDual u d)
  let A : Set ℂ := Complex.ofReal '' Icc (0 : ℝ) Real.pi
  have hA : IsCompact A := isCompact_Icc.image Complex.continuous_ofReal
  have hAU : A ⊆ interior (lagWindow s) := by
    rintro _ ⟨ω,hω,rfl⟩
    exact real_mem_interior_lagWindow hs hω
  let z₀ : lagWindow s := ⟨0,interior_subset (real_mem_interior_lagWindow hs
    ⟨le_rfl,Real.pi_pos.le⟩)⟩
  have hz₀ : (0 : ℂ) ∈ interior (lagWindow s) := real_mem_interior_lagWindow hs
    ⟨le_rfl,Real.pi_pos.le⟩
  have hf₀ : f 0 ≠ 0 := by
    have he := dualHull_endpoint_ne_zero hs hu 0 (Or.inl rfl) z₀ rfl hd
    simpa only [f,← windowExtension_coe] using he
  have hz := finite_zeros_on_compact isOpen_interior (convex_lagWindow s).interior.isPreconnected
    hA hAU (dualHull_holomorphic hs u hd) hz₀ hf₀
  let angle : Frequency → ℂ := fun c => (Real.arccos c : ℂ)
  have hinj : Function.Injective angle := by
    intro c c' he
    apply Subtype.ext
    have he' : Real.arccos (c : ℝ)=Real.arccos (c' : ℝ) := Complex.ofReal_injective he
    have hh := congrArg Real.cos he'
    simpa only [Real.cos_arccos c.property.1 c.property.2,
      Real.cos_arccos c'.property.1 c'.property.2] using hh
  have himage : angle '' dualZeros hs u d ⊆ {w∈A | f w=0} := by
    rintro _ ⟨c,hc,rfl⟩
    refine ⟨⟨Real.arccos c,⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩,rfl⟩,?_⟩
    have he := windowExtension_coe (evaluateDual u d) (dualAngle s hs c)
    exact he.trans hc
  exact Set.Finite.of_finite_image (hz.subset himage) hinj.injOn

/-- Article: no physical endpoint belongs to the limiting dual zero set. -/
theorem dualZeros_interior {s : ℝ} (hs : 0 < s) {u : ℝ} (hu : 0 < u)
    {d : DualCoefficient s} (hd : d ∈ dualHull s hs) {c : Frequency} (hc : c ∈ dualZeros hs u d) :
    -1 < (c : ℝ) ∧ (c : ℝ) < 1 := by
  have hleft : (c : ℝ) ≠ -1 := by
    intro he
    have ha : ((dualAngle s hs c : lagWindow s) : ℂ)=(Real.pi : ℂ) := by
      simp only [dualAngle,he,Real.arccos_neg_one]
    exact dualHull_endpoint_ne_zero hs hu Real.pi (Or.inr rfl) _ ha hd hc
  have hright : (c : ℝ) ≠ 1 := by
    intro he
    have ha : ((dualAngle s hs c : lagWindow s) : ℂ)=(0 : ℂ) := by
      simp only [dualAngle,he,Real.arccos_one,Complex.ofReal_zero]
    exact dualHull_endpoint_ne_zero hs hu 0 (Or.inl rfl) _ ha hd hc
  exact ⟨lt_of_le_of_ne c.property.1 hleft.symm,lt_of_le_of_ne c.property.2 hright⟩

end
end polyak.Spectral
