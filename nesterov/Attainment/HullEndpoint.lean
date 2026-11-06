import nesterov.Attainment.NormalizedCertificate

/-! The negative endpoint gap gives a uniform strictly negative endpoint
value on the entire compact convex dual hull, including both infinity labels. -/
noncomputable section
open Set
open scoped Topology OnePoint
namespace nesterov.Attainment
open Spectral

theorem generator_endpoint_neg (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) (c : Frequency) (hc : (c : ℝ)=1 ∨ (c : ℝ)= -1)
    (hg : g (polynomialPair u p (σ*s)) c < 0)
    {d : DualPoint lo hi}
    (hd : d ∈ dualGenerators lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ)) :
    (d.2 (s,physicalAngle lo hlo c)).re < 0 := by
  obtain ⟨⟨b,l⟩,rfl⟩ := hd
  change ((dualFamily lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ)
    (if b then -1 else 1) l).2 (s,physicalAngle lo hlo c)).re < 0
  induction l using OnePoint.rec with
  | infty => rw [dualFamily_physical_infty]; exact hg
  | coe n =>
    rw [dualFamily_physical_coe]
    simp only [Complex.ofReal_re]
    have hsin : Real.sin ((n+1 : ℕ)*Real.arccos c)=0 := by
      rcases hc with hc | hc
      · simp [hc]
      · rw [hc, Real.arccos_neg_one]
        exact Real.sin_nat_mul_pi (n+1)
    have hs : 0 < (n+1 : ℕ)*(s : ℝ) :=
      mul_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) (hlo.trans_le s.property.1)
    have hA : 0 < Real.cosh ((n+1 : ℕ)*s)-Real.cos ((n+1 : ℕ)*Real.arccos c) := by
      have hh := Real.one_lt_cosh.mpr (ne_of_gt hs)
      linarith [Real.cos_le_one ((n+1 : ℕ)*Real.arccos c)]
    simp only [lagB,hsin,mul_zero,sub_zero,lagA]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hg hA) (Real.sinh_pos_iff.mpr hs)

/-- A strictly negative uniform endpoint reserve survives every normalized dual limit. -/
theorem dualHull_endpoint_neg (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) (c : Frequency) (hc : (c : ℝ)=1 ∨ (c : ℝ)= -1)
    (hg : g (polynomialPair u p (σ*s)) c < 0)
    {d : DualPoint lo hi} (hd : d ∈ polynomialDualHull u p lo hi σ hlo) :
    (d.2 (s,physicalAngle lo hlo c)).re < 0 := by
  let L := traceCLM lo hi s (physicalAngle lo hlo c)
  let f : DualLabel → ℝ := fun l => L (dualLabelMap lo hi hlo
    (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ) l)
  have hf : Continuous f := L.continuous.comp (dualLabelMap lo hi hlo _ _).continuous
  obtain ⟨B,hB⟩ := (isCompact_range hf).exists_isGreatest (Set.range_nonempty f)
  have hBn : B < 0 := by
    obtain ⟨l,rfl⟩ := hB.1
    exact generator_endpoint_neg u p lo hi σ hlo s c hc hg ⟨l,rfl⟩
  have hle : L d ≤ B := dualHull_le L B
    (by rintro g ⟨l,rfl⟩; exact hB.2 ⟨l,rfl⟩) hd
  exact hle.trans_lt hBn

end nesterov.Attainment
