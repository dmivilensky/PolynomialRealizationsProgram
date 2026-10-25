import polyak.Levels.Program.Curve

/-! The literal open and closed dips in the source frequency space. -/
noncomputable section
namespace polyak.Levels.Geometry
open Set

/-- The full closed dip, as a measurable subset of the original frequency
space. The endpoints are automatically absent for every curve. -/
def closedDip (Θ : Curve) : Set Frequency := {ω | Θ ω≤(ω:ℝ)/2}
def dip (Θ : Curve) : Set Frequency := {ω | Θ ω<(ω:ℝ)/2}

theorem closedDip_isCompact (Θ : Curve) : IsCompact (closedDip Θ) :=
  (isClosed_le Θ.continuous (continuous_subtype_val.div_const 2)).isCompact

theorem closedDip_interior_frequency (Θ : Curve) {ω : Frequency} (hω : ω∈closedDip Θ) :
    0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi := by
  have hh : Θ ω≤(ω:ℝ)/2 := hω
  constructor
  · linarith [Θ.pos ω]
  · by_contra hn
    have he : ω=frequencyPi := Subtype.ext (le_antisymm ω.property.2 (le_of_not_gt hn))
    rw [he,Θ.at_pi] at hh
    change Real.pi≤Real.pi/2 at hh
    linarith [Real.pi_pos]


end polyak.Levels.Geometry
