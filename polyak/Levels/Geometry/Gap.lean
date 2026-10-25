import polyak.Levels.Geometry.DipSets

/-! The original geometric gap I_K, including its open dip and both strict
root-of-unity endpoint conditions. -/
namespace polyak.Levels.Geometry
noncomputable section

def Gap (K : ℕ) (q : General.Tuning) : Prop :=
  2≤K ∧ (dip (tuningCurve q)).Nonempty ∧
    (∀ ω∈dip (tuningCurve q),2*Real.pi/(K+1)<(ω:ℝ) ∧ (ω:ℝ)<2*Real.pi/K) ∧
    Real.pi/K<q.angle (2*Real.pi/K) ∧
    Real.pi/(K+1)<q.angle (2*Real.pi/(K+1))

end
end polyak.Levels.Geometry
