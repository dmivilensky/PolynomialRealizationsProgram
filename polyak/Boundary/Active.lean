import polyak.Waves.Polyak

/-! The actual signed primal lag and the common three-constraint active pattern. -/
noncomputable section
namespace polyak.Boundary
open Spectral

def signedRawLag (ν : Spectrum) (u t C : ℝ) (n : ℕ) (σ : ℝ) : ℝ :=
  meanA ν u t n+σ*meanB ν u n-σ*C*Real.sinh (n*t)

def ThreeActive (n : ℕ) (σ : ℝ) : Prop :=
  (n=1 ∧ σ= -1) ∨ ((n=2 ∨ n=3) ∧ σ=1)

end polyak.Boundary
