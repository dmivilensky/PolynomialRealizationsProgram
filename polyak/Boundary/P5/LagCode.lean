import polyak.Numerics.ShiftedCode
import polyak.Boundary.P5.DividedSlacks
import polyak.Boundary.P5.RealChebyshev
import polyak.Boundary.P5.LocalLimits

/-!
Article: (p5arc), exact divided Chebyshev source for the finite lag prefix.
Use: shifted polynomials retain the h factor symbolically before interval evaluation.
The real raw slack is independently specified in System and DividedSlacks.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral LeanCert.Engine Polynomial

/-- Each finite annotation is tied to the actual Chebyshev source at every real input. -/
structure LagCode (n : ℕ) where
  tCentre : ℚ
  uCentre : ℚ
  TGdiv : QPoly
  TXdiv : QPoly
  UXdiv : QPoly
  UG : QPoly
  TY : QPoly
  UY : QPoly
  TG_exact : ∀ h : ℝ, chebT n (1+h)=1+h*aeval h TGdiv.toPoly
  TX_exact : ∀ r : ℝ, chebT n (-1/2+r)=(tCentre : ℝ)+r*aeval r TXdiv.toPoly
  UX_exact : ∀ r : ℝ, chebU (n-1) (-1/2+r)=(uCentre : ℝ)+r*aeval r UXdiv.toPoly
  UG_exact : ∀ h : ℝ, aeval h UG.toPoly=chebU (n-1) (1+h)
  TY_exact : ∀ y : ℝ, aeval y TY.toPoly=chebT n y
  UY_exact : ∀ y : ℝ, aeval y UY.toPoly=chebU (n-1) y

def mainAmplitudeCoefficient (h : ℝ) (Z : Coordinates) : ℝ :=
  3/2*Z 0+Z 1+h*(2*Z 0*Z 1-(Z 1)^2)-2*h^2*Z 0*(Z 1)^2

theorem main_amplitude_difference (h : ℝ) (Z : Coordinates) :
    2*branchU h Z*(1-(branchX h Z)^2)=3/4+h*mainAmplitudeCoefficient h Z := by
  unfold branchU branchX mainAmplitudeCoefficient
  ring

/-- The source divided part of the main-atom raw lag, including every remainder term. -/
def mainDivided (n : ℕ) (code : LagCode n) (h : ℝ) (Z : Coordinates) (σ : ℝ) : ℝ :=
  mainGapCoefficient h Z*(1-(code.tCentre : ℝ))+
    g (branchU h Z) (branchX h Z)*(aeval h code.TGdiv.toPoly-
      Z 1*aeval (h*Z 1) code.TXdiv.toPoly)+
    σ*(mainAmplitudeCoefficient h Z*(code.uCentre : ℝ)+
      2*branchU h Z*(1-(branchX h Z)^2)*Z 1*aeval (h*Z 1) code.UXdiv.toPoly)

/-- The source divided part of the full raw slack. -/
def dividedSlack (n : ℕ) (code : LagCode n) (h : ℝ) (Z : Coordinates) (σ : ℝ) : ℝ :=
  mainDivided n code h Z σ+
    Z 3*(actualRaw (branchU h Z) (1+h) n σ (Z 2)-
      actualRaw (branchU h Z) (1+h) n σ (branchX h Z))-
    σ*Z 4*lagDenominator (1+h) n

theorem LagCode.centres (n : ℕ) (code : LagCode n) :
    (code.tCentre : ℝ)=chebT n (-1/2) ∧ (code.uCentre : ℝ)=chebU (n-1) (-1/2) := by
  have ht := code.TX_exact 0
  have hu := code.UX_exact 0
  constructor
  · simpa only [add_zero,zero_mul] using ht.symm
  · simpa only [add_zero,zero_mul] using hu.symm

/-- Exact h division of the main atom, valid also at h=0. -/
theorem mainRaw_division (n : ℕ) (code : LagCode n) (h : ℝ) (Z : Coordinates) (σ : ℝ) :
    actualRaw (branchU h Z) (1+h) n σ (branchX h Z)=
      actualRaw (1/2) 1 n σ (-1/2)+h*mainDivided n code h Z σ := by
  have hg := main_gap_difference h Z
  have ha := main_amplitude_difference h Z
  have hT := code.TX_exact (h*Z 1)
  have hU := code.UX_exact (h*Z 1)
  have hTG := code.TG_exact h
  have ht0 : chebT n (1 : ℝ)=1 := by simp [chebT]
  obtain ⟨htc,huc⟩ := code.centres n
  unfold actualRaw lagB mainDivided
  rw [ht0,hTG,← htc,← huc]
  change chebT n (branchX h Z)=_ at hT
  change chebU (n-1) (branchX h Z)=_ at hU
  rw [hT,hU]
  have hg' : g (branchU h Z) (branchX h Z)=1/2+h*mainGapCoefficient h Z := by linarith
  rw [hg']
  unfold g
  linear_combination σ*(code.uCentre : ℝ)*ha

/-- Exact source identity for every critical and noncritical lag, without a limiting argument. -/
theorem rawBranch_division (n : ℕ) (code : LagCode n) (h : ℝ) (Z : Coordinates) (σ : ℝ) :
    rawBranch h Z n σ=actualRaw (1/2) 1 n σ (-1/2)+h*dividedSlack n code h Z σ := by
  have hm := mainRaw_division n code h Z σ
  unfold rawBranch dividedSlack branchU branchX at *
  linear_combination hm

end polyak.Boundary.P5
