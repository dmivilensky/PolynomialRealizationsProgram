import polyak.Realization.ExplicitSpiral.Pairs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Article: the near-critical initialized-spiral phase estimate.
Use: control every residue class modulo three by one quadratic lower bound.
Proof: the mean value theorem for arccos on [-1/2,0] and an elementary
lower bound for log, avoiding a numerical approximation of the phase.
-/

namespace polyak.Realization.ExplicitSpiral
noncomputable section

/-- Article: the source logarithmic lower bound for every ρ≥1. -/
theorem log_lower {r : ℝ} (hr : 1≤r) : 2*(r-1)/(r+1)≤Real.log r := by
  let f : ℝ → ℝ := fun x => Real.log x-2*(x-1)/(x+1)
  have hd (x : ℝ) (hx : 1≤x) : HasDerivAt f ((x-1)^2/(x*(x+1)^2)) x := by
    have hx0 : x≠0 := by linarith
    have hx1 : x+1≠0 := by linarith
    convert (Real.hasDerivAt_log hx0).sub
      ((((hasDerivAt_id x).sub_const 1).const_mul 2).div
        ((hasDerivAt_id x).add_const 1) hx1) using 1
    · rfl
    · dsimp
      field_simp [hx0,hx1]
      ring
  have hm : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x (interior_subset hx)).deriv]
      have hxpos : 0<x := by have hxx : 1≤x := interior_subset hx; linarith
      positivity
  have hh := hm (by simp) hr hr
  simp only [f,Real.log_one,sub_self] at hh
  linarith

/-- Article: arccos has the required explicit Lipschitz bound on the source cosine range. -/
theorem arccos_lipschitz {c : ℝ} (hc : c∈Set.Icc (-1/2 : ℝ) 0) :
    |Real.arccos c-Real.arccos (-1/2)|≤(2/Real.sqrt 3)*(c+1/2) := by
  have hd (x : ℝ) (hx : x∈Set.Icc (-1/2 : ℝ) 0) :
      HasDerivAt Real.arccos (-(1/Real.sqrt (1-x^2))) x :=
    Real.hasDerivAt_arccos (by linarith [hx.1]) (by linarith [hx.2])
  have hb (x : ℝ) (hx : x∈Set.Icc (-1/2 : ℝ) 0) :
      ‖deriv Real.arccos x‖≤2/Real.sqrt 3 := by
    rw [(hd x hx).deriv,Real.norm_eq_abs,abs_neg,abs_of_nonneg (by positivity)]
    have hs3 : 0<Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have hx2 : x^2≤1/4 := by nlinarith [hx.1,hx.2]
    have hxs : 0<Real.sqrt (1-x^2) := Real.sqrt_pos.mpr (by nlinarith)
    have hsq := Real.sq_sqrt (show (0 : ℝ)≤1-x^2 by nlinarith)
    have hsq3 := Real.sq_sqrt (show (0 : ℝ)≤3 by norm_num)
    apply (div_le_div_iff₀ hxs hs3).mpr
    nlinarith
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (fun x hx => (hd x hx).differentiableAt)
    hb (convex_Icc (-1/2 : ℝ) 0) (show (-1/2 : ℝ)∈Set.Icc (-1/2 : ℝ) 0 by norm_num) hc
  have he : c-(-1/2 : ℝ)=c+1/2 := by ring
  simpa only [Real.norm_eq_abs,he,abs_of_nonneg (show 0≤c+1/2 by linarith [hc.1])] using hh

/-- Article: ε(ρ) used by the three-residue quadratic certificates. -/
def phaseBudget (r : ℝ) : ℝ := (3/40 : ℝ)*(r^2-1)*(r+1)^2/(r*(r^2+1))

/-- Article: the exact rational spiral cosine in growth-factor coordinates. -/
def radialCosine (r : ℝ) : ℝ := -r/(r^2+1)

/-- Article: the critical angle is exactly 2π/3, not a rounded phase. -/
theorem arccos_neg_half : Real.arccos (-1/2 : ℝ)=2*Real.pi/3 := by
  have hc : Real.cos (2*Real.pi/3)=(-1/2 : ℝ) := by
    rw [show 2*Real.pi/3=Real.pi-Real.pi/3 by ring,Real.cos_pi_sub,Real.cos_pi_div_three]
    ring
  rw [← hc,Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

/-- Article: the exact spiral cosine always lies between -1/2 and zero. -/
theorem radialCosine_mem {r : ℝ} (hr : 0<r) : radialCosine r∈Set.Icc (-1/2 : ℝ) 0 := by
  have hd : 0<r^2+1 := by positivity
  constructor
  · unfold radialCosine
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg (r-1)]
  · exact (div_neg_of_neg_of_pos (neg_neg_of_pos hr) hd).le

/-- Article: one exact phase budget controls every near-critical residue class. -/
theorem phase_error_le {r : ℝ} (hr : 1≤r) :
    |Real.arccos (radialCosine r)-2*Real.pi/3|≤phaseBudget r*Real.log r := by
  have hr0 : 0<r := by linarith
  have hd : 0<r^2+1 := by positivity
  have hs3 : 0<Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs3sq := Real.sq_sqrt (show (0 : ℝ)≤3 by norm_num)
  have hi : 1/Real.sqrt (3 : ℝ)≤(3/5 : ℝ) := by
    apply (div_le_iff₀ hs3).mpr
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hc : (3/5 : ℝ)≤(3/20 : ℝ)*(r+1)^2/r := by
    apply (le_div_iff₀ hr0).mpr
    nlinarith [sq_nonneg (r-1)]
  have hb : 0≤phaseBudget r := by
    unfold phaseBudget
    have hrr : 0≤r^2-1 := by nlinarith
    positivity
  have he : (2/Real.sqrt 3)*(radialCosine r+1/2)=
      ((r-1)^2/(r^2+1))*(1/Real.sqrt 3) := by
    unfold radialCosine
    field_simp
    ring
  have he' : ((r-1)^2/(r^2+1))*((3/20 : ℝ)*(r+1)^2/r)=
      phaseBudget r*(2*(r-1)/(r+1)) := by
    unfold phaseBudget
    field_simp
    ring
  calc
    |Real.arccos (radialCosine r)-2*Real.pi/3|
      ≤ (2/Real.sqrt 3)*(radialCosine r+1/2) := by
        rw [← arccos_neg_half]
        exact arccos_lipschitz (radialCosine_mem hr0)
    _ = ((r-1)^2/(r^2+1))*(1/Real.sqrt 3) := he
    _ ≤ ((r-1)^2/(r^2+1))*((3/20 : ℝ)*(r+1)^2/r) :=
      mul_le_mul_of_nonneg_left (hi.trans hc) (by positivity)
    _ = phaseBudget r*(2*(r-1)/(r+1)) := he'
    _ ≤ phaseBudget r*Real.log r := mul_le_mul_of_nonneg_left (log_lower hr) hb

end
end polyak.Realization.ExplicitSpiral
