import jacobi.Finite.VolterraCosh
import jacobi.Support.VolterraNormInequality

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
The actual original support polynomial satisfies the full printed
global hyperbolic-cosine wave bound at every complex spectral energy.
Every original recurrence, matrix, kernel and positivity premise is
proved for the same genuine support spectral family.
Use: naturalWave_cosh and the genuine wave-difference estimates use precisely this original scaled energy.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference jacobi.Finite
open scoped Topology

/-- The original scaled spectral displacement in the support Volterra estimates.
Use: naturalWave_cosh and the genuine wave-difference estimates use precisely this original scaled energy.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
-/
def volterraEnergy (a b : ℝ) (n m : ℕ) (y : ℂ) : ℝ :=
  ‖y-(cos (gamma a*step a b (n+1)):ℝ)‖*((m:ℝ)+1)^2

/-- The binomial Volterra majorant has exactly the printed square-root scaled-energy argument.
Use: naturalWave_cosh identifies its genuine factorial majorant with the literal source cosh(sqrt(B*epsilon)).
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: both sides are nonnegative and their squares agree by the actual nonnegative square-root identity. -/
theorem volterra_cosh_argument {B r : ℝ} (hB:0≤B) (hr:0≤r) (m : ℕ) :
    sqrt ((4*B)*(r*((m:ℝ)+1)^2))=2*sqrt (r*B)*((m:ℝ)+1) := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  rw [mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hr hB)]
  ring

/-- The actual original complex support spectral polynomial satisfies the full printed global hyperbolic-cosine wave bound.
Use: the genuine support edge limit and both original envelope regimes use this actual wave bound, with the true scaled energy and no asymptotic certificate.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: the actual original wave satisfies the independently proved weighted linear-kernel norm inequality. Its genuine finite binomial majorant is bounded by the community cosh series, and the exact nonnegative square-root identity gives the original printed scaled-energy argument. -/
theorem naturalWave_cosh {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+6→∀y:ℂ,
      ‖naturalWave a b ha hb n m y‖≤C*((m:ℝ)+1)^gamma a*cosh (sqrt (B*volterraEnergy a b n m y)) := by
  -- The same actual norm comparison holds on every original prefix needed by the finite positive majorant.
  obtain ⟨C,B,hC,hB,hineq⟩ := naturalWave_norm_inequality ha hb
  refine ⟨C,4*B,hC,by positivity,?_⟩
  filter_upwards [hineq] with n hn
  intro m hm y
  have h := linear_volterra_cosh hC.le (mul_nonneg (norm_nonneg _) hB.le) m
    (fun j hj => hn j (by omega) y)
  have hw : 0<((m:ℝ)+1)^gamma a := rpow_pos_of_pos (by positivity) _
  have h' := (div_le_iff₀ hw).mp h
  rw [volterraEnergy,volterra_cosh_argument hB.le (norm_nonneg _)]
  calc
    _ ≤ (C*cosh (2*sqrt (‖y-(cos (gamma a*step a b (n+1)):ℝ)‖*B)*((m:ℝ)+1)))*((m:ℝ)+1)^gamma a := h'
    _ = _ := by ring

end
end jacobi.Support
