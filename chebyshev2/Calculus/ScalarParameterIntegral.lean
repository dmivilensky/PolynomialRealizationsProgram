import chebyshev2.Calculus.CompactIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Article: chebyshev2, Proposition 13.
C1 scalar parameter integrals on a fixed compact interval.
Use: `chebyshev2.Calculus.scalar_unit_integral_derivative` feeds
`chebyshev2.Calculus.scalar_unit_integral_c1` (scalar unit integral c1).
Proof chain: `chebyshev2.Primal.mass_directional_derivative` — chebyshev2, Proposition 13;
Actual mass/spectral Frechet derivatives, C1 family and energy bound.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace chebyshev2.Calculus
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Continuity of the displayed function: `Continuous (fun a => ∫ t in (0:ℝ)..1,F a t)`.

Use: `chebyshev2.Calculus.scalar_unit_integral_c1` uses this continuity result to establish
smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ t in (0:ℝ)..1,F a t)`.

Article: chebyshev2, Proposition 13.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem scalar_unit_integral_continuous {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (univ ×ˢ Icc (0:ℝ) 1)) :
    Continuous (fun a => ∫ t in (0:ℝ)..1,F a t) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  rw [continuous_iff_continuousAt]
  intro a
  have hbox : Icc (a-1) (a+1) ×ˢ Icc (0:ℝ) 1⊆univ ×ˢ Icc (0:ℝ) 1 :=
    fun _ hp => ⟨mem_univ _,hp.2⟩
  have hc := (continuousOn_compact_integral (hF.mono hbox)).continuousAt
    (Icc_mem_nhds (by linarith : a-1<a) (by linarith : a<a+1))
  have he : (fun a => ∫ t in (0:ℝ)..1,F a t)=fun a => ∫ t in Icc (0:ℝ) 1,F a t := by
    funext a
    rw [intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc]
  rwa [← he] at hc

/--
The actual derivative at the stated point: `HasDerivAt (fun a => ∫ t in (0:ℝ)..1,F a t) (∫ t in
(0:ℝ)..1,G a t) a`.

Use: `chebyshev2.Calculus.scalar_unit_integral_c1` uses this derivative formula to
establish smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ t in (0:ℝ)..1,F a t)`.

Article: chebyshev2, Proposition 13 via `chebyshev2.Primal.mass_directional_derivative`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `chebyshev2.Calculus.hasDerivWithinAt_compact_integral`
with the arguments shown in the proof.
-/
theorem scalar_unit_integral_derivative {F G : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (univ ×ˢ Icc (0:ℝ) 1))
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (univ ×ˢ Icc (0:ℝ) 1))
    (hd : ∀ a : ℝ,∀ t∈Icc (0:ℝ) 1,HasDerivAt (fun a => F a t) (G a t) a) (a : ℝ) :
    HasDerivAt (fun a => ∫ t in (0:ℝ)..1,F a t) (∫ t in (0:ℝ)..1,G a t) a := by
  -- Use the identities/estimates `chebyshev2.Calculus.hasDerivWithinAt_compact_integral`
  -- with the arguments shown in the proof.
  have hbox : Icc (a-1) (a+1) ×ˢ Icc (0:ℝ) 1⊆univ ×ˢ Icc (0:ℝ) 1 :=
    fun _ hp => ⟨mem_univ _,hp.2⟩
  have h := hasDerivWithinAt_compact_integral (by linarith : a-1<a+1)
    (hF.mono hbox) (hG.mono hbox) (fun b _ t ht => hd b t ht)
    a (by constructor <;> linarith)
  have h' := h.hasDerivAt (Icc_mem_nhds (by linarith : a-1<a) (by linarith : a<a+1))
  have he (f : ℝ → ℝ) : (∫ t in (0:ℝ)..1,f t)=∫ t in Icc (0:ℝ) 1,f t := by
    rw [intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc]
  simpa only [he] using h'

/--
Smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ t in (0:ℝ)..1,F a t)`.

Use: `chebyshev2.Primal.moment_directional_c1` uses this identity to establish smoothness
to the stated order: `ContDiff ℝ 1 (fun a => ∫ x,(speedData (lineProfile ψ θ a)
(lineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2))`.

Article: chebyshev2, Proposition 13.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem scalar_unit_integral_c1 {F G : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (univ ×ˢ Icc (0:ℝ) 1))
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (univ ×ˢ Icc (0:ℝ) 1))
    (hd : ∀ a : ℝ,∀ t∈Icc (0:ℝ) 1,HasDerivAt (fun a => F a t) (G a t) a) :
    ContDiff ℝ 1 (fun a => ∫ t in (0:ℝ)..1,F a t) := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  rw [show (1:ℕ∞ω)=(0:ℕ)+1 by rfl,contDiff_succ_iff_deriv]
  refine ⟨fun a => (scalar_unit_integral_derivative hF hG hd a).differentiableAt,by simp,?_⟩
  have he : deriv (fun a => ∫ t in (0:ℝ)..1,F a t)=fun a => ∫ t in (0:ℝ)..1,G a t :=
    funext (fun a => (scalar_unit_integral_derivative hF hG hd a).deriv)
  rw [he]
  exact contDiff_zero.mpr (scalar_unit_integral_continuous hG)

end
end chebyshev2.Calculus
