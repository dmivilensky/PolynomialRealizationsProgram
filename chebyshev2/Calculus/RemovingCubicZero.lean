import chebyshev2.Calculus.CubicTaylor

/-!
Article: chebyshev2, Lemma 22.
Lemma 22 for a genuine C^(N+4) function.
Use: `chebyshev2.Calculus.removing_cubic_zero` feeds
`chebyshev2.Numerics.cubicQuotientCheck_sound` (cubic Quotient Check sound).
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace chebyshev2.Calculus
noncomputable section
open Set MeasureTheory Real
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
Constructs witnesses with the exact properties `∃ g : ℝ → ℝ, ContDiffOn ℝ (N+1) g (Icc 0 β) ∧
(∀ t∈Icc 0 β,f t=t^3*g t) ∧ (∀ j≤N+1,∀ t∈Icc 0 β, iteratedDerivWithin j g (Icc 0 β)
t/(j.factorial:ℝ)= ∫ v in Icc (0:ℝ) 1,cubicWeight j v* (iteratedDerivWithin (j+3) f (Icc 0 β)
(t*v)/((j+3).factorial:ℝ))) ∧ (∀ j≤N,∀ t∈Icc 0 β,∀ L U : ℝ, (∀ z∈Icc 0 β,iteratedDerivWithin
(N+4) f (Icc 0 β) z/((N+4).factorial:ℝ)∈Icc L U) → ∃ r∈Icc L U,iteratedDerivWithin j g (Icc 0
β) t/(j.factorial:ℝ)= (∑ l∈Finset.range (N-j+1),((j+l).choose j:ℝ)* (iteratedDerivWithin
(j+l+3) f (Icc 0 β) 0/((j+l+3).factorial:ℝ))*t^l)+ ((N+1).choose j:ℝ)*t^(N+1-j)*r)`.

Use: `chebyshev2.Numerics.cubicQuotientCheck_sound` uses this identity to establish the
precise assertion is `JetEncloses G g (Icc 0 β) t N`.

Article: chebyshev2, Lemma 22.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `chebyshev2.Calculus.finite_cubicIntegral_smooth`,
`chebyshev2.Calculus.finite_cubicIntegral_factor`,
`chebyshev2.Calculus.finite_cubicIntegral_normalized_jet` with the arguments shown in the
proof.
-/
theorem removing_cubic_zero {β : ℝ} (hβ : 0<β) (N : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (N+4) f (Icc 0 β))
    (h₀ : f 0=0) (h₁ : derivWithin f (Icc 0 β) 0=0)
    (h₂ : iteratedDerivWithin 2 f (Icc 0 β) 0=0) :
    ∃ g : ℝ → ℝ,
      ContDiffOn ℝ (N+1) g (Icc 0 β) ∧
      (∀ t∈Icc 0 β,f t=t^3*g t) ∧
      (∀ j≤N+1,∀ t∈Icc 0 β,
        iteratedDerivWithin j g (Icc 0 β) t/(j.factorial:ℝ)=
          ∫ v in Icc (0:ℝ) 1,cubicWeight j v*
            (iteratedDerivWithin (j+3) f (Icc 0 β) (t*v)/((j+3).factorial:ℝ))) ∧
      (∀ j≤N,∀ t∈Icc 0 β,∀ L U : ℝ,
        (∀ z∈Icc 0 β,iteratedDerivWithin (N+4) f (Icc 0 β) z/((N+4).factorial:ℝ)∈Icc L U) →
        ∃ r∈Icc L U,iteratedDerivWithin j g (Icc 0 β) t/(j.factorial:ℝ)=
          (∑ l∈Finset.range (N-j+1),((j+l).choose j:ℝ)*
            (iteratedDerivWithin (j+l+3) f (Icc 0 β) 0/((j+l+3).factorial:ℝ))*t^l)+
            ((N+1).choose j:ℝ)*t^(N+1-j)*r) := by
  -- Use the identities/estimates `chebyshev2.Calculus.finite_cubicIntegral_smooth`,
  -- `chebyshev2.Calculus.finite_cubicIntegral_factor`,
  -- `chebyshev2.Calculus.finite_cubicIntegral_normalized_jet` with the arguments shown in
  -- the proof.
  let D := fun j => iteratedDerivWithin j f (Icc 0 β)
  have hc : ∀ j≤N+4,ContinuousOn (D j) (Icc 0 β) := fun j hj =>
    hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_Icc hβ)
  have hd : ∀ j<N+4,∀ t∈Icc 0 β,HasDerivWithinAt (D j) (D (j+1) t) (Icc 0 β) t := by
    intro j hj t ht
    dsimp only [D]
    rw [iteratedDerivWithin_succ]
    exact (hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_Icc hβ) t ht).hasDerivWithinAt
  refine ⟨cubicIntegral D 0,finite_cubicIntegral_smooth hβ (N+1) D
    (by simpa using hc) (by simpa using hd),?_,?_,?_⟩
  · intro t ht
    exact (finite_cubicIntegral_factor D (fun j hj => hc j (by omega))
      (fun j hj => hd j (by omega)) (by simpa [D] using h₀) (by simpa [D] using h₁) h₂ ht).symm
  · intro j hj t ht
    exact finite_cubicIntegral_normalized_jet hβ (N+1) D (by simpa using hc) (by simpa using hd) hj ht
  · intro j hj t ht L U hb
    exact cubic_taylor_enclosure hβ N D hc hd hj ht hb

end
end chebyshev2.Calculus
