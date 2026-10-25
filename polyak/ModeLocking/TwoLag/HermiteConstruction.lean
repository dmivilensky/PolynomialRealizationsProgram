import polyak.ModeLocking.TwoLag.HermiteSource
import polyak.Levels.Chart.Homeomorphism

/-! The compatibility equation is sufficient as well as necessary. The
Hermite quadratic is explicit and its tuning admissibility is precisely the
three strict coefficient conditions of the article. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels

def hermiteQuadratic (K : ℕ) (r c₁ c₂ : ℝ) : Chart.Coefficients :=
  let A := (Psi K r c₂-Psi K r c₁-deriv (Psi K r) c₁*(c₂-c₁))/(c₂-c₁)^2
  ⟨Psi K r c₁-deriv (Psi K r) c₁*c₁+A*c₁^2,
    deriv (Psi K r) c₁-2*A*c₁,A⟩

theorem hermiteQuadratic_eval (K : ℕ) (r c₁ c₂ c : ℝ) :
    (hermiteQuadratic K r c₁ c₂).eval c=Psi K r c₁+deriv (Psi K r) c₁*(c-c₁)+
      (hermiteQuadratic K r c₁ c₂).c2*(c-c₁)^2 := by
  dsimp [hermiteQuadratic,Chart.Coefficients.eval]
  ring

theorem coefficients_hasDerivAt (C : Chart.Coefficients) (c : ℝ) :
    HasDerivAt C.eval (C.c1+2*C.c2*c) c := by
  convert ((hasDerivAt_const c C.c0).add ((hasDerivAt_id c).const_mul C.c1)).add
    (((hasDerivAt_id c).pow 2).const_mul C.c2) using 1
  · rfl
  · simp only [id_eq]; ring

theorem coefficients_secant (C : Chart.Coefficients) {c₁ c₂ : ℝ} (hc : c₁≠c₂) :
    deriv C.eval c₁+deriv C.eval c₂=2*(C.eval c₁-C.eval c₂)/(c₁-c₂) := by
  rw [(coefficients_hasDerivAt C c₁).deriv,(coefficients_hasDerivAt C c₂).deriv]
  dsimp [Chart.Coefficients.eval]
  field_simp
  ring

theorem hermiteQuadratic_first (K : ℕ) (r c₁ c₂ : ℝ) :
    (hermiteQuadratic K r c₁ c₂).eval c₁=Psi K r c₁ ∧
      deriv (hermiteQuadratic K r c₁ c₂).eval c₁=deriv (Psi K r) c₁ := by
  constructor
  · rw [hermiteQuadratic_eval]
    ring
  · rw [(coefficients_hasDerivAt _ _).deriv]
    dsimp [hermiteQuadratic]
    ring

theorem hermiteQuadratic_second_value (K : ℕ) (r : ℝ) {c₁ c₂ : ℝ} (hc : c₁≠c₂) :
    (hermiteQuadratic K r c₁ c₂).eval c₂=Psi K r c₂ := by
  rw [hermiteQuadratic_eval]
  dsimp [hermiteQuadratic]
  have hn : c₂-c₁≠0 := sub_ne_zero.mpr hc.symm
  field_simp
  ring

/-- The missing converse: a root of G forces the second slope of the
explicit quadratic, in addition to both values and the first slope. -/
theorem hermiteQuadratic_second_slope (K : ℕ) (r : ℝ) {c₁ c₂ : ℝ}
    (hc : c₁≠c₂) (hG : G K r c₁ c₂=0) :
    deriv (hermiteQuadratic K r c₁ c₂).eval c₂=deriv (Psi K r) c₂ := by
  have hs := coefficients_secant (hermiteQuadratic K r c₁ c₂) hc
  rw [(hermiteQuadratic_first K r c₁ c₂).1,
    (hermiteQuadratic_first K r c₁ c₂).2,hermiteQuadratic_second_value K r hc] at hs
  dsimp [G] at hG
  linarith

/-- Four Hermite equations have a quadratic solution exactly when the
displayed scalar compatibility equation vanishes, uniformly in K. -/
theorem G_iff_exists_Hermite (K : ℕ) (r : ℝ) {c₁ c₂ : ℝ} (hc : c₁≠c₂) :
    G K r c₁ c₂=0 ↔ ∃C : Chart.Coefficients,
      C.eval c₁=Psi K r c₁ ∧ C.eval c₂=Psi K r c₂ ∧
        deriv C.eval c₁=deriv (Psi K r) c₁ ∧ deriv C.eval c₂=deriv (Psi K r) c₂ := by
  constructor
  · intro hG
    exact ⟨hermiteQuadratic K r c₁ c₂,(hermiteQuadratic_first K r c₁ c₂).1,
      hermiteQuadratic_second_value K r hc,(hermiteQuadratic_first K r c₁ c₂).2,
      hermiteQuadratic_second_slope K r hc hG⟩
  · rintro ⟨C,h₁,h₂,hd₁,hd₂⟩
    have hs := coefficients_secant C hc
    rw [h₁,h₂,hd₁,hd₂] at hs
    exact sub_eq_zero.mpr hs

/-- No extra tuning assumption is hidden in the construction: precisely
negative quadratic coefficient and negative endpoint values are required. -/
theorem hermite_tuning_exists_iff (K : ℕ) (r c₁ c₂ : ℝ) :
    (∃q : Tuning,0<q.beta ∧ Chart.coefficients q=hermiteQuadratic K r c₁ c₂) ↔
      (hermiteQuadratic K r c₁ c₂).c2<0 ∧
        (hermiteQuadratic K r c₁ c₂).eval 1<0 ∧
          (hermiteQuadratic K r c₁ c₂).eval (-1)<0 := by
  constructor
  · rintro ⟨q,hβ,hq⟩
    rw [←hq]
    exact Chart.coefficients_mem q hβ
  · intro hC
    exact Chart.coefficients_surjective _ hC

end polyak.ModeLocking.TwoLag
