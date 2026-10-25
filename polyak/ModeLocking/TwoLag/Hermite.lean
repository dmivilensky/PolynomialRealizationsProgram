import polyak.ModeLocking.TwoLag.Polynomial

/-! The Hermite compatibility equation is proved for all `K`, with no
truncation of the Chebyshev degree. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General

def G (K : ℕ) (r c₁ c₂ : ℝ) : ℝ :=
  deriv (Psi K r) c₁ + deriv (Psi K r) c₂ -
    2*(Psi K r c₁-Psi K r c₂)/(c₁-c₂)

theorem Xi_hasDerivAt (q : Tuning) (c : ℝ) :
    HasDerivAt q.Xi ((2*q.A*(1+q.beta)-8*q.beta*c)/(2*q.B*(1-q.beta))) c := by
  convert (((hasDerivAt_const c (q.B^2-(1-q.beta)^2-q.A^2)).add
    ((hasDerivAt_id c).const_mul (2*q.A*(1+q.beta)))).sub
      (((hasDerivAt_id c).pow 2).const_mul (4*q.beta))).div_const
        (2*q.B*(1-q.beta)) using 1
  · rfl
  · simp only [id_eq]; ring

theorem Xi_secant (q : Tuning) {c₁ c₂ : ℝ} (hc : c₁ ≠ c₂) :
    deriv q.Xi c₁ + deriv q.Xi c₂ = 2*(q.Xi c₁-q.Xi c₂)/(c₁-c₂) := by
  rw [(Xi_hasDerivAt q c₁).deriv, (Xi_hasDerivAt q c₂).deriv]
  dsimp [Tuning.Xi]
  field_simp
  ring

/-- The compatibility equation follows from the two double contacts. -/
theorem G_eq_zero (q : Tuning) (K : ℕ) (r : ℝ) {c₁ c₂ : ℝ}
    (hc : c₁ ≠ c₂)
    (hv₁ : q.Xi c₁ = Psi K r c₁) (hv₂ : q.Xi c₂ = Psi K r c₂)
    (hd₁ : deriv q.Xi c₁ = deriv (Psi K r) c₁)
    (hd₂ : deriv q.Xi c₂ = deriv (Psi K r) c₂) : G K r c₁ c₂ = 0 := by
  unfold G
  rw [← hd₁, ← hd₂, ← hv₁, ← hv₂, Xi_secant q hc]
  ring

/-- A quadratic is determined by two distinct values and the first slope. -/
theorem quadratic_Hermite_unique {a b d A B D x y : ℝ} (hxy : x ≠ y)
    (hx : a*x^2+b*x+d=A*x^2+B*x+D)
    (hy : a*y^2+b*y+d=A*y^2+B*y+D)
    (hs : 2*a*x+b=2*A*x+B) : a=A ∧ b=B ∧ d=D := by
  have h : (a-A)*(x-y)^2=0 := by
    linear_combination hy-hx+(x-y)*hs
  have ha : a=A := by
    have hn : (x-y)^2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hxy)
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hn)
  subst A
  have hb : b=B := by linarith
  subst B
  exact ⟨rfl, rfl, by linarith⟩

end polyak.ModeLocking.TwoLag
