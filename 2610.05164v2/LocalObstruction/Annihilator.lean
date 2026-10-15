import «2610.05164v2».Residual.StatePotential

/-!
Article: 2610.05164v2, Theorem 6.1.
The exact two-constraint multiplier argument in Theorem 6.1.
Use: `«2610.05164v2».LocalObstruction.two_constraint_annihilator` feeds
`«2610.05164v2».LocalObstruction.sine_nonstationary_test` (sine nonstationary test).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section

/--
Constructs witnesses with the exact properties `∃ α ζ : ℝ, ∀ v, L v=α*m₀ v+ζ*m₁ v`.

Use: `«2610.05164v2».LocalObstruction.sine_nonstationary_test` uses this identity to establish
constructs witnesses with the exact properties `∃ v : SmoothTest, (∫ x, v x)=0 ∧ (∫ x, v x/(2*n
x))=0 ∧ (∫ x, v x*((3/2:ℝ)*n x-g x))≠0`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem two_constraint_annihilator {V : Type*} [AddCommGroup V] [Module ℝ V]
    (m₀ m₁ L : V →ₗ[ℝ] ℝ) {w₀ w₁ : V}
    (h₀ : m₀ w₀=1) (h₁ : m₀ w₁=1) (hd : m₁ w₀≠m₁ w₁)
    (hker : ∀ v, m₀ v=0 → m₁ v=0 → L v=0) :
    ∃ α ζ : ℝ, ∀ v, L v=α*m₀ v+ζ*m₁ v := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  let δ := m₁ w₀-m₁ w₁
  have hδ : δ ≠ 0 := sub_ne_zero.mpr hd
  let φ₁ := δ⁻¹ • (w₀-w₁)
  let φ₀ := w₀-(m₁ w₀) • φ₁
  have h01 : m₀ φ₁=0 := by simp [φ₁,h₀,h₁]
  have h11 : m₁ φ₁=1 := by
    simp only [φ₁,map_smul,map_sub,smul_eq_mul]
    exact inv_mul_cancel₀ hδ
  have h00 : m₀ φ₀=1 := by simp [φ₀,h01,h₀]
  have h10 : m₁ φ₀=0 := by simp [φ₀,h11]
  refine ⟨L φ₀,L φ₁,?_⟩
  intro v
  have hz := hker (v-(m₀ v) • φ₀-(m₁ v) • φ₁)
    (by simp [h00,h01]) (by simp [h10,h11])
  simp only [map_sub,map_smul,smul_eq_mul] at hz
  linarith

end
end «2610.05164v2».LocalObstruction
