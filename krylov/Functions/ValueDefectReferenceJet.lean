import krylov.Functions.ValueCorrectionJets

/-!
Article: main_krylov, prop:Fcycle(i), true observed segment/reference jets.
Use: combine the actual Hessian derivative kernel with a quadratic reference
shadow of the actual segment. The result is uniform over all bounded reference
steps, so it applies simultaneously to every retained pair of a compact cycle.
Source: the genuine Frechet remainder and continuous trilinear substitution.
-/

namespace krylov.Functions
noncomputable section
open Real Set Metric Filter Topology
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual enclosed segments with quadratic step shadows have a genuine uniform cubic value-defect jet.
Article: main_krylov, prop:Fcycle(i), delta_tr/epsilon^3 at retained physical pairs.
The derivative at zero and the original derivative fields imply the jet;
no observed defect or normalized model expansion occurs in the premises. -/
theorem segmentValueDefect_reference_jet (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (D : E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hD : HasFDerivAt H D 0)
    (hc : ContinuousOn H (ball 0 r))
    (hF : ∀ z ∈ ball (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ ball (0 : E) r, HasFDerivAt G (H z) z)
    (M C : ℝ) (hM : 0 < M) (hC : 0 ≤ C) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ a s σ : E,
      (∀ t ∈ Icc (0 : ℝ) 1, ‖a + t • s‖ ≤ M * ε) →
      ‖s‖ ≤ M * ε → ‖σ‖ ≤ M → ‖s - ε • σ‖ ≤ C * ε ^ 2 →
      |segmentValueDefect f (fun x => innerSL ℝ (G x)) a s +
        ε ^ 3 * inner ℝ (D σ σ) σ / 12| ≤ η * ε ^ 3 := by
  intro η hη
  let ζ := η / (2 * (M + 1) ^ 3)
  have hζ : 0 < ζ := by dsimp only [ζ]; positivity
  obtain ⟨δ, hδ, _, hkernel⟩ := segmentValueDefect_cubic_expansion f G H D hr hD hc hF hG ζ hζ
  let B := ‖D‖ * M ^ 2 * C / 4
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let ε₀ := min (δ / (M + 1)) (η / (2 * (B + 1)))
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε he a s σ hseg hs hσ herr
  have hR : M * ε < δ := by
    have hh := (lt_div_iff₀ (by positivity : 0 < M + 1)).mp (he.trans_le (min_le_left _ _))
    nlinarith only [hh, hε]
  have hk := hkernel (M * ε) (by positivity) hR a s hseg
  have hshadow := inner_third_diagonal_shadow D s σ ε M C hε.le hM.le hC hs hσ herr
  have hs2 : ‖s‖ ^ 2 ≤ (M * ε) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hs
  have hk' : |segmentValueDefect f (fun x => innerSL ℝ (G x)) a s +
      inner ℝ (D s s) s / 12| ≤ ζ * M ^ 3 * ε ^ 3 :=
    hk.trans ((mul_le_mul_of_nonneg_left hs2 (by positivity)).trans_eq (by ring))
  have heq : segmentValueDefect f (fun x => innerSL ℝ (G x)) a s +
      ε ^ 3 * inner ℝ (D σ σ) σ / 12 =
      (segmentValueDefect f (fun x => innerSL ℝ (G x)) a s + inner ℝ (D s s) s / 12) -
        (inner ℝ (D s s) s - ε ^ 3 * inner ℝ (D σ σ) σ) / 12 := by ring
  rw [heq]
  have hs' : |(inner ℝ (D s s) s - ε ^ 3 * inner ℝ (D σ σ) σ) / 12| ≤ B * ε ^ 4 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12)]
    exact (div_le_div_of_nonneg_right hshadow (by norm_num)).trans_eq (by dsimp only [B]; ring)
  have hζM : ζ * M ^ 3 ≤ η / 2 := by
    have hpow : M ^ 3 ≤ (M + 1) ^ 3 := pow_le_pow_left₀ hM.le (by linarith) 3
    have hh : ζ * (M + 1) ^ 3 = η / 2 := by dsimp only [ζ]; field_simp
    exact (mul_le_mul_of_nonneg_left hpow hζ.le).trans_eq hh
  have hBε : B * ε ≤ η / 2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (B + 1))).mp
      (he.trans_le (min_le_right _ _))
    nlinarith only [hh, hε]
  exact (abs_sub _ _).trans ((add_le_add hk' hs').trans (by
    nlinarith only [mul_le_mul_of_nonneg_right hζM (pow_nonneg hε.le 3),
      mul_le_mul_of_nonneg_right hBε (pow_nonneg hε.le 3)]))

/-- Lipschitz original third derivatives give the same physical reference jet with a uniform fourth-order bound.
Article: main_krylov, prop:Fcycle(i), the Lipschitz-third refinement. -/
theorem segmentValueDefect_reference_quartic (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (D : E → E →L[ℝ] E →L[ℝ] E)
    (S : Set E) (hS : Convex ℝ S) (hz : (0 : E) ∈ S)
    (hF : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ S, HasFDerivAt G (H z) z)
    (hD : ∀ z ∈ S, HasFDerivAt H (D z) z)
    {L : NNReal} (hLip : LipschitzOnWith L D S)
    (a s σ : E) (ε M C : ℝ) (hε : 0 ≤ ε) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, a + t • s ∈ S ∧ ‖a + t • s‖ ≤ M * ε)
    (hs : ‖s‖ ≤ M * ε) (hσ : ‖σ‖ ≤ M) (herr : ‖s - ε • σ‖ ≤ C * ε ^ 2) :
    |segmentValueDefect f (fun x => innerSL ℝ (G x)) a s +
      ε ^ 3 * inner ℝ (D 0 σ σ) σ / 12| ≤
        ((L : ℝ) * M ^ 4 / 2 + ‖D 0‖ * M ^ 2 * C / 4) * ε ^ 4 := by
  have hk := segmentValueDefect_quartic_bound f G H D S hS hz hF hG hD hLip
    a s (M * ε) (mul_nonneg hM hε) hseg
  have hshadow := inner_third_diagonal_shadow (D 0) s σ ε M C hε hM hC hs hσ herr
  have hs2 : ‖s‖ ^ 2 ≤ (M * ε) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM hε)).mpr hs
  have heq : segmentValueDefect f (fun x => innerSL ℝ (G x)) a s +
      ε ^ 3 * inner ℝ (D 0 σ σ) σ / 12 =
      (segmentValueDefect f (fun x => innerSL ℝ (G x)) a s + inner ℝ (D 0 s s) s / 12) -
        (inner ℝ (D 0 s s) s - ε ^ 3 * inner ℝ (D 0 σ σ) σ) / 12 := by ring
  rw [heq]
  apply (abs_sub _ _).trans
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12)]
  apply (add_le_add hk (div_le_div_of_nonneg_right hshadow (by norm_num))).trans
  have hh := mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ (L : ℝ) * (M * ε) ^ 2 / 2)
  nlinarith only [hh]

end
end krylov.Functions
