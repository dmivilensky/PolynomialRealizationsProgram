import krylov.Secant.MSS
import krylov.Secant.Metric
import krylov.LinearAlgebra.PositiveCauchy
import krylov.LinearAlgebra.NormalizedRankOne
import krylov.LinearAlgebra.InformationRadius

/-!
Article: main_krylov, Theorem thm:window, indistinguishable rank-one sequences.
Use: construct the actual physical operators and prove their complete secant
observations are unchanged; the oldest-coordinate dual direction is explicit.
Source: the rank-one construction in Appendix A, apA:content.
-/

namespace krylov.Secant
noncomputable section
open Matrix Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
variable {n p : ℕ}

/-- An arbitrary full-column-rank window has an admissible actual oldest dual direction.
Use: construct the rank-one scenarios for every window, rather than assuming a witness.
Article: main_krylov, thm:window, h=AS(SᵀAS)⁻¹e₀ and γ>0.
Proof: solve the positive-definite Gram system for the oldest coordinate and
normalize its physical rank-one form by the proved positive-metric Cauchy inequality. -/
theorem exists_oldest_hidden_direction (S : Matrix (Fin n) (Fin (p + 1)) ℝ)
    (hS : Function.Injective S.mulVec) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ (h : Fin n → ℝ) (γ : ℝ),
      0 < γ ∧ Sᵀ *ᵥ h = Pi.single 0 1 ∧
      γ = ((Pi.single 0 1) ⬝ᵥ ((Sᵀ * A * S)⁻¹ *ᵥ (Pi.single 0 1)))⁻¹ ∧
      (γ • vecMulVec h h).PosSemidef ∧ γ • vecMulVec h h ≤ A := by
  -- Solve the genuine finite Gram system for the oldest coordinate before normalizing its dual.
  let G := Sᵀ * A * S
  have hG : G.PosDef := by
    simpa only [G, conjTranspose_eq_transpose_of_trivial] using
      hA.conjTranspose_mul_mul_same (B := S) hS
  have hGi : IsUnit G.det := isUnit_iff_ne_zero.mpr hG.det_pos.ne'
  let u := S *ᵥ (G⁻¹ *ᵥ (Pi.single 0 1))
  have hu : Sᵀ *ᵥ (A *ᵥ u) = Pi.single 0 1 := by
    change Sᵀ *ᵥ (A *ᵥ (S *ᵥ (G⁻¹ *ᵥ Pi.single 0 1))) = Pi.single 0 1
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ hGi, one_mulVec]
  have hun : u ≠ 0 := by
    intro hz
    have he := congrFun hu 0
    simp only [hz, mulVec_zero, Pi.zero_apply, Pi.single_eq_same, zero_ne_one] at he
  have hd : 0 < u ⬝ᵥ (A *ᵥ u) := by
    simpa only [star_trivial] using hA.dotProduct_mulVec_pos hun
  have he : u ⬝ᵥ (A *ᵥ u) = (Pi.single 0 1) ⬝ᵥ (G⁻¹ *ᵥ (Pi.single 0 1)) := by
    change (S *ᵥ (G⁻¹ *ᵥ (Pi.single 0 1))) ⬝ᵥ (A *ᵥ u) = _
    rw [krylov.LinearAlgebra.transpose_pairing, hu, dotProduct_comm]
  have hbound := krylov.LinearAlgebra.normalized_rankOne_le A hA u hun
  exact ⟨A *ᵥ u, (u ⬝ᵥ (A *ᵥ u))⁻¹, inv_pos.mpr hd, hu, congrArg Inv.inv he, hbound⟩

/-- An actual physical operator sequence carrying a hidden oldest-coordinate perturbation.
Use: choose signs +1 and −1 to obtain the two indistinguishable scenarios.
Article: main_krylov, proof of thm:window, A_i^±. -/
def hiddenSequence (A H : Matrix (Fin n) (Fin n) ℝ) (ω : ℕ → ℝ) (ε : ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ := A + (ε * ∑ l ∈ range k, ω l) • H

/-- The constructed hidden sequence starts at the prescribed common base.
Use: both scenarios satisfy the same base-operator restriction.
Article: main_krylov, thm:window, A₀=A.
Proof: no increment is present at time zero. -/
theorem hiddenSequence_zero (A H : Matrix (Fin n) (Fin n) ℝ) (ω : ℕ → ℝ) (ε : ℝ) :
    hiddenSequence A H ω ε 0 = A := by simp [hiddenSequence]

/-- Each actual increment uses exactly its assigned budget and the common hidden direction.
Use: verify admissibility for every individual increment, including zero budgets.
Article: main_krylov, thm:window, the displayed rank-one scenarios.
Proof: consecutive cumulative budget sums differ by their newest summand. -/
theorem hiddenSequence_increment (A H : Matrix (Fin n) (Fin n) ℝ) (ω : ℕ → ℝ)
    (ε : ℝ) (k : ℕ) :
    hiddenSequence A H ω ε (k + 1) - hiddenSequence A H ω ε k = (ε * ω k) • H := by
  simp only [hiddenSequence, sum_range_succ, mul_add, add_smul]
  abel

/-- Compressing a rank-one form uses the actual dual coordinates of its generating vector.
Use: the oldest-coordinate construction gives exactly one hidden model entry.
Article: main_krylov, proof of thm:window, SᵀhhᵀS = e₀e₀ᵀ.
Proof: the standard two rank-one multiplication identities apply to the rectangular window. -/
theorem rankOne_compression (S : Matrix (Fin n) (Fin p) ℝ) (h : Fin n → ℝ) :
    Sᵀ * vecMulVec h h * S = vecMulVec (Sᵀ *ᵥ h) (Sᵀ *ᵥ h) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.vecMul_transpose,
    transpose_transpose]

/-- The two rank-one scenarios preserve every complete physical secant observation.
Use: indistinguishability is established at Y itself, hence also at M=SᵀY.
Article: main_krylov, thm:window, identical quadratic data.
Proof: the hidden direction annihilates every later column; on the oldest column
the perturbation has not yet been applied. No conjugacy of the window is required. -/
theorem hiddenSequence_pairImages (S : Matrix (Fin n) (Fin (p + 1)) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (γ : ℝ)
    (hh : Sᵀ *ᵥ h = Pi.single 0 1) (ω : ℕ → ℝ) (ε : ℝ) :
    pairImages S (hiddenSequence A (γ • vecMulVec h h) ω ε) = A * S := by
  -- Later columns annihilate the dual direction; the oldest column has zero prefix budget.
  have hS : (γ • vecMulVec h h) * S = γ • vecMulVec h (Pi.single 0 1) := by
    rw [Matrix.smul_mul, Matrix.vecMulVec_mul]
    have hv : h ᵥ* S = Sᵀ *ᵥ h := by rw [← Matrix.vecMul_transpose, transpose_transpose]
    rw [hv, hh]
  ext a j
  simp only [pairImages, hiddenSequence, Matrix.add_mul, Matrix.smul_mul, hS,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, Pi.single_apply]
  by_cases hj : j = 0
  · subst j
    simp
  · simp [hj]

/-- The hidden model error is an explicit signed rank-one form in the oldest coordinate.
Use: after canonical normalization its two signs force the full information radius.
Article: main_krylov, thm:window, Z^± = ±γW e₀e₀ᵀ.
Proof: use the unchanged full data, exact quadratic model and compressed rank-one action. -/
theorem hiddenSequence_model_error (S : Matrix (Fin n) (Fin (p + 1)) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (h : Fin n → ℝ) (γ : ℝ)
    (hh : Sᵀ *ᵥ h = Pi.single 0 1) (ω : ℕ → ℝ) (ε : ℝ) :
    Sᵀ * hiddenSequence A (γ • vecMulVec h h) ω ε (p + 1) * S -
      latest (Sᵀ * pairImages S (hiddenSequence A (γ • vecMulVec h h) ω ε)) =
        (ε * (∑ l ∈ range (p + 1), ω l) * γ) • vecMulVec (Pi.single 0 1) (Pi.single 0 1) := by
  rw [hiddenSequence_pairImages S A h γ hh ω ε]
  have hG : (Sᵀ * A * S).IsSymm := by
    simp only [Matrix.IsSymm, transpose_mul, transpose_transpose, hA.eq, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, latest_eq_of_isSymm hG]
  simp only [hiddenSequence, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, rankOne_compression, hh, smul_smul]
  abel

/-- Removing a subcritical positive rank-one perturbation preserves strict positivity.
Use: every negative-sign hidden scenario remains a genuine positive-definite operator.
Article: main_krylov, thm:window, A_i^− ⪰ (1−W)A ≻ 0.
Proof: split the matrix into the positive base fraction and a nonnegative budget remainder. -/
theorem posDef_sub_scaled (A H : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hHA : H ≤ A) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) : (A - t • H).PosDef := by
  have hpos := (hA.smul (sub_pos.mpr ht1)).add_posSemidef ((Matrix.le_iff.mp hHA).smul ht)
  have he : (1 - t) • A + t • (A - H) = A - t • H := by
    simp only [sub_smul, one_smul, smul_sub]
    abel
  rwa [he] at hpos

/-- Every prefix budget is nonnegative and bounded by the full window budget.
Use: positivity is verified at all actual operator times, including the output time.
Article: main_krylov, proof of thm:window, subcritical cumulative budgets.
Proof: sum nonnegative budgets over nested finite ranges. -/
theorem prefix_budget_bounds (ω : ℕ → ℝ) {k N : ℕ} (hk : k ≤ N)
    (hω : ∀ l < N, 0 ≤ ω l) :
    0 ≤ (∑ l ∈ range k, ω l) ∧ (∑ l ∈ range k, ω l) ≤ ∑ l ∈ range N, ω l := by
  constructor
  · exact sum_nonneg fun l hl => hω l ((mem_range.mp hl).trans_le hk)
  · exact sum_le_sum_of_subset_of_nonneg (range_mono hk)
      (fun l hl _ => hω l (mem_range.mp hl))

/-- Both hidden signs are positive at every time whenever the total budget is below one.
Use: completes strict operator admissibility of the constructed indistinguishable histories.
Article: main_krylov, thm:window, positive-definite signed scenarios.
Proof: the positive sign adds a positive form; the negative sign uses the proved
subcritical subtraction lemma with its actual finite prefix budget. -/
theorem hiddenSequence_posDef (A H : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hH : H.PosSemidef) (hHA : H ≤ A) (ω : ℕ → ℝ) {k N : ℕ} (hk : k ≤ N)
    (hω : ∀ l < N, 0 ≤ ω l) (hW : (∑ l ∈ range N, ω l) < 1) :
    (hiddenSequence A H ω 1 k).PosDef ∧ (hiddenSequence A H ω (-1) k).PosDef := by
  have hb := prefix_budget_bounds ω hk hω
  constructor
  · simpa only [hiddenSequence, one_mul] using hA.add_posSemidef (hH.smul hb.1)
  · simpa only [hiddenSequence, neg_one_mul, neg_smul, sub_eq_add_neg] using
      posDef_sub_scaled A H hA hHA hb.1 (hb.2.trans_lt hW)

/-- A positive rank-one direction below the base obeys both signed individual budgets.
Use: verify the physical admissibility inequalities for every hidden increment.
Article: main_krylov, thm:window, −ωA ⪯ E_l ⪯ ωA.
Proof: scale the two nonnegative forms H and A−H; negation exchanges the two signs. -/
theorem signed_rankOne_budget (A H : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hH : H.PosSemidef) (hHA : H ≤ A) {ω : ℝ} (hω : 0 ≤ ω) :
    ((-(ω • A) ≤ ω • H) ∧ (ω • H ≤ ω • A)) ∧
      ((-(ω • A) ≤ -(ω • H)) ∧ (-(ω • H) ≤ ω • A)) := by
  -- Scale the positive rank-one form and its positive complement in the base metric.
  have hu : ω • H ≤ ω • A := by
    change (ω • A - ω • H).PosSemidef
    rw [← smul_sub]
    exact (Matrix.le_iff.mp hHA).smul hω
  have hl : -(ω • A) ≤ ω • H := by
    change (ω • H - -(ω • A)).PosSemidef
    rw [sub_neg_eq_add]
    exact (hH.smul hω).add (hA.smul hω)
  exact ⟨⟨hl, hu⟩, ⟨neg_le_neg hu, by simpa only [neg_neg] using neg_le_neg hl⟩⟩

/-- The physical window model error measured in its fixed positive base Gram metric.
Use: at the constructed quadratic data this is exactly the observed model metric.
Article: main_krylov, thm:window, Z_* at M=G. -/
def canonicalWindowError (S : Matrix (Fin n) (Fin p) ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (A : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  relativeOperator (Sᵀ * base * S) (Sᵀ * A p * S - latest (Sᵀ * pairImages S A))

/-- The hidden history has exactly the article's normalized oldest-coordinate rank-one error.
Use: specifies the full canonical witness, including its direction and scalar amplitude.
Article: main_krylov, thm:window, Z_*^±=±W ûûᵀ.
Proof: substitute the actual physical model error and use the proved inverse-root
normalization identity in its positive Gram metric. -/
theorem hiddenSequence_canonical_rankOne (S : Matrix (Fin n) (Fin (p + 1)) ℝ)
    (hS : Function.Injective S.mulVec) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (h : Fin n → ℝ) (γ : ℝ) (hh : Sᵀ *ᵥ h = Pi.single 0 1)
    (hγ : γ = ((Pi.single 0 1) ⬝ᵥ ((Sᵀ * A * S)⁻¹ *ᵥ (Pi.single 0 1)))⁻¹)
    (ω : ℕ → ℝ) (ε : ℝ) :
    canonicalWindowError S A (hiddenSequence A (γ • vecMulVec h h) ω ε) =
      (ε * ∑ l ∈ range (p + 1), ω l) •
        vecMulVec (krylov.LinearAlgebra.normalizedInverseRoot (Sᵀ * A * S) (Pi.single 0 1))
          (krylov.LinearAlgebra.normalizedInverseRoot (Sᵀ * A * S) (Pi.single 0 1)) := by
  have hG : (Sᵀ * A * S).PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hA.conjTranspose_mul_mul_same (B := S) hS
  unfold canonicalWindowError
  rw [hiddenSequence_model_error S A hA.1.isSymm h γ hh ω ε, ← smul_smul,
    relativeOperator_smul, hγ, krylov.LinearAlgebra.normalized_relative_rankOne _ hG]

/-- The actual hidden canonical error has exactly the full cumulative budget norm.
Use: proves sharpness at every full-rank window, including nonconjugate ones.
Article: main_krylov, thm:window, ‖Z_*^±‖=W.
Proof: use the actual oldest-coordinate model error and cancel its exact inverse-Gram
normalizer by the proved spectral norm of a normalized relative rank-one form. -/
theorem hiddenSequence_canonical_norm (S : Matrix (Fin n) (Fin (p + 1)) ℝ)
    (hS : Function.Injective S.mulVec) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (h : Fin n → ℝ) (γ : ℝ) (hh : Sᵀ *ᵥ h = Pi.single 0 1)
    (hγ : γ = ((Pi.single 0 1) ⬝ᵥ ((Sᵀ * A * S)⁻¹ *ᵥ (Pi.single 0 1)))⁻¹)
    (ω : ℕ → ℝ) (ε : ℝ) :
    chebyshev1.opNorm (canonicalWindowError S A
      (hiddenSequence A (γ • vecMulVec h h) ω ε)) = |ε * ∑ l ∈ range (p + 1), ω l| := by
  -- The exact Gram energy cancels the normalizer in the spectral rank-one norm.
  have hG : (Sᵀ * A * S).PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hA.conjTranspose_mul_mul_same (B := S) hS
  have he0 : (Pi.single 0 1 : Fin (p + 1) → ℝ) ≠ 0 := by
    intro he
    have hi := congrFun he 0
    simp at hi
  unfold canonicalWindowError
  rw [hiddenSequence_model_error S A hA.1.isSymm h γ hh ω ε, ← smul_smul,
    relativeOperator_smul, chebyshev1.opNorm_smul, hγ,
    krylov.LinearAlgebra.normalized_relative_rankOne_norm _ hG _ he0, mul_one]

/-- The two actual hidden canonical model errors have opposite signs.
Use: every estimator must use the same centre on their identical observed data.
Article: main_krylov, thm:window, Z_*^−=−Z_*^+.
Proof: both physical model errors use the same oldest-coordinate form with opposite signs. -/
theorem hiddenSequence_canonical_opposite (S : Matrix (Fin n) (Fin (p + 1)) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (h : Fin n → ℝ) (γ : ℝ)
    (hh : Sᵀ *ᵥ h = Pi.single 0 1) (ω : ℕ → ℝ) :
    canonicalWindowError S A (hiddenSequence A (γ • vecMulVec h h) ω (-1)) =
      -canonicalWindowError S A (hiddenSequence A (γ • vecMulVec h h) ω 1) := by
  unfold canonicalWindowError
  rw [hiddenSequence_model_error S A hA h γ hh ω (-1),
    hiddenSequence_model_error S A hA h γ hh ω 1]
  simp only [one_mul, neg_mul, neg_smul, relativeOperator_neg]

/-- Every full-rank window has two actual positive admissible histories with identical
quadratic data and the full summed information obstruction against every common centre.
Use: the constructive information-radius lower bound for arbitrary windows.
Article: main_krylov, thm:window, positive indistinguishable scenarios and radius ≥ W.
Proof: construct the actual oldest dual direction, verify each physical budget and
operator, and apply the two-scenario distance bound to the opposite normalized errors. -/
theorem window_hidden_scenarios (S : Matrix (Fin n) (Fin (p + 1)) ℝ)
    (hS : Function.Injective S.mulVec) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (ω : ℕ → ℝ) (hω : ∀ l < p + 1, 0 ≤ ω l) (hW : (∑ l ∈ range (p + 1), ω l) < 1) :
    ∃ Aplus Aminus : ℕ → Matrix (Fin n) (Fin n) ℝ,
      Aplus 0 = A ∧ Aminus 0 = A ∧
      (∀ k, (Aplus k).IsSymm ∧ (Aminus k).IsSymm) ∧
      (∀ l < p + 1,
        ((-(ω l • A) ≤ Aplus (l + 1) - Aplus l) ∧
          (Aplus (l + 1) - Aplus l ≤ ω l • A)) ∧
        ((-(ω l • A) ≤ Aminus (l + 1) - Aminus l) ∧
          (Aminus (l + 1) - Aminus l ≤ ω l • A))) ∧
      (∀ k ≤ p + 1, (Aplus k).PosDef ∧ (Aminus k).PosDef) ∧
      pairImages S Aplus = A * S ∧ pairImages S Aminus = A * S ∧
      chebyshev1.opNorm (canonicalWindowError S A Aplus) = ∑ l ∈ range (p + 1), ω l ∧
      chebyshev1.opNorm (canonicalWindowError S A Aminus) = ∑ l ∈ range (p + 1), ω l ∧
      (∀ K : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ,
        (∑ l ∈ range (p + 1), ω l) ≤
          max (chebyshev1.opNorm (canonicalWindowError S A Aplus - K))
            (chebyshev1.opNorm (canonicalWindowError S A Aminus - K))) := by
  obtain ⟨h, γ, _, hh, hγ, hH, hHA⟩ := exists_oldest_hidden_direction S hS A hA
  let H := γ • vecMulVec h h
  let Aplus := hiddenSequence A H ω 1
  let Aminus := hiddenSequence A H ω (-1)
  have hW0 : 0 ≤ ∑ l ∈ range (p + 1), ω l := sum_nonneg fun l hl => hω l (mem_range.mp hl)
  have hp := hiddenSequence_canonical_norm S hS A hA h γ hh hγ ω 1
  have hm := hiddenSequence_canonical_norm S hS A hA h γ hh hγ ω (-1)
  simp only [one_mul, neg_one_mul, abs_neg, abs_of_nonneg hW0] at hp hm
  refine ⟨Aplus, Aminus, hiddenSequence_zero _ _ _ _, hiddenSequence_zero _ _ _ _, ?_, ?_,
    (fun k hk => hiddenSequence_posDef A H hA hH hHA ω hk hω hW),
    hiddenSequence_pairImages S A h γ hh ω 1,
    hiddenSequence_pairImages S A h γ hh ω (-1), hp, hm, ?_⟩
  · intro k
    exact ⟨hA.1.isSymm.add (hH.1.isSymm.smul _), hA.1.isSymm.add (hH.1.isSymm.smul _)⟩
  · intro l hl
    have hb := signed_rankOne_budget A H hA.posSemidef hH hHA (hω l hl)
    simpa only [Aplus, Aminus, hiddenSequence_increment, one_mul, neg_one_mul, neg_smul] using hb
  · intro K
    -- Identical full observations force the same centre on both opposite canonical errors.
    have ho : canonicalWindowError S A Aminus = -canonicalWindowError S A Aplus :=
      hiddenSequence_canonical_opposite S A hA.1.isSymm h γ hh ω
    have he : canonicalWindowError S A Aplus - canonicalWindowError S A Aminus =
        (2 : ℝ) • canonicalWindowError S A Aplus := by rw [ho, sub_neg_eq_add, two_smul]
    have hd := krylov.LinearAlgebra.two_scenario_distance
      (canonicalWindowError S A Aplus) (canonicalWindowError S A Aminus) (-K)
    rw [he, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hd
    change chebyshev1.opNorm (canonicalWindowError S A Aplus) = _ at hp
    change 2 * chebyshev1.opNorm (canonicalWindowError S A Aplus) / 2 ≤
      max (chebyshev1.opNorm (canonicalWindowError S A Aplus - K))
        (chebyshev1.opNorm (canonicalWindowError S A Aminus - K)) at hd
    simpa only [hp, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hd

end
end krylov.Secant
