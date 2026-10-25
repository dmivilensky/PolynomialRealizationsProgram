import polyak.Interpolation.FiniteSpan
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Article: Appendix A, growth envelope.
Use: genuine finite interpolation tables with a free two-position initial state.
Proof: the minimizer inequality bounds every gradient by its position.
-/

namespace polyak.Growth
noncomputable section
open polyak.Interpolation

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: Appendix A, segment. Use: all interpolation pairs and the minimizer datum.
The endpoint data may always be filled by the interpolation theorem. -/
structure Segment (A B β : ℝ) (n : ℕ) where
  /-- Article: segment positions. Use: positions indexed from zero. -/
  x : ℕ → E
  /-- Article: segment gradients. Use: normalized gradient data. -/
  σ : ℕ → E
  /-- Article: segment values. Use: potential relative to its value at the origin. -/
  value : ℕ → ℝ
  /-- Article: interpolation. Use: every pair in the finite table. -/
  interpolation : ∀ i, i ≤ n+1 → ∀ j, j ≤ n+1 →
    |datumT x σ value i j| ≤ datumR x σ i j
  /-- Article: minimizer interpolation. Use: include the zero value and gradient at zero. -/
  origin : ∀ i, i ≤ n+1 →
    |value i - (1/2 : ℝ)*inner ℝ (σ i) (x i)| ≤
      (1/4 : ℝ)*(‖x i‖^2-‖σ i‖^2)
  /-- Article: normalized recurrence. Use: each of the n actual transitions. -/
  recurrence : ∀ k, k < n →
    x (k+2) = A • x (k+1) + B • σ (k+1) - β • x k

variable {E}

/-- Article: state S. Use: genuine Hilbert ℓ² norm rather than the product max norm. -/
def stateNorm (x : ℕ → E) (k : ℕ) : ℝ :=
  Real.sqrt (‖x k‖^2 + ‖x (k+1)‖^2)

omit [InnerProductSpace ℝ E] in
/-- Article: state norm. Use: nonnegativity before ratios and roots. -/
theorem stateNorm_nonneg (x : ℕ → E) (k : ℕ) : 0 ≤ stateNorm x k :=
  Real.sqrt_nonneg _

omit [InnerProductSpace ℝ E] in
/-- Article: state norm. Use: squared ℓ² identity. -/
theorem stateNorm_sq (x : ℕ → E) (k : ℕ) :
    stateNorm x k ^ 2 = ‖x k‖^2 + ‖x (k+1)‖^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

omit [InnerProductSpace ℝ E] in
/-- Article: state norm. Use: each position is bounded by its state. -/
theorem norm_left_le_stateNorm (x : ℕ → E) (k : ℕ) : ‖x k‖ ≤ stateNorm x k := by
  nlinarith [stateNorm_sq x k, stateNorm_nonneg x k, norm_nonneg (x k),
    sq_nonneg ‖x (k+1)‖]

omit [InnerProductSpace ℝ E] in
/-- Article: state norm. Use: each position is bounded by its state. -/
theorem norm_right_le_stateNorm (x : ℕ → E) (k : ℕ) : ‖x (k+1)‖ ≤ stateNorm x k := by
  nlinarith [stateNorm_sq x k, stateNorm_nonneg x k, norm_nonneg (x (k+1)),
    sq_nonneg ‖x k‖]

omit [InnerProductSpace ℝ E] in
/-- Article: zero state. Use: both positions vanish, including degenerate dimensions. -/
theorem stateNorm_eq_zero_iff (x : ℕ → E) (k : ℕ) :
    stateNorm x k = 0 ↔ x k = 0 ∧ x (k+1) = 0 := by
  constructor
  · intro h
    have h₀ := norm_left_le_stateNorm x k
    have h₁ := norm_right_le_stateNorm x k
    rw [h] at h₀ h₁
    exact ⟨norm_eq_zero.mp (le_antisymm h₀ (norm_nonneg _)),
      norm_eq_zero.mp (le_antisymm h₁ (norm_nonneg _))⟩
  · rintro ⟨h₀,h₁⟩
    simp [stateNorm, h₀, h₁]

namespace Segment

variable {A B β : ℝ} {n : ℕ}

/-- Article: minimizer inequality. Use: the gradient estimate does not assume a wave. -/
theorem norm_gradient_le (s : Segment E A B β n) (i : ℕ) (hi : i ≤ n+1) :
    ‖s.σ i‖ ≤ ‖s.x i‖ := by
  have h := le_trans (abs_nonneg _) (s.origin i hi)
  nlinarith [norm_nonneg (s.σ i), norm_nonneg (s.x i)]

/-- Article: segment restriction. Use: a consecutive finite window remains admissible. -/
def restrict (s : Segment E A B β n) (l m : ℕ) (h : l+m ≤ n) :
    Segment E A B β m where
  x k := s.x (l+k)
  σ k := s.σ (l+k)
  value k := s.value (l+k)
  interpolation i hi j hj := s.interpolation (l+i) (by omega) (l+j) (by omega)
  origin i hi := s.origin (l+i) (by omega)
  recurrence k hk := by
    simpa only [Nat.add_assoc] using s.recurrence (l+k) (by omega)

/-- Article: segment restriction. Use: exact shifted states. -/
theorem stateNorm_restrict (s : Segment E A B β n) (l m : ℕ) (h : l+m ≤ n)
    (k : ℕ) : stateNorm (s.restrict l m h).x k = stateNorm s.x (l+k) := by
  simp [stateNorm, restrict, Nat.add_assoc]

/-- Article: finite growth bound. Use: a uniform elementary majorant for one transition. -/
theorem stateNorm_succ_le (s : Segment E A B β n) (k : ℕ) (hk : k < n) :
    stateNorm s.x (k+1) ≤
      (1+|A|+|B|+|β|) * stateNorm s.x k := by
  have hx := norm_right_le_stateNorm s.x k
  have hy := norm_left_le_stateNorm s.x k
  have hσ := s.norm_gradient_le (k+1) (by omega)
  have ht : ‖s.x (k+2)‖ ≤ (|A|+|B|+|β|)*stateNorm s.x k := by
    rw [s.recurrence k hk]
    calc
      ‖A • s.x (k+1)+B • s.σ (k+1)-β • s.x k‖ ≤
          ‖A • s.x (k+1)‖+‖B • s.σ (k+1)‖+‖β • s.x k‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ = |A| *‖s.x (k+1)‖+|B| *‖s.σ (k+1)‖+|β| *‖s.x k‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ |A| *stateNorm s.x k+|B| *stateNorm s.x k+|β| *stateNorm s.x k := by
        gcongr
        exact hσ.trans hx
      _ = _ := by ring
  have hz := stateNorm_sq s.x (k+1)
  have hstate := stateNorm_nonneg s.x k
  have hnext := stateNorm_nonneg s.x (k+1)
  have hc : 0 ≤ |A|+|B|+|β| := by positivity
  have hs : 0 ≤ (|A|+|B|+|β|)*stateNorm s.x k := mul_nonneg hc hstate
  have hxx := (sq_le_sq₀ (norm_nonneg _) hstate).2 hx
  have htt := (sq_le_sq₀ (norm_nonneg _) hs).2 ht
  have hn : k+1+1=k+2 := by omega
  rw [hn] at hz
  nlinarith [mul_nonneg hc (sq_nonneg (stateNorm s.x k))]

/-- Article: finite growth bound. Use: finiteness independent of function and dimension. -/
theorem stateNorm_le (s : Segment E A B β n) (k : ℕ) (hk : k ≤ n) :
    stateNorm s.x k ≤ (1+|A|+|B|+|β|)^k * stateNorm s.x 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      stateNorm s.x (k+1) ≤ (1+|A|+|B|+|β|)*stateNorm s.x k :=
        s.stateNorm_succ_le k (by omega)
      _ ≤ (1+|A|+|B|+|β|)*((1+|A|+|B|+|β|)^k*stateNorm s.x 0) := by
        gcongr
        exact ih (by omega)
      _ = _ := by rw [pow_succ]; ring

/-- Article: zero-state absorption. Use: do not divide by an intermediate zero state. -/
theorem stateNorm_eq_zero_of_zero (s : Segment E A B β n)
    (h : stateNorm s.x 0 = 0) (k : ℕ) (hk : k ≤ n) : stateNorm s.x k = 0 := by
  have hh := s.stateNorm_le k hk
  rw [h, mul_zero] at hh
  exact le_antisymm hh (stateNorm_nonneg s.x k)

/-- Article: finite-dimensional reduction. Use: linear isometries preserve complete segments. -/
def map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (s : Segment E A B β n) (J : E →ₗᵢ[ℝ] F) : Segment F A B β n where
  x k := J (s.x k)
  σ k := J (s.σ k)
  value := s.value
  interpolation i hi j hj := by
    simpa only [datumT_isometry, datumR_isometry] using s.interpolation i hi j hj
  origin i hi := by simpa only [J.inner_map_map, J.norm_map] using s.origin i hi
  recurrence k hk := by
    simpa only [map_sub, map_add, map_smul] using congrArg J (s.recurrence k hk)

/-- Article: finite-dimensional reduction. Use: every state norm is preserved exactly. -/
theorem stateNorm_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (s : Segment E A B β n) (J : E →ₗᵢ[ℝ] F) (k : ℕ) :
    stateNorm (s.map J).x k = stateNorm s.x k := by simp [stateNorm, map]

/-- Article: finite-dimensional reduction. Use: clamp irrelevant indices outside the table. -/
def finiteIndex (n k : ℕ) : Fin (n+2) := ⟨min k (n+1), by omega⟩

/-- Article: finite-dimensional reduction. Use: the finite span of the actual table. -/
def inSpan (s : Segment E A B β n) :
    Segment (dataSpan (fun i : Fin (n+2) => s.x i) (fun i : Fin (n+2) => s.σ i)) A B β n where
  x k := spanPosition (fun i : Fin (n+2) => s.x i) (fun i : Fin (n+2) => s.σ i) (finiteIndex n k)
  σ k := spanGradient (fun i : Fin (n+2) => s.x i) (fun i : Fin (n+2) => s.σ i) (finiteIndex n k)
  value k := s.value (finiteIndex n k)
  interpolation i hi j hj := by
    simpa only [datumT, datumR, spanPosition, spanGradient, finiteIndex, min_eq_left hi,
      min_eq_left hj, ← Submodule.norm_coe, Submodule.coe_inner, Submodule.coe_add, Submodule.coe_sub] using s.interpolation i hi j hj
  origin i hi := by
    simpa only [spanPosition, spanGradient, finiteIndex, min_eq_left hi,
      ← Submodule.norm_coe, Submodule.coe_inner, Submodule.coe_add, Submodule.coe_sub] using s.origin i hi
  recurrence k hk := by
    apply Subtype.ext
    change s.x (min (k+2) (n+1)) =
      A • s.x (min (k+1) (n+1)) + B • s.σ (min (k+1) (n+1)) -
        β • s.x (min k (n+1))
    simpa only [min_eq_left (show k+2 ≤ n+1 by omega),
      min_eq_left (show k+1 ≤ n+1 by omega), min_eq_left (show k ≤ n+1 by omega)] using
      s.recurrence k hk

/-- Article: finite-dimensional reduction. Use: compression preserves all admissible states. -/
theorem stateNorm_inSpan (s : Segment E A B β n) (k : ℕ) (hk : k ≤ n) :
    stateNorm s.inSpan.x k = stateNorm s.x k := by
  simp only [stateNorm, inSpan, spanPosition, finiteIndex, ← Submodule.norm_coe,
    min_eq_left (show k ≤ n+1 by omega), min_eq_left (show k+1 ≤ n+1 by omega)]

/-- Article: finite-dimensional realization of segments. Use: arbitrary Hilbert waves
and free trajectories contribute to exactly the finite-dimensional envelope. -/
theorem exists_euclidean (s : Segment E A B β n) :
    ∃ d : ℕ, ∃ q : Segment (EuclideanSpace ℝ (Fin d)) A B β n,
      ∀ k, k ≤ n → stateNorm q.x k = stateNorm s.x k := by
  let J := (stdOrthonormalBasis ℝ
    (dataSpan (fun i : Fin (n+2) => s.x i) (fun i : Fin (n+2) => s.σ i))).repr.toLinearIsometry
  refine ⟨_, s.inSpan.map J, ?_⟩
  intro k hk
  rw [stateNorm_map, stateNorm_inSpan s k hk]

end Segment
end
end polyak.Growth
