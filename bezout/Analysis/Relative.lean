import bezout.Risk.Bounds

/-!
Article: bezout, Theorem 4.1, dimension-uniform local relative errors.
Use: controls errors proportional to the actual noisy query, including
adaptive error choices, rather than substituting the nominal query.
Proof: finite triangular scalar majorants bound the actual queries and
their first deviations. The exact physical response gives a uniform
quadratic remainder, independent of the Hilbert space dimension.
-/

namespace bezout.Analysis
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ}

/-- Scalar majorant for the actual queries up to a fixed error scale `t0`. -/
def queryMajorant (h : bezout.History N) (L t0 : ℝ) (s : Fin N) : ℝ :=
  1 + (L + t0) * ∑ j : Fin N,
    if _hj : j < s then |h.a s j| * queryMajorant h L t0 j else 0
termination_by s.val

/-- Scalar majorant for the noisy-minus-nominal query, divided by `t*r`. -/
def deviationMajorant (h : bezout.History N) (L t0 : ℝ) (s : Fin N) : ℝ :=
  ∑ j : Fin N, if _hj : j < s then
    |h.a s j| * (L * deviationMajorant h L t0 j + queryMajorant h L t0 j) else 0
termination_by s.val

/-- The actual-query majorants are nonnegative. -/
theorem queryMajorant_nonneg (h : bezout.History N) {L t0 : ℝ}
    (hL : 0 ≤ L) (ht0 : 0 ≤ t0) (s : Fin N) : 0 ≤ queryMajorant h L t0 s := by
  induction s using (measure (fun s : Fin N => s.val)).wf.induction with
  | h s ih =>
    rw [queryMajorant]
    apply add_nonneg zero_le_one
    apply mul_nonneg (add_nonneg hL ht0)
    apply Finset.sum_nonneg
    intro j _
    split_ifs with hj
    · exact mul_nonneg (abs_nonneg _) (ih j hj)
    · exact le_rfl

/-- The deviation majorants are nonnegative. -/
theorem deviationMajorant_nonneg (h : bezout.History N) {L t0 : ℝ}
    (hL : 0 ≤ L) (ht0 : 0 ≤ t0) (s : Fin N) : 0 ≤ deviationMajorant h L t0 s := by
  induction s using (measure (fun s : Fin N => s.val)).wf.induction with
  | h s ih =>
    rw [deviationMajorant]
    apply Finset.sum_nonneg
    intro j _
    split_ifs with hj
    · exact mul_nonneg (abs_nonneg _) (add_nonneg (mul_nonneg hL (ih j hj))
        (queryMajorant_nonneg h hL ht0 j))
    · exact le_rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A physical relative-error execution uses one shared nonnegative temporal budget. -/
def RelativeErrors (h : bezout.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (noise : Fin N → E) (u : h.Execution H initial noise) (t : ℝ)
    (δ : Fin N → ℝ) : Prop :=
  (∀ s, 0 ≤ δ s) ∧ (∑ s, δ s ^ 2 ≤ 1) ∧
    ∀ s, ‖noise s‖ ≤ t * δ s * ‖u.query s‖

omit [FiniteDimensional ℝ E] in
/-- Strict causality turns any scalar answer bounds into a query bound. -/
theorem query_norm_le (h : bezout.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (noise : Fin N → E) (u : h.Execution H initial noise) (s : Fin N) :
    ‖u.query s‖ ≤ ‖initial‖ +
      ∑ j : Fin N, if j < s then |h.a s j| * ‖u.answer j‖ else 0 := by
  rw [u.query_eq]
  apply (norm_sub_le _ _).trans
  apply add_le_add le_rfl
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j < s
  · simp only [hj, ite_true, norm_smul, Real.norm_eq_abs, le_refl]
  · simp only [hj, ite_false, h.triangular s j (le_of_not_gt hj), zero_smul, norm_zero,
      le_refl]

/-- Actual noisy queries remain bounded uniformly in dimension and error choices. -/
theorem actual_query_bound (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (initial : E) (noise : Fin N → E)
    (u : h.Execution H initial noise) (r t t0 : ℝ) (_hr : 0 ≤ r)
    (ht : 0 ≤ t) (htt0 : t ≤ t0) (hi : ‖initial‖ ≤ r) (δ : Fin N → ℝ)
    (hw : RelativeErrors h H initial noise u t δ) (s : Fin N) :
    ‖u.query s‖ ≤ r * queryMajorant h I.L t0 s := by
  have hL : 0 ≤ I.L := (I.mu_pos.trans I.mu_lt_L).le
  induction s using (measure (fun s : Fin N => s.val)).wf.induction with
  | h s ih =>
    have ha (j : Fin N) (hj : j < s) :
        ‖u.answer j‖ ≤ (I.L + t0) * (r * queryMajorant h I.L t0 j) := by
      have hd : δ j ≤ 1 := (le_abs_self _).trans (abs_le_one_of_energy hw.2.1 j)
      have hn : ‖noise j‖ ≤ t0 * ‖u.query j‖ := by
        exact (hw.2.2 j).trans (mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left hd ht).trans (by simpa using htt0)) (norm_nonneg _))
      rw [u.answer_eq]
      calc
        _ ≤ I.L * ‖u.query j‖ + t0 * ‖u.query j‖ :=
          (norm_add_le _ _).trans (add_le_add (hessian_action_bound I H hH _) hn)
        _ = (I.L + t0) * ‖u.query j‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (ih j hj) (add_nonneg hL (ht.trans htt0))
    calc
      _ ≤ r + ∑ j : Fin N, if j < s then |h.a s j| * ‖u.answer j‖ else 0 :=
        (query_norm_le h H initial noise u s).trans (add_le_add hi le_rfl)
      _ ≤ r + ∑ j : Fin N, if j < s then
          |h.a s j| * ((I.L + t0) * (r * queryMajorant h I.L t0 j)) else 0 := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro j _
        split_ifs with hj
        · exact mul_le_mul_of_nonneg_left (ha j hj) (abs_nonneg _)
        · exact le_rfl
      _ = _ := by
        rw [queryMajorant, mul_add, mul_one, Finset.mul_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring

omit [FiniteDimensional ℝ E] in
/-- The exact difference of actual and nominal query equations. -/
theorem query_difference (h : bezout.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (noise : Fin N → E) (u : h.Execution H initial noise)
    (v : h.Execution H initial (fun _ => 0)) (s : Fin N) :
    u.query s - v.query s = -∑ j, h.a s j •
      (H (u.query j - v.query j) + noise j) := by
  rw [u.query_eq, v.query_eq]
  have he (j : Fin N) : u.answer j - v.answer j =
      H (u.query j - v.query j) + noise j := by
    rw [u.answer_eq, v.answer_eq, map_sub]
    simp only [add_zero]
    abel
  simp_rw [← he, smul_sub, Finset.sum_sub_distrib]
  abel

/-- Actual queries differ from nominal queries by at most a uniform first-order amount. -/
theorem query_deviation_bound (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (initial : E) (noise : Fin N → E)
    (u : h.Execution H initial noise) (r t t0 : ℝ) (hr : 0 ≤ r)
    (ht : 0 ≤ t) (htt0 : t ≤ t0) (hi : ‖initial‖ ≤ r) (δ : Fin N → ℝ)
    (hw : RelativeErrors h H initial noise u t δ) (s : Fin N) :
    ‖u.query s - (aeval H (h.query s)) initial‖ ≤
      t * r * deviationMajorant h I.L t0 s := by
  let v := h.run H initial (fun _ => 0)
  have hL : 0 ≤ I.L := (I.mu_pos.trans I.mu_lt_L).le
  have hc := actual_query_bound h I H hH initial noise u r t t0 hr ht htt0 hi δ hw
  have hn (j : Fin N) : ‖noise j‖ ≤ t * r * queryMajorant h I.L t0 j := by
    have hd : δ j ≤ 1 := (le_abs_self _).trans (abs_le_one_of_energy hw.2.1 j)
    calc
      _ ≤ t * δ j * ‖u.query j‖ := hw.2.2 j
      _ ≤ t * ‖u.query j‖ := mul_le_mul_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_left hd ht) (norm_nonneg _)
      _ ≤ t * (r * queryMajorant h I.L t0 j) := mul_le_mul_of_nonneg_left (hc j) ht
      _ = _ := by ring
  have hd (s : Fin N) : ‖u.query s - v.query s‖ ≤ t * r * deviationMajorant h I.L t0 s := by
    induction s using (measure (fun s : Fin N => s.val)).wf.induction with
    | h s ih =>
      rw [query_difference h H initial noise u v s, norm_neg]
      calc
        _ ≤ ∑ j, ‖h.a s j • (H (u.query j - v.query j) + noise j)‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin N, if j < s then |h.a s j| *
            (I.L * (t * r * deviationMajorant h I.L t0 j) +
              t * r * queryMajorant h I.L t0 j) else 0 := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j < s
          · simp only [hj, ite_true, norm_smul, Real.norm_eq_abs]
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact (norm_add_le _ _).trans (add_le_add
              ((hessian_action_bound I H hH _).trans
                (mul_le_mul_of_nonneg_left (ih j hj) hL)) (hn j))
          · simp only [hj, ite_false, h.triangular s j (le_of_not_gt hj), zero_smul,
              norm_zero, le_refl]
        _ = _ := by
          rw [deviationMajorant, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> ring
  simpa only [h.nominal_query H initial v] using hd s

/-- Actual relative errors admit a dimension-uniform quadratic remainder.
The constant uses only the fixed history, the upper endpoint and `t0`.
No restriction on how errors depend on earlier answers is imposed. -/
theorem relative_response_bound (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (initial : E) (noise : Fin N → E)
    (u : h.Execution H initial noise) (r t t0 : ℝ) (hr : 0 ≤ r)
    (ht : 0 ≤ t) (htt0 : t ≤ t0) (hi : ‖initial‖ ≤ r) (δ : Fin N → ℝ)
    (hw : RelativeErrors h H initial noise u t δ) (P Q : Fin N → ℝ)
    (hP : Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s) :
    ‖u.output - (aeval H h.terminal) initial‖ ≤
      t * r * energyNorm (fun s => P s * Q s) +
      t ^ 2 * r * energyNorm (fun s => P s * deviationMajorant h I.L t0 s) := by
  let d : Fin N → ℝ := deviationMajorant h I.L t0
  have hd := query_deviation_bound h I H hH initial noise u r t t0 hr ht htt0 hi δ hw
  have hn (s : Fin N) : ‖(aeval H (h.query s)) initial‖ ≤ r * Q s := by
    calc
      _ ≤ Q s * ‖initial‖ := polynomial_action_bound I H hH _ _ (hQ s) (hq s) initial
      _ ≤ Q s * r := mul_le_mul_of_nonneg_left hi (hQ s)
      _ = _ := mul_comm _ _
  have ha (s : Fin N) : ‖u.query s‖ ≤ r * Q s + t * r * d s := by
    calc
      _ = ‖(aeval H (h.query s)) initial +
          (u.query s - (aeval H (h.query s)) initial)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (hn s) (hd s))
  have hw' (s : Fin N) : ‖noise s‖ ≤
      t * r * (Q s * δ s) + t ^ 2 * r * (d s * δ s) := by
    calc
      _ ≤ t * δ s * ‖u.query s‖ := hw.2.2 s
      _ ≤ t * δ s * (r * Q s + t * r * d s) :=
        mul_le_mul_of_nonneg_left (ha s) (mul_nonneg ht (hw.1 s))
      _ = _ := by ring
  rw [h.physical_response H initial noise u, add_sub_cancel_left]
  calc
    _ ≤ ∑ s, P s * ‖noise s‖ := norm_sum_le_energy _ _ (fun s =>
      polynomial_action_bound I H hH _ _ (hP.1 s) (hP.2 s) _)
    _ ≤ ∑ s, P s * (t * r * (Q s * δ s) + t ^ 2 * r * (d s * δ s)) :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hw' s) (hP.1 s)
    _ = t * r * (∑ s, (P s * Q s) * δ s) +
        t ^ 2 * r * (∑ s, (P s * d s) * δ s) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ _ := by
      have he : ∑ s, δ s ^ 2 ≤ (1 : ℝ) ^ 2 := by simpa using hw.2.1
      have h₁ := sum_mul_le_of_energy (a := fun s => P s * Q s) zero_le_one he
      have h₂ := sum_mul_le_of_energy (a := fun s => P s * d s) zero_le_one he
      simp only [mul_one] at h₁ h₂
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ (mul_nonneg ht hr))
        (mul_le_mul_of_nonneg_left h₂ (mul_nonneg (sq_nonneg t) hr))

end
end bezout.Analysis
