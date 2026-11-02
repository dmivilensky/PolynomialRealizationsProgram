import krylov.Secant.FlagNormalization
import krylov.LinearAlgebra.Commutator

/-!
Article: main_krylov, apA:lem:flagcd(d), first-order canonical old flags.
Use: derive the actual data defect and model-error expansions from perturbed
step columns and operators; no expansion is a field of an assumed trajectory.
Source: the exact physical flag identities, genuine matrix product calculus
and smooth observed-diagonal normalization proved in the preceding modules.
-/

namespace krylov.Secant
noncomputable section
open Matrix Filter Asymptotics Topology krylov.LinearAlgebra
open scoped Matrix Matrix.Norms.L2Operator BigOperators
variable {α : Type*} {n p : ℕ} {f : Filter α}

/-- Fixed positive energy normalization preserves every actual spectral matrix order.
Use: transport the actual unnormalized flag remainder into its reference canonical coordinates.
Article: main_krylov, apA:lem:flagcd(d).
Proof: the fixed normalization is a genuine constant diagonal congruence. -/
theorem fixedNormalize_bigO (c : Fin p → ℝ) (Z : α → Matrix (Fin p) (Fin p) ℝ)
    (s : α → ℝ) (hZ : Z =O[f] s) : (fun x => fixedNormalize c (Z x)) =O[f] s := by
  simpa only [fixedNormalize_eq] using matrix_mul_const_bigO _ _ s
    (matrix_const_mul_bigO (diagonal (fun i => (Real.sqrt (c i))⁻¹)) Z s hZ)

/-- Actual reference energy scaling cancels exactly in each normalized form.
Use: identify the fixed-energy normalization with the canonical reference columns Q.
Article: main_krylov, apA:lem:flagcd(d), S⁰=QC^(1/2) in canonical coordinates.
Proof: evaluate the actual diagonal products and cancel both positive square roots. -/
theorem fixedNormalize_reference (c : Fin p → ℝ) (hc : ∀ i, 0<c i)
    (Z : Matrix (Fin p) (Fin p) ℝ) :
    fixedNormalize c (diagonal (fun i => Real.sqrt (c i))*Z*
      diagonal (fun i => Real.sqrt (c i))) = Z := by
  ext i j
  simp only [fixedNormalize, diagonal_mul, mul_diagonal]
  have hi := (Real.sqrt_pos.mpr (hc i)).ne'
  have hj := (Real.sqrt_pos.mpr (hc j)).ne'
  field_simp

/-- Fixed normalization commutes with every actual old-flag compression and commutator.
Use: diagonal reference energies commute with the old coordinate flags.
Article: main_krylov, apA:lem:flagcd(d), commuting C with I_≤l.
Proof: each flag merely retains or removes an entry of the normalized form. -/
theorem fixedNormalize_flags (c : Fin p → ℝ) (Z : Matrix (Fin p) (Fin p) ℝ) (l : ℕ) :
    (fixedNormalize c (prefixProjection p l*Z*prefixProjection p l) =
      prefixProjection p l*fixedNormalize c Z*prefixProjection p l) ∧
    (fixedNormalize c (prefixProjection p l*Z-Z*prefixProjection p l) =
      prefixProjection p l*fixedNormalize c Z-fixedNormalize c Z*prefixProjection p l) := by
  -- Compression selects two indicators; the commutator subtracts their individual selections.
  constructor
  · ext i j
    simp only [fixedNormalize, prefix_compression_apply]
    split_ifs <;> simp
  · ext i j
    simp only [fixedNormalize, prefix_commutator_apply]
    by_cases hi : i.val≤l <;> by_cases hj : j.val≤l <;> simp [hi, hj, neg_div]

/-- The actual normalized reference compression is QᵀEQ.
Use: actual normalized physical reference steps give the printed canonical increment matrix.
Article: main_krylov, apA:lem:flagcd(d), reference compressed X_l.
Proof: associate the actual rectangular products, transpose the diagonal, and
cancel its positive reference energies using the proved exact normalization identity. -/
theorem fixedNormalize_reference_compression (Q : Matrix (Fin n) (Fin p) ℝ)
    (c : Fin p → ℝ) (hc : ∀ i, 0<c i) (E : Matrix (Fin n) (Fin n) ℝ) :
    fixedNormalize c ((Q*diagonal (fun i => Real.sqrt (c i)))ᵀ*E*
      (Q*diagonal (fun i => Real.sqrt (c i)))) = Qᵀ*E*Q := by
  rw [transpose_mul, diagonal_transpose]
  have he : diagonal (fun i => Real.sqrt (c i))*Qᵀ*E*(Q*diagonal (fun i => Real.sqrt (c i))) =
      diagonal (fun i => Real.sqrt (c i))*(Qᵀ*E*Q)*diagonal (fun i => Real.sqrt (c i)) := by
    simp only [Matrix.mul_assoc]
  rw [he, fixedNormalize_reference c hc]

/-- Canonical reference flags yield the exact spatial compression and commutator forms.
Use: the coordinate flag sums are precisely the printed Qᵀ[P,E]Q and QᵀPEPQ.
Article: main_krylov, apA:lem:flagcd(d), P_l=QI_≤lQᵀ.
Proof: associate the actual rectangular factors and cancel QᵀQ on each exterior side. -/
theorem reference_flag_forms (Q : Matrix (Fin n) (Fin p) ℝ) (hQ : Qᵀ*Q=1)
    (E : Matrix (Fin n) (Fin n) ℝ) (l : ℕ) :
    let P := Q*prefixProjection p l*Qᵀ
    (prefixProjection p l*(Qᵀ*E*Q)*prefixProjection p l = Qᵀ*(P*E*P)*Q) ∧
    (prefixProjection p l*(Qᵀ*E*Q)-(Qᵀ*E*Q)*prefixProjection p l = Qᵀ*(P*E-E*P)*Q) := by
  -- Cancel only the exterior orthonormal factors; all increment factors remain in their original order.
  dsimp only
  constructor
  · calc
      _ = (Qᵀ*Q)*prefixProjection p l*(Qᵀ*E*Q)*prefixProjection p l*(Qᵀ*Q) := by simp [hQ]
      _ = _ := by simp only [Matrix.mul_assoc]
  · calc
      _ = (Qᵀ*Q)*prefixProjection p l*(Qᵀ*E*Q)-(Qᵀ*E*Q)*prefixProjection p l*(Qᵀ*Q) := by simp [hQ]
      _ = _ := by simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- An actual orthonormal rectangular column matrix is contractive, including empty columns.
Use: spatial first-order bounds pass to the observed coordinates with constant one.
Article: main_krylov, apA:lem:flagcd(d), compression by Q.
Source: mathlib's genuine rectangular C-star norm identity.
Proof: square its norm using QᵀQ=I; the identity matrix has norm at most one. -/
theorem orthonormal_columns_norm_le (Q : Matrix (Fin n) (Fin p) ℝ) (hQ : Qᵀ*Q=1) :
    ‖Q‖≤1 := by
  -- Empty columns give the zero identity norm; positive dimension gives the norm-one identity.
  have he := Matrix.l2_opNorm_conjTranspose_mul_self Q
  simp only [conjTranspose_eq_transpose_of_trivial, hQ] at he
  have h1 : ‖(1 : Matrix (Fin p) (Fin p) ℝ)‖≤1 := by
    by_cases hp : p=0
    · subst p
      rw [Subsingleton.elim (1 : Matrix (Fin 0) (Fin 0) ℝ) 0, norm_zero]
      norm_num
    · let : NeZero p := ⟨hp⟩
      simp only [norm_one, le_refl]
  nlinarith [norm_nonneg Q]

/-- Every actual reference flag is an orthogonal matrix projector, even in a rectangular window.
Use: the sharp commutator estimate applies to the genuine reference flags P_l.
Article: main_krylov, apA:lem:flagcd(d), orthogonal P_l.
Proof: transpose the symmetric coordinate indicator; squaring cancels QᵀQ
and retains exactly the same finite diagonal indicators. -/
theorem reference_flag_projector (Q : Matrix (Fin n) (Fin p) ℝ) (hQ : Qᵀ*Q=1) (l : ℕ) :
    (Q*prefixProjection p l*Qᵀ).IsSymm ∧
      (Q*prefixProjection p l*Qᵀ)*(Q*prefixProjection p l*Qᵀ)=Q*prefixProjection p l*Qᵀ := by
  -- The actual coordinate indicator is idempotent before transporting it to the ambient space.
  have hi : prefixProjection p l*prefixProjection p l=prefixProjection p l := by
    simp only [prefixProjection, diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp
  constructor
  · simp only [Matrix.IsSymm, transpose_mul, transpose_transpose,
      (prefixProjection_isSymm p l).eq, Matrix.mul_assoc]
  · calc
      _ = Q*prefixProjection p l*(Qᵀ*Q)*prefixProjection p l*Qᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ, Matrix.mul_one, Matrix.mul_assoc Q, hi]

/-- The first-order observed flag sum spends at most the sum of its actual increment norms.
Use: supplies the sharp constant one in the displayed normalized-defect budget bound.
Article: main_krylov, apA:lem:flagcd(d), ‖δ‖≤Σω_l+O(s²).
Proof: each actual reference commutator has its one-cross-block norm; summation
and the actual orthonormal exterior factors are contractive. -/
theorem reference_commutator_sum_bound (Q : Matrix (Fin n) (Fin p) ℝ) (hQ : Qᵀ*Q=1)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l, (E l).IsSymm) (I : Finset ℕ) :
    ‖Qᵀ*(∑ l ∈ I, ((Q*prefixProjection p l*Qᵀ)*E l-E l*(Q*prefixProjection p l*Qᵀ)))*Q‖ ≤
      ∑ l ∈ I, ‖E l‖ := by
  have hq := orthonormal_columns_norm_le Q hQ
  have ht : ‖Qᵀ‖≤1 := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using (Matrix.l2_opNorm_conjTranspose Q).le.trans hq
  have hs : ‖∑ l ∈ I, ((Q*prefixProjection p l*Qᵀ)*E l-E l*(Q*prefixProjection p l*Qᵀ))‖ ≤
      ∑ l ∈ I, ‖E l‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro l _
    exact (matrix_commutator_norm _ _ (reference_flag_projector Q hQ l).1
      (reference_flag_projector Q hQ l).2 (hE l)).2
  -- The rectangular exterior factors are controlled in the same actual L2 operator norm.
  calc
    _ ≤ ‖Qᵀ‖*‖∑ l ∈ I, ((Q*prefixProjection p l*Qᵀ)*E l-E l*(Q*prefixProjection p l*Qᵀ))‖*‖Q‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ ‖∑ l ∈ I, ((Q*prefixProjection p l*Qᵀ)*E l-E l*(Q*prefixProjection p l*Qᵀ))‖ :=
      (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) ht) (norm_nonneg _)).trans
        (mul_le_of_le_one_right (norm_nonneg _) hq)
    _ ≤ _ := hs

/-- Both actual unnormalized flag forms may replace their steps by reference steps to quadratic order.
Use: perturbing the true observed window has no hidden additional first-order flag terms.
Article: main_krylov, apA:lem:flagcd(d), first-order compressed sums.
Proof: use the exact physical flag identities, replace each actual compressed
increment by its proved reference congruence, and sum the finitely many quadratic remainders. -/
theorem flag_reference_order (S : α → Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin p) ℝ) (A : α → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ x k, (A x k).IsSymm) (s : α → ℝ) (hs : Tendsto s f (𝓝 0))
    (hS : (fun x => S x-R) =O[f] s)
    (hE : ∀ l<p, (fun x => A x (l+1)-A x l) =O[f] s) :
    let X0 := fun x l => Rᵀ*(A x (l+1)-A x l)*R
    ((fun x => (S x)ᵀ*A x p*S x-latest ((S x)ᵀ*pairImages (S x) (A x))-
      ∑ l ∈ Finset.range p, prefixProjection p l*X0 x l*prefixProjection p l) =O[f]
        (fun x => s x^2)) ∧
    ((fun x => defect ((S x)ᵀ*pairImages (S x) (A x))-
      ∑ l ∈ Finset.range (p-1), (prefixProjection p l*X0 x l-X0 x l*prefixProjection p l)) =O[f]
        (fun x => s x^2)) := by
  -- Establish a genuine quadratic remainder for each compressed increment before summing.
  dsimp only
  let D := fun l x => (S x)ᵀ*(A x (l+1)-A x l)*S x-Rᵀ*(A x (l+1)-A x l)*R
  have hd (l : ℕ) (hl : l<p) : D l =O[f] (fun x => s x^2) :=
    matrix_congruence_first_order S _ R s hs hS (hE l hl)
  have hc (l : ℕ) (hl : l<p) :
      (fun x => prefixProjection p l*D l x*prefixProjection p l) =O[f] (fun x => s x^2) :=
    matrix_mul_const_bigO _ _ _ (matrix_const_mul_bigO _ _ _ (hd l hl))
  have hk (l : ℕ) (hl : l<p) :
      (fun x => prefixProjection p l*D l x-D l x*prefixProjection p l) =O[f] (fun x => s x^2) :=
    (matrix_const_mul_bigO _ _ _ (hd l hl)).sub (matrix_mul_const_bigO _ _ _ (hd l hl))
  constructor
  · apply (matrix_sum_bigO (Finset.range p) _ _ (fun l hl => hc l (Finset.mem_range.mp hl))).congr_left
    intro x
    rw [(flag_identities (S x) (A x) (hA x)).1]
    simp only [D, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
  · apply (matrix_sum_bigO (Finset.range (p-1)) _ _
      (fun l hl => hk l (lt_of_lt_of_le (Finset.mem_range.mp hl) (Nat.sub_le p 1)))).congr_left
    intro x
    rw [(flag_identities (S x) (A x) (hA x)).2.1]
    simp only [D, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
    abel

/-- Actual secant observations differ from the reference Gram matrix by first order.
Use: establish the observed diagonal and defect orders from actual operator/step perturbations.
Article: main_krylov, apA:lem:flagcd(d), M_ii=c_i+O(s).
Proof: expand each compressed operator using actual rectangular product calculus;
the finite observation selects its own operator time in each actual column. -/
theorem observation_reference_order (S : α → Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin p) ℝ) (A : α → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (s : α → ℝ) (hs : Tendsto s f (𝓝 0)) (hS : (fun x => S x-R) =O[f] s)
    (hA : ∀ k<p, (fun x => A x k-1) =O[f] s) :
    (fun x => (S x)ᵀ*pairImages (S x) (A x)-Rᵀ*R) =O[f] s := by
  -- Each observed column selects its own finite operator time from the compressed trajectory.
  have ht : (fun x => (S x)ᵀ-Rᵀ) =O[f] s := by
    simpa only [transpose_sub] using matrix_transpose_bigO (fun x => S x-R) s hS
  have hc (k : ℕ) (hk : k<p) :
      (fun x => (S x)ᵀ*A x k*S x-Rᵀ*R) =O[f] s := by
    have h1 := matrix_product_first_order (fun x => (S x)ᵀ) (fun x => A x k) Rᵀ 1 s hs ht (hA k hk)
    have h2 := matrix_product_first_order (fun x => (S x)ᵀ*A x k) S (Rᵀ*1) R s hs h1 hS
    simpa only [Matrix.mul_one] using h2
  apply (matrix_bigO_iff_entry _ _).mpr
  intro i j
  have he := (matrix_bigO_iff_entry _ _).mp (hc j.val j.isLt) i j
  apply he.congr_left
  intro x
  rw [← observed_compression]
  rfl

/-- The true normalized canonical defect and model-error form have exactly the printed first-order flags.
Use: closes both first-order displayed identities from actual perturbed observations and increments.
Article: main_krylov, apA:lem:flagcd(d), both O(s²) matrix remainders.
Proof: the actual flag remainders have quadratic order; reference normalization
cancels the actual reference energies, while smooth observed normalization adds
only a quadratic term. Actual orthonormal columns identify the coordinate and spatial flags. -/
theorem canonical_flag_first_order (Q : Matrix (Fin n) (Fin p) ℝ) (hQ : Qᵀ*Q=1)
    (c : Fin p → ℝ) (hc : ∀ i, 0<c i)
    (S : α → Matrix (Fin n) (Fin p) ℝ) (A : α → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ x k, (A x k).IsSymm) (s : α → ℝ) (hs : Tendsto s f (𝓝 0))
    (hS : (fun x => S x-Q*diagonal (fun i => Real.sqrt (c i))) =O[f] s)
    (hpert : ∀ k≤p, (fun x => A x k-1) =O[f] s) :
    let M := fun x => (S x)ᵀ*pairImages (S x) (A x)
    let E := fun x l => A x (l+1)-A x l
    let P := fun l => Q*prefixProjection p l*Qᵀ
    ((fun x => canonicalDefect (M x)-Qᵀ*(∑ l ∈ Finset.range (p-1),
      (P l*E x l-E x l*P l))*Q) =O[f] (fun x => s x^2)) ∧
    ((fun x => fixedNormalize c ((S x)ᵀ*A x p*S x-latest (M x))-
      Qᵀ*(∑ l ∈ Finset.range p, P l*E x l*P l)*Q) =O[f] (fun x => s x^2)) := by
  -- Derive the diagonal and defect orders from the actual observations before normalizing them.
  let R := Q*diagonal (fun i => Real.sqrt (c i))
  let M := fun x => (S x)ᵀ*pairImages (S x) (A x)
  let E := fun x l => A x (l+1)-A x l
  let X := fun x l => Rᵀ*E x l*R
  have he (l : ℕ) (hl : l<p) : (fun x => E x l) =O[f] s := by
    apply ((hpert (l+1) (by omega)).sub (hpert l hl.le)).congr_left
    intro x
    dsimp only [E]
    abel
  have hraw := flag_reference_order S R A hA s hs hS he
  have hobs := observation_reference_order S R A s hs hS (fun k hk => hpert k hk.le)
  have hgram : Rᵀ*R=diagonal c := by
    simp only [R, transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul, diagonal_mul_diagonal]
    congr 1
    ext i
    exact Real.mul_self_sqrt (hc i).le
  rw [hgram] at hobs
  have hdiag (i : Fin p) : (fun x => M x i i-c i) =O[f] s := by
    simpa only [M, Matrix.sub_apply, diagonal_apply_eq] using (matrix_bigO_iff_entry _ _).mp hobs i i
  have hd : (fun x => defect (M x)) =O[f] s := by
    have ht := matrix_transpose_bigO (fun x => M x-diagonal c) s hobs
    apply (hobs.sub ht).congr_left
    intro x
    simp only [transpose_sub, diagonal_transpose, defect]
    abel
  have hn := canonicalDefect_normalization_order M c hc s hs hdiag hd
  have hnraw := fixedNormalize_bigO c _ (fun x => s x^2) hraw.2
  have hzraw := fixedNormalize_bigO c _ (fun x => s x^2) hraw.1
  have href (x : α) (l : ℕ) : fixedNormalize c (X x l)=Qᵀ*E x l*Q :=
    fixedNormalize_reference_compression Q c hc (E x l)
  have hsum (I : Finset ℕ) (Z : ℕ → Matrix (Fin p) (Fin p) ℝ) :
      fixedNormalize c (∑ l ∈ I, Z l)=∑ l ∈ I, fixedNormalize c (Z l) := by
    simp only [fixedNormalize_eq, Matrix.mul_sum, Matrix.sum_mul]
  have hsub (Z W : Matrix (Fin p) (Fin p) ℝ) :
      fixedNormalize c (Z-W)=fixedNormalize c Z-fixedNormalize c W := by
    simp only [fixedNormalize_eq, Matrix.mul_sub, Matrix.sub_mul]
  constructor
  · apply (hn.add hnraw).congr_left
    intro x
    dsimp only
    simp only [hsub, hsum]
    rw [sub_add_sub_cancel]
    congr 1
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    rw [← hsub, (fixedNormalize_flags c (X x l) l).2, href]
    exact (reference_flag_forms Q hQ (E x l) l).2
  · apply hzraw.congr_left
    intro x
    dsimp only
    rw [hsub, hsum]
    congr 1
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    rw [(fixedNormalize_flags c (X x l) l).1, href]
    exact (reference_flag_forms Q hQ (E x l) l).1

/-- The actual canonical data defect satisfies the sharp flag budget with its actual remainder.
Use: coupled with canonical_flag_first_order, the last term is O(s²), exactly
as in the article; each actual increment norm may be replaced by its stated budget.
Article: main_krylov, apA:lem:flagcd(d), final normalized-defect inequality.
Proof: add the actual first-order spatial flag sum and its actual remainder,
then use its proved sharp increment budget and the triangle inequality. -/
theorem canonical_defect_budget (Q : Matrix (Fin n) (Fin p) ℝ) (hQ : Qᵀ*Q=1)
    (M : Matrix (Fin p) (Fin p) ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hE : ∀ l, (E l).IsSymm) (ω : ℕ → ℝ) (hω : ∀ l<p-1, ‖E l‖≤ω l) :
    ‖canonicalDefect M‖ ≤ (∑ l ∈ Finset.range (p-1), ω l)+
      ‖canonicalDefect M-Qᵀ*(∑ l ∈ Finset.range (p-1),
        ((Q*prefixProjection p l*Qᵀ)*E l-E l*(Q*prefixProjection p l*Qᵀ)))*Q‖ := by
  have hb := reference_commutator_sum_bound Q hQ E hE (Finset.range (p-1))
  have hs := Finset.sum_le_sum (fun l hl => hω l (Finset.mem_range.mp hl))
  have ht := norm_le_norm_sub_add (canonicalDefect M)
    (Qᵀ*(∑ l ∈ Finset.range (p-1), ((Q*prefixProjection p l*Qᵀ)*E l-E l*(Q*prefixProjection p l*Qᵀ)))*Q)
  linarith

end
end krylov.Secant
