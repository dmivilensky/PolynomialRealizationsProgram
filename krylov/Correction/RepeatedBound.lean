import krylov.Correction.RepeatedCanonical

/-!
Article: main_krylov, thm:C2(b), the actual repeated-correction norm estimate.
Use: retain the sharp first-factor constant and bound only the subsequent
independently varying staircase factors by the total spectral budget.
Source: the proved sharp true-CG compression inequality, orthogonal projection
contraction and the actual canonical higher-order execution expansion.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Variation krylov.Envelope
  krylov.Methods krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The true staircase spectral norm is at most the total increment and terminal budget.
Use: control each factor after the sharp first factor in the repeated-correction estimate.
Article: main_krylov, thm:C2(b), ‖𝓛_p‖≤W₀+ω′.
Proof: each actual old-flag orthogonal projector has norm at most one;
submultiplicativity, the finite norm triangle inequality and the individual
true spectral budgets give the stated total. -/
theorem staircaseOperator_norm_le {n N : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (ω : ℕ → ℝ) {w : ℝ} (hω : ∀ i∈range (N-1), ‖E i‖≤ω i) (hw : ‖F‖≤w) :
    ‖staircaseOperator base g E F N‖≤(∑ i∈range (N-1), ω i)+w := by
  -- Projector contraction is used on both sides of each actual increment.
  apply (norm_add_le _ _).trans
  apply add_le_add _ (by simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using hw)
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  let P := (oldFlag base g i).starProjection
  have hP : ‖P‖≤1 := (oldFlag base g i).starProjection_norm_le
  have hE : ‖cgOperator (E i)‖≤ω i := by
    simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using hω i hi
  calc
    ‖P*cgOperator (E i)*P‖ ≤ ‖P‖*‖cgOperator (E i)‖*‖P‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1*‖cgOperator (E i)‖*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hP (norm_nonneg _)) hP (norm_nonneg _) (by positivity)
    _ ≤ ω i := by simpa only [one_mul,mul_one] using hE

/-- A nonempty ordered operator product keeps a sharp bound for its first action.
Use: subsequent correction factors contribute only powers of their common norm bound.
Article: main_krylov, thm:C2(b), (W₀+ω′)^(k_c−1)K(W₀,ω′).
Proof: induction applies the newest operator to the previous actual product;
no factors are commuted and the sharp first action is never replaced. -/
theorem orderedProduct_first_bound (L : ℕ → V →L[ℝ] V) (v : V) {B M : ℝ}
    (hB : 0≤B) (c : ℕ) (hfirst : ‖L 0 v‖≤M)
    (hL : ∀ j, 0<j → j<c+1 → ‖L j‖≤B) :
    ‖(chebyshev1.orderedProduct L (c+1)) v‖≤B^c*M := by
  -- The oldest, sharp first action is retained through the full induction.
  induction c with
  | zero => simpa only [chebyshev1.orderedProduct_succ,
      chebyshev1.orderedProduct_zero,mul_one,pow_zero,one_mul] using hfirst
  | succ c ih =>
    rw [chebyshev1.orderedProduct_succ,mul_apply_eq_comp]
    calc
      _ ≤ ‖L (c+1)‖*‖(chebyshev1.orderedProduct L (c+1)) v‖ := (L (c+1)).le_opNorm _
      _ ≤ B*(B^c*M) := mul_le_mul (hL _ (by omega) (by omega))
        (ih (fun j hj hjc => hL j hj (by omega))) (norm_nonneg _) hB
      _ = _ := by ring

omit [NormedSpace ℝ X] [NormedSpace ℝ V] in
/-- A proved higher-order vector remainder transfers any exact leading norm bound to the actual output.
Use: expose a positive remainder constant for arbitrary repeated-correction orders.
Article: main_krylov, thm:C2(b), norm estimate from the actual vector expansion.
Proof: the actual vector is its leading term plus the proved remainder;
the norm triangle inequality and the genuine big-O bound give the estimate. -/
theorem remainder_norm_upper (u v : X → V) (M : X → ℝ) (order : ℕ)
    (hr : (fun z => u z-v z) =O[𝓝 (0 : X)] (fun z => ‖z‖^order))
    (hv : ∀ z, ‖v z‖≤M z) :
    ∃ C>0, ∀ᶠ z in 𝓝 (0 : X), ‖u z‖≤M z+C*‖z‖^order := by
  obtain ⟨C,hC,hrC⟩ := isBigO_iff'.mp hr
  refine ⟨C,hC,?_⟩
  filter_upwards [hrC] with z hz
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] at hz
  have ht : ‖u z‖≤‖v z‖+‖u z-v z‖ := by
    simpa only [add_sub_cancel] using norm_add_le (v z) (u z-v z)
  exact ht.trans (add_le_add (hv z) hz)

/-- The genuine repeated-RFC terminal gradient satisfies the source sharp first-factor spectral estimate.
Use: each independently varying terminal query has its own budget, with one common upper budget w.
Article: main_krylov, thm:C2(b), ‖g_n‖_(A⁻¹)≤(W₀+ω′)^(k_c−1)K(W₀,ω′)‖e_last‖_A+O(ω^(k_c+2)).
Proof: the actual canonical execution expansion supplies the higher-order
remainder. The first true staircase action has the sharp K bound; every
subsequent true factor has norm at most W₀+w. The ordered-product estimate
and genuine full-CG last-step/error identity give the stated result.
-/
theorem full_repeated_canonical_spectral_upper {k : ℕ} (count : ℕ) (hc : 0<count)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (E F : X → ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (T : ℕ → X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hE : ∀ i, AnalyticAt ℝ (fun z => E z i) 0)
    (hF : ∀ i, AnalyticAt ℝ (fun z => F z i) 0)
    (hT : ∀ j<count, AnalyticAt ℝ (T j) 0)
    (hE0 : ∀ i, E 0 i=0) (hF0 : ∀ i, F 0 i=0)
    (hT0 : ∀ j<count, T j 0=0) (hEsym : ∀ z i, (E z i).IsSymm)
    (ω : X → ℕ → ℝ) (w : X → ℝ)
    (hω : ∀ z, ∀ i∈range k, ‖E z i‖≤ω z i)
    (hw : ∀ z, ∀ j<count, ‖T j z‖≤w z) :
    let A := fun z => canonicalFCPath base (E z) 1
    let B := fun z i => canonicalCorrectionOperator base (E z) (F z i) i
    let C := fun j z => canonicalCorrectionOperator base (E z) (T j z) k
    ∃ D>0, ∀ᶠ z in 𝓝 (0 : X),
      ‖cgOperator (metricRoot base)⁻¹
        (repeatedTerminalResult count (A z) (B z) g k (fun j => C j z)).gradient‖≤
        ‖cgCanonicalError base g k‖*((∑ i∈range k, ω z i)+w z)^(count-1)*
          sharpConstant (∑ i∈range k, ω z i) (w z)+D*‖z‖^(count+2) := by
  -- Keep the sharp first action when extracting the actual remainder norm.
  apply remainder_norm_upper _ _ _ (count+2)
    (full_repeated_canonical_order count hc base hb g hN hk E F T hE hF hT hE0 hF0 hT0 hEsym)
  intro z
  let W := ∑ i∈range k, ω z i
  have hW : 0≤W := sum_nonneg fun i hi => (norm_nonneg _).trans (hω z i hi)
  have hw₀ : 0≤w z := (norm_nonneg _).trans (hw z 0 hc)
  have hfirst : ‖staircaseOperator base g (E z) (T 0 z) (k+1)
      (freshDefect base g (E z) (k+1))‖≤sharpConstant W (w z) := by
    simpa only [Nat.add_sub_cancel] using (reference_second_order_bound base hb g hN
      (by omega : 0<k+1) (E z) (fun i _ => hEsym z i) (T 0 z) (ω z) (hω z) (hw z 0 hc))
  have hbnd := orderedProduct_first_bound
    (fun j => staircaseOperator base g (E z) (T j z) (k+1))
    (freshDefect base g (E z) (k+1)) (add_nonneg hW hw₀) (count-1)
    hfirst
    (fun j _ hj => by
      simpa only [Nat.add_sub_cancel] using staircaseOperator_norm_le (N := k+1) base g (E z) (T j z)
        (ω z) (hω z) (hw z j (by omega)))
  rw [show count-1+1=count by omega] at hbnd
  rw [norm_smul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Real.norm_of_nonneg (norm_nonneg _),terminal_step_error_norm base hb g hN]
  exact (mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)).trans_eq (by ring)

end
end krylov.Correction
