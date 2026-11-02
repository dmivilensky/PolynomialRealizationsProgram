import krylov.Correction.CanonicalExpansion

/-!
Article: main_krylov, thm:C and thm:C2(a), sharp upper bounds for the actual cycle.
Use: combine the proved genuine canonical output expansion with the sharp
actual-CG compression bounds in the original spectral and Frobenius budgets.
Source: the actual cubic remainder, true penultimate reference error scale
and the elementary norm triangle inequality; no leading coefficient is assumed.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Variation krylov.Envelope
  krylov.Methods krylov.Secant krylov.Stability
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V]

omit [NormedSpace ℝ X] in
/-- A true cubic remainder and a proved leading norm bound give an eventual norm estimate with a positive remainder constant.
Use: transfer the actual geometric bound to the actual returned gradient.
Article: main_krylov, thm:C, norm estimate from the cubic expansion.
Proof: subtract the true leading vector from the actual remainder, use the
triangle inequality and unpack the already proved big-O bound. -/
theorem cubic_remainder_norm_upper (u v : X → V) (M : X → ℝ)
    (hr : (fun z => u z+v z) =O[𝓝 (0 : X)] (fun z => ‖z‖^3))
    (hv : ∀ z, ‖v z‖≤M z) :
    ∃ C>0, ∀ᶠ z in 𝓝 (0 : X), ‖u z‖≤M z+C*‖z‖^3 := by
  -- The actual residual is the cubic remainder minus its known leading vector.
  obtain ⟨C,hC,hrC⟩ := isBigO_iff'.mp hr
  refine ⟨C,hC,?_⟩
  filter_upwards [hrC] with z hz
  have ht : ‖u z‖≤‖u z+v z‖+‖v z‖ := by
    calc
      _ = ‖(u z+v z)-v z‖ := by rw [add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  have hs : ‖‖z‖^3‖=‖z‖^3 := Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)
  rw [hs] at hz
  exact ht.trans ((add_le_add hz (hv z)).trans_eq (add_comm _ _))

/-- The actual RFC terminal gradient satisfies the source sharp spectral leading bound with a genuine cubic error.
Use: the original individual canonical increment and terminal budgets bound the real algorithm output.
Article: main_krylov, thm:C, ‖g_n‖_(A⁻¹)≤K(W₀,ω′)‖e_(n−1)‖_A+O(ω³).
Proof: the actual canonical expansion has the genuine cubic remainder.
The actual reference sharp compression bound controls its leading vector;
actual full CG termination identifies its step norm with the penultimate error norm. -/
theorem full_canonical_spectral_upper {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (E F : X → ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hE : ∀ i, AnalyticAt ℝ (fun z => E z i) 0)
    (hF : ∀ i, AnalyticAt ℝ (fun z => F z i) 0)
    (hE0 : ∀ i, E 0 i=0) (hF0 : ∀ i, F 0 i=0)
    (hEsym : ∀ z i, (E z i).IsSymm)
    (ω : X → ℕ → ℝ) (w : X → ℝ)
    (hω : ∀ z, ∀ i∈range k, ‖E z i‖≤ω z i) (hw : ∀ z, ‖F z k‖≤w z) :
    let A := fun z => canonicalFCPath base (E z) 1
    let B := fun z i => canonicalCorrectionOperator base (E z) (F z i) i
    ∃ C>0, ∀ᶠ z in 𝓝 (0 : X),
      ‖cgOperator (metricRoot base)⁻¹
        (probedGradient (rfcMethod fullMemory 1) (A z) (B z) g (k+1))‖≤
        ‖cgCanonicalError base g k‖*sharpConstant (∑ i∈range k, ω z i) (w z)+C*‖z‖^3 := by
  -- The bound concerns the exact same genuine output and coefficient as the executed expansion.
  apply cubic_remainder_norm_upper _ _ _
    (full_canonical_second_order base hb g hN hk E F hE hF hE0 hF0 hEsym)
  intro z
  rw [norm_smul,Real.norm_of_nonneg (norm_nonneg _),terminal_step_error_norm base hb g hN]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [Nat.add_sub_cancel] using reference_second_order_bound base hb g hN
    (by omega : 0<k+1) (E z) (fun i _ => hEsym z i) (F z k) (ω z) (hω z) (hw z)

/-- The real RFC terminal gradient has the source square-root-two improved Frobenius leading bound and a genuine cubic error.
Use: the improvement is proved for actual returned gradients in the actual reference metric.
Article: main_krylov, thm:C2(a), K(W₀,ω′)‖e_(n−1)‖_A/√2+O(ω³).
Proof: the same real output expansion applies. The genuine reference
Frobenius compression theorem controls its leading vector; divide by the
positive square root of two and retain the independently proved cubic remainder. -/
theorem full_canonical_frobenius_upper {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (E F : X → ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hE : ∀ i, AnalyticAt ℝ (fun z => E z i) 0)
    (hF : ∀ i, AnalyticAt ℝ (fun z => F z i) 0)
    (hE0 : ∀ i, E 0 i=0) (hF0 : ∀ i, F 0 i=0)
    (hEsym : ∀ z i, (E z i).IsSymm)
    (ω : X → ℕ → ℝ) (w : X → ℝ)
    (hω : ∀ z, ∀ i∈range k, chebyshev1.hsNorm (E z i)≤ω z i)
    (hw : ∀ z, chebyshev1.hsNorm (F z k)≤w z) :
    let A := fun z => canonicalFCPath base (E z) 1
    let B := fun z i => canonicalCorrectionOperator base (E z) (F z i) i
    ∃ C>0, ∀ᶠ z in 𝓝 (0 : X),
      ‖cgOperator (metricRoot base)⁻¹
        (probedGradient (rfcMethod fullMemory 1) (A z) (B z) g (k+1))‖≤
        ‖cgCanonicalError base g k‖*(sharpConstant (∑ i∈range k, ω z i) (w z)/Real.sqrt 2)+C*‖z‖^3 := by
  -- The changed norm budgets affect the leading coefficient, while the actual cubic expansion is shared.
  apply cubic_remainder_norm_upper _ _ _
    (full_canonical_second_order base hb g hN hk E F hE hF hE0 hF0 hEsym)
  intro z
  rw [norm_smul,Real.norm_of_nonneg (norm_nonneg _),terminal_step_error_norm base hb g hN]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2))).mpr
  simpa only [Nat.add_sub_cancel,mul_comm] using reference_frobenius_second_order_bound base hb g hN
    (by omega : 0<k+1) (E z) (fun i _ => hEsym z i) (F z k) (ω z) (hω z) (hw z)

end
end krylov.Correction
