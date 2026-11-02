import krylov.Correction.GatedRecordedBounds
import krylov.Stability.UniformLineSearch

/-!
Article: main_krylov, thm:UCg, genuine uniform search and correction growth.
Use: Bound the actual accepted or skipped spectral-gated phase by its real
incoming gradient, independently of individual step lengths and CG energies.
Source: true normalized measured-model inverse and synthesis bounds,
Cauchy--Schwarz and the original exact line-search quotient.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual coefficient-model correction has a dimension-and-gate bound proportional to its true incoming gradient.
Use: Control actual finite gated-RFC prefixes after a small intermediate line step.
Article: main_krylov, thm:UCg, genuine uniform phase growth.
Proof: The measured gate gives the true unit-step model lower endpoint γ/2. Unit-step Gram and coordinate norms are bounded by the dimension; combine the genuine normalized inverse and physical synthesis estimates.
-/
theorem observed_gate_correction_gradient {p : ℕ} (s y : Fin p → E) (g : E)
    (he : ∀ i, 0 < inner ℝ (s i) (y i)) {γ η : ℝ} (hγ : 0<γ)
    (hhalf : η≤1/2) (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖)
    (hgate : ∀ i, γ≤(observedPairModel_hermitian s y).eigenvalues i) :
    ‖combine s (modelCoefficients s (pairModel s y) g)‖≤(2*(p : ℝ)/γ)*‖g‖ := by
  have hs := positive_pair_steps_ne s y he
  have hlo : ∀ i, γ/2≤(rescale_pairModel_isHermitian s y (fun j => ‖s j‖⁻¹)).eigenvalues i := by
    intro i
    have ht := observed_gate_unit_model_lower s y he hγ.le hy hgate i
    nlinarith [mul_le_mul_of_nonneg_left hhalf hγ.le]
  have hinv := (inverse_bound_of_eigenvalues _ (rescale_pairModel_isHermitian s y _)
    (by positivity : 0<γ/2) hlo).2
  have hρ : ‖projectedResidual (unitWindow s) g‖≤Real.sqrt p*‖g‖ := by
    apply coordinate_norm_le_sqrt_card _ (norm_nonneg g)
    intro i
    have ht := norm_inner_le_norm (𝕜 := ℝ) (unitWindow s i) g
    simpa only [coordinates,Real.norm_eq_abs,unitWindow_norm s hs i,one_mul] using ht
  have hm := normalizedCorrection_movement_bound s (pairModel s y) (fun i => ‖s i‖⁻¹)
    (unitWindow_diagonal_unit s hs) g (Nat.cast_nonneg p) (unit_window_gram_norm_le s hs)
  change ‖combine s (modelCoefficients s (pairModel s y) g)‖≤
    Real.sqrt p*‖(rescaleModel (pairModel s y) (fun i => ‖s i‖⁻¹))⁻¹‖*‖projectedResidual (unitWindow s) g‖ at hm
  calc
    _ ≤ Real.sqrt p*(γ/2)⁻¹*(Real.sqrt p*‖g‖) := hm.trans (by gcongr)
    _ = (Real.sqrt p)^2*(γ/2)⁻¹*‖g‖ := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg p)]; field_simp

/-- Every genuine exact-search line displacement is bounded by twice the incoming gradient for an operator within one half of the identity.
Use: Control actual finite gated-RFC prefixes after a small intermediate line step.
Article: main_krylov, thm:UCg, genuine uniform phase growth.
Proof: Separate the zero direction. The actual normalized direction has curvature at least one half, and Cauchy--Schwarz bounds its true search numerator.
-/
theorem actual_line_norm_bound (A : E →L[ℝ] E) (g d : E) {η : ℝ}
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤η) (hhalf : η≤1/2) :
    ‖lineLength g d (A d) • d‖≤2*‖g‖ := by
  by_cases hd : d=0
  · simp only [hd,smul_zero,norm_zero]
    positivity
  let u := NormedSpace.normalize d
  have hu : ‖u‖=1 := NormedSpace.norm_normalize hd
  have hden : (1/2 : ℝ)≤ inner ℝ u (A u) := by
    have h := (abs_le.mp (unit_curvature_error A u hu hA)).1
    linarith
  have hpos : 0 < inner ℝ u (A u) := lt_of_lt_of_le (by norm_num) hden
  have hi : |inner ℝ u g|≤‖g‖ := by
    simpa only [Real.norm_eq_abs,hu,one_mul] using norm_inner_le_norm (𝕜 := ℝ) u g
  rw [lineStep_eq_unitLineUpdate A g d hd,unitLineUpdate_eq_line A g u,norm_smul,
    Real.norm_eq_abs,hu,mul_one,lineLength,abs_div,abs_neg,abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  nlinarith [norm_nonneg g]

/-- Every genuine operator within one half of the identity has norm at most two.
Use: Control actual finite gated-RFC prefixes after a small intermediate line step.
Article: main_krylov, thm:UCg, genuine uniform phase growth.
Proof: Apply the operator-norm triangle inequality and the true identity norm bound, including a zero-dimensional space.
-/
theorem near_identity_operator_norm (A : E →L[ℝ] E) {η : ℝ}
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤η) (hhalf : η≤1/2) : ‖A‖≤2 := by
  have h := norm_le_norm_sub_add A (ContinuousLinearMap.id ℝ E)
  have hi : ‖ContinuousLinearMap.id ℝ E‖≤1 := ContinuousLinearMap.norm_id_le
  linarith

/-- The true post-search gradient is at most five times the actual incoming gradient under the same near-identity operator bound.
Use: Control actual finite gated-RFC prefixes after a small intermediate line step.
Article: main_krylov, thm:UCg, genuine uniform phase growth.
Proof: The actual line is bounded by twice the gradient and its true operator image by four times the gradient; add the genuine incoming vector.
-/
theorem actual_searched_gradient_norm (A : E →L[ℝ] E) (g d : E) {η : ℝ}
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤η) (hhalf : η≤1/2) :
    ‖searchedGradient g d (A d)‖≤5*‖g‖ := by
  have hl := actual_line_norm_bound A g d hA hhalf
  have hnorm := near_identity_operator_norm A hA hhalf
  have ha := (A.le_opNorm (lineLength g d (A d) • d)).trans
    (mul_le_mul hnorm hl (norm_nonneg _) (by norm_num : (0 : ℝ)≤2))
  have ht := norm_add_le g (A (lineLength g d (A d) • d))
  rw [map_smul] at ht ha
  exact ht.trans (by linarith)

/-- The actual finite spectral-gated RFC phase has one uniform incoming-gradient growth bound through every real accepted and fallback branch.
Use: Control actual finite gated-RFC prefixes after a small intermediate line step.
Article: main_krylov, thm:UCg, genuine uniform phase growth.
Proof: The genuine measured spectral test bounds the actual correction by the searched gradient. The proved exact-search bound and real correction-operator norm control the true returned gradient. Both rejected branches retain their actual zero movement and searched gradient.
-/
theorem gatedArrayPhase_growth {p N : ℕ} (S Y : Fin p → E) (g d : E)
    (A B : E →L[ℝ] E) {γ η : ℝ} (hγ : 0<γ) (hsize : p+1≤N)
    (hhalf : η≤1/2) (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤η)
    (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤η) (hy : ∀ i, ‖Y i-S i‖≤η*‖S i‖) :
    ‖(gatedArrayPhase γ S Y g d (A d) B).movement‖≤(10+2*(10*(N : ℝ)/γ))*‖g‖ ∧
      ‖(gatedArrayPhase γ S Y g d (A d) B).gradient‖≤(10+2*(10*(N : ℝ)/γ))*‖g‖ := by
  classical
  have hN : 0≤(N : ℝ) := Nat.cast_nonneg N
  have hterm : 0≤10*(N : ℝ)/γ := by positivity
  have hC : 5≤10+2*(10*(N : ℝ)/γ) := by linarith
  have hg := actual_searched_gradient_norm A g d hA hhalf
  have hzero : 0≤(10+2*(10*(N : ℝ)/γ))*‖g‖ := by positivity
  by_cases hgate : matrixSpectralGate γ (pairModel (Fin.cons d S) (Fin.cons (A d) Y))
  · obtain ⟨he,hherm,heigen⟩ := hgate
    have henergy (i : Fin (p+1)) : 0 < inner ℝ ((Fin.cons d S : Fin (p+1) → E) i)
        ((Fin.cons (A d) Y : Fin (p+1) → E) i) := by
      simpa only [pairModel,max_self,min_self] using he i
    have heigen' : ∀ i, γ≤(observedPairModel_hermitian (Fin.cons d S) (Fin.cons (A d) Y)).eigenvalues i := by
      simpa only [diagonalNormalizedModel,observedPairModel,pairModel,max_self,min_self] using heigen
    have hdiff (i : Fin (p+1)) : ‖(Fin.cons (A d) Y : Fin (p+1) → E) i-
        (Fin.cons d S : Fin (p+1) → E) i‖≤η*‖(Fin.cons d S : Fin (p+1) → E) i‖ := by
      refine Fin.cases ?_ (fun j => hy j) i
      simpa only [Fin.cons_zero,_root_.sub_apply,ContinuousLinearMap.id_apply] using
        ((A-ContinuousLinearMap.id ℝ E).le_opNorm d).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg d))
    have hm := observed_gate_correction_gradient (Fin.cons d S) (Fin.cons (A d) Y)
      (searchedGradient g d (A d)) henergy hγ hhalf hdiff heigen'
    have hpN : ((p+1 : ℕ) : ℝ)≤N := by exact_mod_cast hsize
    have hm' : ‖combine (Fin.cons d S) (modelCoefficients (Fin.cons d S)
        (pairModel (Fin.cons d S) (Fin.cons (A d) Y)) (searchedGradient g d (A d)))‖≤(10*(N : ℝ)/γ)*‖g‖ := by
      have h := mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpN (by norm_num : (0 : ℝ)≤2)) hγ.le)
        hg (norm_nonneg _) (by positivity : 0≤2*(N : ℝ)/γ)
      exact hm.trans (h.trans_eq (by ring))
    unfold gatedArrayPhase
    rw [ite_eq_left ⟨he,hherm,heigen⟩]
    unfold rfcArrayPhase
    split
    · change ‖_+0‖≤_ ∧ ‖searchedGradient g d (A d)+B (combine _ (modelCoefficients _ _ _))‖≤_
      rw [add_zero]
      have hn := near_identity_operator_norm B hB hhalf
      have hb := (B.le_opNorm (combine _ (modelCoefficients _ _ _))).trans
        (mul_le_mul hn hm' (norm_nonneg _) (by norm_num : (0 : ℝ)≤2))
      constructor
      · exact hm'.trans (by nlinarith [norm_nonneg g])
      · exact (norm_add_le _ _).trans (by nlinarith [norm_nonneg g])
    · exact ⟨by simpa only [norm_zero] using hzero,hg.trans (mul_le_mul_of_nonneg_right hC (norm_nonneg g))⟩
  · unfold gatedArrayPhase
    rw [ite_eq_right hgate]
    exact ⟨by simpa only [norm_zero] using hzero,hg.trans (mul_le_mul_of_nonneg_right hC (norm_nonneg g))⟩

end
end krylov.Correction
