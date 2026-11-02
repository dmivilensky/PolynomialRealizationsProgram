import bezout.Gains.Bounds
import bezout.Lower.EndpointGain
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Article: bezout, Theorem 4.1, the two-eigenspace lower witnesses.
Use: actual symmetric Hessian perturbations force the temporal norm of every
fixed spectral-pair kernel, hence the endpoint parity-corrected lower gain.
Proof: diagonal quadratic Hessians and norm-one coordinate interchanges reduce
physical first variations to scalar temporal inner products.
-/

namespace bezout.Gains
noncomputable section
open Polynomial
open scoped BigOperators

/-- The real two-dimensional Hilbert space used by endpoint witnesses.
Use: both prescribed spectral endpoints occur in a literal quadratic Hessian. -/
abbrev WitnessSpace := EuclideanSpace ℝ (Fin 2)

/-- A diagonal two-coordinate quadratic Hessian.
Use: independent input and output spectral points in the physical kernel. -/
def diagonalOperator (d : Fin 2 → ℝ) : WitnessSpace →ₗ[ℝ] WitnessSpace where
  toFun v := WithLp.toLp 2 (fun i => d i * v i)
  map_add' v w := by ext i; simp [mul_add]
  map_smul' c v := by ext i; simp; ring

/-- Coordinate action of the witness Hessian.
Use: exact polynomial action and admissibility. -/
@[simp] theorem diagonalOperator_apply (d : Fin 2 → ℝ) (v : WitnessSpace) (i : Fin 2) :
    diagonalOperator d v i = d i * v i := rfl

/-- The diagonal witness is a symmetric real Hessian.
Use: the admissible quadratic comparison class. -/
theorem diagonalOperator_symmetric (d : Fin 2 → ℝ) : (diagonalOperator d).IsSymmetric := by
  intro v w
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

/-- Every eigenvalue of the witness is one of its prescribed coordinates.
Use: admissibility with repeated or distinct spectral points. -/
theorem diagonalOperator_admissible (I : chebyshev1.SpectralInterval) (d : Fin 2 → ℝ)
    (hd : ∀ i, d i ∈ Set.Icc I.mu I.L) : Analysis.Admissible I (diagonalOperator d) := by
  refine ⟨diagonalOperator_symmetric d, ?_⟩
  intro lam hlam
  obtain ⟨v, hv⟩ := hlam.exists_hasEigenvector
  have he := hv.apply_eq_smul
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hv.2 (by ext i; exact hn i)
  have hei := congrArg (fun w : WitnessSpace => w i) he
  simp only [diagonalOperator_apply, PiLp.smul_apply, smul_eq_mul] at hei
  have hl : d i = lam := mul_right_cancel₀ hi hei
  simpa only [hl] using hd i

/-- Polynomial actions on the diagonal witness act coordinatewise.
Use: exact physical query and response values in a genuine execution. -/
theorem diagonalOperator_polynomial (d : Fin 2 → ℝ) (p : ℝ[X])
    (v : WitnessSpace) (i : Fin 2) :
    ((aeval (diagonalOperator d) p) v) i = p.eval (d i) * v i := by
  have hpow (n : ℕ) (w : WitnessSpace) :
      (((diagonalOperator d) ^ n) w) i = (d i) ^ n * w i := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, diagonalOperator_apply, ih]
      ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, PiLp.add_apply, hp, hq, eval_add, add_mul]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      PiLp.smul_apply, smul_eq_mul, eval_monomial, hpow]
    ring

/-- The norm-preserving interchange of the two witness eigenspaces.
Use: symmetric perturbations couple any ordered spectral pair. -/
def swapIsometry : WitnessSpace ≃ₗᵢ[ℝ] WitnessSpace :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)

/-- The coordinate interchange as a physical Hessian perturbation.
Use: its operator norm is exactly one. -/
def swapOperator : WitnessSpace →ₗ[ℝ] WitnessSpace := swapIsometry.toLinearMap

/-- The first coordinate after the interchange is the second coordinate.
Use: the output spectral eigenspace of a fixed-pair witness. -/
@[simp] theorem swapOperator_zero (v : WitnessSpace) : swapOperator v 0 = v 1 := by
  simp [swapOperator, swapIsometry, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- The second coordinate after the interchange is the first coordinate.
Use: symmetry of the physical coupling perturbation. -/
@[simp] theorem swapOperator_one (v : WitnessSpace) : swapOperator v 1 = v 0 := by
  simp [swapOperator, swapIsometry, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- The coordinate interchange is a symmetric Hessian perturbation.
Use: the same witness applies to both operator-norm comparison classes. -/
theorem swapOperator_symmetric : swapOperator.IsSymmetric := by
  intro v w
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

/-- Its physical continuous operator norm is exactly one.
Use: temporal coefficient vectors are exactly the perturbation budgets. -/
@[simp] theorem swapOperator_norm : ‖swapOperator.toContinuousLinearMap‖ = 1 := by
  change ‖swapIsometry.toLinearIsometry.toContinuousLinearMap‖ = 1
  exact swapIsometry.toLinearIsometry.norm_toContinuousLinearMap

/-- A scaled coordinate interchange has precisely its scalar operator norm.
Use: enforces the physical temporal operator-norm budget. -/
theorem scaledSwap_norm (c : ℝ) :
    ‖(c • swapOperator).toContinuousLinearMap‖ = |c| := by
  have he : (c • swapOperator).toContinuousLinearMap = c • swapOperator.toContinuousLinearMap := by
    ext v
    rfl
  rw [he, norm_smul, swapOperator_norm, mul_one, Real.norm_eq_abs]

/-- A witness coordinate never exceeds the Hilbert norm.
Use: a scalar physical first-variation coordinate is a valid output lower bound. -/
theorem witness_coordinate_le_norm (v : WitnessSpace) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have h := EuclideanSpace.norm_sq_eq v
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at h
  fin_cases i
  · change |v 0| ≤ ‖v‖
    apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (v 1)]
  · change |v 1| ≤ ‖v‖
    apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (v 0)]

/-- The first output coordinate is exactly the temporal fixed-pair kernel pairing.
Use: the witness consists of actual symmetric perturbation maps. -/
theorem firstVariation_swap_coordinate {N : ℕ} (h : bezout.History N) (x y : ℝ)
    (c : Fin N → ℝ) :
    h.firstVariation (diagonalOperator ![x, y]) (fun s => c s • swapOperator)
      (EuclideanSpace.single 1 1) 0 =
      ∑ s, c s * bezout.Lower.physicalKernel h s x y := by
  simp only [bezout.History.firstVariation, bezout.History.variationNoise,
    WithLp.ofLp_sum, Finset.sum_apply, diagonalOperator_polynomial, LinearMap.smul_apply,
    PiLp.smul_apply, smul_eq_mul, swapOperator_zero, EuclideanSpace.single, PiLp.single_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ite_true,
    mul_one, bezout.Lower.physicalKernel]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Any universal first-variation bound controls every temporal kernel pairing.
Use: the same physical witness works with or without a symmetry restriction. -/
theorem operatorBound_kernel_pairing {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (symmetric : Bool) (C : ℝ)
    (hb : OperatorBound h I symmetric C) (x y : ℝ)
    (hx : x ∈ Set.Icc I.mu I.L) (hy : y ∈ Set.Icc I.mu I.L)
    (c : Fin N → ℝ) (hc : ∑ s, c s ^ 2 ≤ 1) :
    |∑ s, c s * bezout.Lower.physicalKernel h s x y| ≤ C := by
  have hH : Analysis.Admissible I (diagonalOperator ![x, y]) :=
    diagonalOperator_admissible I _ (by intro i; fin_cases i; exact hx; exact hy)
  have hD : ∑ s, ‖(c s • swapOperator).toContinuousLinearMap‖ ^ 2 ≤ 1 := by
    simpa only [scaledSwap_norm, sq_abs] using hc
  have hu := hb WitnessSpace (diagonalOperator ![x, y]) hH
    (fun s => c s • swapOperator) (fun _ s => LinearMap.IsSymmetric.smul (by simp) swapOperator_symmetric) hD
    (EuclideanSpace.single 1 1) (by simp)
  rw [← firstVariation_swap_coordinate]
  exact (witness_coordinate_le_norm _ 0).trans hu

/-- Every universal operator bound dominates each physical kernel's temporal norm.
Use: converts algebraic four-corner bounds into dimension-uniform actual gains. -/
theorem operatorBound_kernel_norm {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (symmetric : Bool) (C : ℝ)
    (hb : OperatorBound h I symmetric C) (x y : ℝ)
    (hx : x ∈ Set.Icc I.mu I.L) (hy : y ∈ Set.Icc I.mu I.L) :
    Real.sqrt (bezout.Lower.physicalKernelSq h x y) ≤ C := by
  let a : Fin N → ℝ := fun s => bezout.Lower.physicalKernel h s x y
  let e := Analysis.energyNorm a
  have he0 : 0 ≤ e := Analysis.energyNorm_nonneg a
  have hes : e ^ 2 = ∑ s, a s ^ 2 := Analysis.energyNorm_sq a
  change e ≤ C
  by_cases he : e = 0
  · rw [he]
    exact operatorBound_nonneg h I symmetric C hb
  · have hc : (∑ s, (a s / e) ^ 2) ≤ 1 := by
      simp only [div_pow, ← Finset.sum_div, ← hes]
      field_simp
      norm_num
    have hs : (∑ s, a s / e * bezout.Lower.physicalKernel h s x y) = e := by
      change (∑ s, a s / e * a s) = e
      simp_rw [show ∀ s, a s / e * a s = a s ^ 2 / e by intro s; ring]
      rw [← Finset.sum_div, ← hes]
      field_simp
    have hp := operatorBound_kernel_pairing h I symmetric C hb x y hx hy (fun s => a s / e) hc
    rw [hs, abs_of_nonneg he0] at hp
    exact hp

/-- The article's sharp parity-corrected lower gain holds for every universal bound.
Use: takes the infimum only after a literal physical witness has been constructed. -/
theorem linearGain_le_operatorBound {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N)
    (symmetric : Bool) (C : ℝ) (hb : OperatorBound h I symmetric C) :
    bezout.Lower.linearGain I N ≤ C := by
  obtain ⟨x, y, hx, hy, hxy⟩ := bezout.Lower.exists_endpoint_gain_lower h I he hN
  have hxi : x ∈ Set.Icc I.mu I.L := by rcases hx with rfl | rfl <;> exact ⟨by linarith [I.mu_lt_L], by linarith [I.mu_lt_L]⟩
  have hyi : y ∈ Set.Icc I.mu I.L := by rcases hy with rfl | rfl <;> exact ⟨by linarith [I.mu_lt_L], by linarith [I.mu_lt_L]⟩
  exact hxy.trans (operatorBound_kernel_norm h I symmetric C hb x y hxi hyi)

/-- The sharp lower gain applies to both universal operator-norm comparison classes.
Use: the unrestricted and symmetric operator versions of Theorem 4.1. -/
theorem linearGain_le_operatorGain {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N)
    (symmetric : Bool) : bezout.Lower.linearGain I N ≤ operatorGain h I symmetric := by
  apply le_csInf (operatorBounds_nonempty h I symmetric)
  intro C hC
  exact linearGain_le_operatorBound h I he hN symmetric C hC

/-- Relative-error bounds for actual queries dominate all physical first variations.
Use: passes from the local relative-error model to the operator-norm witnesses,
with the dimension supremum kept outside the small-scale limit. -/
theorem localRelativeBound_operatorBound {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (C : ℝ) (hb : LocalRelativeBound h I C)
    (symmetric : Bool) : OperatorBound h I symmetric C := by
  intro E _ _ _ H hH D _ hD initial hi
  let noise (t : ℝ) (s : Fin N) := t • D s
    (h.oracleQuery initial (bezout.History.perturbedOracle H D t) s)
  let u (t : ℝ) : h.Execution H initial (noise t) := {
    query := h.oracleQuery initial (bezout.History.perturbedOracle H D t)
    answer := h.oracleAnswers initial (bezout.History.perturbedOracle H D t)
    query_eq := fun _ => rfl
    answer_eq := fun s => h.oracleAnswers_eq initial _ s }
  let f (t : ℝ) := h.oracleOutput initial (bezout.History.perturbedOracle H D t)
  have huoutput (t : ℝ) : (u t).output = f t := rfl
  have hzero : f 0 = (aeval H h.terminal) initial := by
    have hn : noise 0 = fun _ => 0 := by funext s; simp [noise]
    have hz := h.physical_response H initial (noise 0) (u 0)
    rw [huoutput, hn] at hz
    simpa only [map_zero, Finset.sum_const_zero, add_zero] using hz
  have hder := h.hasDerivAt_perturbed_output H D initial
  have hlimit := hder.tendsto_slope_zero_right.norm
  change Filter.Tendsto (fun t => ‖t⁻¹ • (f (0 + t) - f 0)‖)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds ‖h.firstVariation H D initial‖) at hlimit
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨t0, ht0, ht⟩ := hb ε hε
  apply le_of_tendsto hlimit
  have hsmall : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < t0 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds ht0)
  filter_upwards [self_mem_nhdsWithin, hsmall] with t htpos htt
  have htpos : 0 < t := htpos
  have hw : Analysis.RelativeErrors h H initial (noise t) (u t) t
      (fun s => ‖(D s).toContinuousLinearMap‖) := by
    refine ⟨fun _ => norm_nonneg _, hD, ?_⟩
    intro s
    change ‖t • D s ((u t).query s)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact (mul_le_mul_of_nonneg_left ((D s).toContinuousLinearMap.le_opNorm _) htpos.le).trans_eq (by ring)
  have hout := ht t htpos htt E H hH initial (noise t) (u t)
    (fun s => ‖(D s).toContinuousLinearMap‖) hi hw
  rw [huoutput] at hout
  simp only [zero_add, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htpos, hzero]
  calc
    _ ≤ t⁻¹ * (t * (C + ε)) := mul_le_mul_of_nonneg_left hout (inv_nonneg.mpr htpos.le)
    _ = C + ε := by field_simp

/-- The sharp parity-corrected gain also holds for every actual-query local bound.
Use: the local relative-error lower half of Theorem 4.1. -/
theorem linearGain_le_localRelativeBound {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N)
    (C : ℝ) (hb : LocalRelativeBound h I C) : bezout.Lower.linearGain I N ≤ C :=
  linearGain_le_operatorBound h I he hN true C (localRelativeBound_operatorBound h I C hb true)

/-- The sharp lower gain survives the actual dimension-uniform local limit.
Use: the local relative-gain statement of Theorem 4.1. -/
theorem linearGain_le_localRelativeGain {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N) :
    bezout.Lower.linearGain I N ≤ localRelativeGain h I := by
  apply le_csInf (localRelativeBounds_nonempty h I)
  intro C hC
  exact linearGain_le_localRelativeBound h I he hN C hC

end
end bezout.Gains
