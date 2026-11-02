import chebyshev1.Realization.StaticShiftGeneral
import chebyshev1.Jacobi.PrefixBounds
import krylov.Secant.Metric

/-!
Article: main_krylov, def:classes(O) and prop:dict(ii), fixed-memory bridge.
Use: reuse the existing ordered affine realizations and their proved polynomial
and insertion identities, keeping fixed coefficients distinct from adaptive policies.
Source: PasechnyukTakac26; the existing chebyshev1 formalization.
-/

namespace krylov.Realization
noncomputable section
open chebyshev1 Polynomial Polynomial.Chebyshev
open scoped BigOperators Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Constant-preserving normalization of an actual fixed affine realization.
Use: the source's oblivious x₀-plus-gradient-span methods have residual polynomial one at zero.
Article: main_krylov, def:classes(O), p_R(0)=1. -/
def ObliviousNormalized (R : chebyshev1.Realization ι) : Prop :=
  ∀ k, R.scalarTransfer k 0=1

/-- A genuinely normalized fixed realization has the source's residual-polynomial normalization.
Use: the polynomial condition is derived from the actual fixed affine memory transition.
Article: main_krylov, def:classes(O).
Proof: evaluate the actual constructed residual polynomial through its proved actual scalar transfer identity. -/
theorem oblivious_residual_zero (R : chebyshev1.Realization ι) (hR : ObliviousNormalized R) (k : ℕ) :
    (R.residualPolynomial k).eval 0=1 := by
  rw [R.residualPolynomial_eval]
  exact hR k

/-- Every actual fixed affine realization obeys the insertion-kernel static sum rule, at every memory size.
Use: the source dictionary reuses the existing ordered-product differentiation proof.
Article: main_krylov, prop:dict(ii), ΣK_s(λ,λ)=p_R′(λ).
Source: chebyshev1 Realization.kernel_sum_derivative.
Proof: instantiate the already proved actual finite-memory identity. -/
theorem fixed_static_sum_rule (R : chebyshev1.Realization ι) (N : ℕ) (t : ℝ) :
    ∑ s∈Finset.range N, R.kernel N s t t=(R.residualPolynomial N).derivative.eval t :=
  R.kernel_sum_derivative N t

/-- The static response of every actual fixed realization is its residual derivative applied to the real matrix.
Use: the scalar sum rule is an actual physical operator identity, not an assumed diagonal model.
Article: main_krylov, prop:dict(ii), static insertion direction.
Source: chebyshev1 Realization.static_linearResponse_general.
Proof: instantiate the existing actual symmetric-matrix identity with the opposite shift sign. -/
theorem fixed_static_response {d : Type*} [Fintype d] [DecidableEq d]
    (R : chebyshev1.Realization ι) (N : ℕ) (A : Matrix d d ℝ) (hA : A.IsHermitian) (t : ℝ) :
    R.linearResponse N A (fun _ => t • (1 : Matrix d d ℝ))=
      t • aeval A (R.residualPolynomial N).derivative := by
  simpa only [neg_neg] using R.static_linearResponse_general N A hA (-t)

/-- The true finite response of a static query sequence is the actual terminal residual polynomial at that matrix.
Use: fixed polynomial amplification is compared with exact adaptive static termination.
Article: main_krylov, prop:dict(ii), static polynomial response.
Source: chebyshev1 Realization.operatorTransfer_eq_aeval.
Proof: reuse the existing actual ordered matrix-transfer polynomial theorem. -/
theorem fixed_static_polynomial {d : Type*} [Fintype d] [DecidableEq d]
    (R : chebyshev1.Realization ι) (N : ℕ) (A : Matrix d d ℝ) :
    R.operatorTransfer N (fun _ => A)=aeval A (R.residualPolynomial N) :=
  R.operatorTransfer_eq_aeval N A

/-- Every terminal-Chebyshev-exact fixed realization has the printed exact top-eigenvector static amplification.
Use: the conclusion is independent of the fixed memory size or intermediate realization.
Article: main_krylov, prop:dict(ii), ε_N T_N(1+2Lω/(L−μ)).
Source: the earlier actual residual polynomial and mathlib's Chebyshev parity identity.
Proof: evaluate the constructed polynomial at L(1+ω); the affine argument is
the negative printed exterior point, whose parity sign disappears in the actual absolute error. -/
theorem fixed_top_amplification (R : chebyshev1.Realization ι) (I : SpectralInterval) (N : ℕ)
    (hfinal : R.residualPolynomial N=I.residual N) (ω : ℝ) (hω : 0≤ω) :
    |(R.residualPolynomial N).eval (I.L*(1+ω))|=
      I.epsilon N*(T ℝ N).eval (1+2*I.L*ω/I.delta) := by
  -- Only the terminal polynomial is fixed; no special intermediate state or memory representation is used.
  have hL : 0<I.L := I.mu_pos.trans I.mu_lt_L
  have hdelta : I.L-I.mu≠0 := I.delta_pos.ne'
  have hz : I.z (I.L*(1+ω))=-(1+2*I.L*ω/I.delta) := by
    unfold SpectralInterval.z SpectralInterval.delta
    field_simp [hdelta]
    ring
  have hp : 0≤(T ℝ N).eval (1+2*I.L*ω/I.delta) :=
    (by norm_num : (0 : ℝ)≤1).trans (one_le_eval_T_real N (by
      have hh := div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ)≤2) hL.le) hω) I.delta_pos.le
      linarith))
  have hsign : |((N : ℤ).negOnePow : ℝ)|=1 := by
    exact_mod_cast Int.abs_negOnePow (N : ℤ)
  rw [hfinal, I.residual_eval, hz, T_eval_neg, abs_div, abs_mul, hsign, one_mul,
    abs_of_nonneg hp, abs_of_pos (I.den_pos N)]
  unfold SpectralInterval.epsilon
  ring

/-- The exact exterior Chebyshev amplification is attained by an actual positive scalar physical operator.
Use: the source's top-eigenvector example is a real ordered-matrix execution of every fixed realization.
Article: main_krylov, prop:dict(ii), actual static attaining instance.
Source: the existing fixed realization's actual operator-transfer polynomial theorem.
Proof: the genuine one-dimensional matrix transfer equals its residual
polynomial evaluation; its actual Euclidean norm is the absolute scalar error. -/
theorem fixed_top_transfer (R : chebyshev1.Realization ι) (I : SpectralInterval) (N : ℕ)
    (hfinal : R.residualPolynomial N=I.residual N) (ω : ℝ) (hω : 0≤ω) :
    opNorm (R.operatorTransfer N (fun _ => scalarMatrix (I.L*(1+ω))))=
      I.epsilon N*(T ℝ N).eval (1+2*I.L*ω/I.delta) := by
  -- Evaluate the actual one-dimensional ordered matrix transfer through its genuine scalar polynomial.
  rw [R.operatorTransfer_eq_aeval]
  have he : aeval (scalarMatrix (I.L*(1+ω))) (R.residualPolynomial N)=
      scalarMatrix ((R.residualPolynomial N).eval (I.L*(1+ω))) := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [scalarMatrix, aeval_diagonal, Matrix.diagonal_apply_eq]
  rw [he, opNorm_scalarMatrix]
  exact fixed_top_amplification R I N hfinal ω hω

omit [Fintype ι] [DecidableEq ι] in
/-- The actual relative exterior argument has the printed condition-number form.
Use: identifies the Lω absolute shift with 2κω/(κ−1), κ=L/μ.
Article: main_krylov, prop:dict(ii), relative static query budget.
Proof: clear only the positive physical interval denominators. -/
theorem relative_top_argument (I : SpectralInterval) (ω : ℝ) :
    1+2*I.L*ω/I.delta=1+2*(I.L/I.mu)*ω/(I.L/I.mu-1) := by
  have hm : I.mu≠0 := I.mu_pos.ne'
  have hd : I.L/I.mu-1≠0 := by
    have hp : 1<I.L/I.mu := (lt_div_iff₀ I.mu_pos).mpr (by simpa only [one_mul] using I.mu_lt_L)
    linarith
  unfold SpectralInterval.delta
  field_simp

omit [Fintype ι] [DecidableEq ι] in
/-- The actual attaining top-eigenvector static shift has exactly the prescribed relative spectral budget and stays positive.
Use: the finite Chebyshev amplification is an admissible physical relative-drift example.
Article: main_krylov, prop:dict(ii), E=ωLvvᵀ.
Proof: in the actual one-dimensional physical space the drift is ω times the
positive base; genuine canonical congruence cancels the base and leaves ωI. -/
theorem top_static_admissible (I : SpectralInterval) (ω : ℝ) (hω : 0≤ω) :
    (scalarMatrix I.L).PosDef ∧ (scalarMatrix (I.L*(1+ω))).PosDef ∧
      krylov.Secant.relativeBudget (scalarMatrix I.L) (scalarMatrix (I.L*ω))=ω := by
  -- Positivity and the exact budget use the actual metric-root normalization of the physical matrices.
  have hL : 0<I.L := I.mu_pos.trans I.mu_lt_L
  have hb : (scalarMatrix I.L).PosDef := Matrix.posDef_diagonal_iff.mpr (fun _ => hL)
  have hs : (scalarMatrix (I.L*(1+ω))).PosDef :=
    Matrix.posDef_diagonal_iff.mpr (fun _ => mul_pos hL (by linarith))
  refine ⟨hb,hs,?_⟩
  have hD : scalarMatrix (I.L*ω)=ω • scalarMatrix I.L := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [scalarMatrix, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul, mul_comm]
  rw [hD, krylov.Secant.relativeBudget, krylov.Secant.relativeOperator_smul,
    krylov.Secant.relativeOperator_base _ hb]
  change ‖ω • (1 : Matrix (Fin 1) (Fin 1) ℝ)‖=ω
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hω, norm_one, mul_one]

omit [Fintype ι] [DecidableEq ι] in
/-- The exact relative exterior Chebyshev response has the printed first-order static coefficient.
Use: the universal fixed-realization lower coefficient follows by differentiating the attained finite response.
Article: main_krylov, prop:dict(ii), 2LN²ε_N/(L−μ).
Source: the existing Chebyshev endpoint derivative identity.
Proof: differentiate the actual exterior affine argument at zero and multiply
by the actual normalized Chebyshev endpoint derivative N². -/
theorem top_amplification_hasDerivAt (I : SpectralInterval) (N : ℕ) :
    HasDerivAt (fun ω : ℝ => I.epsilon N*(T ℝ N).eval (1+(2*I.L/I.delta)*ω))
      (2*I.L*(N : ℝ)^2*I.epsilon N/I.delta) 0 := by
  -- The exterior argument has value one at zero; the exact endpoint derivative controls the attained response.
  have ha : HasDerivAt (fun ω : ℝ => 1+(2*I.L/I.delta)*ω) (2*I.L/I.delta) 0 := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (0 : ℝ)).const_mul (2*I.L/I.delta)).const_add (1 : ℝ)
  have h := ((T ℝ N).hasDerivAt (1+(2*I.L/I.delta)*0)).comp 0 ha
  simp only [mul_zero, add_zero, derivative_T_eval_one, Int.cast_natCast] at h
  convert! h.const_mul (I.epsilon N) using 1
  ring

/-- The prefix Jacobi chain has the proved sharp static-direction first-order upper bound for all noncommuting drifts.
Use: the matching endpoint-maximal chain estimate is reused without reproving its Jacobi kernel calculus.
Article: main_krylov, prop:dict(ii), prefix matching coefficient.
Source: chebyshev1 Prefix.opNorm_linearResponse_le.
Proof: specialize the existing actual prefix operator estimate to an absolute query budget Lω. -/
theorem prefix_static_coefficient {d : Type*} [Fintype d] [DecidableEq d]
    (I : SpectralInterval) (N : ℕ) (A : Matrix d d ℝ) (hA : A.IsHermitian)
    (hspec : spectrum ℝ A⊆Set.Icc I.mu I.L) (D : ℕ → Matrix d d ℝ)
    (ω : ℝ) (hD : ∀ s<N, opNorm (D s)≤I.L*ω) :
    opNorm ((Prefix.realization I).linearResponse N A D)≤2*(N : ℝ)^2*I.epsilon N*(I.L*ω)/I.delta :=
  Prefix.opNorm_linearResponse_le I N A hA hspec D (I.L*ω) hD

omit [Fintype ι] [DecidableEq ι] in
/-- Actual canonical relative query budgets imply the corresponding physical absolute budgets.
Use: connect the printed relative perturbation model to the reused fixed-realization absolute estimates.
Article: main_krylov, prop:dict(ii), ‖D‖≤Lω.
Proof: reconstruct the physical perturbation by the actual metric root;
submultiplicativity costs its squared norm, exactly the norm of the positive physical base. -/
theorem relative_to_absolute_budget {n : ℕ} (base D : Matrix (Fin n) (Fin n) ℝ)
    (hb : base.PosDef) (upper ω : ℝ) (hω : 0≤ω) (hA : ‖base‖≤upper)
    (hD : krylov.Secant.relativeBudget base D≤ω) : ‖D‖≤upper*ω := by
  -- Both normalizations use the actual positive root, whose squared operator norm is exactly the physical base norm.
  let R := krylov.Secant.metricRoot base
  have hs : IsSelfAdjoint R := by
    change R.IsHermitian
    exact Matrix.isHermitian_iff_isSymm.mpr (krylov.Secant.metricRoot_isSymm base)
  have hn : ‖base‖=‖R‖*‖R‖ := by
    rw [← pow_two, ← hs.norm_mul_self]
    exact congrArg norm (krylov.Secant.metricRoot_square base hb).symm
  have he : D=R*krylov.Secant.relativeOperator base D*R :=
    (krylov.Secant.relativeOperator_reconstruct base D hb).symm
  have hcanon : ‖krylov.Secant.relativeOperator base D‖≤ω := hD
  calc
    ‖D‖ = ‖R*krylov.Secant.relativeOperator base D*R‖ := congrArg norm he
    _ ≤ (‖R‖*‖krylov.Secant.relativeOperator base D‖)*‖R‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg R))
    _ = ‖base‖*‖krylov.Secant.relativeOperator base D‖ := by rw [hn]; ring
    _ ≤ ‖base‖*ω := mul_le_mul_of_nonneg_left hcanon (norm_nonneg base)
    _ ≤ upper*ω := mul_le_mul_of_nonneg_right hA hω

/-- Every endpoint-maximal Jacobi chain has the printed matching upper coefficient under the actual relative query budgets.
Use: includes the prefix chain and discharges the absolute-budget conversion for the source's relative operator model.
Article: main_krylov, prop:dict(ii), matching relative coefficient for endpoint-maximal chains.
Source: chebyshev1 JacobiData.opNorm_linearResponse_endpoint_le.
Proof: true spectral interval control bounds the physical base norm by L,
canonical congruence converts each actual relative budget to Lω, and the existing sharp chain estimate applies. -/
theorem endpoint_relative_coefficient {n N : ℕ} (J : JacobiData) (I : SpectralInterval)
    (hJ : J.Admissible I N) (hmax : J.EndpointMax N)
    (hfinal : (J.realization I).residualPolynomial N=I.residual N)
    (A : Matrix (Fin n) (Fin n) ℝ) (hb : A.PosDef) (hspec : spectrum ℝ A⊆Set.Icc I.mu I.L)
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (hω : 0≤ω)
    (hD : ∀ s<N, krylov.Secant.relativeBudget A (D s)≤ω) :
    opNorm ((J.realization I).linearResponse N A D)≤2*(N : ℝ)^2*I.epsilon N*(I.L*ω)/I.delta := by
  -- The actual relative budgets are converted before invoking the earlier chain theorem.
  have hA : ‖A‖≤I.L := by
    have he := opNorm_aeval_le X I A hb.1 hspec I.L (I.mu_pos.trans I.mu_lt_L).le
      (fun t ht => by simp only [eval_X]; rw [abs_of_nonneg (I.mu_pos.le.trans ht.1)]; exact ht.2)
    simpa only [aeval_X, opNorm] using he
  exact J.opNorm_linearResponse_endpoint_le I hJ hmax hfinal A hb.1 hspec D (I.L*ω)
    (fun s hs => relative_to_absolute_budget A (D s) hb I.L ω hω hA (hD s hs))

end
end krylov.Realization
