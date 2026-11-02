import krylov.Stability.FCWorstReferences

/-!
Article: main_krylov, thm:A, complete actual worst-reference FC asymptotics.
Use: prove convergence of the true worst-reference defined-cycle gradient
ratio divided by its positive budget scale to the genuine sharp coefficient
supremum, with no compactness or common lower-path radius assumption.
Source: actual symmetric sharp CG increments, real affine-path derivative,
genuine local solve/search domains and the proved uniform quadratic upper estimate.
-/

namespace krylov.Stability
noncomputable section
open Matrix Finset Filter Set Topology krylov.Methods krylov.Reference krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ} {μ κ : ℝ}

/-- Actual cumulative physical drift commutes with canonical increment scaling.
Use: Actual cumulative physical drift commutes with canonical increment scaling.
Article: main_krylov, thm:A, complete actual worst-reference FC asymptotics.
Proof: The true finite prefix sum and genuine metric congruence are linear. -/
theorem cumulativeDrift_scalar (base : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (k : ℕ) :
    cumulativeDrift base (fun l => c • E l) k=c • cumulativeDrift base E k := by
  unfold cumulativeDrift
  rw [← Finset.smul_sum,Matrix.mul_smul,Matrix.smul_mul,map_smul]

/-- Scaling true canonical increments is exactly the actual scalar perturbation path.
Use: Scaling true canonical increments is exactly the actual scalar perturbation path.
Article: main_krylov, thm:A, complete actual worst-reference FC asymptotics.
Proof: Use the genuine cumulative physical drift scalar identity. -/
theorem canonicalFCPath_scalar (base : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    canonicalFCPath base (fun l => c • E l) 1=canonicalFCPath base E c := by
  funext k
  rw [canonicalFCPath,one_smul,cumulativeDrift_scalar]
  rfl

/-- Every actual nonzero full-reference physical space has positive dimension.
Use: Every actual nonzero full-reference physical space has positive dimension.
Article: main_krylov, thm:A, complete actual worst-reference FC asymptotics.
Proof: The empty true Euclidean space has only the zero gradient. -/
theorem FCReference.dimension_pos (R : FCReference n μ κ) : 0<n := by
  by_contra hn
  have hn0 : n=0 := by omega
  subst n
  exact R.nonzero (Subsingleton.elim _ _)

/-- The true full-active canonical CG reference error vanishes at the actual ambient dimension.
Use: The true full-active canonical CG reference error vanishes at the actual ambient dimension.
Article: main_krylov, thm:A, complete actual worst-reference FC asymptotics.
Proof: Use the genuine active-count stopping theorem and actual inverse-root linearity. -/
theorem FCReference.terminal_error (R : FCReference n μ κ) : cgCanonicalError R.base R.gradient n=0 := by
  unfold cgCanonicalError
  have hg : CG.gradient (cgOperator R.base) R.gradient n=0 := by
    simpa only [R.full] using cg_terminates R.base R.positive R.gradient
  rw [hg,map_zero]

/-- The genuine full-reference response omits its actual zero terminal tail.
Use: The genuine full-reference response omits its actual zero terminal tail.
Article: main_krylov, thm:A, complete actual worst-reference FC asymptotics.
Proof: The only removed actual summand has the genuinely zero terminal CG error. -/
theorem FCReference.response_trim (R : FCReference n μ κ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    fullCycleResponse R.base R.gradient (range n) E=fullCycleResponse R.base R.gradient (range (n-1)) E := by
  -- The real terminal tail is exactly zero, so no artificial last increment enters the coefficient.
  unfold fullCycleResponse
  symm
  apply sum_subset (range_mono (Nat.sub_le n 1))
  intro l hl hnot
  have he : l+1=n := by have := mem_range.mp hl;simp only [Finset.mem_range] at hnot;omega
  simp only [remainingTail,he,R.terminal_error,neg_zero,map_zero]

/-- The actual sharp coefficient sum has no terminal-tail contribution.
Use: The actual sharp coefficient sum has no terminal-tail contribution.
Article: main_krylov, thm:A, complete actual worst-reference FC asymptotics.
Proof: The true CG terminal error vanishes in the only removed finite summand. -/
theorem FCReference.mass_trim (R : FCReference n μ κ) (ω : ℕ → ℝ) :
    (∑ l∈range n, ω l*‖cgCanonicalError R.base R.gradient (l+1)‖)=
      ∑ l∈range (n-1), ω l*‖cgCanonicalError R.base R.gradient (l+1)‖ := by
  symm
  apply sum_subset (range_mono (Nat.sub_le n 1))
  intro l hl hnot
  have he : l+1=n := by have := mem_range.mp hl;simp only [Finset.mem_range] at hnot;omega
  rw [he,R.terminal_error,norm_zero,mul_zero]

/-- Every actual physical reference has genuine symmetric component-budget increments attaining its true normalized sharp response coefficient.
Use: Every actual physical reference has genuine symmetric component-budget increments attaining its true normalized sharp response coefficient.
Article: main_krylov, thm:A, complete actual worst-reference FC asymptotics.
Proof: Use the proved real planar CG attainers on all nonterminal tails and extend them by true zero increments; the actual full response and coefficient omit the genuine terminal zero tail. -/
theorem FCReference.attaining_increments (R : FCReference n μ κ) (ω : ℕ → ℝ) (hω : ∀ l<n, 0≤ω l) :
    ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ, (∀ l, (E l).IsSymm) ∧ (∀ l<n, ‖E l‖≤ω l) ∧
      ‖fullCycleResponse R.base R.gradient (range n) E‖/R.initialNorm=R.coefficient ω := by
  -- Construct true finite symmetric budget attainers and extend only unused increments by zero.
  obtain ⟨E,hE,hsharp⟩ := spectral_response_attained R.base R.positive R.gradient
    (by rw [R.full];exact R.dimension_pos) (range (n-1))
    (fun l hl => by rw [R.full];have := mem_range.mp hl;omega) ω
    (fun l hl => hω l (by have := mem_range.mp hl;omega))
  let F := fun l => if l<n-1 then E l else 0
  refine ⟨F,?_,?_,?_⟩
  · intro l
    by_cases hl : l<n-1
    · simpa only [F,ite_eq_left hl] using (hE l (mem_range.mpr hl)).1
    · simp only [F,ite_eq_right hl]
      exact Matrix.isSymm_zero
  · intro l hl
    by_cases hi : l<n-1
    · simpa only [F,ite_eq_left hi] using (hE l (mem_range.mpr hi)).2
    · simpa only [F,ite_eq_right hi,norm_zero] using hω l hl
  · rw [R.response_trim]
    have heq : fullCycleResponse R.base R.gradient (range (n-1)) F=
        fullCycleResponse R.base R.gradient (range (n-1)) E := by
      apply sum_congr rfl
      intro l hl
      rw [show F l=E l by exact ite_eq_left (mem_range.mp hl)]
    rw [heq,hsharp]
    exact congrArg (fun v => v/R.initialNorm) (R.mass_trim ω).symm

/-- Each genuine physical reference has a locally feasible actual FC perturbation path whose normalized gradient ratio has its true sharp first-order limit.
Use: Each genuine physical reference has a locally feasible actual FC perturbation path whose normalized gradient ratio has its true sharp first-order limit.
Article: main_krylov, thm:A, complete actual worst-reference FC asymptotics.
Proof: The actual affine-path derivative gives the true slope limit. Genuine reference stopping removes the constant term; proved actual solve/search domains make the scaled symmetric attaining increments feasible near zero. -/
theorem FCReference.attaining_path (R : FCReference n μ κ) (ω : ℕ → ℝ) (hω : ∀ l<n, 0≤ω l) :
    ∃ f : ℝ → ℝ, Tendsto (fun t => f t/t) (𝓝[>] (0 : ℝ)) (𝓝 (R.coefficient ω)) ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), f t∈fcValueSet n μ κ ω t := by
  -- The lower path is the genuine executed FC cycle on these actual attaining increments.
  obtain ⟨E,hE,hbudget,hsharp⟩ := R.attaining_increments ω hω
  let G := fun t => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot R.base)⁻¹
    (fcGradient fullMemory (canonicalFCPath R.base E t) R.gradient n)
  let f := fun t => ‖G t‖/R.initialNorm
  have hG0 : G 0=0 := by
    dsimp only [G]
    rw [canonicalFCPath_zero,(fullFC_reference_step (cgOperator R.base)
      (cgOperator_positive R.base R.positive).1 (cgOperator_positive R.base R.positive).2 R.gradient n).1]
    exact R.terminal_error
  have hd := canonicalFC_response_hasDerivAt R.base R.positive R.gradient R.full E hE
  have hle : 𝓝[>] (0 : ℝ)≤𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ (fun _ ht => ne_of_gt ht)
  have hlim := (hd.tendsto_slope.mono_left hle).norm.div_const R.initialNorm
  have heq : (fun t => f t/t)=ᶠ[𝓝[>] (0 : ℝ)] (fun t => ‖slope G 0 t‖/R.initialNorm) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    simp only [slope_def_module,hG0,sub_zero,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos ht]
    dsimp only [f]
    ring
  have hlimit : Tendsto (fun t => f t/t) (𝓝[>] (0 : ℝ)) (𝓝 (R.coefficient ω)) := by
    rw [← hsharp]
    exact (tendsto_congr' heq).mpr hlim
  -- Actual inverse and exact-search domains are derived before declaring the path feasible.
  have hdom := quadraticFC_domains (canonicalFCPath R.base E) (fun _ : ℝ => R.gradient) 0
    (fun k => (canonicalFCPath_calculus R.base E k).1) analyticAt_const (cgOperator R.base)
    (canonicalFCPath_zero R.base E) (cgOperator_positive R.base R.positive).1 (cgOperator_positive R.base R.positive).2 n
    (fun i hi => cg_nonstagnation R.base R.positive R.gradient i (by simpa only [R.full] using hi))
  refine ⟨f,hlimit,?_⟩
  filter_upwards [hdom.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht hp
  let S : FCScenario R ω t := {
    increments := fun l => t • E l
    symmetric := fun l => (hE l).smul t
    budget := fun l hl => by
      rw [norm_smul,Real.norm_of_nonneg hp.le]
      exact mul_le_mul_of_nonneg_left (hbudget l hl) hp.le
    solve := fun i hi => by rw [canonicalFCPath_scalar];exact (ht i hi).1
    curvature := fun i hi => by rw [canonicalFCPath_scalar];exact (ht i hi).2 }
  apply Set.mem_insert_of_mem
  refine ⟨⟨R,S⟩,?_⟩
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot R.base)⁻¹
    (fcGradient fullMemory (canonicalFCPath R.base (fun l => t • E l) 1) R.gradient n)‖/R.initialNorm=f t
  rw [canonicalFCPath_scalar]

/-- The actual worst-reference defined FC terminal-gradient ratio has exactly the printed sharp first-order asymptotic supremum.
Use: The actual worst-reference defined FC terminal-gradient ratio has exactly the printed sharp first-order asymptotic supremum.
Article: main_krylov, thm:A, complete actual worst-reference FC asymptotics.
Proof: The completed genuine global quadratic upper bound controls all actual scenarios uniformly. Each true reference coefficient has its own genuinely feasible attaining path; the real supremum convergence theorem gives the exact limit without assuming a worst-reference maximizer. -/
theorem fcWorstRatio_asymptotic (ω : ℕ → ℝ) (hω : ∀ l<n, 0≤ω l) (hμ : 0<μ) (hκ : 1≤κ) :
    Tendsto (fun t => fcWorstRatio n μ κ ω t/t) (𝓝[>] (0 : ℝ)) (𝓝 (fcWorstCoefficient n μ κ ω)) := by
  -- A uniform upper radius and separate actual near-extremizing lower paths suffice for the true supremum.
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 8*((n : ℝ)+1)*(t*(∑ l∈range n, ω l))≤1 := by
    have hc : ContinuousAt (fun t : ℝ => 8*((n : ℝ)+1)*(t*(∑ l∈range n, ω l))) 0 := by fun_prop
    have hh := hc.eventually (Iio_mem_nhds (show 8*((n : ℝ)+1)*((0 : ℝ)*(∑ l∈range n, ω l))<1 by simp))
    exact (hh.filter_mono nhdsWithin_le_nhds).mono fun _ ht => ht.le
  apply supremum_firstOrder (fcCoefficientSet n μ κ ω) ⟨0,Set.mem_insert 0 _⟩ (fcValueSet n μ κ ω)
    (fun _ => ⟨0,Set.mem_insert 0 _⟩) (fcResponseConstant n κ*(∑ l∈range n, ω l)^2)
  · filter_upwards [hsmall,self_mem_nhdsWithin] with t ht hp
    intro v hv
    exact (fcValueSet_upper ω hω hμ hκ hp.le ht v hv).trans_eq (by unfold fcWorstCoefficient;ring)
  · intro b hb
    rcases hb with rfl|⟨R,rfl⟩
    · refine ⟨fun _ => 0,?_,Eventually.of_forall (fun _ => Set.mem_insert 0 _)⟩
      simpa only [zero_div] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
    · exact R.attaining_path ω hω
end
end krylov.Stability
