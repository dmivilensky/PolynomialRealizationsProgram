import krylov.Information.KnownBaseAdmissibility

/-!
Article: main_krylov, thm:C2(c), genuine sharp informed-base lower scenarios.
Use: every actual source method is forced by two original admissible
single-increment fixed-base scenarios to the coefficient 2/(3√3).
Source: actual full CG geometry, proved spectral consistency-interval
endpoints and the genuine one-query complete-data information radius.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability
open scoped BigOperators MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
/-- The actual single-increment profile at the first source index, with all other independent increment budgets zero.
Use: the informed-base theorem retains exactly the source's one nonzero increment, including zero total budget.
Article: main_krylov, thm:C2(c), ω_l=ω₀ 1_{l=0}. -/
def firstBudget (μ : ℝ) (i : ℕ) : ℝ := if i=0 then μ else 0

/-- The genuine first-increment source profile has exactly its stated finite total at every positive horizon.
Use: retain the exact original normalization in the known-base lower coefficient.
Article: main_krylov, thm:C2(c), W₀=ω₀.
Proof: the actual finite range contains zero once, and every other profile entry vanishes. -/
theorem firstBudget_sum (μ : ℝ) {N : ℕ} (hN : 0<N) : (∑ i∈range N, firstBudget μ i)=μ := by
  simp only [firstBudget,sum_ite_eq',mem_range.mpr hN,ite_true]

/-- The sharp informed-base coefficient is forced by actual admissible one-increment fixed-base signed physical scenarios for every true source method.
Use: the matching lower bound is about real returned gradients, with all original norm budgets and exactly known base proved.
Article: main_krylov, thm:C2(c), actual normalized lower coefficient 2ω₀²/(3√3).
Proof: use the true first and last CG steps and the exact scalar maximizer
a=1/√3. The two genuine planar consistency-interval endpoints have spectral
norm at most one and give every original primitive physical budget. The
proved actual complete-data one-query radius has numerator a(1−a²)ω₀².
Its uniform two-cubic loss and the attained scalar identity give the claim.
-/
theorem admissible_known_base_normalized_lower {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) (h1 : OneCorrectionMethod m)
    (μ τ r : ℝ) (hμ : 0≤μ) (hτ : 0≤τ) (hr : 0≤r) (hsmall : μ≤(1/2 : ℝ)) :
    let a := cubicMaximizer
    let γ := 1-a^2
    let S := fun σ => (knownBasePlanarScenario (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g N)
      (fun i => a*firstBudget μ i) (fun i => γ*firstBudget μ i) 0 σ).inPhysical (metricRoot A)⁻¹
    (S 1).base=A ∧ (S (-1)).base=A ∧
      (S 1).Admissible N A r (firstBudget μ) 0 τ ∧ (S (-1)).Admissible N A r (firstBudget μ) 0 τ ∧
      (2/(3*Real.sqrt 3))*μ^2-2*μ^3≤max ((S 1).outputRatio m g N) ((S (-1)).outputRatio m g N) := by
  -- Derive every genuine attaining direction and primitive zero/nonzero budget from the full actual reference.
  let a := cubicMaximizer
  let γ := 1-a^2
  obtain ⟨ha,ha₁,ha₂⟩ := cubicMaximizer_spec
  have haSq : a^2≤1 := by dsimp only [a]; linarith
  have hγ : 0≤γ := by dsimp only [γ]; linarith
  have hγ₁ : γ≤1 := by dsimp only [γ]; nlinarith [sq_nonneg a]
  have hω (i : ℕ) (_hi : i<N) : 0≤firstBudget μ i := by simp only [firstBudget]; split_ifs <;> positivity
  have ho := canonicalCG_frame_of_full_atoms A hA g hcount
  let e := canonicalCGUnitStep A g 0
  let f := canonicalCGUnitStep A g N
  have he : ‖e‖=1 := by simpa only [e,Fin.val_zero] using ho.norm_eq_one (0 : Fin (N+1))
  have hf : ‖f‖=1 := by simpa only [f,Fin.val_last] using ho.norm_eq_one (Fin.last N)
  have hef : inner ℝ e f=0 := by
    simpa only [e,f,Fin.val_zero,Fin.val_last] using ho.inner_eq_zero (i := 0) (j := Fin.last N)
      (by intro h; have hv : (0 : ℕ)=N := congrArg Fin.val h; omega)
  have hadm (σ : ℝ) (hσ : σ^2=1) := knownBasePlanarScenario_spectral_admissible A hA e f he
    (firstBudget μ) 0 τ r N hω (by norm_num) hτ hr a γ σ hσ
    (planar_endpoint_norm_le e f he hf hef a σ haSq hσ)
  refine ⟨physical_knownBasePlanarScenario_base A hA e f _ _ 0 1,
    physical_knownBasePlanarScenario_base A hA e f _ _ 0 (-1),hadm 1 (by norm_num),hadm (-1) (by norm_num),?_⟩
  -- The actual source radius retains the exact attained informed quadratic coefficient.
  have hsum (b : ℝ) : (∑ i∈range N, b*firstBudget μ i)=b*μ := by
    rw [← mul_sum,firstBudget_sum μ hN]
  have hX : 0≤∑ i∈range N, a*firstBudget μ i := by rw [hsum]; positivity
  have hβ : 0≤(∑ i∈range N, γ*firstBudget μ i)+0 := by rw [hsum]; positivity
  have hXs : (∑ i∈range N, a*firstBudget μ i)≤μ := by
    rw [hsum]
    exact (mul_le_mul_of_nonneg_right ha₁ hμ).trans_eq (one_mul μ)
  have hβs : (∑ i∈range N, γ*firstBudget μ i)+0≤μ := by
    rw [hsum,add_zero]
    exact (mul_le_mul_of_nonneg_right hγ₁ hμ).trans_eq (one_mul μ)
  have hl := knownBasePlanarScenario_lower A hA g hN hcount m hm h1
    (fun i => a*firstBudget μ i) (fun i => γ*firstBudget μ i) 0 μ hX hβ hXs hβs hsmall
  have hvalue : (∑ i∈range N, a*firstBudget μ i)*((∑ i∈range N, γ*firstBudget μ i)+0)=
      (2/(3*Real.sqrt 3))*μ^2 := by
    rw [hsum,hsum,add_zero]
    calc
      _ = (a*(1-a^2))*μ^2 := by dsimp only [γ]; ring
      _ = _ := by rw [show a*(1-a^2)=2/(3*Real.sqrt 3) from cubic_tradeoff_attained]
  rw [hvalue] at hl
  exact hl

end
end krylov.Information
