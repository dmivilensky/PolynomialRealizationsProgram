import krylov.Information.PlanarTerminalExecution

/-!
Article: main_krylov, thm:C, actual admissible all-profile residual lower bound.
Use: combine explicit physical budget witnesses with the genuinely returned
terminal gradients of every source method, retaining a uniform cubic loss.
Source: exact executed common-correction normal form, genuine CG geometry,
quantitative two-scenario radius and the proved sharp scalar optimizer.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Secant krylov.Reference krylov.LinearAlgebra krylov.Correction
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {n : ℕ}

/-- Every actual at-most-one-correction globally CG-consistent method obeys the explicit planar lower radius on the constructed signed source scenarios.
Use: the information lower bound applies to real complete executions rather than an arbitrary vector supplied as a method output.
Article: main_krylov, thm:C, actual two-scenario residual lower bound in the fixed reference metric.
Proof: the real terminal outputs have the proved common-correction normal
form. Actual full active spectral data derive the two orthonormal witness
directions. Primitive nonnegative budgets and the unit-circle parameters
bound the true cross mean by one half, so its quantitative two-scenario
radius bounds the maximum of the two genuinely returned gradients.
-/
theorem planarLowerScenario_reference_lower {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1)
    (m : krylov.Methods.ProbedMethod (EuclideanSpace ℝ (Fin (N+1))))
    (hm : krylov.Methods.CGConsistent m) (h1 : krylov.Methods.OneCorrectionMethod m)
    (ω : ℕ → ℝ) (w a γ : ℝ)
    (hω : ∀ i∈range N, 0≤ω i) (hw : 0≤w) (hW : (∑ i∈range N, ω i)≤(1/2 : ℝ))
    (ha : 0≤a) (hγ : 0≤γ) (hac : a^2+γ^2=1) :
    let e := canonicalCGUnitStep A g 0
    let f := canonicalCGUnitStep A g N
    let W := ∑ i∈range N, ω i
    let t := 1-W
    let β := t*(γ*W+w)
    let ρ := t*a*W*Real.sqrt (cgEnergy A g N)
    let out := fun σ =>
      let S := (planarLowerScenario e f ω w N a γ σ).inPhysical (metricRoot A)⁻¹
      cgOperator (metricRoot A)⁻¹
        (krylov.Methods.probedGradient m S.probeOracle (S.correctionOracle N) g (N+1))
    β*ρ/(1+2*β)≤max ‖out 1‖ ‖out (-1)‖ := by
  -- Derive the real frame and small-mean conditions before applying its exact radius.
  let W := ∑ i∈range N, ω i
  let t := 1-W
  let e := canonicalCGUnitStep A g 0
  let f := canonicalCGUnitStep A g N
  have hW₀ : 0≤W := sum_nonneg hω
  have ht : 0≤t := by dsimp only [t]; linarith
  have ht₁ : t≤1 := by dsimp only [t]; linarith
  have ha₁ : a≤1 := by nlinarith [sq_nonneg γ]
  have hx₀ : 0≤t*a*W := mul_nonneg (mul_nonneg ht ha) hW₀
  have hx : |t*a*W|≤(1/2 : ℝ) := by
    rw [abs_of_nonneg hx₀]
    have hta : t*a≤1 :=
      ((mul_le_mul_of_nonneg_left ha₁ ht).trans_eq (mul_one t)).trans ht₁
    exact ((mul_le_mul_of_nonneg_right hta hW₀).trans_eq (one_mul W)).trans hW
  have ho := canonicalCG_frame_of_full_atoms A hA g hcount
  have he : ‖e‖=1 := by simpa only [e,Fin.val_zero] using ho.norm_eq_one (0 : Fin (N+1))
  have hf : ‖f‖=1 := by simpa only [f,Fin.val_last] using ho.norm_eq_one (Fin.last N)
  have hef : inner ℝ e f=0 := by
    simpa only [e,f,Fin.val_zero,Fin.val_last] using
      (ho.inner_eq_zero (i := 0) (j := Fin.last N) (by
        intro h
        have hv : (0 : ℕ)=N := congrArg Fin.val h
        omega))
  obtain ⟨u,hu⟩ := planarLowerScenario_terminal_form A hA g hN hcount m hm h1 ω w a γ
  have hbnd := planar_two_scenario_lower e f he hf hef (t*a*W) (t*(γ*W+w))
    (t*a*W*Real.sqrt (cgEnergy A g N)) hx (mul_nonneg ht (add_nonneg (mul_nonneg hγ hW₀) hw))
      (mul_nonneg hx₀ (Real.sqrt_nonneg _)) u
  dsimp only
  rw [hu 1,hu (-1)]
  simpa only [e,f,t,W,one_smul,neg_one_smul,sub_eq_add_neg] using hbnd

/-- For every original profile the explicit admissible signed scenarios force the sharp reference-metric second-order lower coefficient for each genuine source method.
Use: combine actual primitive admissibility, complete observation preservation and the real executed worst-residual lower bound in one theorem.
Article: main_krylov, thm:C, all-profile sharp lower scenarios before own-base normalization.
Proof: select the already proved scalar maximizing coordinates. Both signed
physical scenarios satisfy every original individual budget and reference
radius. Their genuinely returned gradients satisfy the actual planar radius;
the proved uniform scalar estimate loses at most four times the cube of the
total increment and terminal budget. Zero-total profiles require no division.
-/
theorem admissible_planar_sharp_reference_lower {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1)
    (m : krylov.Methods.ProbedMethod (EuclideanSpace ℝ (Fin (N+1))))
    (hm : krylov.Methods.CGConsistent m) (h1 : krylov.Methods.OneCorrectionMethod m)
    (ω : ℕ → ℝ) (w τ r : ℝ) (hω : ∀ i∈range N, 0≤ω i) (hw : 0≤w) (hτ : 0≤τ)
    (hs : (∑ i∈range N, ω i)+w≤(1/2 : ℝ)) (hWr : (∑ i∈range N, ω i)≤r) :
    let W := ∑ i∈range N, ω i
    let a := maximizingCross W w
    let γ := maximizingComplement W w
    let S := fun σ => (planarLowerScenario (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g N)
      ω w N a γ σ).inPhysical (metricRoot A)⁻¹
    (S 1).Admissible N A r ω w τ ∧ (S (-1)).Admissible N A r ω w τ ∧
      Real.sqrt (cgEnergy A g N)*(sharpConstant W w-4*(W+w)^3)≤
        max ‖cgOperator (metricRoot A)⁻¹
          (krylov.Methods.probedGradient m (S 1).probeOracle ((S 1).correctionOracle N) g (N+1))‖
          ‖cgOperator (metricRoot A)⁻¹
            (krylov.Methods.probedGradient m (S (-1)).probeOracle ((S (-1)).correctionOracle N) g (N+1))‖ := by
  -- The same actual maximizing family supplies all budgets and both real method outputs.
  let W := ∑ i∈range N, ω i
  let a := maximizingCross W w
  let γ := maximizingComplement W w
  have hW₀ : 0≤W := sum_nonneg hω
  obtain ⟨hγ,ha,hcircle⟩ := maximizing_coordinates hW₀ hw
  have hcirc : a^2+γ^2=1 := by linarith
  have hW : W≤(1/2 : ℝ) := by linarith
  refine ⟨cg_planarLowerScenario_admissible A hA g hN hcount ω w τ r hω hw hτ
      (hW.trans_lt (by norm_num)) hWr a γ 1 hγ hcirc (by norm_num),
    cg_planarLowerScenario_admissible A hA g hN hcount ω w τ r hω hw hτ
      (hW.trans_lt (by norm_num)) hWr a γ (-1) hγ hcirc (by norm_num),?_⟩
  exact (maximizing_planar_radius_lower hW₀ hw hs (Real.sqrt_nonneg _)).trans
    (planarLowerScenario_reference_lower A hA g hN hcount m hm h1 ω w a γ hω hw hW ha hγ hcirc)

end
end krylov.Information
