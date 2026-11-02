import krylov.Information.KnownBasePlanar

/-!
Article: main_krylov, thm:C2(a),(c), actual known-base planar radius.
Use: the genuine signed common-data source execution forces its normalized
quadratic coefficient with one explicit all-profile cubic loss.
Source: exact real one-query terminal normal form, the actual planar mean
inverse and genuine positive fixed-base last-CG-error normalization.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability
open scoped BigOperators MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
/-- A nonnegative planar information radius loses at most two cubic units relative to its quadratic numerator.
Use: one explicit all-profile cubic loss controls the fixed-base Frobenius lower witnesses.
Article: main_krylov, thm:C2(a), uniform lower-radius remainder.
Proof: the numerator is at most s² and the extra denominator term at most
2s. Cross-multiplication by the positive denominator gives the cubic loss.
-/
theorem planar_radius_cubic_loss {X β s : ℝ} (hX : 0≤X) (hβ : 0≤β)
    (hXs : X≤s) (hβs : β≤s) : X*β-2*s^3≤β*X/(1+2*β) := by
  -- Keep the true denominator positive, including every zero-budget case.
  have hs : 0≤s := hX.trans hXs
  have hprod : X*β≤s^2 := by nlinarith [mul_le_mul hXs hβs hβ hs]
  have hcube : β*(X*β)≤s^3 := by
    have hh := mul_le_mul hβs hprod (mul_nonneg hX hβ) hs
    nlinarith
  apply (le_div_iff₀ (by positivity : 0<1+2*β)).mpr
  have hterm : 0≤β*s^3 := mul_nonneg hβ (pow_nonneg hs 3)
  nlinarith

/-- Every genuine source one-correction policy has the fixed-base planar own-normalized lower radius with a common cubic loss.
Use: the Frobenius minimax obstruction concerns actual outputs on genuine common-data source scenarios with exactly known base.
Article: main_krylov, thm:C2(a),(c), normalized actual fixed-base signed lower pair.
Proof: the proved genuine complete-data executor derives one common
terminal query and exact signed outputs. The true planar mean inverse
bounds their worst original-metric norm below. Both scenarios have base A,
so the actual source φ is the same positive last CG scale. Divide that
scale out of the genuine output comparison and retain the explicit cubic loss.
-/
theorem knownBasePlanarScenario_lower {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) (h1 : OneCorrectionMethod m)
    (x y : ℕ → ℝ) (w s : ℝ)
    (hX : 0≤∑ i∈range N, x i) (hβ : 0≤(∑ i∈range N, y i)+w)
    (hXs : (∑ i∈range N, x i)≤s) (hβs : (∑ i∈range N, y i)+w≤s) (hs : s≤(1/2 : ℝ)) :
    let S := fun σ => (knownBasePlanarScenario (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g N)
      x y w σ).inPhysical (metricRoot A)⁻¹
    (∑ i∈range N, x i)*((∑ i∈range N, y i)+w)-2*s^3≤
      max ((S 1).outputRatio m g N) ((S (-1)).outputRatio m g N) := by
  -- The original full active reference supplies every actual unit and orthogonality condition.
  let e := canonicalCGUnitStep A g 0
  let f := canonicalCGUnitStep A g N
  let X := ∑ i∈range N, x i
  let β := (∑ i∈range N, y i)+w
  let scale := ‖cgCanonicalError A g N‖
  let S := fun σ => (knownBasePlanarScenario e f x y w σ).inPhysical (metricRoot A)⁻¹
  let R := max ((S 1).outputRatio m g N) ((S (-1)).outputRatio m g N)
  have ho := canonicalCG_frame_of_full_atoms A hA g hcount
  have he : ‖e‖=1 := by simpa only [e,Fin.val_zero] using ho.norm_eq_one (0 : Fin (N+1))
  have hf : ‖f‖=1 := by simpa only [f,Fin.val_last] using ho.norm_eq_one (Fin.last N)
  have hef : inner ℝ e f=0 := by
    simpa only [e,f,Fin.val_zero,Fin.val_last] using ho.inner_eq_zero (i := 0) (j := Fin.last N)
      (by intro h; have hv : (0 : ℕ)=N := congrArg Fin.val h; omega)
  have hscale : 0<scale := canonical_error_pos A hA _ (cg_nonstagnation A hA g N (by omega))
  obtain ⟨u,hout⟩ := knownBasePlanarScenario_terminal_form A hA g hN hcount m hm h1 x y w
  have henergy : Real.sqrt (cgEnergy A g N)=scale :=
    (cgEnergy_sqrt A hA g N).trans (terminal_step_error_norm A hA g (by omega)).symm
  have hrad := planar_two_scenario_lower e f he hf hef X β (X*scale)
    (by rw [abs_of_nonneg (show 0≤X from hX)]; exact hXs.trans hs) hβ (mul_nonneg hX hscale.le) u
  have hp := hout 1
  have hmout := hout (-1)
  dsimp only at hp hmout
  rw [henergy,one_smul] at hp
  rw [henergy,neg_one_smul,← sub_eq_add_neg] at hmout
  dsimp only [e,f,X,β] at hrad
  rw [← hp,← hmout] at hrad
  change β*(X*scale)/(1+2*β)≤max
    ‖cgOperator (metricRoot A)⁻¹ (probedGradient m (S 1).probeOracle ((S 1).correctionOracle N) g (N+1))‖
    ‖cgOperator (metricRoot A)⁻¹ (probedGradient m (S (-1)).probeOracle ((S (-1)).correctionOracle N) g (N+1))‖ at hrad
  have hbase (σ : ℝ) : (S σ).base=A := physical_knownBasePlanarScenario_base A hA e f x y w σ
  have hnorm (σ : ℝ) :
      ‖cgOperator (metricRoot A)⁻¹ (probedGradient m (S σ).probeOracle ((S σ).correctionOracle N) g (N+1))‖=
        (S σ).outputRatio m g N*scale := by
    rw [Scenario.outputRatio,hbase,div_mul_cancel₀ _ hscale.ne']
  rw [hnorm 1,hnorm (-1),← max_mul_of_nonneg _ _ hscale.le] at hrad
  have hcancel : β*X/(1+2*β)≤R := by
    apply (mul_le_mul_iff_left₀ hscale).mp
    convert hrad using 1; ring
  exact (planar_radius_cubic_loss hX hβ hXs hβs).trans hcancel


end
end krylov.Information
