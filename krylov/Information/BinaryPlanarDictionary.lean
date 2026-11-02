import krylov.Information.BinaryPlanarAdmissible

/-!
Article: main_krylov, thm:H, the exact compatible-source execution dictionary.
Use: identify the explicit equal-probe lower witnesses with the same full
binary scenario class used in the RFC upper theorem, including the genuine
intermediate correction oracle. Source: exact finite matrix telescoping and
the actual CG-consistent prefix theorem.
-/

namespace krylov.Information
noncomputable section
open Real Matrix Finset krylov.Tensor krylov.Tensor.BinaryCubic krylov.Secant
  krylov.Reference krylov.LinearAlgebra krylov.Correction krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- Cancelling the hidden final diagonal identifies the actual complete compatible source path with the genuine terminal information fibre.
Article: main_krylov, thm:H, the two true lower scenarios. -/
theorem binaryPlanarScenario_probe_cancelled (e h : EuclideanSpace ℝ (Fin n))
    (κ r : ℝ) (N : ℕ) (hN : 0 < N) (t : BinaryCubic) (j : ℕ) :
    (binaryPlanarScenario e h κ r (-κ*(t.t2+r*t.t3)) N t).probe j =
      binaryPlanarSegments e h κ r N t j := by
  induction j with
  | zero =>
    rw [binaryPlanarSegments_base e h κ r N hN]
    simp only [Scenario.probe, sum_range_zero, add_zero, binaryPlanarScenario]
  | succ j ih =>
    rw [Scenario.probe_succ, ih]
    have heq : (binaryPlanarScenario e h κ r (-κ*(t.t2+r*t.t3)) N t).increment j =
        planarMatrix e h (binaryFirstLast N (κ*t.t0) (κ*r*t.t1) j)
          (binaryFirstLast N (κ*t.t1) (κ*r*t.t2) j)
          (binaryFirstLast N (κ*t.t2) (κ*r*t.t3) j) := by
      change (if j=0 then κ • planarMatrix e h t.t0 t.t1 t.t2 else 0) +
        (if j=N-1 then (κ*r) • planarMatrix e h t.t1 t.t2 t.t3 else 0) = _
      unfold binaryFirstLast
      split_ifs <;>
        simp only [planarMatrix, zero_smul, add_zero, zero_add, smul_add, smul_smul, add_smul]
      all_goals module
    rw [heq]
    have hh := terminalSegments_increment e h
      (binaryFirstLast N (κ*t.t1) (κ*r*t.t2))
      (binaryFirstLast N (κ*t.t0) (κ*r*t.t1))
      (binaryFirstLast N (κ*t.t2) (κ*r*t.t3)) N j
    change binaryPlanarSegments e h κ r N t (j+1) - binaryPlanarSegments e h κ r N t j = _ at hh
    rw [← hh]
    abel

/-- The genuine physical lower probe oracle is exactly the explicit binary compatible probe path.
Article: main_krylov, thm:H, no coordinate-model oracle is substituted. -/
theorem physical_binaryPlanarScenario_probe_cancelled
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (e h : EuclideanSpace ℝ (Fin n))
    (κ r : ℝ) (N : ℕ) (hN : 0 < N) (t : BinaryCubic) :
    ((binaryPlanarScenario e h κ r (-κ*(t.t2+r*t.t3)) N t).inPhysical (metricRoot A)⁻¹).probeOracle =
      binaryPlanarProbe A e h κ r N t := by
  funext j
  rw [Scenario.probeOracle, Scenario.inPhysical, Scenario.mapForms_probe,
    binaryPlanarScenario_probe_cancelled e h κ r N hN, inverseRootForm A _ hA]
  rfl

/-- The actual terminal correction operator is the same genuine compatible tensor completion in both source representations.
Article: main_krylov, thm:H, true last-gradient query. -/
theorem binaryPlanarScenario_last_cancelled (e h : EuclideanSpace ℝ (Fin n))
    (κ r : ℝ) (N : ℕ) (hN : 0 < N) (t : BinaryCubic) :
    (binaryPlanarScenario e h κ r (-κ*(t.t2+r*t.t3)) N t).lastOperator N =
      binaryPlanarOutput e h κ r N t := by
  change (binaryPlanarScenario e h κ r (-κ*(t.t2+r*t.t3)) N t).probe N +
    (κ*r) • planarMatrix e h t.t1 t.t2 t.t3 = _
  rw [binaryPlanarScenario_probe_cancelled e h κ r N hN]
  simp only [binaryPlanarOutput, planarMatrix, smul_add, smul_smul]

/-- The actually executed original source output equals the common-query binary output used in the information lower bound.
Article: main_krylov, thm:H, the actual original information class. -/
theorem binaryPlanarScenario_gradient_cancelled
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0 < N)
    (hcount : referenceAtomCount A hA g=N+1)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m)
    (κ r : ℝ) (t : BinaryCubic) :
    let e := canonicalCGUnitStep A g 0
    let h := canonicalCGUnitStep A g N
    let S := (binaryPlanarScenario e h κ r (-κ*(t.t2+r*t.t3)) N t).inPhysical (metricRoot A)⁻¹
    probedGradient m S.probeOracle (S.correctionOracle N) g (N+1) =
      probedGradient m (binaryPlanarProbe A e h κ r N t)
        (fun _ => cgOperator (metricRoot A * binaryPlanarOutput e h κ r N t * metricRoot A)) g (N+1) := by
  dsimp only
  let e := canonicalCGUnitStep A g 0
  let h := canonicalCGUnitStep A g N
  let S := (binaryPlanarScenario e h κ r (-κ*(t.t2+r*t.t3)) N t).inPhysical (metricRoot A)⁻¹
  let probe := binaryPlanarProbe A e h κ r N t
  let B := cgOperator (metricRoot A * binaryPlanarOutput e h κ r N t * metricRoot A)
  have hprobe : S.probeOracle = probe := physical_binaryPlanarScenario_probe_cancelled A hA e h κ r N hN t
  have hB : S.correctionOracle N N = B := by
    rw [Scenario.correctionOracle, ite_eq_right (by omega : ¬N<N)]
    change cgOperator ((Scenario.mapForms _ (inverseFormMap (metricRoot A)⁻¹)).lastOperator N) = B
    rw [Scenario.mapForms_lastOperator, binaryPlanarScenario_last_cancelled e h κ r N hN,
      inverseRootForm A _ hA]
  have hp (C : ℕ → EuclideanSpace ℝ (Fin (N+1)) →L[ℝ] EuclideanSpace ℝ (Fin (N+1))) :
      methodRun m probe C g N = methodRun m (fun _ => cgOperator A) (fun _ => cgOperator A) g N := by
    simpa only [probe, binaryPlanarProbe, binaryPlanarSegments, physicalTerminalSegments, cgOperator, e, h] using!
      terminal_method_prefix A hA g N hN (canonicalCG_frame_of_full_atoms A hA g hcount) m hm
        (binaryFirstLast N (κ*t.t1) (κ*r*t.t2)) (binaryFirstLast N (κ*t.t0) (κ*r*t.t1))
        (binaryFirstLast N (κ*t.t2) (κ*r*t.t3)) C N le_rfl
  change probedGradient m S.probeOracle (S.correctionOracle N) g (N+1) = probedGradient m probe (fun _ => B) g (N+1)
  rw [hprobe, probedGradient_succ, probedGradient_succ]
  unfold probedPhase
  rw [hp, hp, hB]

end
end krylov.Information
