import krylov.Information.NormalizedLower

/-!
Article: main_krylov, thm:C2(a),(c), actual known-base planar source fibres.
Use: construct the true fixed-base signed physical scenarios and derive
exact complete data and one-query output forms from genuine execution.
Source: the existing actual terminal information fibre, fixed root
congruence and exact finite planar increment identities.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability
open scoped BigOperators MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual fixed-base signed planar source family with an independently assigned cross profile, old diagonal profile and terminal defect.
Use: construct the genuine known-base lower witnesses without varying the reference metric or normalization.
Article: main_krylov, thm:C2(a),(c), Â₀=I and Ê_l=(σy_l,x_l;x_l,0). -/
def knownBasePlanarScenario (e f : EuclideanSpace ℝ (Fin n)) (x y : ℕ → ℝ)
    (w σ : ℝ) : Scenario n where
  base := 1
  increment := fun i => planarMatrix e f (σ*y i) (x i) 0
  terminal := planarMatrix e f (σ*w) 0 0
  correction := fun _ => 0

/-- Genuine fixed-base planar source probes equal the actual previously proved terminal information-fibre operators.
Use: all complete transcript identities concern the actual concrete known-base source scenarios.
Article: main_krylov, thm:C2(a),(c), exact known-base physical probe bridge.
Proof: the initial hidden terminal diagonal is zero, so the first operator
is I. Exact chronological planar increments then agree at every successor.
-/
theorem knownBasePlanarScenario_probe (e f : EuclideanSpace ℝ (Fin n))
    (x y : ℕ → ℝ) (w σ : ℝ) (N k : ℕ) :
    (knownBasePlanarScenario e f x y w σ).probe k=
      terminalSegments e f x (fun i => σ*y i) (fun _ => 0) N k := by
  -- The actual initial identity and each chronological planar increment agree exactly.
  induction k with
  | zero => simp only [Scenario.probe,sum_range_zero,add_zero,knownBasePlanarScenario,
      terminalSegments_zero,sum_const_zero,zero_smul,sub_zero]
  | succ k ih =>
    rw [Scenario.probe_succ,ih]
    change terminalSegments e f x (fun i => σ*y i) (fun _ => 0) N k+
      planarMatrix e f (σ*y k) (x k) 0=_
    rw [← terminalSegments_increment e f x (fun i => σ*y i) (fun _ => 0) N k]
    abel

/-- Fixed-base planar physical probes are exactly the genuine reference terminal-fibre physical operators.
Use: derive actual complete data indistinguishability for the original physical source executor.
Article: main_krylov, thm:C2(a),(c), exact fixed-base physical oracle family.
Proof: true linear form transport preserves the finite probe sum, and the
actual inverse-root congruence is the positive-root physical congruence.
-/
theorem physical_knownBasePlanarScenario_probe (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e f : EuclideanSpace ℝ (Fin n)) (x y : ℕ → ℝ) (w σ : ℝ) (N k : ℕ) :
    ((knownBasePlanarScenario e f x y w σ).inPhysical (metricRoot A)⁻¹).probe k=
      physicalTerminalSegments A e f x (fun i => σ*y i) (fun _ => 0) N k := by
  change (Scenario.mapForms _ (inverseFormMap (metricRoot A)⁻¹)).probe k=_
  rw [Scenario.mapForms_probe,knownBasePlanarScenario_probe,inverseRootForm A _ hA]
  rfl

/-- Every actual fixed-base planar final operator has the true common cross mean and its signed hidden old diagonal.
Use: identify the exact physical output uncertainty on the genuine common-data fibre.
Article: main_krylov, thm:C2(a),(c), B^σ=M+σΔ.
Proof: the genuine terminal fibre combines the true old-diagonal prefix and
independent terminal term; only their sum changes with the hidden sign.
-/
theorem knownBasePlanarScenario_output (e f : EuclideanSpace ℝ (Fin n))
    (x y : ℕ → ℝ) (w σ : ℝ) (N : ℕ) :
    (knownBasePlanarScenario e f x y w σ).lastOperator N=
      (1+planarMatrix e f 0 (∑ i∈range N, x i) 0)+
        σ • planarMatrix e f ((∑ i∈range N, y i)+w) 0 0 := by
  -- Combine only the actual finite prefix sums of the original source.
  have hsum : (∑ i∈range N, σ*y i)=σ*(∑ i∈range N, y i) := (mul_sum _ _ _).symm
  change (knownBasePlanarScenario e f x y w σ).probe N+planarMatrix e f (σ*w) 0 0=_
  rw [knownBasePlanarScenario_probe]
  simp only [terminalSegments,hsum,planarMatrix,zero_smul,add_zero,zero_add,
    smul_add,smul_smul]
  module

/-- Every globally CG-consistent genuine at-most-one-correction method has one common actual query on the fixed-base planar family and its exact signed terminal outputs.
Use: known-base norm and prior-information lower bounds apply to true execution without an assumed transcript or output response.
Article: main_krylov, thm:C2(a),(c), genuine fixed-base terminal information radius.
Proof: the actual planar oracle identity places this source family in the
proved complete terminal information fibre. Its true complete history,
last probe and searched residual are independent of the hidden sign. The
real one-query correction tree therefore issues the same actual movement.
Normalize its true returned gradient through the actual inverse root and
identify the real final operator as the common mean plus the signed defect.
-/
theorem knownBasePlanarScenario_terminal_form {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) (h1 : OneCorrectionMethod m)
    (x y : ℕ → ℝ) (w : ℝ) :
    let e := canonicalCGUnitStep A g 0
    let f := canonicalCGUnitStep A g N
    let X := ∑ i∈range N, x i
    let Y := ∑ i∈range N, y i
    let ρ := X*Real.sqrt (cgEnergy A g N)
    let M := 1+planarMatrix e f 0 X 0
    let Δ := planarMatrix e f (Y+w) 0 0
    ∃ u : EuclideanSpace ℝ (Fin (N+1)), ∀ σ : ℝ,
      let S := (knownBasePlanarScenario e f x y w σ).inPhysical (metricRoot A)⁻¹
      cgOperator (metricRoot A)⁻¹ (probedGradient m S.probeOracle (S.correctionOracle N) g (N+1))=
        ρ • e+cgOperator (M+σ • Δ) u := by
  -- The real complete-data terminal fibre fixes the same actual final query on every sign.
  let e := canonicalCGUnitStep A g 0
  let f := canonicalCGUnitStep A g N
  let X := ∑ i∈range N, x i
  let H₀ := methodRun m (fun _ => cgOperator A) (fun _ => cgOperator A) g N
  obtain ⟨c,_,hdata⟩ := terminal_data_fibre A hA g hN hcount m hm x
  let z₀ := cgOperator (metricRoot A) (c • (f+X • e))
  let u₀ := firstCorrectionStep (m.correction H₀ z₀)
  refine ⟨cgOperator (metricRoot A) u₀,?_⟩
  intro σ
  let S := (knownBasePlanarScenario e f x y w σ).inPhysical (metricRoot A)⁻¹
  have hp : S.probeOracle=fun i => cgOperator (physicalTerminalSegments A e f x
      (fun i => σ*y i) (fun _ => 0) N i) := by
    funext i
    exact congrArg cgOperator (physical_knownBasePlanarScenario_probe A hA e f x y w σ N i)
  have hd := hdata (fun i => σ*y i) (fun _ => 0) (S.correctionOracle N)
  change _ ∧ _ ∧ _ ∧ _ at hd
  dsimp only [cgOperator] at hp
  have hlast := congrFun hp N
  rw [← hp,← hlast] at hd
  have hH : methodRun m S.probeOracle (S.correctionOracle N) g N=H₀ := hd.1
  have hz : S.probeOracle N (m.direction H₀)=z₀ := by
    have ht := hd.2.1
    rw [hH] at ht
    exact ht
  have hr : cgOperator (metricRoot A)⁻¹ (searchedGradient H₀.gradient (m.direction H₀) z₀)=
      (X*Real.sqrt (cgEnergy A g N)) • e := by
    have ht := hd.2.2.2
    rw [hH,hz] at ht
    exact ht
  have hout : probedGradient m S.probeOracle (S.correctionOracle N) g (N+1)=
      searchedGradient H₀.gradient (m.direction H₀) z₀+cgOperator (S.lastOperator N) u₀ := by
    rw [probedGradient_succ]
    change (runCorrections _ _ _).gradient=_
    rw [one_correction_gradient _ (h1 _ _),hH,hz]
    simp only [Scenario.correctionOracle,ite_eq_right (by omega : ¬ N<N)]
    rfl
  change cgOperator (metricRoot A)⁻¹ (probedGradient m S.probeOracle (S.correctionOracle N) g (N+1))=_
  rw [hout,map_add,hr]
  congr 1
  change cgOperator (metricRoot A)⁻¹
    (cgOperator ((Scenario.mapForms _ (inverseFormMap (metricRoot A)⁻¹)).lastOperator N) u₀)=_
  rw [Scenario.mapForms_lastOperator,inverseRootForm_action A _ hA,knownBasePlanarScenario_output]


/-- The genuine relative operator of every inverse-root physical form is exactly its original canonical matrix.
Use: the known-base physical Frobenius constraints are precisely their actual canonical Frobenius budgets.
Article: main_krylov, thm:C2(a),(c), exact fixed-reference relative form.
Proof: the actual positive roots and their inverses cancel on both sides of the original canonical form. -/
theorem relativeOperator_inverseRootForm (A E : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    relativeOperator A (inverseFormMap (metricRoot A)⁻¹ E)=E := by
  rw [inverseRootForm A E hA]
  simp only [relativeOperator,← Matrix.mul_assoc]
  rw [nonsing_inv_mul _ (metricRoot_det_unit A hA),Matrix.one_mul,Matrix.mul_assoc,
    mul_nonsing_inv _ (metricRoot_det_unit A hA),Matrix.mul_one]

/-- The fixed-base physical signed planar family has exactly the original physical reference as its base.
Use: both genuine lower witnesses have identical source normalization, including when the base is known.
Article: main_krylov, thm:C2(a),(c), A₀^σ=A.
Proof: true inverse-root physical form transport sends the canonical identity exactly to A. -/
theorem physical_knownBasePlanarScenario_base (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e f : EuclideanSpace ℝ (Fin n)) (x y : ℕ → ℝ) (w σ : ℝ) :
    ((knownBasePlanarScenario e f x y w σ).inPhysical (metricRoot A)⁻¹).base=A :=
  inverseRootForm_one A hA

end
end krylov.Information
