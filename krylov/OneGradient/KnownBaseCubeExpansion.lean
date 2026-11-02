import krylov.OneGradient.KnownBaseSourceCube
import krylov.OneGradient.InformedBasisPivot
import krylov.OneGradient.InformedReferenceBound
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), genuine joint known-base source expansion.
Use: derive a common actual cubic output remainder on the full original
finite prior/increment/output source space, before any profile is chosen.
Source: real native informed pivot output, primitive full source data and
exact equality with the actual source oracle/history/output program.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset Filter Topology Asymptotics krylov.Reference krylov.Methods krylov.Secant
  krylov.Information krylov.Stability krylov.Correction krylov.Envelope
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The real semantic output on an original physical source, computed by
the actual informed native S/D policy and its actual source-oracle history.
Use: sharp known-base guarantees quantify original physical scenarios.
Article: main_krylov, thm:local, actual informed source output. -/
def informedScenarioOutput (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (g : EuclideanSpace ℝ (Fin (n+1)))
    (S : Scenario (n+1)) : EuclideanSpace ℝ (Fin (n+1)) :=
  let m := xrfcBasisMethod directions (informedTrial (cgOperator base))
  m.outputGradient (cgOperator (S.lastOperator n)) (oneGradientRun m S.probeOracle g (n+1))

/-- The source's full correlated informed coefficient, retaining its
actual physical prior, each real canonical increment and independent
output form in the known reference metric.
Use: original source budgets apply directly to the actual native output.
Article: main_krylov, thm:local(b), actual full source pivot coefficient. -/
def informedSourcePivotCoefficient
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (g : EuclideanSpace ℝ (Fin (n+1)))
    (S : Scenario (n+1)) : EuclideanSpace ℝ (Fin (n+1)) :=
  let E := canonicalIncrement base (oneGradientScenarioMatrices S n)
  let h := canonicalCGUnitStep base g n
  let q := inner ℝ h (cgOperator (relativeOperator base (S.base-base)+∑ l∈range n,E l) h)
  staircaseOperator base g E (E n) (n+1) (freshDefect base g E (n+1))+q • cgOperator (E n) h

/-- A genuine informed S output expansion on arbitrary original physical
source families follows from primitive query/output matrix regularity.
Use: one native/source theorem covers both the whole finite source cube
and actual original physical attaining families without copied execution
or output-jet proofs.
Article: main_krylov, thm:local(b), genuine source-family cubic expansion.
Proof: apply the actual native pivot-output theorem to the true extended
source matrices. Their exact first-base, complete actual source history
and independent output dictionaries identify the original source expression. -/
theorem informed_basis_scenario_output_cubic (directions : Bool) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (S : X → Scenario (n+1))
    (hM : ∀ j,ContDiffAt ℝ 1 (fun z => oneGradientScenarioMatrices (S z) n j) 0)
    (hsym : ∀ z j,(oneGradientScenarioMatrices (S z) n j).IsSymm)
    (hzero : ∀ j,oneGradientScenarioMatrices (S 0) n j=base) :
    (fun z => cgOperator (metricRoot base)⁻¹ (informedScenarioOutput directions base g (S z))+
      ‖cgCanonicalError base g n‖ • informedSourcePivotCoefficient base g (S z))
        =O[𝓝 0] (fun z => ‖z‖^3) := by
  let A := fun Theta j => oneGradientScenarioMatrices (S Theta) n j
  let trial := informedTrial (cgOperator base)
  let m := xrfcBasisMethod directions trial
  have h := informed_basis_pivot_output_cubic directions base hb g hc A hM hsym hzero
  apply h.congr_left
  intro Theta
  have hout : m.outputGradient (cgOperator (A Theta (n+1)))
      (oneGradientRun m (fun j => cgOperator (A Theta j)) g (n+1))=
        informedScenarioOutput directions base g (S Theta) := by
    change m.outputGradient (cgOperator (oneGradientScenarioMatrices (S Theta) n (n+1)))
      (oneGradientRun m (fun j => cgOperator (oneGradientScenarioMatrices (S Theta) n j)) g (n+1))=_
    rw [oneGradientScenarioMatrices_output,oneGradientScenarioMatrices_histories (S Theta) n m g (n+1) le_rfl]
    rfl
  change cgOperator (metricRoot base)⁻¹
    (m.outputGradient (cgOperator (A Theta (n+1))) (oneGradientRun m (fun j => cgOperator (A Theta j)) g (n+1)))+_=_
  rw [hout]
  change _+‖cgCanonicalError base g n‖ •
    (staircaseOperator base g (canonicalIncrement base (A Theta)) (canonicalIncrement base (A Theta) n) (n+1)
      (freshDefect base g (canonicalIncrement base (A Theta)) (n+1))+
        inner ℝ (canonicalCGUnitStep base g n)
          (cgOperator (relativeOperator base (A Theta 0-base)+
            ∑ l∈range n,canonicalIncrement base (A Theta) l) (canonicalCGUnitStep base g n)) •
              cgOperator (canonicalIncrement base (A Theta) n) (canonicalCGUnitStep base g n))=_
  have hzero : A Theta 0=(S Theta).base := oneGradientScenarioMatrices_zero (S Theta) n
  rw [hzero]
  rfl

/-- The original S specialization of the common both-basis source theorem.
Use: preserve the established step-policy source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the genuine shared source theorem to the S basis. -/
theorem informed_scenario_output_cubic {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (S : X → Scenario (n+1))
    (hM : ∀ j,ContDiffAt ℝ 1 (fun z => oneGradientScenarioMatrices (S z) n j) 0)
    (hsym : ∀ z j,(oneGradientScenarioMatrices (S z) n j).IsSymm)
    (hzero : ∀ j,oneGradientScenarioMatrices (S 0) n j=base) :
    (fun z => cgOperator (metricRoot base)⁻¹ (informedScenarioOutput false base g (S z))+
      ‖cgCanonicalError base g n‖ • informedSourcePivotCoefficient base g (S z))
        =O[𝓝 0] (fun z => ‖z‖^3)  := by
  exact informed_basis_scenario_output_cubic false base hb g hc S hM hsym hzero

/-- The genuine informed S output on the entire original finite source
cube has its fully computed correlated leading coefficient and a cubic
remainder jointly in all actual source parameters. The policy sees only
the real source oracle, and the terminal form remains unevaluated.
Use: one common source-wide remainder follows before fixing any prior or
individual query/output profile, rather than merely along smooth paths.
Article: main_krylov, thm:local(b), complete joint physical source expansion.
Proof: primitive full source coordinate data give the genuine C-one native
matrix family. Apply the actual native pivot-output theorem, then use the
exact source query/output history dictionary and actual first-base identity. -/
theorem knownBaseSourceCube_basis_output_cubic (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    (fun Theta : symmetricScenarios (n+1) (n+1) =>
      cgOperator (metricRoot base)⁻¹ (informedScenarioOutput directions base g (knownBaseSourceCube base Theta))+
        ‖cgCanonicalError base g n‖ • informedSourcePivotCoefficient base g (knownBaseSourceCube base Theta))
      =O[𝓝 0] (fun Theta => ‖Theta‖^3) := by
  have hdata := knownBaseSourceCube_operator_data base hb
  exact informed_basis_scenario_output_cubic directions base hb g hc (knownBaseSourceCube base)
    hdata.1 hdata.2.1 hdata.2.2

/-- The original S specialization of the common both-basis source theorem.
Use: preserve the established step-policy source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the genuine shared source theorem to the S basis. -/
theorem knownBaseSourceCube_output_cubic
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    (fun Theta : symmetricScenarios (n+1) (n+1) =>
      cgOperator (metricRoot base)⁻¹ (informedScenarioOutput false base g (knownBaseSourceCube base Theta))+
        ‖cgCanonicalError base g n‖ • informedSourcePivotCoefficient base g (knownBaseSourceCube base Theta))
      =O[𝓝 0] (fun Theta => ‖Theta‖^3)  := by
  exact knownBaseSourceCube_basis_output_cubic false base hb g hc

/-- A single positive radius and cubic constant control the actual
informed S output remainder for every full original symmetric source tuple.
Use: the constant is chosen before all physical scenarios and budget profiles.
Article: main_krylov, thm:local(b), genuine uniform full-source cubic tube.
Proof: unpack the proved joint actual source big-O remainder and take a
real metric neighborhood of the zero tuple in the existing source subspace. -/
theorem knownBaseSourceCube_basis_cubic_tube (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ delta C : ℝ,0<delta ∧ 0<C ∧ ∀ Theta : symmetricScenarios (n+1) (n+1),‖Theta‖<delta →
      ‖cgOperator (metricRoot base)⁻¹ (informedScenarioOutput directions base g (knownBaseSourceCube base Theta))+
        ‖cgCanonicalError base g n‖ • informedSourcePivotCoefficient base g (knownBaseSourceCube base Theta)‖≤C*‖Theta‖^3 := by
  obtain ⟨C,hC,hbound⟩ := isBigO_iff'.mp (knownBaseSourceCube_basis_output_cubic directions base hb g hc)
  obtain ⟨delta,hdelta,hnear⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨delta,C,hdelta,hC,?_⟩
  intro Theta hTheta
  have h := hnear (by simpa only [dist_zero_right] using hTheta)
  simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg Theta) 3)] using h

/-- The original S specialization of the common both-basis source theorem.
Use: preserve the established step-policy source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the genuine shared source theorem to the S basis. -/
theorem knownBaseSourceCube_cubic_tube
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ delta C : ℝ,0<delta ∧ 0<C ∧ ∀ Theta : symmetricScenarios (n+1) (n+1),‖Theta‖<delta →
      ‖cgOperator (metricRoot base)⁻¹ (informedScenarioOutput false base g (knownBaseSourceCube base Theta))+
        ‖cgCanonicalError base g n‖ • informedSourcePivotCoefficient base g (knownBaseSourceCube base Theta)‖≤C*‖Theta‖^3  := by
  exact knownBaseSourceCube_basis_cubic_tube false base hb g hc

/-- The actual correlated coefficient of every original physical source
has the full sharp informed bound in its true known-reference budgets.
Use: source-wide upper estimates quantify every individual physical
increment and the independent terminal form, before any path is chosen.
Article: main_krylov, thm:local(b), actual physical source leading bound.
Proof: the genuine source/native canonical increment dictionary gives each
real query and terminal form. Apply the existing exact source CG bound. -/
theorem informedSourcePivotCoefficient_bound
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (S : Scenario (n+1)) (omega : ℕ → ℝ) (w c : ℝ)
    (hinc : ∀ l<n,(S.increment l).IsSymm ∧ relativeBudget base (S.increment l)≤omega l)
    (hterm : relativeBudget base S.terminal≤w) (hprior : relativeBudget base (S.base-base)≤c) :
    ‖informedSourcePivotCoefficient base g S‖≤ informedConstant (∑ l∈range n,omega l) w c := by
  let E := canonicalIncrement base (oneGradientScenarioMatrices S n)
  have hE (l : ℕ) (hl : l∈range n) : E l=relativeOperator base (S.increment l) := by
    simp only [E,oneGradientScenarioMatrices_canonicalIncrement,ite_eq_left (mem_range.mp hl)]
  have hF : E n=relativeOperator base S.terminal := by
    simp only [E,oneGradientScenarioMatrices_canonicalIncrement,lt_self_iff_false,ite_false,ite_true]
  exact informed_reference_second_order_bound base hb g hc E
    (fun l hl => hE l hl ▸ relativeOperator_isSymm base _ (hinc l (mem_range.mp hl)).1)
    omega (fun l hl => by rw [hE l hl];exact (hinc l (mem_range.mp hl)).2)
    (relativeOperator base (S.base-base)) (E n) w c (by rw [hF];exact hterm) hprior

/-- One genuine common cube radius and cubic constant give the full
actual informed S source upper estimate for every independent known-base
prior and increment/output budget profile simultaneously.
Use: the actual whole-source upper remainder is uniform before all source
matrices and profiles, and retains the sharp correlated K_X coefficient.
Article: main_krylov, thm:local(b), uniform full-source informed upper bound.
Proof: take the common true cubic tube and bound its actual source leading
coefficient by the existing sharp informed physical source inequality.
The real norm triangle bound transfers this to the true semantic output. -/
theorem knownBaseSourceCube_basis_uniform_upper (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ delta C : ℝ,0<delta ∧ 0<C ∧ ∀ Theta : symmetricScenarios (n+1) (n+1),‖Theta‖<delta →
      ∀ (omega : ℕ → ℝ) (w c : ℝ),
      (∀ l<n,((knownBaseSourceCube base Theta).increment l).IsSymm ∧
        relativeBudget base ((knownBaseSourceCube base Theta).increment l)≤omega l) →
      relativeBudget base (knownBaseSourceCube base Theta).terminal≤w →
      relativeBudget base ((knownBaseSourceCube base Theta).base-base)≤c →
      ‖cgOperator (metricRoot base)⁻¹ (informedScenarioOutput directions base g (knownBaseSourceCube base Theta))‖≤
        ‖cgCanonicalError base g n‖*informedConstant (∑ l∈range n,omega l) w c+C*‖Theta‖^3 := by
  obtain ⟨delta,C,hd,hC,htube⟩ := knownBaseSourceCube_basis_cubic_tube directions base hb g hc
  refine ⟨delta,C,hd,hC,?_⟩
  intro Theta hTheta omega w c hinc hterm hprior
  let S := knownBaseSourceCube base Theta
  let v := informedSourcePivotCoefficient base g S
  let out := cgOperator (metricRoot base)⁻¹ (informedScenarioOutput directions base g S)
  let sigma := ‖cgCanonicalError base g n‖
  have hv : ‖v‖≤ informedConstant (∑ l∈range n,omega l) w c :=
    informedSourcePivotCoefficient_bound base hb g hc S omega w c hinc hterm hprior
  have hlead : ‖sigma • v‖≤sigma*informedConstant (∑ l∈range n,omega l) w c := by
    rw [norm_smul,Real.norm_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left hv (norm_nonneg _)
  have hr : ‖out+sigma • v‖≤C*‖Theta‖^3 := htube Theta hTheta
  have htriangle := norm_sub_le (out+sigma • v) (sigma • v)
  rw [add_sub_cancel_right] at htriangle
  exact htriangle.trans ((add_le_add hr hlead).trans_eq (add_comm _ _))

/-- The original S specialization of the common both-basis source theorem.
Use: preserve the established step-policy source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the genuine shared source theorem to the S basis. -/
theorem knownBaseSourceCube_uniform_upper
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ delta C : ℝ,0<delta ∧ 0<C ∧ ∀ Theta : symmetricScenarios (n+1) (n+1),‖Theta‖<delta →
      ∀ (omega : ℕ → ℝ) (w c : ℝ),
      (∀ l<n,((knownBaseSourceCube base Theta).increment l).IsSymm ∧
        relativeBudget base ((knownBaseSourceCube base Theta).increment l)≤omega l) →
      relativeBudget base (knownBaseSourceCube base Theta).terminal≤w →
      relativeBudget base ((knownBaseSourceCube base Theta).base-base)≤c →
      ‖cgOperator (metricRoot base)⁻¹ (informedScenarioOutput false base g (knownBaseSourceCube base Theta))‖≤
        ‖cgCanonicalError base g n‖*informedConstant (∑ l∈range n,omega l) w c+C*‖Theta‖^3  := by
  exact knownBaseSourceCube_basis_uniform_upper false base hb g hc

end
end krylov.OneGradient
