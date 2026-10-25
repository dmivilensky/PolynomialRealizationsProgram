import chebyshev1.SineJacobi.PanelCertificates
import Lean.Elab.Tactic.Decide

/-!
Article: chebyshev1, Theorem 5.2, seven-decimal sine energy.
`chebyshev1.Numerics.energyCertificateCandidates` proposes interval witnesses for the
`energy_certificate` tactic used by `chebyshev1.SineJacobi.sineEnergy_decimal` in
`SineJacobi/EnergyDecimal`.
Use: the tactic constructs literal safe data, kernel-proves each panel acceptance and combines the
proofs; witness generation itself is outside the mathematical trust boundary.
Source: Lean.Elab.Tactic.Decide.mkDecideProof — kernel reduction of a decidable proposition.
-/
namespace chebyshev1.Numerics
open LeanCert.Core chebyshev1.SineJacobi

/--
Propose a finite Landen descent for an elliptic integral at the modulus interval `I`. At each
step, store a square-root interval and the resulting elliptic-value interval. Stop after `n`
steps or when the squared modulus is at most `10⁻¹²`; the latter uses the small-modulus
residual bound. This function supplies the two elliptic witnesses in `energyWitnessCandidate`,
ultimately for chebyshev1, Theorem 5.2's energy value. These are proposed data:
`ellipticWitnessCheck` verifies all root and descent bounds.

Use: `chebyshev1.Numerics.energyWitnessCandidate` uses this definition in the displayed
construction of `energyWitnessCandidate`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev1, Theorem 5.2, seven-decimal sine energy.

Source: Lean.Elab.Tactic.Decide.mkDecideProof — kernel reduction of a decidable proposition.
-/
def rootWitnesses : ℕ → IntervalRat → Option (List EllipticWitness)
  | n, I => do
    let R := root (IntervalRat.sub (IntervalRat.singleton 1) I)
    let w : RootWitness := intervalWitness R
    if I.hi ≤ (1/10^12:ℚ) ∨ n = 0 then
      pure [(w, intervalWitness (residualBounds w))]
    else
      let ws ← rootWitnesses (n-1) (rounded (IntervalRat.pow (modulusBounds w) 2))
      pure ((w, intervalWitness (descentBounds w (ellipticWitnessValue ws)))::ws)
termination_by n _ => n

/--
Propose `n` successive cosine-doubling enclosures, beginning with `I`. Used by
`cosineWitnessCandidate` to move from the small-angle cosine expansion to the argument needed
in the elliptic energy integrand (chebyshev1, Theorem 5.2). Each stored step is subsequently
checked by `cosineWitnessCheck`.

Use: `chebyshev1.Numerics.cosineWitnessCandidate` uses this definition in the displayed
construction of `cosineWitnessCandidate`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev1, Theorem 5.2, seven-decimal sine energy.

Source: Lean.Elab.Tactic.Decide.mkDecideProof — kernel reduction of a decidable proposition.
-/
def doubleWitnessCandidates : ℕ → IntervalRat → List IntervalWitness
  | 0, _ => []
  | n+1, I =>
    let w := intervalWitness (cosineDouble I)
    w::doubleWitnessCandidates n (proposedInterval w)

/--
Propose the initial cosine enclosure and six doubling steps for the argument `I`.
`energyWitnessCandidate` uses the resulting value to enclose both complementary elliptic moduli
in the sine-energy formula of chebyshev1, Theorem 5.2.

Use: `chebyshev1.Numerics.energyWitnessCandidate` uses this definition in the displayed
construction of `energyWitnessCandidate`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev1, Theorem 5.2, seven-decimal sine energy.

Source: Lean.Elab.Tactic.Decide.mkDecideProof — kernel reduction of a decidable proposition.
-/
def cosineWitnessCandidate (I : IntervalRat) : CosineWitness :=
  let w := intervalWitness (cosineInitial I)
  (w, doubleWitnessCandidates 6 (proposedInterval w))

/--
Propose the cosine and two elliptic witnesses for the energy integrand at `t`. Failure to
construct either finite descent propagates as `none`; it cannot become a proof.
`panelWitnessCandidate` uses this data at its three quadrature nodes, and `energyWitnessCheck`
supplies acceptance for chebyshev1, Theorem 5.2.

Use: `chebyshev1.Numerics.panelWitnessCandidate` uses this definition in the displayed
construction of `panelWitnessCandidate`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev1, Theorem 5.2, seven-decimal sine energy.

Source: Lean.Elab.Tactic.Decide.mkDecideProof — kernel reduction of a decidable proposition.
-/
def energyWitnessCandidate (t : ℚ) : Option EnergyWitness := do
  let c := cosineWitnessCandidate (energyArgument t)
  let X := (energyModuli c).1
  let Y := (energyModuli c).2
  let A ← rootWitnesses 5 X
  let B ← rootWitnesses 5 Y
  pure ⟨c,A,B⟩

/--
Propose endpoint/midpoint integrand witnesses on graded panel `j` of `N`. The change of
variables is `t = x³/2`; the three displayed rational arguments are its values at the panel's
left endpoint, midpoint and right endpoint. `panelCertificateCandidate` turns them into a
candidate Simpson-panel enclosure for the sine-energy proof of chebyshev1, Theorem 5.2.

Use: `chebyshev1.Numerics.panelCertificateCandidate` uses this definition in the displayed
construction of `panelCertificateCandidate`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev1, Theorem 5.2, seven-decimal sine energy.

Source: Lean.Elab.Tactic.Decide.mkDecideProof — kernel reduction of a decidable proposition.
-/
def panelWitnessCandidate (N j : ℕ) : Option PanelWitness := do
  let A ← energyWitnessCandidate (((j:ℚ)/N)^3/2)
  let B ← energyWitnessCandidate (((2*j+1:ℚ)/(2*N))^3/2)
  let C ← energyWitnessCandidate (((j+1:ℚ)/N)^3/2)
  pure ⟨A,B,C⟩

/--
Pair a panel's three integrand proposals with its computed quadrature interval.
`energyCertificateCandidates` collects these records; `panelCertificateCheck` validates their
numerical content against the proved quadrature error bound. Article chain: chebyshev1,
Theorem 5.2, via `sineEnergy_decimal`.

Use: `chebyshev1.Numerics.energyCertificateCandidates` uses this definition in the
displayed construction of `energyCertificateCandidates`. Its inputs and component formulas are
fixed by that definition.

Source: Lean.Elab.Tactic.Decide.mkDecideProof — kernel reduction of a decidable proposition.
-/
def panelCertificateCandidate (N j : ℕ) : Option PanelCertificate := do
  let w ← panelWitnessCandidate N j
  let I := panelWitnessValue N j w
  pure ⟨w, intervalWitness I⟩

/--
Propose all panels numbered `1, …, N-1`, omitting the separately controlled singular first
panel. `energy_certificate` quotes this list as safe literal Lean data, then proves every
acceptance obligation by kernel reduction. Article chain: chebyshev1, Theorem 5.2, via
`sineEnergy_decimal`.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Source: Lean.Elab.Tactic.Decide.mkDecideProof — kernel reduction of a decidable proposition.
-/
def energyCertificateCandidates (N : ℕ) : Option (List PanelCertificate) :=
  (List.range (N-1)).mapM fun j => panelCertificateCandidate N (j+1)

end chebyshev1.Numerics

set_option synthInstance.maxSize 256 in
open Lean Meta Elab Tactic in
/-- Propose data natively, kernel-check small groups, and compose their proofs.
Every generated definition and lemma is checked by the kernel.
Use: `SineJacobi.verifiedQuadrature` invokes the tactic to discharge the complete
panel-certificate goal. Native evaluation proposes values; it is never the proof
of the acceptance proposition. Source: `mkDecideProof` and the proved append rule.
Article: chebyshev1, Theorem 5.2, via `SineJacobi.sineEnergy_decimal`. -/
elab "energy_certificate " N:num : tactic => do
  -- Native evaluation is used only to obtain proposed rational intervals. It does
  -- not prove the goal: the proposals are quoted back into safe kernel declarations.
  let n := N.getNat
  let expression := mkApp (mkConst ``chebyshev1.Numerics.energyCertificateCandidates) (toExpr n)
  let type ← inferType expression
  let candidates ← unsafe evalExpr (Option (List chebyshev1.SineJacobi.PanelCertificate)) type expression
  let some witnesses := candidates | throwError "Energy witness generation failed"
  let listType := toTypeExpr (List chebyshev1.SineJacobi.PanelCertificate)
  let addData (value : Expr) : TacticM Name := do
    -- Store explicit witness terms, rather than importing a trusted native result.
    let name ← mkAuxDeclName (kind := `_energyWitnessData)
    addDecl (.defnDecl {
      name := name
      levelParams := []
      type := listType
      value := value
      hints := .abbrev
      safety := .safe })
    return name
  let accepted (j : Nat) (dataName : Name) : TacticM Expr := do
    -- Acceptance is a decidable proposition about this exact named witness list.
    mkEq (mkApp3 (mkConst ``chebyshev1.SineJacobi.panelsAccepted) (toExpr n) (toExpr j)
      (mkConst dataName)) (mkConst ``Bool.true)
  let data := witnesses.toArray
  let mut groups : Array (Nat × Name × Name) := #[]
  for k in [: (data.size+7)/8] do
    -- Eight-panel groups keep reduction memory bounded. mkDecideProof constructs
    -- an ordinary proof whose validity follows from kernel reduction of the checker.
    let j := 8*k+1
    let chunk := (data.extract (8*k) (min (8*k+8) data.size)).toList
    let name ← addData (toExpr chunk)
    let proposition ← accepted j name
    let proof ← mkDecideProof proposition
    let lemmaName ← withOptions (Elab.async.set · false) do
      mkAuxLemma [] proposition proof
    groups := groups.push (j, name, lemmaName)
    if k%16 == 15 then
      IO.eprintln s!"Kernel checked {min (8*k+8) data.size}/{data.size} energy panels"
  let mut suffix ← addData (toExpr ([] : List chebyshev1.SineJacobi.PanelCertificate))
  let nilProp ← accepted (data.size+1) suffix
  let mut certified ← mkAuxLemma [] nilProp (← mkDecideProof nilProp)
  for (j, chunk, headProof) in groups.reverse do
    -- Assemble checked groups from the end using the proved append rule. This
    -- avoids reducing the entire long witness list in a single decision proof.
    let appended := mkApp3 (mkConst ``List.append [Level.zero])
      (toTypeExpr chebyshev1.SineJacobi.PanelCertificate) (mkConst chunk) (mkConst suffix)
    let next ← addData appended
    let proof := mkAppN (mkConst ``chebyshev1.SineJacobi.panelsAccepted_append_true)
      #[toExpr n, toExpr j, mkConst chunk, mkConst suffix, mkConst headProof, mkConst certified]
    certified ← mkAuxLemma [] (← accepted j next) proof
    suffix := next
  evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
  let witnessGoal :: proofGoals ← getGoals | throwError "Expected an existential witness goal"
  witnessGoal.assign (mkConst suffix)
  setGoals proofGoals
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  if goalType.isAppOfArity ``Eq 3 && (goalType.getAppArgs[1]!).isAppOf ``chebyshev1.SineJacobi.panelsAccepted then
    goal.assign (mkConst certified)
    setGoals []
  else
    -- The quadrature-certificate goal also needs the list length and total bound.
    -- These remaining finite arithmetic obligations are checked by the kernel too.
    evalTactic (← `(tactic| refine chebyshev1.SineJacobi.panelCertificateCheck_intro ?_ ?_ ?_))
    let [lengthGoal, acceptedGoal, boundGoal] ← getGoals | throwError "Expected certificate goals"
    acceptedGoal.assign (mkConst certified)
    setGoals [lengthGoal, boundGoal]
    evalTactic (← `(tactic| all_goals decide +kernel))
