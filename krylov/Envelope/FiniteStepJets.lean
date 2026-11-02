import krylov.Envelope.FiniteObservationJets

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), actual recorded-step finite oracle first jets.
Use: transfer true recorded-step derivatives through the actual finite
operator-coordinate chart, preserving genuine earlier prefixes and
deriving real regularity from primitive observed coefficients.
Source: genuine full-history prefix execution and actual raw-step
primitive smoothness, followed by the true finite oracle chain rule.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual finite operator extension executes every genuine shorter history prefix exactly.
Use: The actual finite operator extension executes every genuine shorter history prefix exactly.
Article: main_krylov, apB:lem:mu(c), actual recorded-step finite oracle first jets.
Proof: Every real queried operator before the true prefix endpoint reads its actual finite coordinate. -/
theorem finiteOracleExtension_run_prefix (m : ProbedMethod E) (Q : E →L[ℝ] E) (A B : ℕ → E →L[ℝ] E)
    (g : E) (N k : ℕ) (hk : k≤N) :
    methodRun m (finiteOracleExtension Q (fun i : Fin N => A i.val))
      (finiteOracleExtension Q (fun i : Fin N => B i.val)) g k=methodRun m A B g k :=
  methodRun_congr_prefix m _ _ _ _ g k (fun _ hi => dite_eq_left (hi.trans_le hk))
    (fun _ hi => dite_eq_left (hi.trans_le hk))

/-- The actual finite operator extension preserves every genuine recorded step before its true horizon.
Use: The actual finite operator extension preserves every genuine recorded step before its true horizon.
Article: main_krylov, apB:lem:mu(c), actual recorded-step finite oracle first jets.
Proof: Read the real newest-step observation from the exact actual extended prefix history. -/
theorem finiteOracleExtension_step (m : ProbedMethod E) (Q : E →L[ℝ] E) (A B : ℕ → E →L[ℝ] E)
    (g : E) (N k : ℕ) (hk : k<N) :
    probedStep m (finiteOracleExtension Q (fun i : Fin N => A i.val))
      (finiteOracleExtension Q (fun i : Fin N => B i.val)) g k=probedStep m A B g k :=
  congrArg (fun H : History E => H.observationList.getD 4 0)
    (finiteOracleExtension_run_prefix m Q A B g N (k+1) hk)

/-- Every actual recorded step has a genuine primitive-derived C-two finite operator-coordinate chart.
Use: Every actual recorded step has a genuine primitive-derived C-two finite operator-coordinate chart.
Article: main_krylov, apB:lem:mu(c), actual recorded-step finite oracle first jets.
Proof: Apply the true primitive smooth recorded-field theorem to actual finite operator coordinate projections. -/
theorem finiteOracle_step_regular (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ k<N, CG.gradient Q g k≠0)
    (hsmooth : SmoothProbedCycleAt m 2 Q g N) (k : ℕ) (hk : k<N) :
    ContDiffAt ℝ 2 (fun p : (Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E) =>
      probedStep m (finiteOracleExtension Q p.1) (finiteOracleExtension Q p.2) g k)
      ((fun _ => Q),(fun _ => Q)) := by
  -- Derive genuine recorded-step regularity from the actual primitive full-history coefficient representation.
  have hf := smoothProbed_fields_regular m hm
    (fun p : (Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E) => finiteOracleExtension Q p.1)
    (fun p => finiteOracleExtension Q p.2) (fun _ => g) ((fun _ => Q),(fun _ => Q)) N
    (fun i hi => by simp only [finiteOracleExtension,dite_eq_left hi];exact (contDiffAt_pi.mp contDiffAt_fst) (⟨i,hi⟩ : Fin N))
    (fun i hi => by simp only [finiteOracleExtension,dite_eq_left hi];exact (contDiffAt_pi.mp contDiffAt_snd) (⟨i,hi⟩ : Fin N))
    contDiffAt_const Q (finiteOracleExtension_reference N Q) (finiteOracleExtension_reference N Q)
    hQ hpos hpre hsmooth k hk
  exact hf.2.2.1

/-- Actual recorded steps have equal genuine first derivatives on real operator paths sharing all true finite reference inputs and operator first jets.
Use: Actual recorded steps have equal genuine first derivatives on real operator paths sharing all true finite reference inputs and operator first jets.
Article: main_krylov, apB:lem:mu(c), actual recorded-step finite oracle first jets.
Proof: Use the genuine finite oracle derivative chain rule on the actual smooth recorded-step map and identify both real finite extensions with their true step prefixes. -/
theorem actual_step_firstJet_transfer (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ k<N, CG.gradient Q g k≠0) (hsmooth : SmoothProbedCycleAt m 2 Q g N)
    (A B A' B' : ℝ → ℕ → E →L[ℝ] E) (dA dB : ℕ → E →L[ℝ] E)
    (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hA0' : A' 0=fun _ => Q) (hB0' : B' 0=fun _ => Q)
    (hA : ∀ i<N, HasDerivAt (fun t => A t i) (dA i) 0)
    (hB : ∀ i<N, HasDerivAt (fun t => B t i) (dB i) 0)
    (hA' : ∀ i<N, HasDerivAt (fun t => A' t i) (dA i) 0)
    (hB' : ∀ i<N, HasDerivAt (fun t => B' t i) (dB i) 0) (k : ℕ) (hk : k<N) :
    deriv (fun t => probedStep m (A t) (B t) g k) 0=
      deriv (fun t => probedStep m (A' t) (B' t) g k) 0 := by
  -- Transfer the actual recorded-step derivative on the true finite operator chart, then recover both genuine original prefixes.
  have hf := finiteOracle_step_regular m hm Q hQ hpos g N hpre hsmooth k hk
  have he := finiteOracle_firstJet_transfer Q N
    (fun p => probedStep m (finiteOracleExtension Q p.1) (finiteOracleExtension Q p.2) g k)
    (hf.differentiableAt (by norm_num)) A B A' B' dA dB hA0 hB0 hA0' hB0' hA hB hA' hB'
  have hleft : (fun t => probedStep m (finiteOracleExtension Q (fun i : Fin N => A t i.val))
      (finiteOracleExtension Q (fun i : Fin N => B t i.val)) g k)=fun t => probedStep m (A t) (B t) g k := by
    funext t
    exact finiteOracleExtension_step m Q (A t) (B t) g N k hk
  have hright : (fun t => probedStep m (finiteOracleExtension Q (fun i : Fin N => A' t i.val))
      (finiteOracleExtension Q (fun i : Fin N => B' t i.val)) g k)=fun t => probedStep m (A' t) (B' t) g k := by
    funext t
    exact finiteOracleExtension_step m Q (A' t) (B' t) g N k hk
  rwa [hleft,hright] at he
end
end krylov.Envelope
