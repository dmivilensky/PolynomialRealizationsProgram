import krylov.Envelope.OracleFirstJets
import krylov.Methods.SmoothTrace

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), actual full-observation first-jet transfer.
Use: transfer genuine first variations of every real observation coordinate,
including all intermediate correction answers, probes and recorded steps,
from actual finite operator paths with equal true first jets.
Source: primitive smooth full-history charts and genuine finite-oracle
Frechet chain rules, preserving the actual query boundaries.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual full-history observation coordinate has a genuine primitive-derived C-two chart in the true finite line and correction operator coordinates.
Use: Every actual full-history observation coordinate has a genuine primitive-derived C-two chart in the true finite line and correction operator coordinates.
Article: main_krylov, apB:lem:mu(c), actual full-observation first-jet transfer.
Proof: Apply genuine full-trace primitive smoothness to actual finite operator coordinate projections and read the true observation coordinate with its real zero default. -/
theorem finiteOracle_observation_regular (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ k<N, CG.gradient Q g k≠0)
    (hsmooth : SmoothProbedCycleAt m 2 Q g N) (j : ℕ) :
    ContDiffAt ℝ 2 (fun p : (Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E) =>
      (methodRun m (finiteOracleExtension Q p.1) (finiteOracleExtension Q p.2) g N).observationList.getD j 0)
      ((fun _ => Q),(fun _ => Q)) := by
  -- Derive the genuine complete observation chart from primitive coefficients before reading its actual selected coordinate.
  apply SmoothListAt.getD (i := j)
  apply smoothProbed_trace_regular m hm
    (fun p : (Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E) => finiteOracleExtension Q p.1)
    (fun p => finiteOracleExtension Q p.2) (fun _ => g) ((fun _ => Q),(fun _ => Q)) N _ _ contDiffAt_const Q
    (finiteOracleExtension_reference N Q) (finiteOracleExtension_reference N Q) hQ hpos hpre hsmooth
  · intro k hk
    simp only [finiteOracleExtension,dite_eq_left hk]
    exact (contDiffAt_pi.mp contDiffAt_fst) (⟨k,hk⟩ : Fin N)
  · intro k hk
    simp only [finiteOracleExtension,dite_eq_left hk]
    exact (contDiffAt_pi.mp contDiffAt_snd) (⟨k,hk⟩ : Fin N)

/-- Every genuine actual observation coordinate has the same first derivative on true finite operator paths sharing their real reference input and all actual operator first jets.
Use: Every genuine actual observation coordinate has the same first derivative on true finite operator paths sharing their real reference input and all actual operator first jets.
Article: main_krylov, apB:lem:mu(c), actual full-observation first-jet transfer.
Proof: Derive the genuine full-trace coordinate regularity, apply the actual finite-oracle chain rule and identify each real finite extended executor with its true original full-history prefix. -/
theorem actual_observation_firstJet_transfer (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ k<N, CG.gradient Q g k≠0) (hsmooth : SmoothProbedCycleAt m 2 Q g N)
    (A B A' B' : ℝ → ℕ → E →L[ℝ] E) (dA dB : ℕ → E →L[ℝ] E)
    (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hA0' : A' 0=fun _ => Q) (hB0' : B' 0=fun _ => Q)
    (hA : ∀ i<N, HasDerivAt (fun t => A t i) (dA i) 0)
    (hB : ∀ i<N, HasDerivAt (fun t => B t i) (dB i) 0)
    (hA' : ∀ i<N, HasDerivAt (fun t => A' t i) (dA i) 0)
    (hB' : ∀ i<N, HasDerivAt (fun t => B' t i) (dB i) 0) (j : ℕ) :
    deriv (fun t => (methodRun m (A t) (B t) g N).observationList.getD j 0) 0=
      deriv (fun t => (methodRun m (A' t) (B' t) g N).observationList.getD j 0) 0 := by
  -- The true finite-coordinate chain rule transfers every actual observation; exact genuine prefix execution identifies both real paths.
  have hf := finiteOracle_observation_regular m hm Q hQ hpos g N hpre hsmooth j
  have he := finiteOracle_firstJet_transfer Q N
    (fun p => (methodRun m (finiteOracleExtension Q p.1) (finiteOracleExtension Q p.2) g N).observationList.getD j 0)
    (hf.differentiableAt (by norm_num)) A B A' B' dA dB hA0 hB0 hA0' hB0' hA hB hA' hB'
  have hleft : (fun t => (methodRun m (finiteOracleExtension Q (fun i : Fin N => A t i.val))
      (finiteOracleExtension Q (fun i : Fin N => B t i.val)) g N).observationList.getD j 0)=
      fun t => (methodRun m (A t) (B t) g N).observationList.getD j 0 := by
    funext t
    rw [finiteOracleExtension_run]
  have hright : (fun t => (methodRun m (finiteOracleExtension Q (fun i : Fin N => A' t i.val))
      (finiteOracleExtension Q (fun i : Fin N => B' t i.val)) g N).observationList.getD j 0)=
      fun t => (methodRun m (A' t) (B' t) g N).observationList.getD j 0 := by
    funext t
    rw [finiteOracleExtension_run]
  rwa [hleft,hright] at he
end
end krylov.Envelope
