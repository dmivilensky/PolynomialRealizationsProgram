import krylov.Envelope.ActualObservationFiltration
import krylov.Envelope.ActualGradientJet
import krylov.Envelope.FrozenFiltration

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, actual smooth-method frozen response.
Use: identify the real common frozen first variation of every genuinely
smooth source-admissible globally CG-consistent raw method, modulo the true
physical Krylov displacement flag and its actual reference-operator image.
Source: proved complete real observed-history filtration, genuine executed
gradient-variation balance and actual measured-coefficient physical frozen
recurrence; no coherence or cycle expansion remains as an extra premise.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Methods krylov.Reference
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true physical reference-step injection measured from the actual segment-operator first derivative.
Use: The true physical reference-step injection measured from the actual segment-operator first derivative.
Article: main_krylov, apB:lem:filtration, actual smooth-method frozen response.
Proof: Evaluate the actual primitive oracle derivative on the genuine executed CG step; the empty injection is zero. -/
def referenceInjection (Q : E →L[ℝ] E) (g : E) (A : ℝ → ℕ → E →L[ℝ] E) : ℕ → E
  | 0 => 0
  | k+1 => deriv (fun t => A t k) 0 (referenceStep Q g k)

/-- Every genuine smooth source-admissible globally CG-consistent raw step has the true reference-gradient-lift first-jet congruence in its actual next Krylov flag.
Use: Every genuine smooth source-admissible globally CG-consistent raw step has the true reference-gradient-lift first-jet congruence in its actual next Krylov flag.
Article: main_krylov, apB:lem:filtration, actual smooth-method frozen response.
Proof: Apply the proved complete actual observation filtration only through the genuinely nonstagnating earlier prefix. Primitive actual direction coefficients and the true zero-reference correction derivative give the real total step jet; identify its genuine reference value. No nonzero final gradient is required, so the exhausted endpoint is included. -/
theorem actual_step_jet_coherence (memory : ℕ → ℕ) (m : ProbedMethod E)
    (hm : CGConsistent m) (hspan : ProbedSpanRestricted memory m)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : E) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q) (N : ℕ)
    (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0)
    (hpre : ∀ i<N, CG.gradient Q g i≠0) (hsmooth : SmoothProbedCycleAt m 2 Q g N) :
    let δg := fun i => deriv (fun t => probedGradient m (A t) (B t) g i) 0
    ∀ k<N, deriv (fun t => probedStep m (A t) (B t) g k) 0-
      gradientJetLift Q g δg k (referenceStep Q g k)∈CG.krylovSpace Q g (k+1) := by
  dsimp only
  -- Use only the true earlier nonstagnating prefix, so this actual step congruence also includes a final exhausted gradient.
  let δg := fun i => deriv (fun t => probedGradient m (A t) (B t) g i) 0
  intro k hk
  let L := gradientJetLift Q g δg k
  let d := fun t => probedDirection m (A t) (B t) g k
  let α := fun t => lineLength (probedGradient m (A t) (B t) g k) (d t) (probedProbe m (A t) (B t) g k)
  let χ := fun t => (probedPhase m (A t) (B t) g k).movement
  have hH := (actual_observation_filtration memory m hm hspan A B (fun _ => g) k
    (fun i hi => hA i (hi.trans hk)) (fun i hi => hB i (hi.trans hk)) contDiffAt_const Q hA0 hB0 hQ hpos
    (fun i hi => hpre i (hi.trans_lt hk)) (hsmooth.mono m hk.le)).1
  have hdj : (d 0,deriv d 0)∈jetSubspace (CG.krylovSpace Q g (k+1)) L :=
    actual_direction_jet m hm A B (fun _ => g) N hA hB contDiffAt_const Q hA0 hB0 hQ hpos hpre hsmooth k hk _ L hH
  have hf := smoothProbed_fields_regular m hm A B (fun _ => g) 0 N hA hB contDiffAt_const
    Q hA0 hB0 hQ hpos hpre hsmooth k hk
  have hα := (smoothProbed_search_regular m hm A B (fun _ => g) 0 N hA hB contDiffAt_const
    Q hA0 hB0 hQ hpos hpre hsmooth k hk).1
  have hχ := (actual_correction_jets memory m hm hspan A B (fun _ => g) N hA hB contDiffAt_const
    Q hA0 hB0 hQ hpos hpre hsmooth k hk).1
  have hχ0 : χ 0=0 := by
    dsimp only [χ,probedPhase]
    rw [hA0,hB0]
    exact (zeroCorrections_change_operator _ Q Q _ (hm Q hQ hpos g k).choose_spec.2.2).2.1
  -- Differentiate the genuine line-plus-correction step after deriving actual direction coherence and the true correction derivative flag.
  have hsD : HasDerivAt (fun t => probedStep m (A t) (B t) g k)
      (α 0 • deriv d 0+deriv α 0 • d 0+deriv χ 0) 0 :=
    ((hα.differentiableAt (by norm_num)).hasDerivAt.smul (hf.1.differentiableAt (by norm_num)).hasDerivAt).add
      (hf.2.2.2.differentiableAt (by norm_num)).hasDerivAt
  have hs0 : probedStep m (A 0) (B 0) g k=α 0 • d 0 := by
    change α 0 • d 0+χ 0=_
    rw [hχ0,add_zero]
  have hj : (probedStep m (A 0) (B 0) g k,
      deriv (fun t => probedStep m (A t) (B t) g k) 0)∈jetSubspace (CG.krylovSpace Q g (k+1)) L := by
    rw [hsD.deriv,hs0]
    exact jetSubspace_line_correction _ L hdj hχ (α 0) (deriv α 0)
  have href : probedStep m (A 0) (B 0) g k=referenceStep Q g k := by
    rw [hA0,hB0]
    exact quadratic_probedStep_eq_cg m hm Q hQ hpos g k
  have h := hj.2
  change deriv (fun t => probedStep m (A t) (B t) g k) 0-L (probedStep m (A 0) (B 0) g k)∈_ at h
  rwa [href] at h

/-- Every actual smooth source-admissible globally CG-consistent raw trajectory has its true displacement derivative equal to the genuine frozen physical response modulo the real Krylov flag, and its actual gradient derivative differs by the true reference-operator image of that flag.
Use: Every actual smooth source-admissible globally CG-consistent raw trajectory has its true displacement derivative equal to the genuine frozen physical response modulo the real Krylov flag, and its actual gradient derivative differs by the true reference-operator image of that flag.
Article: main_krylov, apB:lem:filtration, actual smooth-method frozen response.
Proof: The complete real observation theorem supplies actual step coherence. Genuine executed gradient balance and the measured frozen recurrence give the true filtered finite induction; differentiate the actual recorded displacement sum and apply the real operator to its genuine filtered remainder. -/
theorem actual_frozen_filtration (memory : ℕ → ℕ) (m : ProbedMethod E)
    (hm : CGConsistent m) (hspan : ProbedSpanRestricted memory m)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : E) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q) (N : ℕ)
    (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0)
    (hpre : ∀ i<N, CG.gradient Q g i≠0) (hsmooth : SmoothProbedCycleAt m 2 Q g N) :
    let ζ := referenceInjection Q g A
    ∀ k≤N,
      (deriv (fun t => (methodRun m (A t) (B t) g k).displacement) 0-
        frozenDisplacement Q (CG.length Q g) (CG.beta Q g) ζ k∈CG.krylovSpace Q g k) ∧
      (deriv (fun t => probedGradient m (A t) (B t) g k) 0-
        frozenResponse Q (CG.length Q g) (CG.beta Q g) ζ k 0∈(CG.krylovSpace Q g k).map Q.toLinearMap) := by
  dsimp only
  -- Both actual derivative sequences come from the genuine raw executor, and the injections use its real primitive oracle derivatives.
  let δs := fun i => deriv (fun t => probedStep m (A t) (B t) g i) 0
  let δg := fun i => deriv (fun t => probedGradient m (A t) (B t) g i) 0
  let ζ := referenceInjection Q g A
  have hgrad (k : ℕ) (hk : k≤N) : δg k=Q (∑ i∈Finset.range k, δs i)+∑ i∈Finset.range k, ζ (i+1) :=
    probed_gradient_jet_sum m hm A B g Q hQ hpos hA0 hB0 k
      (fun i hi => hA i (by omega)) (fun i hi => hB i (by omega))
      (fun i hi => hpre i (by omega)) (hsmooth.mono m hk)
  have hstep := actual_step_jet_coherence memory m hm hspan A B g Q hQ hpos hA0 hB0 N hA hB hpre hsmooth
  have hfiltered := coherent_steps_frozen_filtration Q hQ hpos g N hpre δs δg ζ hgrad hstep
  -- Identify the genuine physical displacement derivative with the true finite sum of actual recorded-step derivatives.
  intro k hk
  have hdx : deriv (fun t => (methodRun m (A t) (B t) g k).displacement) 0=∑ i∈Finset.range k, δs i := by
    have hfields := fun i (hi : i<k) => (smoothProbed_fields_regular m hm A B (fun _ => g) 0 N hA hB
      contDiffAt_const Q hA0 hB0 hQ hpos hpre hsmooth i (hi.trans_le hk)).2.2.1
    have hd := HasDerivAt.sum (fun i (hi : i∈Finset.range k) =>
      ((hfields i (Finset.mem_range.mp hi)).differentiableAt (by norm_num)).hasDerivAt)
    have he : (fun t => (methodRun m (A t) (B t) g k).displacement)=
        fun t => ∑ i∈Finset.range k, probedStep m (A t) (B t) g i := by
      funext t
      exact history_displacement_eq_steps m (A t) (B t) g k
    rw [he]
    have hf : (fun t => ∑ i∈Finset.range k, probedStep m (A t) (B t) g i)=
        ∑ i∈Finset.range k, (fun t => probedStep m (A t) (B t) g i) := by
      funext t
      simp only [Finset.sum_apply]
    rw [hf]
    exact hd.deriv
  refine ⟨?_,?_⟩
  · rw [hdx]
    exact hfiltered k hk
    -- The genuine frozen and actual gradients share exactly the same real source injection sum.
  · have hf := frozen_gradient_displacement Q (CG.length Q g) (CG.beta Q g) ζ k
    change δg k-_∈_
    rw [hgrad k hk,hf]
    have he : Q (∑ i∈Finset.range k, δs i)+(∑ i∈Finset.range k, ζ (i+1))-
        (Q (frozenDisplacement Q (CG.length Q g) (CG.beta Q g) ζ k)+(∑ i∈Finset.range k, ζ (i+1)))=
        Q ((∑ i∈Finset.range k, δs i)-frozenDisplacement Q (CG.length Q g) (CG.beta Q g) ζ k) := by
      rw [map_sub]
      abel
    rw [he]
    exact Submodule.mem_map_of_mem (hfiltered k hk)
end
end krylov.Envelope
