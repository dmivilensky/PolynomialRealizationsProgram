import krylov.Correction.GatedWindowPhase
import krylov.Correction.GatedEmptyPrefix
import krylov.Correction.GatedPrefixGrowth
import krylov.Correction.GatedCutoffParameters

/-!
Article: main_krylov, thm:UCg, actual uniform cutoff-prefix induction.
Use: Derive the true recorded-step angle and quadratic projected-residual
bounds for every real full-memory gated prefix before its first small line,
with constants chosen before every reference matrix and original run.
Source: original actual observed execution, genuine canonical dictionary,
proved global recording/growth bounds and constructed uniform cutoff allowances.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original full-memory gated run has genuine nonsingular old conjugacy solves and nonzero actual search curvature through its finite horizon.
Use: Complete the genuine finite-prefix part of the whole spectral-class gated-RFC theorem.
Article: main_krylov, thm:UCg, actual uniform cutoff-prefix induction.
-/
def gatedFullRunDefined (γ : ℝ)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) : Prop :=
  let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
  ∀ i<N, let H := methodRun m A B g i
    let W := selectedWindow fullMemory H
    IsUnit (crossGram (windowImages W) (windowSteps W)).det ∧
      inner ℝ (m.direction H) (A i (m.direction H))≠0

/-- The actual exact-search line displacement in the original full-memory spectral-gated run.
Use: Complete the genuine finite-prefix part of the whole spectral-class gated-RFC theorem.
Article: main_krylov, thm:UCg, actual uniform cutoff-prefix induction.
-/
def gatedObservedLineStep (γ : ℝ)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) : EuclideanSpace ℝ (Fin n) :=
  let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
  let H := methodRun m A B g i
  lineLength H.gradient (m.direction H) (A i (m.direction H)) • m.direction H

/-- Every genuine defined gated prefix before a quadratic small-line cutoff has the real nonzero recorded steps, uniform normalized angles and quadratic old projected-gradient bound.
Use: Complete the genuine finite-prefix part of the whole spectral-class gated-RFC theorem.
Article: main_krylov, thm:UCg, actual uniform cutoff-prefix induction.
Proof: The proved true recording and growth inductions control every actual old pair and incoming gradient. Induct on the genuine full observed history. Its exact canonical phase fields identify the real next gradient and total recorded step. Actual observed inverse domains derive the old nonzero columns and real image conjugacy. The genuine empty iteration starts the invariant; the proved accepted large-line step preserves it. The real next observed-window identity closes the induction without fixed-length surrogate data.
-/
theorem gated_actual_prefix_before_cutoff (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1) (N : ℕ) (hN : 1≤N)
    (a C M ε : ℝ) (ha : 0<a) (ha1 : a<1) (hC : 0≤C) (hM : 0<M) (hε : 0<ε)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (hdefined : gatedFullRunDefined γ A B g N)
    (hinit : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g‖≤1)
    (hA : ∀ i<N, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hB : ∀ i<N, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hrecord : (N : ℝ)*((1+2*gatedCorrectionConstant N γ)*ε)≤γ/4)
    (hrecordSize : (N : ℝ)*((1+2*gatedCorrectionConstant N γ)*ε)≤1)
    (hangle : (N : ℝ)*a≤(1-γ)/8)
    (hpair : (1+2*gatedCorrectionConstant N γ)*ε≤a/2)
    (hratio : 4*C/M+4*(Real.sqrt N*(2+2*gatedCorrectionConstant N γ))*ε≤a/4)
    (hsmall : gatedProjectedConstant N (2*gatedCorrectionConstant N γ)*ε≤1/2)
    (hallow : 4*gatedProjectedConstant N (2*gatedCorrectionConstant N γ)*
      (Real.sqrt N*(2+2*gatedCorrectionConstant N γ))*(gatedGrowthConstant N γ)^N≤C) :
    let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    ∀ i≤N, (∀ j< i, M*ε^2≤‖R (gatedObservedLineStep γ A B g j)‖) →
      recordedPrefixBound a C ε
        (primalWindow base (windowSteps (selectedWindow fullMemory (methodRun m A B g i))))
        (J (probedGradient m A B g i)) := by
  let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let W := fun i => selectedWindow fullMemory (methodRun m A B g i)
  let K := 2*gatedCorrectionConstant N γ
  let η := (1+K)*ε
  let L := (gatedGrowthConstant N γ)^N
  have hK0 := gatedCorrectionConstant_nonneg N γ
  have hK : 0≤K := by dsimp only [K]; positivity
  have hηhalf : η≤1/2 := by change (1+K)*ε≤1/2; change (1+K)*ε≤a/2 at hpair; linarith
  have hrecorded := gated_uniform_recorded_bounds base hb fullMemory γ hγ A B g N hε.le hA hB hηhalf hrecord hrecordSize
  have hgrowth := gated_uniform_prefix_growth base hb fullMemory γ hγ A B g N hε.le hA hB hηhalf hrecord hrecordSize
  have hcgrow : 1≤gatedGrowthConstant N γ := by
    unfold gatedGrowthConstant
    have ht : 0≤10*(N : ℝ)/γ := by positivity
    linarith
  have hbound i (hi : i≤N) : ‖J (probedGradient m A B g i)‖≤L := by
    calc
      _ ≤ (gatedGrowthConstant N γ)^i*‖J g‖ := hgrowth.2 i hi
      _ ≤ (gatedGrowthConstant N γ)^N*1 := mul_le_mul (pow_le_pow_right₀ hcgrow hi) hinit (norm_nonneg _) (by positivity)
      _ = L := by rw [mul_one]
  have hlen i : (W i).length=i := by
    dsimp only [W]
    rw [fullWindow_methodRun,executedPairs_length]
  dsimp only
  intro i
  induction i with
  | zero =>
    intro _ _
    have he : primalWindow base (windowSteps (selectedWindow fullMemory (methodRun m A B g 0)))=
        (fun i : Fin 0 => Fin.elim0 i) := by funext i; exact Fin.elim0 i
    rw [he]
    exact recordedPrefixBound_empty a C ε hC (J g)
  | succ i ih =>
    intro hi hbefore
    have hiN : i<N := by omega
    have hprev := ih hiN.le (fun j hj => hbefore j (hj.trans (Nat.lt_succ_self i)))
    let H := methodRun m A B g i
    let S := primalWindow base (windowSteps (W i))
    let Y := dualWindow base (windowImages (W i))
    let G := J H.gradient
    let d := R (m.direction H)
    let Ac := canonicalOperator base (A i)
    let Bc := canonicalOperator base (B i)
    let P := gatedArrayPhase γ S Y G d (Ac d) Bc
    let line := lineLength G d (Ac d) • d
    have hfields := probedGated_canonical_window_fields base hb fullMemory γ A B g i
    change P.movement=R (probedPhase m A B g i).movement ∧
      P.gradient=J (probedGradient m A B g (i+1)) ∧ line+P.movement=R (probedStep m A B g i) at hfields
    have hlineeq : line=R (gatedObservedLineStep γ A B g i) := by
      dsimp only [line,Ac,d]
      rw [canonicalOperator_primal base hb,canonical_lineLength base hb]
      change _=R (lineLength H.gradient (m.direction H) (A i (m.direction H)) • m.direction H)
      rw [map_smul]
    have hlarge : M*ε^2≤‖line‖ := by rw [hlineeq]; exact hbefore i (Nat.lt_succ_self i)
    have hline : 0<‖line‖ := lt_of_lt_of_le (mul_pos hM (sq_pos_of_pos hε)) hlarge
    have hcurv : inner ℝ d (Ac d)≠0 := by
      dsimp only [d,Ac]
      rw [canonicalOperator_primal base hb,← canonical_search_pairing base hb]
      exact (hdefined i hiN).2
    have hnext : recordedPrefixBound a C ε (Fin.cons (line+P.movement) S) P.gradient := by
      by_cases hi0 : i=0
      · subst i
        exact recordedPrefixBound_empty_step a C ε γ hC S Y Ac Bc G d hcurv hline
      · have hp : 0<(W i).length := by rw [hlen]; omega
        have hsize : (W i).length+1≤N := by rw [hlen]; omega
        have hy : ∀ j, ‖Y j-S j‖≤η*‖S j‖ := selectedWindow_pair_bound fullMemory m A B g i R J η
          (fun j hj => hrecorded.2 j (hj.trans hiN))
        have ho (j : Fin (W i).length) : inner ℝ (Y j) d=0 := by
          exact canonical_window_image_conjugacy base hb (W i) H.gradient (hdefined i hiN).1 j
        have hrel : ‖P.movement‖≤K*‖line+P.movement‖ := by
          rw [hfields.2.2,hfields.1]
          exact (hrecorded.1 i hiN).trans (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) (norm_nonneg _))
        exact recordedPrefixBound_gated_step S Y Ac Bc G d hp hN hsize hγ.le hγ1 ha ha1 hC hM hε hK
          (hbound i hiN.le) hprev (hA i hiN) (hB i hiN) hy ho hcurv hangle hpair hratio hsmall hallow hlarge hrel
    change recordedPrefixBound a C ε (primalWindow base (windowSteps (W (i+1))))
      (J (probedGradient m A B g (i+1)))
    rw [show W (i+1)=(probedStep m A B g i,probedSecant m A B g i)::W i from full_observed_window_next m A B g i,
      windowSteps_cons]
    have hmap : primalWindow base (Fin.cons (probedStep m A B g i) (windowSteps (W i)))=
        Fin.cons (R (probedStep m A B g i)) S := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    rw [hmap,← hfields.2.2,← hfields.2.1]
    exact hnext

/-- One set of positive constants depending only on horizon and gate threshold controls every actual defined full-memory gated prefix before its first quadratic small line, uniformly before dimension, reference, operators and initial data.
Use: Complete the genuine finite-prefix part of the whole spectral-class gated-RFC theorem.
Article: main_krylov, thm:UCg, actual uniform cutoff-prefix induction.
Proof: Construct the actual relative-error and projected-residual coefficients from horizon and threshold. The proved scalar allowance theorem selects a common angle, residual, cutoff and radius. Intersect this radius with the genuine recording radius, then apply the actual finite-prefix induction and true gradient growth to every admitted original run.
-/
theorem gated_uniform_cutoff_prefix (N : ℕ) (hN : 1≤N) (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ a C M ε₀ : ℝ, 0<a ∧ a<1 ∧ 0<C ∧ 0<M ∧ 0<ε₀ ∧
      (N : ℝ)*a≤(1-γ)/8 ∧
      ∀ (n : ℕ) (base : Matrix (Fin n) (Fin n) ℝ) (_hb : base.PosDef),
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0<ε → ε<ε₀ →
        gatedFullRunDefined γ A B g N →
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g‖≤1 →
        (∀ i<N, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
        (∀ i<N, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
        let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
        let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
        let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
        (1+2*gatedCorrectionConstant N γ)*ε≤a/2 ∧
        (∀ i<N, ‖J (probedGradient m A B g (i+1))‖≤gatedGrowthConstant N γ*‖J (probedGradient m A B g i)‖) ∧
        ∀ i≤N, (∀ j< i, M*ε^2≤‖R (gatedObservedLineStep γ A B g j)‖) →
          recordedPrefixBound a C ε (primalWindow base
            (windowSteps (selectedWindow fullMemory (methodRun m A B g i)))) (J (probedGradient m A B g i)) := by
  let K := 2*gatedCorrectionConstant N γ
  let F := gatedProjectedConstant N K
  let H := Real.sqrt N*(2+K)
  let L := (gatedGrowthConstant N γ)^N
  have hK : 0≤K := mul_nonneg (by norm_num) (gatedCorrectionConstant_nonneg N γ)
  have hNp : (0 : ℝ)<N := by
    have hN' : (1 : ℝ)≤N := by exact_mod_cast hN
    exact lt_of_lt_of_le zero_lt_one hN'
  have hF : 0<F := by dsimp only [F,gatedProjectedConstant]; positivity
  have hH : 0<H := by dsimp only [H]; positivity
  have hL : 0≤L := by dsimp only [L,gatedGrowthConstant]; positivity
  obtain ⟨a,C,M,δ,ha,ha1,hC,hM,hδ,hangle,hallow,hconditions⟩ :=
    uniform_cutoff_allowances N hN γ K F H L hγ.le hγ1 hK hF hH hL
  obtain ⟨ρ,hρ,hrecording⟩ := gated_recording_radius N γ hγ
  refine ⟨a,C,M,min δ ρ,ha,ha1,hC,hM,lt_min hδ hρ,hangle,?_⟩
  intro n base hb A B g ε hε he hdefined hinit hA hB
  have hp := hconditions ε hε.le (he.le.trans (min_le_left _ _))
  have hr := hrecording ε hε.le (he.le.trans (min_le_right _ _))
  dsimp only
  refine ⟨hp.1,?_,?_⟩
  · exact fun i hi => (gated_uniform_prefix_growth base hb fullMemory γ hγ A B g N hε.le hA hB hr.1 hr.2.1 hr.2.2).1 i hi |>.1
  · exact gated_actual_prefix_before_cutoff base hb γ hγ hγ1 N hN a C M ε ha ha1 hC.le hM hε
      A B g hdefined hinit hA hB hr.2.1 hr.2.2 hangle hp.1 hp.2.1 hp.2.2 hallow

end
end krylov.Correction
