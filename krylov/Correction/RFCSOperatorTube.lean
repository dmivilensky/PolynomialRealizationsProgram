import krylov.Correction.RFCSCompact

/-!
Article: main_krylov, thm:RFCS, full genuine operator/initial-gradient tube.
Use: Cover independently varying actual physical segment operators, including
the first segment, all independent probes and the nonlinear initial-gradient
drift with one compact-reference quadratic remainder bound.
Source: genuine RFC-S measured execution, original physical only-last-probe
expansion, joint primitive operator regularity, global quadratic CG termination
and the proved full zero-jet compact Taylor theorem. The finite direct operator
coordinates impose no off-reference symmetry restriction.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra krylov.Secant krylov.Variation
open scoped Matrix.Norms.L2Operator InnerProductSpace
set_option maxHeartbeats 600000
variable {k : ℕ}

/-- All genuine finite direct physical segment deviations and independent probe mismatches in one original RFC-S cycle.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
-/
abbrev RFCSOperatorParameters (n : ℕ) :=
  (Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
    (Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))

/-- The exact zero extension of a genuine finite physical operator-coordinate array.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
-/
def rfcsOperatorAt {n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ℕ) :=
  if hi : i<n then a ⟨i,hi⟩ else 0

/-- The actual physical segment operator sequence with every original segment allowed to vary independently, including the first.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
-/
def rfcsDirectLine (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) (i : ℕ) :=
  cgOperator base+rfcsOperatorAt z.2.1 i

/-- The actual independent physical probe sequence with its genuine difference from each physical segment operator.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
-/
def rfcsDirectProbe (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) (i : ℕ) :=
  rfcsDirectLine base z i-rfcsOperatorAt z.2.2 i

/-- The actual terminal RFC-S gradient on the full physical segment/probe and initial-gradient parameter space.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
-/
def rfcsDirectOutput (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) :=
  rfcSGradient fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 (k+1)

/-- All genuine direct physical segment and independent probe operators are jointly analytic in the full actual reference/source coordinates.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
Proof: Use genuine primitive operator coordinates, actual measured-prefix regularity and the original physical expansion with its true reference step.
-/
theorem rfcs_direct_operators_analytic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) :
    (∀ i, AnalyticAt ℝ (fun z => rfcsDirectLine base z i) (g,0)) ∧
      (∀ i, AnalyticAt ℝ (fun z => rfcsDirectProbe base z i) (g,0)) := by
  -- Each genuine segment and mismatch coordinate is an exact finite continuous linear projection of the full physical source.
  have hA (i : ℕ) : AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1) =>
      rfcsOperatorAt z.2.1 i) (g,0) := by
    unfold rfcsOperatorAt
    split_ifs with hi
    · have hf : AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1) => z.2.1) (g,0) := by
        exact (analyticAt_fst : AnalyticAt ℝ
          (Prod.fst : RFCSOperatorParameters (k+1) →
            (Fin (k+1) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))) 0).comp
            (f := Prod.snd) (x := (g,0)) analyticAt_snd
      exact ((ContinuousLinearMap.proj (⟨i,hi⟩ : Fin (k+1)) :
        (Fin (k+1) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) →L[ℝ]
          (EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))).analyticAt _).comp hf
    · exact analyticAt_const
  have hP (i : ℕ) : AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1) =>
      rfcsOperatorAt z.2.2 i) (g,0) := by
    unfold rfcsOperatorAt
    split_ifs with hi
    · have hf : AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1) => z.2.2) (g,0) := by
        exact (analyticAt_snd : AnalyticAt ℝ
          (Prod.snd : RFCSOperatorParameters (k+1) →
            (Fin (k+1) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))) 0).comp
            (f := Prod.snd) (x := (g,0)) analyticAt_snd
      exact ((ContinuousLinearMap.proj (⟨i,hi⟩ : Fin (k+1)) :
        (Fin (k+1) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) →L[ℝ]
          (EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))).analyticAt _).comp hf
    · exact analyticAt_const
  exact ⟨fun i => analyticAt_const.add (hA i),fun i => (analyticAt_const.add (hA i)).sub (hP i)⟩

/-- Every genuine physical segment and probe operator equals the original positive quadratic reference at zero direct source.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
Proof: Use genuine primitive operator coordinates, actual measured-prefix regularity and the original physical expansion with its true reference step.
-/
theorem rfcs_direct_operators_zero (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) :
    rfcsDirectLine base (g,0)=(fun _ => cgOperator base) ∧
      rfcsDirectProbe base (g,0)=(fun _ => cgOperator base) := by
  constructor
  · funext i
    simp [rfcsDirectLine,rfcsOperatorAt]
  · funext i
    simp [rfcsDirectProbe,rfcsDirectLine,rfcsOperatorAt]

/-- Every actual RFC-S prefix gradient, direction, total step and measured secant is jointly analytic with all genuine direct segment/probe coordinates and its true initial gradient.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
Proof: Use genuine primitive operator coordinates, actual measured-prefix regularity and the original physical expansion with its true reference step.
-/
theorem rfcs_direct_prefix_analytic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (N : ℕ) (hN : N≤referenceAtomCount base hb g) :
    AnalyticAt ℝ (fun z => rfcSGradient fullMemory (rfcsDirectProbe base z)
      (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 N) (g,0) ∧
    ∀ i<N,
      AnalyticAt ℝ (fun z => rfcSDirection fullMemory (rfcsDirectProbe base z)
        (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i) (g,0) ∧
      AnalyticAt ℝ (fun z => rfcSStep fullMemory (rfcsDirectProbe base z)
        (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i) (g,0) ∧
      AnalyticAt ℝ (fun z => rfcSSecant fullMemory (rfcsDirectProbe base z)
        (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i) (g,0) := by
  have hop := rfcs_direct_operators_analytic base g
  have hz := rfcs_direct_operators_zero base g
  have hQ := cgOperator_positive base hb
  exact quadraticRFCS_prefix_analytic fullMemory (rfcsDirectProbe base) (rfcsDirectLine base) (rfcsDirectLine base)
    Prod.fst (g,0) hop.2 hop.1 hop.1 analyticAt_fst (cgOperator base) hz.2 hz.1 hz.1 hQ.1 hQ.2
    (fun _ _ hj => hj) N (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hN))

/-- The actual physical last reference step of the genuine RFC-S executor on the original static positive quadratic.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
-/
def rfcsDirectReferenceStep (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) :=
  rfcSStep fullMemory (fun _ => cgOperator base) (fun _ => cgOperator base) (fun _ => cgOperator base) g k

/-- The genuine physical RFC-S reference step is exactly the original actual CG step, including degenerate references and stopped tails.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
Proof: Use genuine primitive operator coordinates, actual measured-prefix regularity and the original physical expansion with its true reference step.
-/
theorem rfcsDirectReferenceStep_eq_cg (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) : rfcsDirectReferenceStep base g=referenceStep (cgOperator base) g k := by
  have hQ := cgOperator_positive base hb
  rw [rfcsDirectReferenceStep,(rfcSFields_exact fullMemory (fun _ => cgOperator base) (fun _ => cgOperator base) g k).2.2.1]
  exact quadratic_probedStep_eq_cg _ (rfcMethod_consistent fullMemory (fun _ h => h) 1) _ hQ.1 hQ.2 g k

/-- The genuine physical last reference step is analytic in its actual initial gradient near every full active reference.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
Proof: Use genuine primitive operator coordinates, actual measured-prefix regularity and the original physical expansion with its true reference step.
-/
theorem rfcsDirectReferenceStep_analytic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) :
    AnalyticAt ℝ (rfcsDirectReferenceStep base) g := by
  -- Restrict the actual jointly analytic step to the true zero-source initial-gradient slice.
  have hs := ((rfcs_direct_prefix_analytic base hb g (k+1) hN).2 k (Nat.lt_succ_self k)).2.1
  have ht := hs.comp (f := fun v : EuclideanSpace ℝ (Fin (k+1)) => (v,0))
    (analyticAt_id.prod analyticAt_const)
  dsimp only [Function.comp_def] at ht
  have hA : ∀ v : EuclideanSpace ℝ (Fin (k+1)), rfcsDirectLine base (v,0)=(fun _ => cgOperator base) :=
    fun v => (rfcs_direct_operators_zero base v).1
  have hP : ∀ v : EuclideanSpace ℝ (Fin (k+1)), rfcsDirectProbe base (v,0)=(fun _ => cgOperator base) :=
    fun v => (rfcs_direct_operators_zero base v).2
  change AnalyticAt ℝ (fun v => rfcSStep fullMemory (fun _ => cgOperator base)
    (fun _ => cgOperator base) (fun _ => cgOperator base) v k) g
  simpa only [hA,hP] using ht


/-- The genuine physical last segment-to-probe mismatch acting on its actual original reference step.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
-/
def rfcsDirectLeading (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) :=
  (rfcsDirectLine base z k-rfcsDirectProbe base z k) (rfcsDirectReferenceStep base z.1)

/-- The real physical terminal RFC-S output minus its genuine only-last-probe leading term on the complete direct operator source space.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
-/
def rfcsDirectRemainder (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) :=
  rfcsDirectOutput base z-rfcsDirectLeading base z

/-- The true physical remainder is jointly analytic in all original direct segment, independent probe and initial-gradient coordinates.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
Proof: Use genuine primitive operator coordinates, actual measured-prefix regularity and the original physical expansion with its true reference step.
-/
theorem rfcs_direct_remainder_analytic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) :
    AnalyticAt ℝ (rfcsDirectRemainder base) (g,0) := by
  -- The physical output and true last mismatch/reference-step action share the same genuine joint analytic coordinates.
  have hop := rfcs_direct_operators_analytic base g
  have hstep : AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1) =>
      rfcsDirectReferenceStep base z.1) (g,0) := by
    simpa only [Function.comp_def] using
      (rfcsDirectReferenceStep_analytic base hb g hN).comp (f := Prod.fst)
        (x := (g,(0 : RFCSOperatorParameters (k+1)))) analyticAt_fst
  have hlead := analytic_operator_apply ((hop.1 k).sub (hop.2 k)) hstep
  exact (rfcs_direct_prefix_analytic base hb g (k+1) hN).1.sub hlead

/-- The genuine direct-source physical RFC-S remainder has quadratic source order at every full active reference, including arbitrary first-segment drift.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
Proof: Use genuine primitive operator coordinates, actual measured-prefix regularity and the original physical expansion with its true reference step.
-/
theorem rfcs_direct_remainder_order (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    (fun Θ : RFCSOperatorParameters (k+1) => rfcsDirectRemainder base (g,Θ)) =O[𝓝 0] (fun Θ => ‖Θ‖^2) := by
  -- Invoke the original physical last-probe theorem on every independently varying actual segment, including the first.
  let A := fun Θ : RFCSOperatorParameters (k+1) => rfcsDirectLine base (g,Θ)
  let Ap := fun Θ : RFCSOperatorParameters (k+1) => rfcsDirectProbe base (g,Θ)
  have hop := rfcs_direct_operators_analytic base g
  have hA (i : ℕ) : AnalyticAt ℝ (fun Θ => A Θ i) 0 :=
    (hop.1 i).comp (f := fun Θ : RFCSOperatorParameters (k+1) => (g,Θ)) (analyticAt_const.prod analyticAt_id)
  have hAp (i : ℕ) : AnalyticAt ℝ (fun Θ => Ap Θ i) 0 :=
    (hop.2 i).comp (f := fun Θ : RFCSOperatorParameters (k+1) => (g,Θ)) (analyticAt_const.prod analyticAt_id)
  have hz := rfcs_direct_operators_zero base g
  have hr := full_rfcs_last_probe_order base hb g hN hk Ap A A hAp hA hA hz.2 hz.1 hz.1
  apply hr.congr_left
  intro Θ
  change rfcSGradient fullMemory (Ap Θ) (A Θ) (A Θ) g (k+1)-
      (A Θ k-Ap Θ k) (referenceStep (cgOperator base) g k)=
    rfcSGradient fullMemory (Ap Θ) (A Θ) (A Θ) g (k+1)-
      (A Θ k-Ap Θ k) (rfcsDirectReferenceStep base g)
  rw [rfcsDirectReferenceStep_eq_cg base hb]

/-- The actual terminal direct-source output is exactly zero on every original static positive quadratic reference, including all degenerate and stopped initial gradients.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
Proof: Use genuine primitive operator coordinates, actual measured-prefix regularity and the original physical expansion with its true reference step.
-/
theorem rfcs_direct_output_zero (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) : rfcsDirectOutput base (g,0)=0 := by
  -- Genuine global quadratic consistency and finite-dimensional CG termination make the whole original reference slice zero, including degenerate initial gradients.
  have hQ := cgOperator_positive base hb
  have hcount : referenceAtomCount base hb g≤k+1 := by
    classical
    unfold referenceAtomCount activeSpectralValues
    calc
      _ ≤ _ := Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin (k+1))).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = k+1 := by simp
  have hz := rfcs_direct_operators_zero base g
  change rfcSGradient fullMemory (rfcsDirectProbe base (g,0)) (rfcsDirectLine base (g,0))
    (rfcsDirectLine base (g,0)) g (k+1)=0
  rw [hz.1,hz.2]
  exact (rfcSRun_static fullMemory (cgOperator base) hQ.1 hQ.2 g (fun _ _ hj => hj) (k+1)).1.trans
    ((cg_stopping_iff base hb g (k+1)).mpr hcount)

/-- The true physical remainder vanishes on the complete zero-source reference slice for every original initial gradient.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
Proof: Use genuine primitive operator coordinates, actual measured-prefix regularity and the original physical expansion with its true reference step.
-/
theorem rfcs_direct_remainder_zero (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) : rfcsDirectRemainder base (g,0)=0 := by
  have hz := rfcs_direct_operators_zero base g
  change rfcsDirectOutput base (g,0)-
    (rfcsDirectLine base (g,0) k-rfcsDirectProbe base (g,0) k) (rfcsDirectReferenceStep base g)=0
  rw [rfcs_direct_output_zero base hb,hz.1,hz.2,sub_self,_root_.zero_apply,sub_zero]

/-- One genuine compact-reference quadratic remainder tube covers simultaneous actual initial-gradient drift and all physical segment/probe deviations, including the first physical segment.
Use: Apply the original RFC-S operator expansion to genuinely evaluated nonlinear cycles without freezing their first segment or initial gradient.
Article: main_krylov, thm:RFCS, complete physical operator and initial-gradient perturbations.
Proof: Use genuine primitive operator coordinates, actual measured-prefix regularity and the original physical expansion with its true reference step.
-/
theorem compact_rfcs_operator_quadratic_tube (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ g∈K, ∀ v : EuclideanSpace ℝ (Fin (k+1)),
      ∀ Θ : RFCSOperatorParameters (k+1), ‖(v,Θ)‖≤δ →
      ‖rfcsDirectOutput base (g+v,Θ)-
        (rfcsDirectLine base (g+v,Θ) k-rfcsDirectProbe base (g+v,Θ) k)
          (referenceStep (cgOperator base) (g+v) k)‖≤C*‖(v,Θ)‖^2 := by
  -- The genuine initial-gradient reference slice and all operator-source first jets vanish, so compact full-product Taylor bounds both actual drifts together.
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_reference_full_zero_quadratic (rfcsDirectRemainder base) K hK
    (fun g hg => rfcs_direct_remainder_analytic base hb g (hN g hg))
    (rfcs_direct_remainder_zero base hb)
    (fun g hg => rfcs_direct_remainder_order base hb g (hN g hg) hk)
  refine ⟨δ,C+1,hδ,by linarith,?_⟩
  intro g hg v Θ hΘ
  have hh := hbound g hg v Θ hΘ
  change ‖rfcsDirectOutput base (g+v,Θ)-rfcsDirectLeading base (g+v,Θ)‖≤_ at hh
  simp only [rfcsDirectLeading,rfcsDirectReferenceStep_eq_cg base hb] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : C≤C+1) (sq_nonneg ‖(v,Θ)‖))

end
end krylov.Correction
