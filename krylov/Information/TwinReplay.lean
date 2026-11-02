import krylov.Information.AdmissibleTwin

/-!
Article: main_krylov, thm:centre, joint admissibility and actual-data preservation.
Use: return a genuinely admissible physical twin with the same full observed
past, final probe, final decision and opposite terminal operator.
Source: the actual method's direction flag, exact physical reflected columns,
H1--H3 budget transport and H4 symmetric single-action completion.
-/

namespace krylov.Information
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.LinearAlgebra krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {p : ℕ}

/-- The first actual query belongs to every subspace containing its correction tree.
Use: the H4 vector lies in the method's own direction flag, including stopped phases.
Article: main_krylov, thm:centre, u_k∈𝒱_k.
Proof: a stopped phase has zero displacement; otherwise this is the first
membership assertion of the actual all-branch tree constraint. -/
theorem firstCorrectionStep_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) (q : CorrectionTree E) (hq : q.InSubspace K) :
    firstCorrectionStep q∈K := by
  cases q with
  | done => exact K.zero_mem
  | query _ _ => exact hq.1

/-- The actual single correction chosen from the scenario's real history and real current probe.
Use: H4 refers to an executed vector determined by actual information.
Article: main_krylov, thm:centre, actual u_k before its correction observation. -/
def Scenario.correctionQuery (S : Scenario p) (N : ℕ)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin p))) (g : EuclideanSpace ℝ (Fin p))
    (k : ℕ) : EuclideanSpace ℝ (Fin p) :=
  firstCorrectionStep (m.correction (methodRun m S.probeOracle (S.correctionOracle N) g k)
    (probedProbe m S.probeOracle (S.correctionOracle N) g k))

/-- Completing the twin only at actual intermediate queries preserves the full actual history.
Use: the returned admissible twin needs no full-flag correction norm bound.
Article: main_krylov, thm:centre(iii), replay after H4 completion.
Proof: the original query belongs to the true direction flag. The reflected
intermediate operator agrees there with the original one, while the completed
perturbation agrees with its required action on this actual query. The
one-query replay induction therefore preserves every actual observed record. -/
theorem Scenario.completed_twin_run {N : ℕ} (S : Scenario (N+1))
    (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hD : IsUnit D.det)
    (memory : ℕ → ℕ) (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))))
    (hm : ProbedSpanRestricted memory m) (h1 : OneCorrectionMethod m)
    (g : EuclideanSpace ℝ (Fin (N+1)))
    (hdir : ∀ i : Fin (N+1), probedDirection m (S.inPhysical D).probeOracle
      ((S.inPhysical D).correctionOracle N) g i.val=euclideanColumn D i)
    (F : ℕ → Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hF : ∀ k<N, cgOperator (F k) ((S.inPhysical D).correctionQuery N m g k)=
      cgOperator (((S.reflect N).inPhysical D).correction k)
        ((S.inPhysical D).correctionQuery N m g k)) :
    methodRun m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N=
      methodRun m (((S.reflect N).inPhysical D).withCorrections F).probeOracle
        ((((S.reflect N).inPhysical D).withCorrections F).correctionOracle N) g N := by
  -- The replay compares genuine queries from the original run, before assuming history equality.
  let O := S.inPhysical D
  let R := (S.reflect N).inPhysical D
  let T := R.withCorrections F
  apply one_correction_run_replay m h1 O.probeOracle (O.correctionOracle N)
    T.probeOracle (T.correctionOracle N) g N
  · intro k hk
    change O.probeOracle k (probedDirection m O.probeOracle (O.correctionOracle N) g k)=
      T.probeOracle k (probedDirection m O.probeOracle (O.correctionOracle N) g k)
    rw [hdir (⟨k,by omega⟩ : Fin (N+1))]
    ext a
    exact (S.physical_reflect_probe_column D hD hk.le ⟨k,by omega⟩ rfl a).symm
  · intro k hk
    let u := O.correctionQuery N m g k
    have hu : u∈executedDirectionSpan m O.probeOracle (O.correctionOracle N) g k :=
      firstCorrectionStep_mem _ _ (correction_in_executedDirectionSpan memory m hm _ _ g k)
    have he : executedDirectionSpan m O.probeOracle (O.correctionOracle N) g k≤
        (O.correctionOracle N k-R.correctionOracle N k).toLinearMap.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,hj,rfl⟩
      change j≤k at hj
      change O.correctionOracle N k (probedDirection m _ _ g j)-
        R.correctionOracle N k (probedDirection m _ _ g j)=0
      rw [hdir (⟨j,by omega⟩ : Fin (N+1))]
      apply sub_eq_zero.mpr
      simp only [Scenario.correctionOracle,ite_eq_left hk]
      ext a
      exact (S.physical_reflect_intermediate_column D hD hk.le ⟨j,by omega⟩ hj a).symm
    have horig := sub_eq_zero.mp (he hu)
    change O.correctionOracle N k u=R.correctionOracle N k u at horig
    change O.correctionOracle N k u=T.correctionOracle N k u
    rw [horig]
    simp only [Scenario.correctionOracle,ite_eq_left hk,Scenario.intermediate]
    change cgOperator (R.probe k+R.correction k) u=cgOperator (R.probe k+F k) u
    have hFu := hF k hk
    change cgOperator (F k) u=cgOperator (R.correction k) u at hFu
    simpa only [cgOperator,map_add,_root_.add_apply] using
      congrArg (fun z => cgOperator (R.probe k) u+z) hFu.symm

/-- H1--H4 construct a jointly admissible physical twin and preserve its entire actual preterminal history.
Use: this is an existence theorem inside the original finite-budget scenario class, not a conditional radius estimate for assumed twins.
Article: main_krylov, thm:centre(iii), admissible data-fibre twin.
Proof: the exact flag estimates supply all physical H1--H3 constraints.
Complete each required H4 action by a genuine symmetric operator in the
actual new-base ball, keep all reflected probe and terminal forms fixed,
and replay the real at-most-one-correction executor. -/
theorem Scenario.exists_admissible_physical_twin {N : ℕ} (S : Scenario (N+1))
    (A D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef) (hD : IsUnit D.det)
    (hG : S.base.PosDef) (he : directionDefect S.base<1)
    (hE : ∀ l<N, (S.increment l).IsSymm) (hT : S.terminal.IsSymm)
    (hv : S.twinDisplacement N<1) {r w τ : ℝ} (hr : 0≤r) (hw : 0≤w) (hτ : 0≤τ)
    (ω : ℕ → ℝ) (hω : ∀ l<N, 0≤ω l)
    (hH1 : ∀ l<N, relativeBudget S.base (S.increment l)≤
      ((1-S.twinDisplacement N)/flagDistortion S.base)*ω l)
    (hH2 : relativeBudget S.base S.terminal≤(1-S.twinDisplacement N)*w)
    (hH3 : relativeBudget A (S.base-A)+(1+r)*S.twinDisplacement N≤r)
    (memory : ℕ → ℕ) (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))))
    (hm : ProbedSpanRestricted memory m) (h1 : OneCorrectionMethod m)
    (g : EuclideanSpace ℝ (Fin (N+1)))
    (hdir : ∀ i : Fin (N+1), probedDirection m (S.inPhysical D).probeOracle
      ((S.inPhysical D).correctionOracle N) g i.val=euclideanColumn D i)
    (hH4 : ∀ k<N, let u := (S.inPhysical D).correctionQuery N m g k
      let R := (S.reflect N).inPhysical D
      u=0 ∨ ‖cgOperator (metricRoot R.base)⁻¹ (cgOperator (R.correction k) u)‖≤
        τ*‖cgOperator (metricRoot R.base) u‖) :
    ∃ T : Scenario (N+1),
      T.Admissible N (inverseFormMap D A) r ω w τ ∧
      T.base=((S.reflect N).inPhysical D).base ∧
      T.increment=((S.reflect N).inPhysical D).increment ∧
      T.terminal=((S.reflect N).inPhysical D).terminal ∧
      T.lastOperator N=((S.reflect N).inPhysical D).lastOperator N ∧
      (∀ k, T.probe k=((S.reflect N).inPhysical D).probe k) ∧
      methodRun m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N=
        methodRun m T.probeOracle (T.correctionOracle N) g N := by
  -- Assemble all budget witnesses for one and the same physical reflected scenario.
  let R := (S.reflect N).inPhysical D
  obtain ⟨hp,hb,hi,ht,hbt⟩ := S.physical_reflection_budgets N A D hA hD hG he hE hT
    hv hr hw ω hω hH1 hH2 hH3
  obtain ⟨F,hF⟩ := R.complete_correction_actions N hp
    ((S.inPhysical D).correctionQuery N m g) hτ hH4
  refine ⟨R.withCorrections F,⟨hp,hb,hi,ht,hbt,?_⟩,rfl,rfl,rfl,rfl,(fun _ => rfl),?_⟩
  · intro k hk
    exact ⟨(hF k hk).1,(hF k hk).2.1⟩
  · exact S.completed_twin_run D hD memory m hm h1 g hdir F (fun k hk => (hF k hk).2.2)

end
end krylov.Information
