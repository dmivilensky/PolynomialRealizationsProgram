import krylov.Information.ObservationFibre

/-!
Article: Proposition B.23 [thm:centre] of krylov.tex.
Use: take the supremum over the original admissible information fibre,
with all reflected witnesses constructed from the primitive H1--H4 conditions.
Source: the proved physical admissible twin, recovery of the actual measured
model from the allowed data and the existing every-seminorm reflection bound.
-/

namespace krylov.Information
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.LinearAlgebra krylov.Secant
open scoped Matrix.Norms.L2Operator

/-- The article's admissible inner conditions on one actual scenario in its own direction coordinates.
Use: only primitive geometry, original budgets and H1--H4 are stored; a twin
or an information-radius conclusion is never an input field.
Article: main_krylov, thm:centre, admissible inner class (H1)--(H4). -/
structure Scenario.CentreInner {N : ℕ} (S : Scenario (N+1))
    (A D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (g : EuclideanSpace ℝ (Fin (N+1)))
    (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) : Prop where
  /-- The original physical scenario satisfies the source reference ball and all original budgets. -/
  original : (S.inPhysical D).Admissible N (inverseFormMap D A) r ω w τ
  /-- The genuine coordinate base is a positive metric. -/
  base_pos : S.base.PosDef
  /-- All actual increment operators are symmetric. -/
  increment_symm : ∀ l, (S.increment l).IsSymm
  /-- The independent terminal perturbation is symmetric. -/
  terminal_symm : S.terminal.IsSymm
  /-- The actual normalized direction Gram defect is strictly below one. -/
  defect_lt : directionDefect S.base<1
  /-- The actual summed hidden-base displacement bound is strictly below one. -/
  displacement_lt : S.twinDisplacement N<1
  /-- H1 is imposed on each original individual increment, with the exact common slack. -/
  H1 : ∀ l<N, relativeBudget S.base (S.increment l)≤
    ((1-S.twinDisplacement N)/flagDistortion S.base)*ω l
  /-- H2 is imposed on the original independent terminal perturbation. -/
  H2 : relativeBudget S.base S.terminal≤(1-S.twinDisplacement N)*w
  /-- H3 is the original fixed-reference radius margin before constructing the twin. -/
  H3 : relativeBudget A (S.base-A)+(1+r)*S.twinDisplacement N≤r
  /-- H4 constrains precisely the actual queried intermediate vector, allowing it to vanish. -/
  H4 : ∀ k<N, let u := (S.inPhysical D).correctionQuery N m g k
    let R := (S.reflect N).inPhysical D
    u=0 ∨ ‖cgOperator (metricRoot R.base)⁻¹ (cgOperator (R.correction k) u)‖≤
      τ*‖cgOperator (metricRoot R.base) u‖

/-- Every actual inner-class scenario has an admissible twin in its exact allowed information fibre.
Use: the terminal reflected partner required by the minimax argument is derived from H1--H4.
Article: main_krylov, thm:centre(iii,v), admissible data-preserving twin.
Proof: apply the joint physical budget and one-query replay construction;
the unchanged reflected last probe follows from the actual equal histories.
The exact terminal reflection survives every intermediate action replacement. -/
theorem Scenario.CentreInner.admissible_twin {N : ℕ} {S : Scenario (N+1)}
    {A D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ}
    {m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))} {g : EuclideanSpace ℝ (Fin (N+1))}
    {r w τ : ℝ} {ω : ℕ → ℝ} (h : S.CentreInner A D m g r ω w τ)
    (hA : A.PosDef) (hD : IsUnit D.det) (hr : 0≤r) (hw : 0≤w) (hτ : 0≤τ)
    (hω : ∀ l<N, 0≤ω l) (memory : ℕ → ℕ) (hm : ProbedSpanRestricted memory m)
    (h1 : OneCorrectionMethod m)
    (hdir : ∀ i : Fin (N+1), probedDirection m (S.inPhysical D).probeOracle
      ((S.inPhysical D).correctionOracle N) g i.val=euclideanColumn D i) :
    ∃ T : Scenario (N+1), T.Admissible N (inverseFormMap D A) r ω w τ ∧
      methodRun m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N=
        methodRun m T.probeOracle (T.correctionOracle N) g N ∧
      probedProbe m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N=
        probedProbe m T.probeOracle (T.correctionOracle N) g N ∧
      T.lastOperator N=(2 : ℝ) • S.physicalCentre D-(S.inPhysical D).lastOperator N := by
  -- All constraints and all observations concern one actual completed physical twin.
  obtain ⟨T,ha,_,_,_,ht,hp,hh⟩ := S.exists_admissible_physical_twin A D hA hD h.base_pos
    h.defect_lt (fun l _ => h.increment_symm l) h.terminal_symm h.displacement_lt hr hw hτ
    ω hω h.H1 h.H2 h.H3 memory m hm h1 g hdir h.H4
  exact ⟨T,ha,hh,S.completed_twin_probe T D hD m g hh (hp N) hdir,
    ht.trans (S.physical_reflect_about_centre D hD h.base_pos.1.isSymm h.increment_symm)⟩

/-- Latest information is a centre for every seminorm relative to the actual H1--H4 inner class.
Use: the larger supremum is over all genuinely admissible scenarios with the
same allowed complete data, and may be unbounded; no reflected membership is assumed.
Article: main_krylov, thm:centre(v), admissible-fibre supremal radius.
Proof: equal data recover the common actual direction basis and the same
data-only centre for every inner scenario. Its H1--H4 certificate constructs
an admissible partner in that exact fibre. The two true terminal forms are
opposite about the common centre, so their seminorm lower bound is dominated
by the fibre's extended supremum. -/
theorem Scenario.centre_fibre_radius {N : ℕ} (O : Scenario (N+1))
    (A D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef) (hD : IsUnit D.det)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (g : EuclideanSpace ℝ (Fin (N+1)))
    (memory : ℕ → ℕ) (hm : ProbedSpanRestricted memory m) (h1 : OneCorrectionMethod m)
    {r w τ : ℝ} (hr : 0≤r) (hw : 0≤w) (hτ : 0≤τ) (ω : ℕ → ℝ) (hω : ∀ l<N, 0≤ω l)
    (hdir : ∀ i : Fin (N+1), probedDirection m (O.inPhysical D).probeOracle
      ((O.inPhysical D).correctionOracle N) g i.val=euclideanColumn D i)
    (I : Set (Scenario (N+1)))
    (hI : ∀ S∈I, S.CentreInner A D m g r ω w τ ∧
      methodRun m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N=
        methodRun m (O.inPhysical D).probeOracle ((O.inPhysical D).correctionOracle N) g N ∧
      probedProbe m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N=
        probedProbe m (O.inPhysical D).probeOracle ((O.inPhysical D).correctionOracle N) g N)
    (ν : Seminorm ℝ (Matrix (Fin (N+1)) (Fin (N+1)) ℝ))
    (K : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    let F := Scenario.admissibleFibre m g N
      (methodRun m (O.inPhysical D).probeOracle ((O.inPhysical D).correctionOracle N) g N)
      (probedProbe m (O.inPhysical D).probeOracle ((O.inPhysical D).correctionOracle N) g N)
      (inverseFormMap D A) r ω w τ
    (⨆ S : I, ENNReal.ofReal (ν ((S.val.inPhysical D).lastOperator N-O.physicalCentre D)))≤
      ⨆ T : F, ENNReal.ofReal (ν (T.val.lastOperator N-K)) := by
  -- Construct the true reflected member separately for every original inner-class point.
  dsimp only
  apply iSup_le
  intro S
  obtain ⟨hi,hh,hz⟩ := hI S.val S.property
  have hd := (O.inPhysical D).direction_fibre (S.val.inPhysical D) D m g hh.symm hdir
  obtain ⟨T,ha,ht,hzt,hterm⟩ := hi.admissible_twin hA hD hr hw hτ hω memory hm h1 hd
  have hc := O.physicalCentre_fibre S.val D m g hh.symm hz.symm hdir
  have hOrig : S.val.inPhysical D∈Scenario.admissibleFibre m g N
      (methodRun m (O.inPhysical D).probeOracle ((O.inPhysical D).correctionOracle N) g N)
      (probedProbe m (O.inPhysical D).probeOracle ((O.inPhysical D).correctionOracle N) g N)
      (inverseFormMap D A) r ω w τ := ⟨hi.original,hh,hz⟩
  have hTwin : T∈Scenario.admissibleFibre m g N
      (methodRun m (O.inPhysical D).probeOracle ((O.inPhysical D).correctionOracle N) g N)
      (probedProbe m (O.inPhysical D).probeOracle ((O.inPhysical D).correctionOracle N) g N)
      (inverseFormMap D A) r ω w τ := ⟨ha,ht.symm.trans hh,hzt.symm.trans hz⟩
  have hp := le_iSup (fun X : Scenario.admissibleFibre m g N _ _ _ r ω w τ =>
    ENNReal.ofReal (ν (X.val.lastOperator N-K))) ⟨S.val.inPhysical D,hOrig⟩
  have hn := le_iSup (fun X : Scenario.admissibleFibre m g N _ _ _ r ω w τ =>
    ENNReal.ofReal (ν (X.val.lastOperator N-K))) ⟨T,hTwin⟩
  rw [← hc] at hterm
  have hb := reflected_seminorm ν ((S.val.inPhysical D).lastOperator N) (O.physicalCentre D) K
  rw [← hterm] at hb
  exact (ENNReal.ofReal_le_ofReal hb).trans (by
    rw [ENNReal.ofReal_max]
    exact max_le hp hn)

end
end krylov.Information
