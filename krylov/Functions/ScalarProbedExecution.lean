import krylov.Functions.NativeRFCModel
import krylov.Methods.ReferenceSearch
import krylov.Methods.StaticTermination

/-!
Article: main_krylov, prop:Fcycle(iii), genuine scalar execution of class M.
Use: execute every original nonanticipating probed policy using actual
scalar exact searches, actual observed secants and actual gradient queries.
The unknown Hessian is not an algorithm input. Source: the original raw
ProbedMethod protocol, actual line-parameter observation and causal replay.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Execute a finite adaptive correction tree by true scalar-function
gradient queries at its actual physical displaced points. Article: prop:Fcycle(iii). -/
def scalarFunctionCorrections (q : CorrectionTree E) (G : E → E) (x : E) : CorrectionResult E :=
  match q with
  | .done => ⟨0,G x,[]⟩
  | .query u next =>
      let g := G (x+u)
      let r := scalarFunctionCorrections (next g) G (x+u)
      ⟨u+r.movement,r.gradient,(u,g)::r.trace⟩

omit [InnerProductSpace ℝ E] in
/-- The real correction executor returns the true gradient at its full
actual endpoint, including every adaptive intermediate query.
Article: main_krylov, prop:Fcycle(iii). -/
theorem scalarFunctionCorrections_gradient (q : CorrectionTree E) (G : E → E) (x : E) :
    (scalarFunctionCorrections q G x).gradient=G (x+(scalarFunctionCorrections q G x).movement) := by
  induction q generalizing x with
  | done => simp [scalarFunctionCorrections]
  | query u next ih =>
    simpa only [scalarFunctionCorrections,add_assoc] using ih (G (x+u)) (x+u)

/-- Quadratic-zero correction decisions stay exactly zero under every
actual scalar gradient oracle. This is derived by executing the tree.
Article: main_krylov, prop:Fcycle(iii), causal zero-query replay. -/
theorem scalarFunctionCorrections_zero (q : CorrectionTree E) (G : E → E) (x : E)
    (Q : E →L[ℝ] E) (hz : ZeroCorrections q Q (G x)) :
    scalarFunctionCorrections q G x=runCorrections q Q (G x) := by
  induction q generalizing x with
  | done => rfl
  | query u next ih =>
    obtain ⟨hu,hn⟩ := hz
    subst u
    simp only [map_zero,add_zero] at hn
    simp only [scalarFunctionCorrections,runCorrections,map_zero,add_zero]
    rw [ih (G x) x hn]

/-- One actual scalar observation record of an arbitrary original probed
policy. The probe is recovered from the true searched gradient difference.
Article: main_krylov, prop:Fcycle(iii). -/
def scalarFunctionRecord (m : ProbedMethod E) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (H : History E) : IterationRecord E :=
  let x := x₀+H.displacement
  let d := m.direction H
  let y := metricLocalExactPoint T f x d r
  let s := y-x
  let α := observedLineParameter d s
  let z := α⁻¹ • (G y-H.gradient)
  let c := scalarFunctionCorrections (m.correction H z) G y
  ⟨d,z,s+c.movement,c.gradient,c.trace⟩

/-- The true complete scalar-function run for every original probed policy.
No reference path or asymptotic input is supplied to the executor.
Article: main_krylov, prop:Fcycle(iii). -/
def scalarFunctionRun (m : ProbedMethod E) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) : ℕ → History E
  | 0 => ⟨G x₀,[]⟩
  | k+1 =>
      let H := scalarFunctionRun m T f G r x₀ k
      ⟨H.initial,scalarFunctionRecord m T f G r x₀ H::H.records⟩

/-- The actual physical point of the general scalar executor.
Article: main_krylov, prop:Fcycle(iii). -/
def scalarFunctionPoint (m : ProbedMethod E) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (k : ℕ) : E :=
  x₀+(scalarFunctionRun m T f G r x₀ k).displacement

/-- The actual scalar iteration equals the genuine quadratic protocol
advance whenever its real search and real post-search gradient match that
quadratic observation and consistency supplies zero correction queries.
Article: main_krylov, prop:Fcycle(iii), causal primitive. -/
theorem scalarFunctionRecord_quadratic (m : ProbedMethod E) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (H : History E)
    (Q : E →L[ℝ] E) (α : ℝ) (hα : α≠0) (hd : m.direction H≠0)
    (hαeq : α=lineLength H.gradient (m.direction H) (Q (m.direction H)))
    (hstep : metricLocalExactPoint T f (x₀+H.displacement) (m.direction H) r-(x₀+H.displacement)=α • m.direction H)
    (hpost : G (metricLocalExactPoint T f (x₀+H.displacement) (m.direction H) r)=
      searchedGradient H.gradient (m.direction H) (Q (m.direction H)))
    (hz : ZeroCorrections (m.correction H (Q (m.direction H))) Q
      (searchedGradient H.gradient (m.direction H) (Q (m.direction H)))) :
    ⟨H.initial,scalarFunctionRecord m T f G r x₀ H::H.records⟩=methodAdvance m Q Q H := by
  let y := metricLocalExactPoint T f (x₀+H.displacement) (m.direction H) r
  have hs : observedLineParameter (m.direction H) (y-(x₀+H.displacement))=α := by
    rw [hstep]
    exact observedLineParameter_smul _ α hd
  have hp : α⁻¹ • (G y-H.gradient)=Q (m.direction H) := by
    rw [hpost,searchedGradient,add_sub_cancel_left,←hαeq,smul_smul,inv_mul_cancel₀ hα,one_smul]
  have hc : scalarFunctionCorrections (m.correction H (Q (m.direction H))) G y=
      runCorrections (m.correction H (Q (m.direction H))) Q
        (searchedGradient H.gradient (m.direction H) (Q (m.direction H))) := by
    rw [←hpost] at hz ⊢
    exact scalarFunctionCorrections_zero _ G y Q hz
  change (⟨H.initial,⟨m.direction H,
    (observedLineParameter (m.direction H) (y-(x₀+H.displacement)))⁻¹ • (G y-H.gradient),
    y-(x₀+H.displacement)+(scalarFunctionCorrections
      (m.correction H ((observedLineParameter (m.direction H) (y-(x₀+H.displacement)))⁻¹ • (G y-H.gradient))) G y).movement,
    (scalarFunctionCorrections (m.correction H ((observedLineParameter (m.direction H) (y-(x₀+H.displacement)))⁻¹ • (G y-H.gradient))) G y).gradient,
    (scalarFunctionCorrections (m.correction H ((observedLineParameter (m.direction H) (y-(x₀+H.displacement)))⁻¹ • (G y-H.gradient))) G y).trace⟩::H.records⟩ : History E)=_
  rw [hs,hp,hc,hstep,hαeq]
  rfl

/-- Primitive actual search/gradient matching forces the whole real scalar
prefix to be its genuine quadratic history, for every globally consistent
original probed policy. Zero intermediate corrections are a conclusion.
Article: main_krylov, prop:Fcycle(iii). -/
theorem scalarFunctionRun_quadratic_prefix (m : ProbedMethod E) (hm : CGConsistent m)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (hinit : G x₀=g) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient Q g i≠0)
    (hsearch : ∀ i<N,
      let H := methodRun m (fun _=>Q) (fun _=>Q) g i
      let α := lineLength H.gradient (m.direction H) (Q (m.direction H))
      metricLocalExactPoint T f (x₀+H.displacement) (m.direction H) r-(x₀+H.displacement)=α • m.direction H ∧
      G (metricLocalExactPoint T f (x₀+H.displacement) (m.direction H) r)=
        searchedGradient H.gradient (m.direction H) (Q (m.direction H))) :
    ∀ i≤N, scalarFunctionRun m T f G r x₀ i=methodRun m (fun _=>Q) (fun _=>Q) g i := by
  intro i hi
  induction i with
  | zero => simp only [scalarFunctionRun,methodRun,hinit]
  | succ i ih =>
    have hiN : i<N := by omega
    let H := methodRun m (fun _=>Q) (fun _=>Q) g i
    have hs := hsearch i hiN
    have hp := quadratic_search_positive m hm Q hQ hpos g i (hpre i hiN)
    obtain ⟨_,_,_,hz⟩ := hm Q hQ hpos g i
    have hd : m.direction H≠0 := by
      intro hd
      have hh := hp.1
      change 0 < inner ℝ (m.direction H) (Q (m.direction H)) at hh
      simp only [hd,inner_zero_left] at hh
      exact lt_irrefl _ hh
    change (⟨(scalarFunctionRun m T f G r x₀ i).initial,
      scalarFunctionRecord m T f G r x₀ (scalarFunctionRun m T f G r x₀ i)::
        (scalarFunctionRun m T f G r x₀ i).records⟩ : History E)=_
    rw [ih (by omega)]
    exact scalarFunctionRecord_quadratic m T f G r x₀ H Q _ hp.2.ne' hd rfl hs.1 hs.2 hz

end
end krylov.Functions
