import krylov.Functions.ReferencePlaneSmallSource
import krylov.Functions.NativeRFCEmbedding
import krylov.Functions.NativeRFCF

/-!
Article: main_krylov, thm:Fplanar, literal native RFC-F prefix on scalar sources.
Use: identify the actual data-only rfcFunctionRun with the genuine static CG
reference before its last value correction. All searches and zero correction
queries are proved from the original scalar objective and global consistency.
Source: actual model column rescaling, native record dictionary and the
genuine positive scalar search-domain construction.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Reference krylov.Tensor krylov.Nonlinear krylov.Methods
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

/-- The literal native RFC record has its actual quadratic protocol form
when true source searches match the genuine active quadratic prefix.
The zero native correction is derived from global RFC consistency.
Article: main_krylov, thm:Fplanar. -/
theorem rfcFunctionRecord_quadratic (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (H : History E) (Q : E →L[ℝ] E)
    (hd : rfcFunctionDirection memory H≠0)
    (hα : lineLength H.gradient (rfcFunctionDirection memory H) (Q (rfcFunctionDirection memory H))≠0)
    (hstep : rfcFunctionLineStep T f memory r x₀ H=
      lineLength H.gradient (rfcFunctionDirection memory H) (Q (rfcFunctionDirection memory H)) • rfcFunctionDirection memory H)
    (hpost : G (rfcFunctionLinePoint T f memory r x₀ H)=
      searchedGradient H.gradient (rfcFunctionDirection memory H) (Q (rfcFunctionDirection memory H)))
    (hz : ZeroCorrections (rfcCorrection memory 1 H (Q (rfcFunctionDirection memory H))) Q
      (searchedGradient H.gradient (rfcFunctionDirection memory H) (Q (rfcFunctionDirection memory H)))) :
    (⟨H.initial,rfcFunctionRecord T f G memory r x₀ H::H.records⟩ : History E)=
      methodAdvance (rfcMethod memory 1) Q Q H := by
  have hsec : G (rfcFunctionLinePoint T f memory r x₀ H)-H.gradient=
      lineLength H.gradient (rfcFunctionDirection memory H) (Q (rfcFunctionDirection memory H)) •
        Q (rfcFunctionDirection memory H) := by rw [hpost,searchedGradient]; abel
  have hcor := rfcFunctionCorrectionStep_operator T f G memory r x₀ H Q Q _ hα hstep hsec hpost
  have hu : rfcFunctionCorrectionStep T f G memory r x₀ H=0 :=
    hcor.trans (zeroCorrections_change_operator _ Q Q _ hz).2.1
  exact (rfcFunctionRecord_operator T f G memory r x₀ H Q Q hd hα hstep hpost
    (by rw [hu,map_zero,add_zero,add_zero])).symm

/-- True scalar source fields force the complete literal native RFC prefix
to equal the actual static reference history, including every recorded query.
Article: main_krylov, thm:Fplanar, original executor replay. -/
theorem rfcFunctionRun_quadratic_prefix
    (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (hinit : G x₀=g) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient Q g i≠0)
    (hsearch : ∀ i<N,
      let H := methodRun (rfcMethod memory 1) (fun _=>Q) (fun _=>Q) g i
      let d := rfcFunctionDirection memory H
      rfcFunctionLineStep T f memory r x₀ H=lineLength H.gradient d (Q d) • d ∧
      G (rfcFunctionLinePoint T f memory r x₀ H)=searchedGradient H.gradient d (Q d)) :
    ∀ i≤N, rfcFunctionRun T f G memory r x₀ i=
      methodRun (rfcMethod memory 1) (fun _=>Q) (fun _=>Q) g i := by
  let m : ProbedMethod E := rfcMethod memory 1
  have hc := rfcMethod_consistent memory hm 1 (E:=E)
  intro i hi
  induction i with
  | zero => simp only [rfcFunctionRun,methodRun,hinit]
  | succ i ih =>
    have hiN : i<N := by omega
    let H := methodRun m (fun _=>Q) (fun _=>Q) g i
    have hs := hsearch i hiN
    have hp := quadratic_search_positive m hc Q hQ hpos g i (hpre i hiN)
    obtain ⟨_,_,_,hz⟩ := hc Q hQ hpos g i
    have hd : rfcFunctionDirection memory H≠0 := by
      intro hd
      have hh := hp.1
      change 0 < inner ℝ (rfcFunctionDirection memory H) (Q (rfcFunctionDirection memory H)) at hh
      rw [hd,inner_zero_left] at hh
      exact lt_irrefl _ hh
    change (⟨(rfcFunctionRun T f G memory r x₀ i).initial,
      rfcFunctionRecord T f G memory r x₀ (rfcFunctionRun T f G memory r x₀ i)::
        (rfcFunctionRun T f G memory r x₀ i).records⟩ : History E)=_
    rw [ih (by omega)]
    exact rfcFunctionRecord_quadratic T f G memory r x₀ H Q hd hp.2.ne' hs.1 hs.2 hz

set_option maxHeartbeats 1000000 in
/-- Every actual native RFC prefix on the full reference-plane scalar
source equals its genuine static quadratic history. The true scalar search
and correction queries are all derived, with no supplied trajectory fields.
Article: main_krylov, thm:Fplanar, literal rfcFPoint foundation. -/
theorem referencePlaneCubic_rfc_prefix (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t : krylov.Tensor.BinaryCubic) (R : ℝ) (hH : ReferencePlanePositiveBall A hA g t R)
    (hnodes : ∀ i≤referenceAtomCount A hA g, ‖referencePlaneNode A g i‖≤R) :
    ∀ i≤referenceAtomCount A hA g-1,
      rfcFunctionRun (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t)
        (gradient (referencePlaneCubicObjective A hA g t)) fullMemory R 0 i=
      methodRun (rfcMethod fullMemory 1) (fun _=>cgOperator A) (fun _=>cgOperator A) g i := by
  let Q := cgOperator A
  let f := referencePlaneCubicObjective A hA g t
  let m := rfcMethod fullMemory 1 (E:=EuclideanSpace ℝ (Fin n))
  have hm := rfcMethod_consistent fullMemory (fun _ ha=>ha) 1 (E:=EuclideanSpace ℝ (Fin n))
  have hpos := cgOperator_positive A hA
  have hinit : gradient f 0=g := by
    have hg := referencePlaneCubicGradient_prefix A hA g hN t 0 (by omega)
    simpa only [CG.displacement,range_zero,sum_empty,CG.gradient,cgRun] using hg
  apply rfcFunctionRun_quadratic_prefix fullMemory (fun _ ha=>ha) (metricCoordinates A hA) f (gradient f)
    R 0 Q hpos.1 hpos.2 g hinit
  · intro i hi
    exact cg_nonstagnation A hA g i (by omega)
  · intro i hi
    let H := methodRun m (fun _=>Q) (fun _=>Q) g i
    let α := lineLength H.gradient (m.direction H) (Q (m.direction H))
    have hiN : i<referenceAtomCount A hA g := by omega
    have hnext : i+1<referenceAtomCount A hA g := by omega
    have hs := referencePlaneCubic_quadratic_search A hA g hN t R hH m hm i hiN (hnodes (i+1) (by omega))
    have hstep := scalar_quadratic_line_step m hm Q hpos.1 hpos.2 g i
    have hx := quadratic_displacement_eq_cg m hm Q hpos.1 hpos.2 g i
    change metricLocalExactPoint (metricCoordinates A hA) f H.displacement (m.direction H) R=
      CG.displacement Q g (i+1) at hs
    dsimp only
    simp only [rfcFunctionLineStep,rfcFunctionLinePoint,zero_add]
    change metricLocalExactPoint (metricCoordinates A hA) f H.displacement (m.direction H) R-H.displacement=
      α • m.direction H ∧
      gradient f (metricLocalExactPoint (metricCoordinates A hA) f H.displacement (m.direction H) R)=
        searchedGradient H.gradient (m.direction H) (Q (m.direction H))
    rw [hs]
    constructor
    · rw [hx,CG.displacement_succ,add_sub_cancel_left]
      exact hstep.symm
    · rw [referencePlaneCubicGradient_prefix A hA g hN t (i+1) hnext]
      obtain ⟨_,_,_,hz⟩ := hm Q hpos.1 hpos.2 g i
      have hg := quadratic_gradient_eq_cg m hm Q hpos.1 hpos.2 g (i+1)
      change (runCorrections (m.correction H (Q (m.direction H))) Q
        (searchedGradient H.gradient (m.direction H) (Q (m.direction H)))).gradient=_ at hg
      rw [(zeroCorrections_change_operator _ Q Q _ hz).2.2] at hg
      exact hg.symm

end
end krylov.Functions
