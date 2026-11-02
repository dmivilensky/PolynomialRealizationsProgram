import krylov.Convergence.OrderSearchOnlyLeading
import krylov.Convergence.OrderDeferredResponse
import krylov.Cancellation.DeferredSchurNative

/-!
Article: main_krylov, thm:D and thm:DC, genuine complete deferred tensor coordinates.
Use: identify the actual joint native finite derivative, including the true
initial-gradient drift, with the printed deferred flag/tail response.
Initial-gradient variation vanishes by genuine full quadratic termination;
common operator drift remains in the derived physical first variation.
Source: actual policy calculus and true full CG reference-slice cancellation.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Finset krylov.Cancellation krylov.Methods krylov.Reference
  krylov.Functions krylov.Stability krylov.Variation krylov.Envelope krylov.Secant
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The full genuine quadratic reference slice kills every initial-gradient
first variation, before any native source jet is substituted. Article: thm:D. -/
theorem searchOnlyFiniteTerminal_initial_derivative_zero
    (m : ProbedMethod E) (hc : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v,v≠0 →0 < inner ℝ v (Q v)) (g : E)
    (hpre : ∀ i<n,CG.gradient Q g i≠0) (hs : SmoothProbedCycleAt m 2 Q g n) (v : E) :
    fderiv ℝ (searchOnlyFiniteTerminal m Q n) (g,0) (v,0)=0 := by
  have hzero : ∀ y : E,searchOnlyFiniteTerminal m Q n (y,0)=0 := by
    intro y
    have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n))=n := finrank_euclideanSpace_fin
    have hz:=searchOnlyFiniteTerminal_reference_zero m hc Q hQ hpos y
    rw [hn] at hz
    exact hz
  have hd0 : HasFDerivAt (fun y : E=>searchOnlyFiniteTerminal m Q n (y,0)) (0 : E →L[ℝ] E) g := by
    have he : (fun y : E=>searchOnlyFiniteTerminal m Q n (y,0))=fun _=>0 := funext hzero
    rw [he]
    exact hasFDerivAt_const (0:E) g
  have hF:=searchOnlyFiniteTerminal_contDiffAt m hc Q hQ hpos n g hpre hs
  have hd:=(hF.differentiableAt (by norm_num)).hasFDerivAt.comp g
    (ContinuousLinearMap.inl ℝ E (Fin n → E →L[ℝ] E)).hasFDerivAt
  have he:=congrArg (fun L : E →L[ℝ] E=>L v) (hd.unique hd0)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,_root_.zero_apply] using he

/-- The complete actual finite deferred derivative equals the printed
canonical response on genuine physical differences, including arbitrary
initial-gradient and common first-secant drift. Article: thm:D and thm:DC. -/
theorem deferredFiniteTerminal_fderiv_response
    (estimate : History E → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (k : ℕ) (hcount : referenceAtomCount base hb g=n) (hfull : k+1=n)
    (ha :
      let H:=methodRun (deferredDataMethod fullMemory (k+1) estimate)
        (fun _=>cgOperator base) (fun _=>cgOperator base) g k
      ContDiffAt ℝ 2 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : 0<estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate)
      (fun _=>cgOperator base) (fun _=>cgOperator base) g k))
    (z : E × (Fin n → E →L[ℝ] E)) (hz : ∀ i,(z.2 i).toLinearMap.IsSymmetric) :
    let Q:=cgOperator base
    let a0:=estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _=>Q) (fun _=>Q) g k)
    let m:=deferredDataMethod fullMemory (k+1) estimate
    cgOperator (metricRoot base)⁻¹ (fderiv ℝ (searchOnlyFiniteTerminal m Q n) (g,0) z)=
      deferredResponse base g k (1-CG.length Q g k/a0)
        (fun l=>physicalCanonicalMatrix base hb (fcFiniteDrift n z.2 (l+1)-fcFiniteDrift n z.2 l)) := by
  let Q:=cgOperator base
  let m:=deferredDataMethod fullMemory (k+1) estimate
  let R:=cgOperator (metricRoot base)⁻¹
  let W:=fcFiniteDrift n z.2
  let A:=fun (t : ℝ) i=>Q+t • W i
  let F:=searchOnlyFiniteTerminal m Q n
  let zop : E × (Fin n → E →L[ℝ] E):=(0,z.2)
  have hp:=cgOperator_positive base hb
  have hpre i (hi : i<n) : CG.gradient Q g i≠0 := cg_nonstagnation base hb g i (by omega)
  have hc : CGConsistent m := deferred_data_consistent fullMemory (fun _ hj=>hj) (k+1) estimate
  have hs0:=deferred_data_smoothCycleAt fullMemory (fun _ hj=>hj) (k+1) estimate Q hp.1 hp.2 g (k+1)
    (fun i hi=>hpre i (by omega)) 2
    (by
      intro j _ hj
      have he : j=k := by omega
      subst j
      exact ha)
    (by
      intro j _ hj
      have he : j=k := by omega
      subst j
      exact ha0)
  have hs : SmoothProbedCycleAt m 2 Q g n := hs0.mono m (by omega)
  have hF:=searchOnlyFiniteTerminal_contDiffAt m hc Q hp.1 hp.2 n g hpre hs
  have hW i : (W i).toLinearMap.IsSymmetric := by
    dsimp only [W,fcFiniteDrift]
    split_ifs with hi
    · exact hz ⟨i,hi⟩
    · exact LinearMap.IsSymmetric.zero
  have hfirst:=deferred_affine_full_hasDerivAt estimate base hb g W hW k hcount hfull ha ha0
  have hline : HasDerivAt (fun t : ℝ=>(g,0)+t • zop) zop 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const zop).const_add (g,0)
  have hdf : HasFDerivAt F (fderiv ℝ F (g,0)) ((g,0)+(0:ℝ) • zop) := by
    rw [show (g,0)+(0:ℝ) • zop=(g,0) by module]
    exact (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hchain:=R.hasFDerivAt.comp_hasDerivAt 0 (hdf.comp_hasDerivAt 0 hline)
  have he (t : ℝ) : R (F ((g,0)+t • zop))=R (probedGradient m (A t) (A t) g (k+1)) := by
    have hpair : (g,0)+t • zop=(g,t • z.2) := by
      apply Prod.ext
      · change g+t • (0:E)=g
        module
      · change (0 : Fin n → E →L[ℝ] E)+t • z.2=t • z.2
        exact zero_add _
    rw [hpair]
    have hpath i (hi : i<n) : fcFiniteOperatorPath Q n (t • z.2) i=A t i := by
      simp only [fcFiniteOperatorPath,dite_eq_left hi,Pi.smul_apply,A,W,fcFiniteDrift]
    change R (probedGradient m (fcFiniteOperatorPath Q n (t • z.2))
      (fcFiniteOperatorPath Q n (t • z.2)) g n)=_
    rw [probedGradient,methodRun_congr_prefix m _ _ (A t) (A t) g n hpath hpath,hfull]
    rfl
  have hopresponse:=(hchain.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t=>(he t).symm))).unique hfirst
  have hgzero:=searchOnlyFiniteTerminal_initial_derivative_zero m hc Q hp.1 hp.2 g hpre hs z.1
  have hsplit : z=(z.1,0)+zop := by
    apply Prod.ext
    · exact (add_zero _).symm
    · exact (zero_add _).symm
  change R (fderiv ℝ F (g,0) z)=_
  conv_lhs=>rw [hsplit]
  rw [map_add,hgzero,zero_add]
  exact hopresponse

end
end krylov.Convergence
