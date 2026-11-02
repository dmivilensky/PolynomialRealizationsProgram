import krylov.Convergence.VirtualDirectionOutputFields
import krylov.Convergence.VirtualDerivativeCoordinates
import krylov.OneGradient.XRFCDirectionVariation

/-!
Article: main_krylov, thm:V, native direction-basis source derivative.
Use: include arbitrary actual initial-gradient drift in the original
printed direction response. Its derivative vanishes because the native
quadratic output remains exactly zero on a genuine open full-reference
neighborhood, derived here from true nonstagnation and primitive trials.
Source: actual native C² calculus, open finite nonstagnation, quadratic
termination and the already proved original fixed-gradient first variation.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Stability krylov.OneGradient krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The genuine full output has zero initial-gradient derivative at its
true full quadratic reference; this is derived from native termination,
not imposed as a response assumption. Article: main_krylov, thm:V. -/
theorem xrfcDFiniteOutput_initial_gradient_derivative_zero
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) g i)≠0)
    (hT : ∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) g i)) (v : E) :
    fderiv ℝ (oneGradientFiniteOutput (xrfcDMethod fullMemory trial) (cgOperator base) n) (g,0) (v,0)=0 := by
  let method:=xrfcDMethod fullMemory trial
  let Q:=cgOperator base
  let gp:=fun t : ℝ=>g+t • v
  let F:=oneGradientFiniteOutput method Q n
  let zg : E × ((Fin n → E →L[ℝ] E) × (E →L[ℝ] E)):=(v,0)
  have hgp : AnalyticAt ℝ gp 0 := analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hg0 : gp 0=g := by simp only [gp,zero_smul,add_zero]
  have hpre (i : ℕ) (hi : i<n) := cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hp:=cgOperator_positive base hb
  have hcg := cg_prefix_analytic (fun _ : ℝ=>Q) gp 0 analyticAt_const hgp hp.1 hp.2 (n-1)
    (by intro i hi;rw [hg0];exact hpre i (by omega))
  have hgn : CG.gradient Q (gp 0) (n-1)≠0 := by rw [hg0];exact hpre _ (by omega)
  have hcount : ∀ᶠ t : ℝ in 𝓝 0,referenceAtomCount base hb (gp t)=n := by
    filter_upwards [hcg.1.continuousAt.eventually_ne hgn] with t ht'
    have hlo : n-1<referenceAtomCount base hb (gp t) := by
      by_contra hh
      exact ht' ((cg_stopping_iff base hb (gp t) (n-1)).mpr (by omega))
    have hhi : referenceAtomCount base hb (gp t)≤n := by
      unfold referenceAtomCount activeSpectralValues
      exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n))
    omega
  have hreg := quadraticXRFCD_prefix_contDiffAt (r:=1) trial (fun _ : ℝ=>fun _=>Q) gp 0
    (fun _=>contDiffAt_const) hgp.contDiffAt Q rfl hp.1 hp.2 n
    (by rw [hg0];exact hpre) (by rw [hg0];exact ht) (by rw [hg0];exact fun i hi=>(hT i hi).of_le (by norm_num))
  have htrial (i : Fin n) : ∀ᶠ t : ℝ in 𝓝 0,trial (oneGradientRun method (fun _=>Q) (gp t) i.val)≠0 := by
    have hr := actual_trial_contDiffAt trial method (fun _ : ℝ=>fun _=>Q) gp 0 i.val hgp.contDiffAt
      (fun j hj=>hreg.2.1 j (hj.trans i.isLt)) (fun j hj=>hreg.1 j (hj.trans i.isLt.le))
      (by rw [hg0];exact (hT i.val i.isLt).of_le (by norm_num))
    exact hr.continuousAt.eventually_ne (by rw [hg0];exact ht i.val i.isLt)
  have htrialAll : ∀ᶠ t : ℝ in 𝓝 0,∀ i : Fin n,trial (oneGradientRun method (fun _=>Q) (gp t) i.val)≠0 :=
    Filter.eventually_all.mpr htrial
  have hzero : ∀ᶠ t : ℝ in 𝓝 0,F ((g,0)+t • zg)=0 := by
    filter_upwards [hcount,htrialAll] with t hcountt htrials
    have hout := (xrfcD_terminates base hb (gp t) fullMemory trial (fun _ _ hi=>hi)
      (fun i hi=>htrials ⟨i,by simpa only [hcountt] using hi⟩)).2.1
    rw [hcountt] at hout
    have hpair : (g,0)+t • zg=(gp t,0) := by
      apply Prod.ext
      · rfl
      · change (0 : (Fin n → E →L[ℝ] E) × (E →L[ℝ] E))+t • 0=0
        rw [zero_add]
        exact _root_.smul_zero (A := (Fin n → E →L[ℝ] E) × (E →L[ℝ] E)) t
    rw [hpair]
    change method.outputGradient (Q+0) (oneGradientRun method (fcFiniteOperatorPath Q n 0) (gp t) n)=0
    rw [add_zero,fcFiniteOperatorPath_zero]
    exact hout
  have hF := xrfcDFiniteOutput_contDiffAt trial Q hp.1 hp.2 n g hpre ht hT
  have hline : HasDerivAt (fun t : ℝ=>(g,0)+t • zg) zg 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const zg).const_add (g,0)
  have hdf : HasFDerivAt F (fderiv ℝ F (g,0)) ((g,0)+(0:ℝ) • zg) := by
    rw [show (g,0)+(0:ℝ) • zg=(g,0) by module]
    exact (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hchain:=hdf.comp_hasDerivAt 0 hline
  have hconst : HasDerivAt (fun t : ℝ=>F ((g,0)+t • zg)) 0 0 :=
    (hasDerivAt_const (0:ℝ) (0:E)).congr_of_eventuallyEq hzero
  exact hchain.unique hconst

/-- The full actual joint finite derivative, including arbitrary initial
force drift, is precisely the printed direction-basis response with Pi=I.
No symmetry premise is needed on its operator perturbation coordinates.
Article: main_krylov, thm:V, direction-basis formula. -/
theorem xrfcDFiniteOutput_fderiv_response
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) g i)≠0)
    (hT : ∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) g i))
    (z : E × ((Fin n → E →L[ℝ] E) × (E →L[ℝ] E))) :
    let R:=cgOperator (metricRoot base)⁻¹
    let W:=oneGradientOutputDrift n z.2.1 z.2.2
    R (fderiv ℝ (oneGradientFiniteOutput (xrfcDMethod fullMemory trial) (cgOperator base) n) (g,0) z)=
      xrfcDirectionResponse trial base g (fun l=>R*(W (l+1)-W l)*R) := by
  let method:=xrfcDMethod fullMemory trial
  let Q:=cgOperator base
  let R:=cgOperator (metricRoot base)⁻¹
  let W:=oneGradientOutputDrift n z.2.1 z.2.2
  let op:=fun (t : ℝ) i=>Q+t • W i
  let F:=oneGradientFiniteOutput method Q n
  have hop (i : ℕ) : ContDiffAt ℝ 1 (fun t=>op t i) 0 := by dsimp only [op];fun_prop
  have hop0 : op 0=fun _=>Q := by
    funext i
    change Q+(0:ℝ) • W i=Q
    module
  have hfirst := xrfc_direction_output_first_jet trial base hb g hc hn op hop hop0 ht
    (fun i hi=>(hT i hi).of_le (by norm_num))
  have hD (i : ℕ) : deriv (fun t=>op t i) 0=W i := by
    simpa only [op,one_smul,id_eq] using (((hasDerivAt_id (0:ℝ)).smul_const (W i)).const_add Q).deriv
  simp only [hD] at hfirst
  have hF:=xrfcDFiniteOutput_contDiffAt trial Q (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 n g (fun i hi=>cg_nonstagnation base hb g i (by rw [hc];exact hi)) ht hT
  let zop : E × ((Fin n → E →L[ℝ] E) × (E →L[ℝ] E)):=(0,z.2)
  have hline : HasDerivAt (fun t : ℝ=>(g,0)+t • zop) zop 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const zop).const_add (g,0)
  have hdf : HasFDerivAt F (fderiv ℝ F (g,0)) ((g,0)+(0:ℝ) • zop) := by
    rw [show (g,0)+(0:ℝ) • zop=(g,0) by module]
    exact (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hchain:=R.hasFDerivAt.comp_hasDerivAt 0 (hdf.comp_hasDerivAt 0 hline)
  have he (t : ℝ) : R (F ((g,0)+t • zop))=
      R (method.outputGradient (op t n) (oneGradientRun method (op t) g n)) := by
    have hb' : op t n=Q+t • z.2.2 := by simp only [op,W,oneGradientOutputDrift,lt_self_iff_false,dite_eq_right,not_false_eq_true]
    have hp' : ∀ i<n,fcFiniteOperatorPath Q n (t • z.2.1) i=op t i := by
      intro i hi
      simp only [fcFiniteOperatorPath,dite_eq_left hi,Pi.smul_apply,op,W,oneGradientOutputDrift]
    have hpair : (g,0)+t • zop=(g,(t • z.2.1,t • z.2.2)) := by
      rcases z with ⟨a,b,c⟩
      simp [zop]
    rw [hpair]
    dsimp only [F,oneGradientFiniteOutput]
    rw [oneGradientRun_congr_prefix method _ _ _ n hp',←hb']
  have hopresponse := (hchain.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t=>(he t).symm))).unique hfirst
  have hgzero:=xrfcDFiniteOutput_initial_gradient_derivative_zero trial base hb g hc hn ht hT z.1
  have hsplit : z=(z.1,0)+zop := by dsimp only [zop];simp
  change R (fderiv ℝ F (g,0) z)=_
  conv_lhs => rw [hsplit]
  rw [map_add,hgzero,zero_add]
  exact hopresponse

end
end krylov.Convergence
