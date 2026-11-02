import krylov.Convergence.VirtualVaryingGradient
import krylov.Convergence.VirtualOutputFields
import krylov.Functions.NativeRFCPhysicalInputs

/-!
Article: main_krylov, thm:V and lem:cycle-transfer.
Use: identify the genuine joint finite-output derivative with the printed
step-basis response, including arbitrary initial-gradient drift. Actual
symmetric segment directions are converted through the true matrix isometry.
Source: full-model launch variation and exact causal finite coordinates.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.OneGradient
  krylov.Functions
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Finite segment variations extended by their semantic last value.
Article: main_krylov, thm:V, full finite output coordinates. -/
def oneGradientOutputDrift (N : ℕ) (θ : Fin N → E →L[ℝ] E) (B : E →L[ℝ] E) (i : ℕ) : E →L[ℝ] E :=
  if h : i<N then θ ⟨i,h⟩ else B

/-- The full actual finite derivative is the source oblique-flag sum;
initial-gradient drift contributes no additional first-order term.
Article: main_krylov, thm:V and lem:cycle-transfer. -/
theorem xrfcFiniteOutput_fderiv_response
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) g i)≠0)
    (hT : ∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _=>cgOperator base) g i))
    (z : E × ((Fin n → E →L[ℝ] E) × (E →L[ℝ] E)))
    (hz : ∀ i,(z.2.1 i).toLinearMap.IsSymmetric) (hB : z.2.2.toLinearMap.IsSymmetric) :
    let R := cgOperator (metricRoot base)⁻¹
    let W := oneGradientOutputDrift n z.2.1 z.2.2
    R (fderiv ℝ (oneGradientFiniteOutput (xrfcMethod fullMemory trial) (cgOperator base) n) (g,0) z)=
      xrfcStepResponse trial base g (fun l=>R*(W (l+1)-W l)*R) := by
  let m := xrfcMethod fullMemory trial
  let Q := cgOperator base
  let R := cgOperator (metricRoot base)⁻¹
  let W := oneGradientOutputDrift n z.2.1 z.2.2
  let A := fun (t : ℝ) i=>physicalOperatorMatrix (Q+t • W i)
  let gp := fun t : ℝ=>g+t • z.1
  let P := (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ)).symm.toAlgEquiv.toLinearMap.toContinuousLinearMap
  have hop (t : ℝ) (i : ℕ) : cgOperator (A t i)=Q+t • W i := physicalOperatorMatrix_operator _
  have hA (i : ℕ) : ContDiffAt ℝ 1 (fun t=>A t i) 0 := by
    have hp : ContDiffAt ℝ 1 (fun t : ℝ=>Q+t • W i) 0 := by fun_prop
    exact P.contDiff.contDiffAt.comp (0:ℝ) hp
  have hA₀ (i : ℕ) : A 0 i=base := by
    change physicalOperatorMatrix (Q+(0:ℝ) • W i)=base
    rw [show Q+(0:ℝ) • W i=Q by module]
    exact (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ)).symm_apply_apply base
  have hsym (t : ℝ) (i : ℕ) : (A t i).IsSymm := by
    have hw : (W i).toLinearMap.IsSymmetric := by
      dsimp only [W,oneGradientOutputDrift]
      split_ifs with hi
      · exact hz ⟨i,hi⟩
      · exact hB
    apply physicalOperatorMatrix_symmetric
    exact (cgOperator_positive base hb).1.add (LinearMap.IsSymmetric.smul (by rfl) hw)
  have hgp : ContDiffAt ℝ 1 gp 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hg₀ : gp 0=g := by simp only [gp,zero_smul,add_zero]
  have hfirst := xrfc_step_output_first_jet_varying_gradient trial base hb gp hgp
    (by rw [hg₀];exact hc) hn A hA hsym hA₀
    (by rw [hg₀];exact ht) (by rw [hg₀];exact fun i hi=>(hT i hi).of_le (by norm_num))
  have hD (i : ℕ) : deriv (fun t=>cgOperator (A t i)) 0=W i := by
    have hh : HasDerivAt (fun t : ℝ=>Q+t • W i) (W i) 0 := by
      simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const (W i)).const_add Q
    simpa only [hop] using hh.deriv
  simp only [hg₀,hD] at hfirst
  let F := oneGradientFiniteOutput m Q n
  have hF : ContDiffAt ℝ 2 F (g,0) := xrfcFiniteOutput_contDiffAt trial Q
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 n g
    (fun i hi=>cg_nonstagnation base hb g i (by rw [hc];exact hi)) ht hT
  have hline : HasDerivAt (fun t : ℝ=>(g,0)+t • z) z 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const z).const_add (g,0)
  have hdf : HasFDerivAt F (fderiv ℝ F (g,0)) ((g,0)+(0:ℝ) • z) := by
    rw [show (g,0)+(0:ℝ) • z=(g,0) by module]
    exact (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hchain := R.hasFDerivAt.comp_hasDerivAt 0 (hdf.comp_hasDerivAt 0 hline)
  have he (t : ℝ) : R (F ((g,0)+t • z))=
      R (m.outputGradient (cgOperator (A t n))
        (oneGradientRun m (fun i=>cgOperator (A t i)) (gp t) n)) := by
    have hb : cgOperator (A t n)=Q+t • z.2.2 := by
      rw [hop]
      simp only [W,oneGradientOutputDrift,lt_self_iff_false,dite_eq_right,not_false_eq_true]
    have hp : ∀ i<n,fcFiniteOperatorPath Q n (t • z.2.1) i=cgOperator (A t i) := by
      intro i hi
      simp only [fcFiniteOperatorPath,dite_eq_left hi,Pi.smul_apply,hop,W,oneGradientOutputDrift]
    have hpair : (g,0)+t • z=(g+t • z.1,(t • z.2.1,t • z.2.2)) := by
      rcases z with ⟨a,b,c⟩
      simp
    rw [hpair]
    dsimp only [F,oneGradientFiniteOutput]
    rw [oneGradientRun_congr_prefix m _ _ _ n hp,←hb]
  have hc' := hchain.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t=>(he t).symm))
  exact hc'.unique hfirst

end
end krylov.Convergence
