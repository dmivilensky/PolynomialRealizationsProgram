import krylov.Functions.HilbertPlaneRFCFSplits
import krylov.Functions.PlanarRFCFSolve

/-!
Article: main_krylov, thm:Fplanar, actual full-window corrected model.
Use: derive the original planar block and identity complement from the true
complete source observations, including every middle pair and actual split.
Source: scalar defect projection, real secant pairings and first/last geometry.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Correction krylov.Tensor.BinaryCubic
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [DecidableEq ι]

/-- The full operator computed by the genuine first/last planar model.
Article: main_krylov, thm:Fplanar, identity on the orthogonal complement. -/
def hilbertPlaneRFCFOperator (e h : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E+
    p • ((hilbertPlaneEmbed e h).comp ((planeRFCFModelOperator r t).comp (hilbertPlaneProject e h)))

/-- The complete full-source observed corrected model equals the compression
of the genuine planar block plus identity complement. All actual model-metric
splits are derived from the original reference geometry.
Article: main_krylov, thm:Fplanar, exact full-window reduction. -/
theorem hilbertPlaneRFCF_observed_model (hι : (⊥ : ι)≠⊤)
    (e h m : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (a s : ι → E) (z : E)
    (ha : ∀ i, hilbertPlaneProject e h (a i)=planeRFCFWindowAnchor p i)
    (hs : ∀ i, hilbertPlaneProject e h (s i)=planeRFCFWindowStep p r i)
    (hne : ∀ i, s i≠0) (hfuture : ∀ i, inner ℝ (s i) (z-a i)=‖s i‖^2)
    (hlast : z=a ⊤+s ⊤) :
    valueCorrectedModel (hilbertPlaneObjective e h m p r t)
      (fun x=>innerSL ℝ (gradient (hilbertPlaneObjective e h m p r t) x)) a s
      (fun i=>covectorSplit (innerSL ℝ (gradient (hilbertPlaneObjective e h m p r t) (a i+s i)-
        gradient (hilbertPlaneObjective e h m p r t) (a i))) (a i) (s i) z)=
      correctionCompression s (hilbertPlaneRFCFOperator e h p r t) := by
  have hl := funext (hilbertPlaneRFCF_window_split hι e h m p r t a s z ha hs hne hfuture hlast)
  rw [hl,hilbertPlane_value_model]
  have ha' : (fun i=>hilbertPlaneProject e h (a i))=planeRFCFWindowAnchor p := funext ha
  have hs' : (fun i=>hilbertPlaneProject e h (s i))=planeRFCFWindowStep p r := funext hs
  rw [ha',hs',planeRFCF_window_model hι]
  rw [←hs']
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,correctionCompression,crossGram,
    hilbertPlaneRFCFOperator,_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply,inner_add_right,inner_smul_right]
  have hadj : inner ℝ (s i) (hilbertPlaneEmbed e h (planeRFCFModelOperator r t (hilbertPlaneProject e h (s j))))=
      inner ℝ (hilbertPlaneProject e h (s i)) (planeRFCFModelOperator r t (hilbertPlaneProject e h (s j))) :=
    (real_inner_comm _ _).trans ((hilbertPlane_adjoint e h _ _).trans (real_inner_comm _ _))
  rw [hadj]
  ring

omit [CompleteSpace E] in
/-- The full observed block is a symmetric physical operator.
Article: main_krylov, thm:Fplanar. -/
theorem hilbertPlaneRFCFOperator_symmetric (e h : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    (hilbertPlaneRFCFOperator e h p r t).toLinearMap.IsSymmetric := by
  intro u v
  change inner ℝ (hilbertPlaneRFCFOperator e h p r t u) v=inner ℝ u (hilbertPlaneRFCFOperator e h p r t v)
  simp only [hilbertPlaneRFCFOperator,_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply,inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right,
    hilbertPlane_adjoint]
  have hadj : inner ℝ u (hilbertPlaneEmbed e h (planeRFCFModelOperator r t (hilbertPlaneProject e h v)))=
      inner ℝ (hilbertPlaneProject e h u) (planeRFCFModelOperator r t (hilbertPlaneProject e h v)) :=
    (real_inner_comm _ _).trans ((hilbertPlane_adjoint e h _ _).trans (real_inner_comm _ _))
  have hs := (planeRFCFModelOperator_symmetric r t) (hilbertPlaneProject e h u) (hilbertPlaneProject e h v)
  change inner ℝ (planeRFCFModelOperator r t (hilbertPlaneProject e h u)) (hilbertPlaneProject e h v)=
    inner ℝ (hilbertPlaneProject e h u) (planeRFCFModelOperator r t (hilbertPlaneProject e h v)) at hs
  rw [hadj,hs]

omit [CompleteSpace E] in
/-- The actual full block preserves precisely the original planar action.
Article: main_krylov, thm:Fplanar. -/
theorem hilbertPlaneRFCFOperator_embed (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (v : Plane) :
    hilbertPlaneRFCFOperator e h p r t (hilbertPlaneEmbed e h v)=
      hilbertPlaneEmbed e h ((ContinuousLinearMap.id ℝ Plane+p • planeRFCFModelOperator r t) v) := by
  simp only [hilbertPlaneRFCFOperator,_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply,hilbertPlaneProject_embed e h he hh heh,map_add,map_smul]

omit [CompleteSpace E] in
/-- Positivity of the actual full observed block follows from its small
genuine planar perturbation and the true orthogonal coordinate contraction.
Article: main_krylov, thm:Fplanar, actual full inverse domain. -/
theorem hilbertPlaneRFCFOperator_pos (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (p r : ℝ) (hp : 0≤p) (t : krylov.Tensor.BinaryCubic)
    (hsmall : p*‖planeRFCFModelOperator r t‖≤1/2) (v : E) (hv : v≠0) :
    0 < inner ℝ v (hilbertPlaneRFCFOperator e h p r t v) := by
  let M := planeRFCFModelOperator r t
  let P := hilbertPlaneProject e h
  let J := hilbertPlaneEmbed e h
  have hslice : ‖J (M (P v))‖≤‖M‖*‖v‖ := by
    rw [hilbertPlaneEmbed_norm e h he hh heh]
    exact (M.le_opNorm (P v)).trans (mul_le_mul_of_nonneg_left
      (hilbertPlaneProject_norm_le e h he hh heh v) (norm_nonneg _))
  have hb := (abs_le.mp ((abs_real_inner_le_norm v (J (M (P v)))).trans
    (mul_le_mul_of_nonneg_left hslice (norm_nonneg _)))).1
  have hn := sq_pos_of_pos (norm_pos_iff.mpr hv)
  simp only [hilbertPlaneRFCFOperator,_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,inner_add_right,inner_smul_right,
    real_inner_self_eq_norm_sq]
  change 0 < ‖v‖^2+p*inner ℝ v (J (M (P v)))
  nlinarith only [mul_le_mul_of_nonneg_left hb hp,mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖v‖),hn]

end
end krylov.Functions
