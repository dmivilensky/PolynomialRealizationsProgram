import krylov.Functions.HilbertPlaneRFCFModel
import krylov.Functions.PlanarRFCFResponse

/-!
Article: main_krylov, thm:Fplanar, actual full-window RFC-F solve reduction.
Use: solve the genuine full observed corrected model and identify its output
with the original planar model output, retaining every middle observation.
Source: exact scalar model compression, positive inverse domain and uniqueness
of the implemented Galerkin solve on the actual independent reference steps.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Correction krylov.Tensor.BinaryCubic
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [DecidableEq ι]

/-- The original value-corrected full observed model, with genuine scalar
values, genuine gradients and actual covector splits.
Article: main_krylov, thm:Fplanar. -/
def hilbertPlaneRFCFModel (e h m : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (a s : ι → E) (z : E) : Matrix ι ι ℝ :=
  let f := hilbertPlaneObjective e h m p r t
  let G := gradient f
  valueCorrectedModel f (fun x=>innerSL ℝ (G x)) a s
    (fun i=>covectorSplit (innerSL ℝ (G (a i+s i)-G (a i))) (a i) (s i) z)

/-- The actual full-space final observed-model output.
Article: main_krylov, thm:Fplanar. -/
def hilbertPlaneRFCFOutput (e h m : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (a s : ι → E) (z : E) : E :=
  z+combine s (modelCoefficients s (hilbertPlaneRFCFModel e h m p r t a s z)
    (gradient (hilbertPlaneObjective e h m p r t) z))

/-- At every correction in the genuine plane, the full actual gradient is
precisely the embedded planar gradient; the complement is already minimized.
Article: main_krylov, thm:Fplanar. -/
theorem hilbertPlaneRFCF_corrected_gradient (e h m : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (hm : hilbertPlaneProject e h m=0)
    (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (v : Plane) :
    gradient (hilbertPlaneObjective e h m p r t)
      (hilbertPlaneTerminal e h m p r+hilbertPlaneEmbed e h v)=
      hilbertPlaneEmbed e h (gradient (planeCubicObjective p r t) (planeOfPair (p,r*p)+v)) := by
  simp only [hilbertPlaneGradient_actual,hilbertPlaneGradient,hilbertPlaneTerminal,map_add,
    hilbertPlaneProject_embed e h he hh heh,hm,add_zero]
  module

set_option maxHeartbeats 1000000 in
/-- The actual full observed RFC-F solve reduces exactly to its genuine
first/last planar solve. All middle pairs remain in the implemented model;
their identity block is derived from the source observations.
Article: main_krylov, thm:Fplanar, full-space solve dictionary. -/
theorem hilbertPlaneRFCFOutput_eq_plane (hι : (⊥ : ι)≠⊤)
    (e h m : E) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (hm : hilbertPlaneProject e h m=0) (p r : ℝ) (hp : 0<p) (hr : r≠0)
    (t : krylov.Tensor.BinaryCubic) (a s : ι → E)
    (ha : ∀ i, hilbertPlaneProject e h (a i)=planeRFCFWindowAnchor p i)
    (hs : ∀ i, hilbertPlaneProject e h (s i)=planeRFCFWindowStep p r i)
    (hfirst : s ⊥=p • e) (hlaststep : s ⊤=(r*p) • h)
    (hind : LinearIndependent ℝ s)
    (hfuture : ∀ i, inner ℝ (s i) (hilbertPlaneTerminal e h m p r-a i)=‖s i‖^2)
    (hlast : hilbertPlaneTerminal e h m p r=a ⊤+s ⊤)
    (hsmall : p*‖planeRFCFModelOperator r t‖≤1/2) :
    hilbertPlaneRFCFOutput e h m p r t a s (hilbertPlaneTerminal e h m p r)=
      hilbertPlaneEmbed e h (planeRFCFOutput p r t)+m := by
  let Q := hilbertPlaneRFCFOperator e h p r t
  let J := hilbertPlaneEmbed e h
  let z := hilbertPlaneTerminal e h m p r
  let v := planeRFCFCorrection p r t
  let g := gradient (hilbertPlaneObjective e h m p r t) z
  have hQ := hilbertPlaneRFCFOperator_symmetric e h p r t
  have hpos := hilbertPlaneRFCFOperator_pos e h he hh heh p r hp.le t hsmall
  have hpair : crossGram (fun i=>Q (s i)) s=correctionCompression s Q := by
    ext i j
    exact hQ _ _
  have hunit : IsUnit (crossGram (fun i=>Q (s i)) s).det :=
    isUnit_iff_ne_zero.mpr (operatorGram_posDef Q hQ hpos hind).det_pos.ne'
  have he_mem : e∈Submodule.span ℝ (Set.range s) := by
    have ht := (Submodule.span ℝ (Set.range s)).smul_mem p⁻¹ (Submodule.subset_span ⟨⊥,rfl⟩)
    rw [hfirst,smul_smul,inv_mul_cancel₀ hp.ne',one_smul] at ht
    exact ht
  have hh_mem : h∈Submodule.span ℝ (Set.range s) := by
    have ht := (Submodule.span ℝ (Set.range s)).smul_mem (r*p)⁻¹ (Submodule.subset_span ⟨⊤,rfl⟩)
    rw [hlaststep,smul_smul,inv_mul_cancel₀ (mul_ne_zero hr hp.ne'),one_smul] at ht
    exact ht
  have hu : J v∈Submodule.span ℝ (Set.range s) :=
    (Submodule.span ℝ (Set.range s)).add_mem
      ((Submodule.span ℝ (Set.range s)).smul_mem (v 0) he_mem)
      ((Submodule.span ℝ (Set.range s)).smul_mem (v 1) hh_mem)
  have hppos w (hw : w≠0) : 0 < inner ℝ w
      ((ContinuousLinearMap.id ℝ Plane+p • planeRFCFModelOperator r t) w) := by
    have hlow := planeRFCFModel_lower p r hp.le t w
    have hn := sq_pos_of_pos (norm_pos_iff.mpr hw)
    nlinarith only [hlow,mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖w‖),hn]
  have hsolve := planeRFCFCorrection_equation p r hp.ne' hr t hppos
  have hgp : gradient (planeCubicObjective p r t) (planeOfPair (p,r*p))=p^2 • planeTerminalRho r t := by
    have ht := planeCubicGradient_terminal_identity p r t (0 : Plane)
    have hz : planeOfPair (0,0)=0 := by ext i; fin_cases i <;> rfl
    simpa [planarValueCoordinateDerivative,pairOfPlane,hz] using ht
  have hg : g=J (p^2 • planeTerminalRho r t) := by
    have ht := hilbertPlaneRFCF_corrected_gradient e h m he hh heh hm p r t 0
    simpa only [map_zero,add_zero,hgp] using ht
  have hzero : g+Q (J v)=0 := by
    rw [hg,hilbertPlaneRFCFOperator_embed e h he hh heh p r t,←map_add]
    have hz : p^2 • planeTerminalRho r t+
        (ContinuousLinearMap.id ℝ Plane+p • planeRFCFModelOperator r t) v=0 := by
      change p^2 • planeTerminalRho r t+(v+p • planeRFCFModelOperator r t v)=0
      rw [hsolve]
      module
    rw [hz,map_zero]
  have ho : coordinates s (g+Q (J v))=0 := by
    rw [hzero]
    ext i
    exact inner_zero_right (s i)
  have hcor := modelCorrection_unique Q hQ s g (J v) hunit hu ho
  have hmodel := hilbertPlaneRFCF_observed_model hι e h m p r t a s z ha hs
    (fun i=>hind.ne_zero i) hfuture hlast
  unfold hilbertPlaneRFCFOutput
  change z+combine s (modelCoefficients s (hilbertPlaneRFCFModel e h m p r t a s z) g)=_
  change hilbertPlaneRFCFModel e h m p r t a s z=correctionCompression s Q at hmodel
  rw [hmodel,←hpair,hcor]
  simp only [z,hilbertPlaneTerminal,planeRFCFOutput,map_add]
  module

end
end krylov.Functions
