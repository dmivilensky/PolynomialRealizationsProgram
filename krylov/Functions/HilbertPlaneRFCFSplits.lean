import krylov.Functions.PlanarRFCFWindow
import krylov.Functions.HilbertPlaneSamples

/-!
Article: main_krylov, thm:Fplanar, actual full-space model-metric splits.
Use: derive one-half from genuine scalar secants and original orthogonal
reference geometry, including the actual last nonquadratic gradient.
Source: exact first/middle/last cubic gradient identities and covector pairing.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Correction krylov.Tensor.BinaryCubic
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [LinearOrder ι] [OrderBot ι] [OrderTop ι] [DecidableEq ι]

/-- The true planar source secants are exactly quadratic except for the
known first-direction increment in the last pair.
Article: main_krylov, thm:Fplanar. -/
theorem planeRFCF_window_secant (hι : (⊥ : ι)≠⊤) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (i : ι) :
    gradient (planeCubicObjective p r t) (planeRFCFWindowAnchor p i+planeRFCFWindowStep p r i)-
      gradient (planeCubicObjective p r t) (planeRFCFWindowAnchor p i)=
      planeRFCFWindowStep p r i+if i=⊤ then p^2 • planeTerminalRho r t else 0 := by
  by_cases hi0 : i=⊥ <;> by_cases hi1 : i=⊤ <;> ext j <;> fin_cases j <;>
    simp_all [planeRFCFWindowAnchor,planeRFCFWindowStep,planeCubicGradient_actual,
      planeCubicGradient,planarCubicGradient,planarValueCoordinateDerivative,
      planeTerminalRho,planeOfPair,pairOfPlane] <;> ring

/-- The full actual source secants follow the real reference steps, with
only the genuine last observed planar gradient added.
Article: main_krylov, thm:Fplanar. -/
theorem hilbertPlaneRFCF_window_secant (hι : (⊥ : ι)≠⊤)
    (e h m : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (a s : ι → E)
    (ha : ∀ i, hilbertPlaneProject e h (a i)=planeRFCFWindowAnchor p i)
    (hs : ∀ i, hilbertPlaneProject e h (s i)=planeRFCFWindowStep p r i) (i : ι) :
    gradient (hilbertPlaneObjective e h m p r t) (a i+s i)-
      gradient (hilbertPlaneObjective e h m p r t) (a i)=
      s i+if i=⊤ then hilbertPlaneEmbed e h (p^2 • planeTerminalRho r t) else 0 := by
  simp only [hilbertPlaneGradient_actual,hilbertPlaneGradient,map_add,ha,hs]
  have hplan := congrArg (hilbertPlaneEmbed e h) (planeRFCF_window_secant hι p r t i)
  rw [map_sub,map_add] at hplan
  by_cases hi : i=⊤
  · simp only [ite_eq_left hi] at hplan ⊢
    linear_combination (norm := module) hplan
  · simp only [ite_eq_right hi,map_zero,add_zero] at hplan ⊢
    linear_combination (norm := module) hplan

/-- The actual observed scalar curvature is the original squared step
length, including the last pair's nonquadratic first-coordinate observation.
Article: main_krylov, thm:Fplanar. -/
theorem hilbertPlaneRFCF_window_curvature (hι : (⊥ : ι)≠⊤)
    (e h m : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (a s : ι → E)
    (ha : ∀ i, hilbertPlaneProject e h (a i)=planeRFCFWindowAnchor p i)
    (hs : ∀ i, hilbertPlaneProject e h (s i)=planeRFCFWindowStep p r i) (i : ι) :
    inner ℝ (gradient (hilbertPlaneObjective e h m p r t) (a i+s i)-
      gradient (hilbertPlaneObjective e h m p r t) (a i)) (s i)=‖s i‖^2 := by
  rw [hilbertPlaneRFCF_window_secant hι e h m p r t a s ha hs i]
  by_cases hi : i=⊤
  · simp only [ite_eq_left hi,inner_add_left,hilbertPlane_adjoint,hs]
    simp [planeRFCFWindowStep,hi,Ne.symm hι,planeTerminalRho,planeOfPair,
      PiLp.inner_apply,Fin.sum_univ_two]
  · simp only [ite_eq_right hi,add_zero,real_inner_self_eq_norm_sq]

/-- Every actual model-metric split is exactly one-half, derived from
the true scalar gradients and the original reference orthogonality.
Article: main_krylov, thm:Fplanar, full-window lambda^Y dictionary. -/
theorem hilbertPlaneRFCF_window_split (hι : (⊥ : ι)≠⊤)
    (e h m : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (a s : ι → E) (z : E)
    (ha : ∀ i, hilbertPlaneProject e h (a i)=planeRFCFWindowAnchor p i)
    (hs : ∀ i, hilbertPlaneProject e h (s i)=planeRFCFWindowStep p r i)
    (hne : ∀ i, s i≠0) (hfuture : ∀ i, inner ℝ (s i) (z-a i)=‖s i‖^2)
    (hlast : z=a ⊤+s ⊤) (i : ι) :
    covectorSplit (innerSL ℝ (gradient (hilbertPlaneObjective e h m p r t) (a i+s i)-
      gradient (hilbertPlaneObjective e h m p r t) (a i))) (a i) (s i) z=1/2 := by
  have hcurv := hilbertPlaneRFCF_window_curvature hι e h m p r t a s ha hs i
  unfold covectorSplit
  simp only [innerSL_apply_apply]
  rw [hcurv]
  by_cases hi : i=⊤
  · subst i
    rw [hlast]
    have he : a ⊤+s ⊤-(a ⊤+(1/2:ℝ) • s ⊤)=(1/2:ℝ) • s ⊤ := by module
    rw [he,inner_smul_right,hcurv]
    field_simp [norm_ne_zero_iff.mpr (hne ⊤)]
  · rw [hilbertPlaneRFCF_window_secant hι e h m p r t a s ha hs i,ite_eq_right hi,add_zero]
    have he : z-(a i+(1/2:ℝ) • s i)=(z-a i)-(1/2:ℝ) • s i := by module
    rw [he,inner_sub_right,inner_smul_right,hfuture,real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr (hne i)]
    norm_num

end
end krylov.Functions
