import krylov.Functions.HilbertPlaneHessian
import krylov.Functions.PlanarSourceShrink
import krylov.Functions.ReferenceFibreNormalization

/-!
Article: main_krylov, prop:Fcycle(iii), full-space self-concordant realization.
Use: adjoin a genuine positive quadratic on the orthogonal complement of the
actual first/last CG plane. Self-concordance and minimization are transported
from real planar scalar functions, keeping their actual differential fields.
Source: exact adjoint/projection identities and orthogonal Hessian energy.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Filter Topology krylov.Tensor.BinaryCubic krylov.Nonlinear krylov.Reference krylov.Secant
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Adding the orthogonal quadratic preserves actual Hessian symmetry.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneHessian_symmetric (e h : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : E) :
    (hilbertPlaneHessian e h p r t x).IsSymmetric := by
  intro v w
  change inner ℝ (hilbertPlaneHessian e h p r t x v) w=inner ℝ v (hilbertPlaneHessian e h p r t x w)
  rw [real_inner_comm w (hilbertPlaneHessian e h p r t x v),hilbertPlaneHessian_pair,hilbertPlaneHessian_pair]
  have hs := planeCubicHessian_symmetric p r t (hilbertPlaneProject e h x)
    (hilbertPlaneProject e h v) (hilbertPlaneProject e h w)
  have hp : inner ℝ (hilbertPlaneProject e h w) (planeCubicHessian p r t (hilbertPlaneProject e h x) (hilbertPlaneProject e h v))=
      inner ℝ (hilbertPlaneProject e h v) (planeCubicHessian p r t (hilbertPlaneProject e h x) (hilbertPlaneProject e h w)) := by
    exact (real_inner_comm _ _).trans hs
  rw [hp,real_inner_comm v w,real_inner_comm (hilbertPlaneProject e h v) (hilbertPlaneProject e h w)]

omit [CompleteSpace E] in
/-- The added quadratic is exactly the squared actual orthogonal error.
Article: main_krylov, prop:Fcycle(iii), true minimizer transport. -/
theorem hilbertPlaneObjective_orthogonal_square (e h m : E)
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (hm : hilbertPlaneProject e h m=0) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : E) :
    hilbertPlaneObjective e h m p r t x=
      planeCubicObjective p r t (hilbertPlaneProject e h x)+
        ‖x-hilbertPlaneEmbed e h (hilbertPlaneProject e h x)-m‖^2/2 := by
  have him : inner ℝ (x-hilbertPlaneEmbed e h (hilbertPlaneProject e h x)) m=inner ℝ m x := by
    rw [inner_sub_left,real_inner_comm x m,hilbertPlane_adjoint,hm,inner_zero_right,sub_zero]
  rw [norm_sub_sq_real,hilbertPlane_residual_norm_sq e h he hh heh,him]
  dsimp only [hilbertPlaneObjective]
  ring

/-- The true full critical point is the planar critical point plus the
actual orthogonal quadratic centre. Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneGradient_critical (e h m : E)
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (hm : hilbertPlaneProject e h m=0) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (z : Plane) (hz : gradient (planeCubicObjective p r t) z=0) :
    gradient (hilbertPlaneObjective e h m p r t) (hilbertPlaneEmbed e h z+m)=0 := by
  rw [hilbertPlaneGradient_actual,hilbertPlaneGradient,map_add,
    hilbertPlaneProject_embed e h he hh heh,hm,add_zero,hz,map_zero,zero_add]
  abel

omit [CompleteSpace E] in
/-- Every genuine planar minimum lifts to an actual full-space minimum
on any domain projecting into the planar certified domain.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneObjective_isMinOn (e h m : E)
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (hm : hilbertPlaneProject e h m=0) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (U : Set Plane) (z : Plane) (hz : IsMinOn (planeCubicObjective p r t) U z)
    (V : Set E) (hV : ∀ x∈V,hilbertPlaneProject e h x∈U) :
    IsMinOn (hilbertPlaneObjective e h m p r t) V (hilbertPlaneEmbed e h z+m) := by
  intro x hx
  change hilbertPlaneObjective e h m p r t (hilbertPlaneEmbed e h z+m)≤hilbertPlaneObjective e h m p r t x
  rw [hilbertPlaneObjective_orthogonal_square e h m he hh heh hm,
    hilbertPlaneObjective_orthogonal_square e h m he hh heh hm]
  have hz0 : hilbertPlaneEmbed e h z+m-hilbertPlaneEmbed e h z-m=0 := by abel
  simp only [map_add,hilbertPlaneProject_embed e h he hh heh,hm,add_zero,hz0,
    norm_zero,zero_pow (by decide : 2≠0),zero_div,add_zero]
  exact (hz (hV x hx)).trans (le_add_of_nonneg_right (by positivity))

set_option maxHeartbeats 800000 in
/-- A genuine planar self-concordant scalar function remains standard
self-concordant after adjoining its true orthogonal quadratic. The domain
may be any open convex subset of the actual planar preimage.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneObjective_selfConcordant (e h m : E)
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (U : Set Plane)
    (hsc : IsStandardSelfConcordantOn (planeCubicObjective p r t) U)
    (V : Set E) (hVo : IsOpen V) (hVc : Convex ℝ V)
    (hVU : ∀ x∈V,hilbertPlaneProject e h x∈U) :
    IsStandardSelfConcordantOn (hilbertPlaneObjective e h m p r t) V := by
  obtain ⟨D⟩ := hsc
  have hH z (hz : z∈U) : D.hessian z=planeCubicHessian p r t z :=
    (D.gradient_derivative z hz).unique (planeCubicGradient_hasFDerivAt p r t z)
  have hD z (hz : z∈U) : D.variation z=canonicalVariation t.tensor := by
    have hev : D.hessian =ᶠ[𝓝 z] planeCubicHessian p r t :=
      Filter.eventually_of_mem (D.open_domain.mem_nhds hz) (fun w hw=>hH w hw)
    exact ((D.hessian_derivative z hz).congr_of_eventuallyEq hev.symm).unique
      (planeCubicHessian_hasFDerivAt p r t z)
  have hn z (hz : z∈U) v : 0≤ inner ℝ v (planeCubicHessian p r t z v) := by
    rw [←hH z hz]
    exact D.hessian_nonnegative z hz v
  have hfull x (hx : x∈V) v :
      inner ℝ (hilbertPlaneProject e h v) (planeCubicHessian p r t (hilbertPlaneProject e h x) (hilbertPlaneProject e h v))≤
        inner ℝ v (hilbertPlaneHessian e h p r t x v) := by
    rw [hilbertPlaneHessian_energy e h he hh heh]
    exact le_add_of_nonneg_right (sq_nonneg _)
  refine ⟨{
    open_domain := hVo
    convex_domain := hVc
    differentiable := fun x _=>(hilbertPlaneObjective_hasFDerivAt e h m p r t x).differentiableAt.differentiableWithinAt
    hessian := hilbertPlaneHessian e h p r t
    variation := fun _=>hilbertPlaneVariation e h t
    gradient_derivative := fun x _=>hilbertPlaneGradient_hasFDerivAt e h m p r t x
    hessian_derivative := fun x _=>hilbertPlaneHessian_hasFDerivAt e h p r t x
    variation_continuous := continuous_const.continuousOn
    hessian_symmetric := fun x _=>hilbertPlaneHessian_symmetric e h p r t x
    hessian_nonnegative := ?_
    mixed := ?_ }⟩
  · intro x hx v
    exact (hn _ (hVU x hx) _).trans (hfull x hx v)
  · intro x hx u v w
    rw [hilbertPlaneVariation_pair]
    have hb := D.mixed _ (hVU x hx) (hilbertPlaneProject e h u) (hilbertPlaneProject e h v) (hilbertPlaneProject e h w)
    rw [hH _ (hVU x hx),hD _ (hVU x hx),canonicalVariation_pair] at hb
    apply hb.trans
    gcongr
    · exact hfull x hx u
    · exact hfull x hx v
    · exact hfull x hx w

end
end krylov.Functions
