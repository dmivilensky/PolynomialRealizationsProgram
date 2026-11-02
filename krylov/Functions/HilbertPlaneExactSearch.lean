import krylov.Functions.HilbertPlaneHessian
import krylov.Functions.PlanarCubicMinima
import krylov.Functions.NativeRFCModel
import krylov.Functions.MetricHilbertPlane

/-!
Article: main_krylov, prop:Fcycle(iii), genuine exact searches of cubic fibres.
Use: derive an actual selected search endpoint from true scalar stationarity
and the actual positive endpoint Hessians. Source: the exact degree-three
Taylor identity, with its true one-third/one-sixth endpoint weights.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor.BinaryCubic
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The actual quadratic norm has its exact second-order gap. Article: prop:Fcycle(iii). -/
theorem hilbert_norm_sq_gap (x y : E) :
    ‖y‖^2-‖x‖^2-2*inner ℝ x (y-x)=‖y-x‖^2 := by
  rw [norm_sub_sq_real,inner_sub_right,real_inner_self_eq_norm_sq,real_inner_comm x y]
  ring

/-- The full-space scalar cubic obeys the exact true endpoint-Hessian
Taylor identity. Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneObjective_endpoint_identity (e h m : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x y : E) :
    hilbertPlaneObjective e h m p r t y-hilbertPlaneObjective e h m p r t x-
      inner ℝ (gradient (hilbertPlaneObjective e h m p r t) x) (y-x)=
      (1/3 : ℝ)*inner ℝ (y-x) (hilbertPlaneHessian e h p r t x (y-x))+
        (1/6 : ℝ)*inner ℝ (y-x) (hilbertPlaneHessian e h p r t y (y-x)) := by
  let C := hilbertPlaneProject e h
  have hp := planeCubicObjective_endpoint_identity p r t (C x) (C y)
  have hq := hilbert_norm_sq_gap x y
  have hc := hilbert_norm_sq_gap (C x) (C y)
  rw [hilbertPlaneGradient_actual]
  simp only [hilbertPlaneObjective,hilbertPlaneGradient,inner_add_left,inner_sub_left,
    hilbertPlane_adjoint,hilbertPlaneHessian_pair,real_inner_self_eq_norm_sq,map_sub,
    inner_sub_right]
  dsimp only [C] at hp hc
  simp only [map_sub,inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq] at hp hq hc
  nlinarith only [hp,hq,hc,real_inner_comm x y,
    real_inner_comm (hilbertPlaneProject e h x) (hilbertPlaneProject e h y)]

/-- A genuinely stationary point on the actual chord is its unique scalar
minimum whenever the true endpoint Hessians are uniformly positive on the
whole chord domain. No search identity is an assumption.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneObjective_unique_chord (e h m : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (R q : ℝ) (hq : 0<q)
    (hH : ∀ z : E, ‖z‖≤R → ∀ v : E, q*‖v‖^2 ≤ inner ℝ v (hilbertPlaneHessian e h p r t z v))
    (x d y : E) (hy : ‖y‖≤R) (hline : ∃ α : ℝ, y=x+α • d)
    (hstationary : inner ℝ (gradient (hilbertPlaneObjective e h m p r t) y) d=0) :
    IsChordMinimum (hilbertPlaneObjective e h m p r t) x d R y ∧
      ∀ z : E, IsChordMinimum (hilbertPlaneObjective e h m p r t) x d R z → z=y := by
  have hgap (z : E) (hz : ‖z‖≤R) :
      q/2*‖z-y‖^2≤hilbertPlaneObjective e h m p r t z-hilbertPlaneObjective e h m p r t y-
        inner ℝ (gradient (hilbertPlaneObjective e h m p r t) y) (z-y) := by
    have hh := hilbertPlaneObjective_endpoint_identity e h m p r t y z
    have hyH := hH y hy (z-y)
    have hzH := hH z hz (z-y)
    linarith only [hh,hyH,hzH]
  have hzero (z : E) (hz : ∃ α : ℝ, z=x+α • d) :
      inner ℝ (gradient (hilbertPlaneObjective e h m p r t) y) (z-y)=0 := by
    obtain ⟨α,hα⟩ := hz
    obtain ⟨β,hβ⟩ := hline
    have he : z-y=(α-β) • d := by rw [hα,hβ]; module
    rw [he,inner_smul_right,hstationary,mul_zero]
  have hmin : IsChordMinimum (hilbertPlaneObjective e h m p r t) x d R y := by
    refine ⟨by simpa only [mem_closedBall,dist_zero_right] using hy,hline,?_⟩
    intro α hα
    have hz : ‖x+α • d‖≤R := by simpa only [chordParameters,mem_ofPred_eq,mem_closedBall,dist_zero_right] using hα
    have hh := hgap _ hz
    rw [hzero _ ⟨α,rfl⟩,sub_zero] at hh
    exact sub_nonneg.mp ((by positivity : 0≤q/2*‖x+α • d-y‖^2).trans hh)
  refine ⟨hmin,?_⟩
  intro z hz
  have hzball : ‖z‖≤R := by simpa only [mem_closedBall,dist_zero_right] using hz.1
  have hh := hgap z hzball
  rw [hzero z hz.2.1,sub_zero] at hh
  obtain ⟨β,hβ⟩ := hline
  have hvalue : hilbertPlaneObjective e h m p r t z≤hilbertPlaneObjective e h m p r t y :=
    hβ ▸ hz.2.2 β (by simpa only [chordParameters,mem_ofPred_eq,←hβ,mem_closedBall,dist_zero_right] using hy)
  have hnorm : ‖z-y‖^2=0 := by nlinarith only [hh,hvalue,hq,sq_nonneg ‖z-y‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))

/-- The real selected local exact search equals the derived stationary
endpoint, using only actual Hessian positivity. Article: prop:Fcycle(iii). -/
theorem hilbertPlaneObjective_localExactPoint (e h m : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (R q : ℝ) (hq : 0<q)
    (hH : ∀ z : E, ‖z‖≤R → ∀ v : E, q*‖v‖^2 ≤ inner ℝ v (hilbertPlaneHessian e h p r t z v))
    (x d y : E) (hy : ‖y‖≤R) (hline : ∃ α : ℝ, y=x+α • d)
    (hstationary : inner ℝ (gradient (hilbertPlaneObjective e h m p r t) y) d=0) :
    localExactPoint (hilbertPlaneObjective e h m p r t) x d R=y := by
  have hu := hilbertPlaneObjective_unique_chord e h m p r t R q hq hH x d y hy hline hstationary
  have hex : ∃! z : E, IsChordMinimum (hilbertPlaneObjective e h m p r t) x d R z := ⟨y,hu.1,hu.2⟩
  exact hu.2 _ (localExactPoint_spec _ x d R hex)

/-- A true physical exact-search endpoint follows from its actual canonical
stationarity and the derived positive cubic domain. Article: prop:Fcycle(iii). -/
theorem metricHilbertPlaneObjective_localExactPoint (S : E ≃L[ℝ] E) (e h m : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (R q : ℝ) (hq : 0<q)
    (hH : ∀ z : E, ‖z‖≤R → ∀ v : E, q*‖v‖^2 ≤ inner ℝ v (hilbertPlaneHessian e h p r t z v))
    (x d y : E) (hy : ‖S y‖≤R) (hline : ∃ α : ℝ, y=x+α • d)
    (hstationary : inner ℝ (gradient (hilbertPlaneObjective e h m p r t) (S y)) (S d)=0) :
    metricLocalExactPoint S (metricHilbertPlaneObjective S e h m p r t) x d R=y := by
  have hf : coordinateObjective S (metricHilbertPlaneObjective S e h m p r t)=
      hilbertPlaneObjective e h m p r t := by
    funext z
    simp only [coordinateObjective,metricHilbertPlaneObjective,ContinuousLinearEquiv.symm_symm,S.apply_symm_apply]
  rw [metricLocalExactPoint,hf]
  have hl : ∃ α : ℝ, S y=S x+α • S d := by
    obtain ⟨α,hα⟩ := hline
    exact ⟨α,by rw [hα,map_add,map_smul]⟩
  rw [hilbertPlaneObjective_localExactPoint e h m p r t R q hq hH (S x) (S d) (S y) hy hl hstationary]
  exact S.symm_apply_apply y

end
end krylov.Functions
