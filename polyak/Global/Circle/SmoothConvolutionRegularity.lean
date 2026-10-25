import polyak.Global.Circle.SmoothConvolutionBasic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! A smooth periodic kernel smooths every finite circle measure to C∞. -/
noncomputable section
namespace polyak.Global.Circle
open MeasureTheory Set Function Filter
open scoped Topology ContDiff

def realPullback (K:Circle→ℝ) (x:ℝ) : ℝ := K (ofReal x)

theorem realPullback_periodic (K:Circle→ℝ) : Periodic (realPullback K) (2*Real.pi) := by
  intro x
  change K ((x+2*Real.pi:ℝ):Circle)=K (x:Circle)
  rw [AddCircle.coe_add_period]

theorem periodic_derivative {f:ℝ→ℝ} {T:ℝ} (hp:Periodic f T) : Periodic (deriv f) T := by
  have he : (fun x=>f (x+T))=f := funext hp
  intro x
  rw [←deriv_comp_add_const,he]

theorem periodic_iteratedDeriv {f:ℝ→ℝ} {T:ℝ} (hp:Periodic f T) (j:ℕ) :
    Periodic (iteratedDeriv j f) T := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hp
  | succ j hj => rw [iteratedDeriv_succ];exact periodic_derivative hj

def circleDerivative (K:Circle→ℝ) (j:ℕ) : Circle→ℝ :=
  (periodic_iteratedDeriv (realPullback_periodic K) j).lift

@[simp] theorem circleDerivative_ofReal (K:Circle→ℝ) (j:ℕ) (x:ℝ) :
    circleDerivative K j (ofReal x)=iteratedDeriv j (realPullback K) x :=
  (periodic_iteratedDeriv (realPullback_periodic K) j).lift_coe x

@[simp] theorem circleDerivative_zero (K:Circle→ℝ) : circleDerivative K 0=K := by
  funext x
  induction x using Quotient.inductionOn' with | h v =>
    change circleDerivative K 0 (ofReal v)=K (ofReal v)
    rw [circleDerivative_ofReal,iteratedDeriv_zero]
    rfl

theorem continuous_circleDerivative {K:Circle→ℝ}
    (hK:ContDiff ℝ ∞ (realPullback K)) (j:ℕ) : Continuous (circleDerivative K j) :=
  (hK.continuous_iteratedDeriv j (by simp)).quotient_lift _

def derivativeBound (K:Circle→ℝ) (hK:ContDiff ℝ ∞ (realPullback K)) (j:ℕ) : ℝ :=
  ‖(⟨circleDerivative K j,continuous_circleDerivative hK j⟩:C(Circle,ℝ))‖

theorem circleDerivative_bound {K:Circle→ℝ}
    (hK:ContDiff ℝ ∞ (realPullback K)) (j:ℕ) (x:Circle) :
    ‖circleDerivative K j x‖≤derivativeBound K hK j :=
  (⟨circleDerivative K j,continuous_circleDerivative hK j⟩:C(Circle,ℝ)).norm_coe_le_norm x

def convolutionDerivative (K:Circle→ℝ) (j:ℕ) (μ:Measure Circle) (x:ℝ) : ℝ :=
  ∫v,circleDerivative K j (ofReal x-v)∂μ

@[simp] theorem convolutionDerivative_zero (K:Circle→ℝ) (μ:Measure Circle) :
    convolutionDerivative K 0 μ=realPullback (convolutionDensity K μ) := by
  funext x
  simp only [convolutionDerivative,circleDerivative_zero,realPullback,convolutionDensity]

theorem hasDerivAt_convolutionDerivative {K:Circle→ℝ}
    (hK:ContDiff ℝ ∞ (realPullback K)) (j:ℕ)
    (μ:Measure Circle) [IsFiniteMeasure μ] (x:ℝ) :
    HasDerivAt (convolutionDerivative K j μ) (convolutionDerivative K (j+1) μ x) x := by
  let F : ℝ→Circle→ℝ := fun x v=>circleDerivative K j (ofReal x-v)
  let F' : ℝ→Circle→ℝ := fun x v=>circleDerivative K (j+1) (ofReal x-v)
  have hFcont (x:ℝ) : Continuous (F x) := by
    change Continuous (fun v:Circle=>circleDerivative K j (ofReal x-v))
    exact (continuous_circleDerivative hK j).comp
      ((continuous_const : Continuous (fun _:Circle=>ofReal x)).sub continuous_id)
  have hF'cont (x:ℝ) : Continuous (F' x) := by
    change Continuous (fun v:Circle=>circleDerivative K (j+1) (ofReal x-v))
    exact (continuous_circleDerivative hK (j+1)).comp
      ((continuous_const : Continuous (fun _:Circle=>ofReal x)).sub continuous_id)
  have hbound : ∀ᵐv∂μ,∀x∈(univ:Set ℝ),‖F' x v‖≤derivativeBound K hK (j+1) :=
    ae_of_all _ fun v x _=>circleDerivative_bound hK (j+1) _
  have hdiff : ∀ᵐv∂μ,∀x∈(univ:Set ℝ),HasDerivAt (F · v) (F' x v) x := by
    apply ae_of_all
    intro v
    induction v using Quotient.inductionOn' with | h y =>
      intro x _
      have hh := ((hK.differentiable_iteratedDeriv j (by exact ENat.natCast_lt_of_coe_top_le_withTop (N:=∞) le_rfl j)) (x-y)).hasDerivAt
      rw [←iteratedDeriv_succ] at hh
      have hd := hh.comp_sub_const x y
      change HasDerivAt
        (fun x=>circleDerivative K j (ofReal x-ofReal y))
        (circleDerivative K (j+1) (ofReal x-ofReal y)) x
      simp_rw [←map_sub ofReal,circleDerivative_ofReal]
      exact hd
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ)
    (F:=F) (F':=F') (bound:=fun _=>derivativeBound K hK (j+1))
    (by simp) (Eventually.of_forall fun y=>(hFcont y).aestronglyMeasurable)
    ((hFcont x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hF'cont x).aestronglyMeasurable hbound (integrable_const _) hdiff).2

theorem iteratedDeriv_convolutionDensity {K:Circle→ℝ}
    (hK:ContDiff ℝ ∞ (realPullback K)) (μ:Measure Circle) [IsFiniteMeasure μ] (j:ℕ) :
    iteratedDeriv j (realPullback (convolutionDensity K μ))=convolutionDerivative K j μ := by
  induction j with
  | zero => rw [iteratedDeriv_zero,convolutionDerivative_zero]
  | succ j hj =>
    rw [iteratedDeriv_succ,hj]
    funext x
    exact (hasDerivAt_convolutionDerivative hK j μ x).deriv

theorem smooth_convolutionDensity {K:Circle→ℝ}
    (hK:ContDiff ℝ ∞ (realPullback K)) (μ:Measure Circle) [IsFiniteMeasure μ] :
    ContDiff ℝ ∞ (realPullback (convolutionDensity K μ)) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro j _
  rw [iteratedDeriv_convolutionDensity hK]
  intro x
  exact (hasDerivAt_convolutionDerivative hK j μ x).differentiableAt

end polyak.Global.Circle
