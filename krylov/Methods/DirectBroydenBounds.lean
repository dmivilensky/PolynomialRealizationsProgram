import krylov.Methods.DirectBroydenModel
import krylov.Stability.CompactParameterBound
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), native uniform direct-model domains.
Use: derive bounded actual chronological models and inverse old curvatures
from positive reference pairs for every arbitrary original convex schedule.
Source: genuine primitive joint model regularity, proved native positivity
and the compact parameter bound, without a smooth schedule assumption.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
open Set Filter Topology Asymptotics
open scoped InnerProductSpace
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Extend a genuine finite interpolation array by zero beyond its actual
chronological update count.
Use: native model bounds retain all original finite convex schedules.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenFiniteSchedule (theta : Fin p → ℝ) (j : ℕ) : ℝ :=
  if hj : j<p then theta ⟨j,hj⟩ else 0

/-- The actual direct chronological model on a complete finite observed
pair array stored newest first, with its original finite schedule.
Use: compact primitive charts represent exactly the native recursion.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenFiniteModel (B0 : E →L[ℝ] E) (theta : Fin p → ℝ)
    (D : Fin p → E × E) : E →L[ℝ] E :=
  directBroydenOperatorModel B0 (directBroydenFiniteSchedule theta) (List.ofFn D)

/-- The genuine finite direct model is jointly C-r in every actual pair
and interpolation coordinate at its true recursive curvature domains.
Use: derive uniform native bounds even for interpolation schedules with
no limiting value and no perturbation regularity.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: primitive coordinate projections are smooth. The actual list map
is exactly the original finite array; apply the proved native recursion
calculus with its genuine chronological interpolation indices. -/
theorem directBroydenFiniteModel_contDiffAt {r : WithTop ℕ∞} (B0 : E →L[ℝ] E)
    (z : (Fin p → ℝ) × (Fin p → E × E))
    (hpiv : DirectBroydenPivots B0 (directBroydenFiniteSchedule z.1) (List.ofFn z.2)) :
    ContDiffAt ℝ r (fun w => directBroydenFiniteModel B0 w.1 w.2) z := by
  let W := List.ofFn (fun i : Fin p => fun w : (Fin p → ℝ) × (Fin p → E × E) => w.2 i)
  have hpairs : ∀ f∈W,ContDiffAt ℝ r (fun w => (f w).1) z ∧ ContDiffAt ℝ r (fun w => (f w).2) z := by
    intro f hf
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    have h : ContDiffAt ℝ r (fun w : (Fin p → ℝ) × (Fin p → E × E) => w.2 i) z :=
      (contDiff_apply ℝ (E × E) i).contDiffAt.comp z contDiffAt_snd
    exact ⟨h.fst,h.snd⟩
  have htheta : ∀ j<W.length,ContDiffAt ℝ r
      (fun w : (Fin p → ℝ) × (Fin p → E × E) => directBroydenFiniteSchedule w.1 j) z := by
    intro j hj
    have hjp : j<p := by simpa only [W,List.length_ofFn] using hj
    simpa only [directBroydenFiniteSchedule,dite_eq_left hjp,Function.comp_def] using
      (contDiff_apply ℝ ℝ (⟨j,hjp⟩ : Fin p)).contDiffAt.comp z contDiffAt_fst
  have h := directBroydenOperatorModel_contDiffAt (fun _ => B0)
    (fun w => directBroydenFiniteSchedule w.1) W z contDiffAt_const hpairs htheta
    (by simpa only [W,List.map_ofFn,Function.comp_def] using hpiv)
  simpa only [W,List.map_ofFn,Function.comp_def,directBroydenFiniteModel] using h

/-- Actual finite direct Broyden models and their actual next old-model
inverse curvatures stay bounded along convergent positive reference data
for all original convex schedules, with no continuity of those schedules.
Use: supplies the genuine native bounds needed in the original quadratic
model-comparison induction; bounded model or pivot fields are not assumed.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: native positivity gives every real reference pivot throughout the
compact parameter cube. Primitive joint regularity gives continuity of
the actual model and actual reciprocal curvature there. Compactness and
the genuine data limit give a common bound along arbitrary cube choices. -/
theorem directBroydenFiniteModel_uniform_bounds (B0 : E →L[ℝ] E)
    (hB0 : B0.toLinearMap.IsSymmetric) (hpos : ∀ w : E,w≠0 → 0 < inner ℝ w (B0 w))
    (D0 : Fin p → E × E) (hpair : ∀ i,0 < inner ℝ (D0 i).1 (D0 i).2)
    (s0 : E) (hs0 : s0≠0) (l : Filter α) (theta : α → Fin p → ℝ)
    (D : α → Fin p → E × E) (s : α → E)
    (htheta : ∀ᶠ z in l,∀ i,0≤theta z i ∧ theta z i≤1)
    (hD : Tendsto D l (𝓝 D0)) (hs : Tendsto s l (𝓝 s0)) :
    (fun z => directBroydenFiniteModel B0 (theta z) (D z)) =O[l] (fun _ => (1 : ℝ)) ∧
    (fun z => (inner ℝ (s z) (directBroydenFiniteModel B0 (theta z) (D z) (s z)))⁻¹)
      =O[l] (fun _ => (1 : ℝ)) := by
  let K : Set (Fin p → ℝ) := Icc 0 1
  let F : (Fin p → ℝ) × ((Fin p → E × E) × E) → (E →L[ℝ] E) × ℝ := fun z =>
    let B := directBroydenFiniteModel B0 z.1 z.2.1
    (B,(inner ℝ z.2.2 (B z.2.2))⁻¹)
  have hF (a : Fin p → ℝ) (ha : a∈K) : ContinuousAt F (a,(D0,s0)) := by
    have hn : ∀ j,0≤directBroydenFiniteSchedule a j := by
      intro j
      unfold directBroydenFiniteSchedule
      split_ifs with hj
      · exact ha.1 ⟨j,hj⟩
      · exact le_refl 0
    have hpairs : ∀ q∈List.ofFn D0,0 < inner ℝ q.1 q.2 := List.forall_mem_ofFn_iff.mpr hpair
    have hpiv := directBroydenOperatorModel_pivots B0 hB0 hpos _ hn _ hpairs
    have hB : ContDiffAt ℝ 1 (fun z : (Fin p → ℝ) × ((Fin p → E × E) × E) =>
        directBroydenFiniteModel B0 z.1 z.2.1) (a,(D0,s0)) :=
      (directBroydenFiniteModel_contDiffAt B0 (a,D0) hpiv).comp (a,(D0,s0))
        (contDiffAt_fst.prodMk contDiffAt_snd.fst)
    have hstep : ContDiffAt ℝ 1 (fun z : (Fin p → ℝ) × ((Fin p → E × E) × E) => z.2.2)
        (a,(D0,s0)) := contDiffAt_snd.snd
    have ha0 := (directBroydenOperatorModel_positive B0 hB0 hpos _ hn _ hpairs).2 s0 hs0
    exact (hB.prodMk ((hstep.inner ℝ (hB.clm_apply hstep)).inv ha0.ne')).continuousAt
  have h := compact_parameter_bigO F K isCompact_Icc (D0,s0) hF l theta
    (fun z => (D z,s z)) (htheta.mono (fun z hz => ⟨fun i => (hz i).1,fun i => (hz i).2⟩))
    (hD.prodMk_nhds hs)
  exact ⟨((ContinuousLinearMap.fst ℝ (E →L[ℝ] E) ℝ).isBigO_comp _ l).trans h,
    ((ContinuousLinearMap.snd ℝ (E →L[ℝ] E) ℝ).isBigO_comp _ l).trans h⟩

end
end krylov.Methods
