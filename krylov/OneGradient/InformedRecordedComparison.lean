import krylov.Methods.DirectionRecordedFields
import krylov.OneGradient.InformedStepChange
import krylov.OneGradient.NativeVirtualData
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual informed D policy fields.
Use: compare the real recorded-pair fields used by the informed history
rule with the actual native D fields on that same physical execution.
Source: genuine observed-change identities, actual latest congruence order,
and native prefix regularity with all true inverse domains derived.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- On the actual informed D execution, the original recorded-pair
virtual gradient and direction differ quadratically from the real native
D fields. The primitive operators are the only regularity input.
Use: justify the real history-only informed trial's native D curvature jet;
the two off-quadratic virtual pairs are never assumed equal.
Article: main_krylov, thm:local(a), genuine informed policy comparison.
Proof: actual recorded steps and images have their exact common native
change. It is C-one with a nonsingular diagonal reference; true quadratic
images give symmetric reference pairings. The genuine latest-model
comparison gives the virtual-gradient order. Exact conjugacy invariance
and the actual nonsingular native solve preserve that same order. -/
theorem informed_native_recorded_fields_quadratic
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (k : ℕ) (hk : k≤N) :
    let trial := informedTrial (cgOperator base)
    let H := fun z => oneGradientRun (xrfcDMethod fullMemory trial) (A z) g k
    let gv := fun z => virtualGradient (H z).pairs (H z).gradient
    let d := fun z => windowDirection (H z).pairs (gv z)
    ((fun z => gv z-xrfcNativeVirtualGradient true trial (A z) g k) =O[𝓝 0] (fun z => ‖z‖^2)) ∧
      ((fun z => d z-xrfcNativeDirection true trial (A z) g k) =O[𝓝 0] (fun z => ‖z‖^2)) := by
  dsimp only
  let Q := cgOperator base
  let trial := informedTrial Q
  let m := xrfcDMethod fullMemory trial
  let H := fun z => oneGradientRun m (A z) g k
  let s := fun z => xrfcNativeColumns true trial (A z) g k
  let y := fun z => xrfcNativeImages true trial (A z) g k
  let G := fun z => oneGradientGradient m (A z) g k
  let T := fun z => xrfcDObservedStepChange trial (A z) g k
  let u := fun z => pairVirtualGradient (rightChange (s z) (T z)) (rightChange (y z) (T z)) (G z)
  let v := fun z => xrfcNativeVirtualGradient true trial (A z) g k
  have hp := cgOperator_positive base hb
  have hreg := informed_native_prefix_contDiff true base hb g N hpre A hA hA0
  have hT := informed_native_step_change_data base hb g N hpre A hA hA0 k hk
  have hdom : (crossGram (y 0) (s 0)).det≠0 ∧ (pairModel (s 0) (y 0)).det≠0 := by
    dsimp only [s,y];rw [hA0]
    exact informed_native_reference_domains true Q hp.1 hp.2 g N hpre k hk
  have himage (i : Fin k) : y 0 i=Q (s 0 i) := by
    dsimp only [s,y];rw [hA0]
    exact informed_native_reference_image true Q hp.1 hp.2 g N hpre k hk i
  have hsym : (crossGram (y 0) (s 0)).IsSymm := by
    ext i j
    change inner ℝ (y 0 j) (s 0 i)=inner ℝ (y 0 i) (s 0 j)
    rw [himage i,himage j]
    exact (hp.1 (s 0 j) (s 0 i)).trans (real_inner_comm _ _)
  have huv : (fun z => u z-v z) =O[𝓝 0] (fun z => ‖z‖^2) :=
    pairVirtualGradient_change_quadratic s y G T
      (fun i => (hreg.2.1 k hk i).1) (fun i => (hreg.2.1 k hk i).2)
      (hreg.1 k hk) hT.1 _ hT.2.1 hT.2.2 hsym (isUnit_iff_ne_zero.mpr hdom.2)
  have heq (z : X) : virtualGradient (H z).pairs (H z).gradient=u z ∧
      windowDirection (H z).pairs (virtualGradient (H z).pairs (H z).gradient)=
        conjugacyDirection (rightChange (s z) (T z)) (rightChange (y z) (T z)) (u z) :=
    xrfcD_recorded_virtual_fields trial (A z) g k (fun _ _ => (informed_trial_positive Q _).ne')
  have hgv : (fun z => virtualGradient (H z).pairs (H z).gradient-v z) =O[𝓝 0] (fun z => ‖z‖^2) := by
    exact huv.congr_left fun z => by rw [(heq z).1]
  refine ⟨hgv,?_⟩
  have hd := conjugacyDirection_difference_order s y u v (s 0) (y 0)
    (contDiffAt_pi.mpr (fun i => (hreg.2.1 k hk i).1)).continuousAt.tendsto
    (contDiffAt_pi.mpr (fun i => (hreg.2.1 k hk i).2)).continuousAt.tendsto
    (isUnit_iff_ne_zero.mpr hdom.1) _ huv
  apply hd.congr' ?_ EventuallyEq.rfl
  have hunit : IsUnit (T 0) := (Matrix.isUnit_iff_isUnit_det _).mpr hT.2.2
  filter_upwards [hT.1.continuousAt.eventually (Units.isOpen.mem_nhds hunit)] with z hz
  rw [(heq z).2,conjugacyDirection_rightChange (s z) (y z) (T z)
    ((Matrix.isUnit_iff_isUnit_det _).mp hz)]
  rfl

end
end krylov.OneGradient
