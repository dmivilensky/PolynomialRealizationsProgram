import krylov.OneGradient.NativeVirtualData
import krylov.OneGradient.InformedCurvatureJet
import krylov.OneGradient.NativeTrialError
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual informed last-curvature expansion.
Use: derive the genuine implemented informed S error jet from primitive
physical operators, retaining its actual unknown measured curvature.
Source: real full-history virtual solve dictionary, positive reference
branch and actual vanishing-middle curvature remainder.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The literal history-only informed raw length is the quotient of
the genuine native S virtual fields, on arbitrary physical operators.
Use: the actual error identity never substitutes an unobserved direction.
Article: main_krylov, thm:local(a), exact informed implementation dictionary.
Proof: full memory retains the actual recorded pairs. Reuse their exact
finite virtual-gradient and conjugacy-direction coordinate dictionaries. -/
theorem informed_native_step_raw_length
    (known : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    let trial := informedTrial known
    let H := oneGradientRun (xrfcMethod fullMemory trial) A g k
    let gv := xrfcNativeVirtualGradient false trial A g k
    let d := xrfcNativeDirection false trial A g k
    informedTrialLength known H=lineLength gv d (known d) := by
  let trial := informedTrial known
  let m := xrfcMethod fullMemory trial
  let H := oneGradientRun m A g k
  have hv := (oneGradient_full_virtual_coordinates m A g k).2
  rw [selectedWindow_full] at hv
  have hd := oneGradient_full_direction_coordinates m A g
    (virtualGradient H.pairs H.gradient) k
  rw [selectedWindow_full,hv] at hd
  change lineLength (virtualGradient H.pairs H.gradient)
    (windowDirection H.pairs (virtualGradient H.pairs H.gradient))
    (known (windowDirection H.pairs (virtualGradient H.pairs H.gradient)))=_
  rw [hv,hd]
  rfl

/-- The genuine implemented informed S trial error has its frozen actual
curvature coefficient with a quadratic remainder, from primitive C-one
operators alone. All actual direction regularity and positivity domains
come from the real observed implementation and active CG geometry.
Use: the unknown-base and segment drift term is derived for the actual
native trial, rather than for a prescribed smooth quotient field.
Article: main_krylov, thm:local(a), actual informed curvature error jet.
Proof: genuine native virtual data give C-one fields and their true CG
values. Their actual known-curvature quotient is positive at reference,
so the real totalized policy equals this quotient on a neighborhood.
The true descent pairing remains nonzero. The exact informed line-error
identity identifies the actual error with its real curvature difference;
the existing vanishing-middle remainder freezes only its direction. -/
theorem informed_native_step_curvature_remainder
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (k : ℕ) (hk : k<N) :
    let Q := cgOperator base
    let d0 := CG.direction Q g k
    (fun z => xrfcNativeTrialError false (informedTrial Q) (A z) g k+
      inner ℝ d0 ((A z k-Q) d0)/inner ℝ d0 (Q d0)) =O[𝓝 0] (fun z => ‖z‖^2) := by
  let Q := cgOperator base
  let trial := informedTrial Q
  let m := xrfcMethod fullMemory trial
  let H := fun z => oneGradientRun m (A z) g k
  let gv := fun z => xrfcNativeVirtualGradient false trial (A z) g k
  let d := fun z => xrfcNativeDirection false trial (A z) g k
  let raw := fun z => lineLength (gv z) (d z) (Q (d z))
  have hp := cgOperator_positive base hb
  have hdata := informed_native_virtual_data false base hb g N hpre A hA hA0 k hk.le
  have hgv : ContDiffAt ℝ 1 gv 0 := hdata.1
  have hd : ContDiffAt ℝ 1 d 0 := hdata.2.1
  have hgv0 : gv 0=CG.gradient Q g k := hdata.2.2.1
  have hd0 : d 0=CG.direction Q g k := hdata.2.2.2
  have hinv := CG.invariant Q hp.1 hp.2 g k (fun i hi => hpre i (hi.trans hk))
  have hdir := (CG.invariant_line_pos Q hp.2 g k hinv (hpre k hk)).1
  have hcurv : inner ℝ (d 0) (Q (d 0))≠0 := by rw [hd0];exact (hp.2 _ hdir).ne'
  have hdesc : inner ℝ (d 0) (gv 0)≠0 := by
    rw [hd0,hgv0,hinv.search_pair]
    exact neg_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hpre k hk)))
  have hraw : ContDiffAt ℝ 1 raw 0 :=
    ((hd.inner ℝ hgv).neg).div (hd.inner ℝ (Q.contDiff.contDiffAt.comp 0 hd)) hcurv
  have hraw0 : 0<raw 0 := by
    rw [show raw 0=CG.length Q g k from by dsimp only [raw];rw [hd0,hgv0]]
    exact (CG.invariant_line_pos Q hp.2 g k hinv (hpre k hk)).2.1
  have heq : (fun z => xrfcNativeTrialError false trial (A z) g k)=ᶠ[𝓝 0]
      (fun z => informedCurvatureError Q (A z k) (d z)) := by
    filter_upwards [hraw.continuousAt.eventually (lt_mem_nhds hraw0),
      (hd.inner ℝ hgv).continuousAt.eventually_ne hdesc,
      (hd.inner ℝ (Q.contDiff.contDiffAt.comp 0 hd)).continuousAt.eventually_ne hcurv]
        with z hz hdz hqz
    have hrl : informedTrialLength Q (H z)=raw z := informed_native_step_raw_length Q (A z) g k
    have ht : trial (H z)=raw z := by
      change (if 0 < informedTrialLength Q (H z) then informedTrialLength Q (H z) else 1)=_
      rw [hrl,ite_eq_left hz]
    change lastLaunchTrialError (trial (H z)) (d z) (gv z) (A z k)=_
    rw [lastLaunchTrialError_eq_relative,ht]
    exact informed_length_error Q (A z k) (gv z) (d z) hdz hqz
  have hj := informed_curvature_c1_remainder Q (fun z => A z k) d (hA k) hd
    (congrFun hA0 k) hcurv
  apply hj.congr' ?_ EventuallyEq.rfl
  filter_upwards [heq] with z hz
  rw [hz,hd0]

end
end krylov.OneGradient
