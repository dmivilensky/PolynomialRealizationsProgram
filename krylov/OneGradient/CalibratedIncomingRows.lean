import krylov.OneGradient.CalibratedNativeImage
import krylov.OneGradient.CalibratedNativeRegularity
import krylov.OneGradient.LastLaunchRows
import krylov.Reference.FullCycle
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine both-native incoming-gradient rows.
Use: derive the original physical first-order last-cycle coefficients for
the actual calibrated S/D gradients, from only primitive C-one operators.
Source: true native program dictionary, actual calibrated CG reference,
primitive native data calculus and the proved observed final-launch rows.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- The original full-cycle calibrated S/D incoming gradients have their
true old-direction drift coordinates and actual last-pivot trial-error
coordinate, with quadratic remainders in the full primitive parameter.
Every source trial, replay, trajectory, inverse-domain and reference
calibration premise is derived for the actual native implementation.
Use: supplies the real incoming coefficients for canonical reconstruction
and the already proved actual S/D cubic output launch formulas.
Article: main_krylov, thm:local(a), genuine native incoming first-order rows.
Proof: the actual native observed arrays and returned-gradient program
are exactly the shared finite virtual launch. True full reference atoms
give the CG last state, zero old projected gradient, true calibrated trial,
nonzero descent pairing and actual model domains. Primitive observations
derive all smoothness; native S images are exact and D replay errors are
quadratic. Apply the proved primitive observed-row theorem and substitute
the actual gradient recursion and genuine CG reference values. -/
theorem calibrated_native_incoming_rows (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (hcal : CalibratedTrial trial (cgOperator base) g (n+1))
    (hT : ∀ (directions : Bool) (k : ℕ),k<n+1 → ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcBasisMethod directions trial) (fun _ => cgOperator base) g k))
    (A : X → ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (hsym : ∀ z j,(A z j).toLinearMap.IsSymmetric) :
    let Q := cgOperator base
    let m := xrfcBasisMethod directions trial
    let s := fun z => xrfcNativeColumns directions trial (A z) g n
    let y := fun z => xrfcNativeImages directions trial (A z) g n
    let G := fun z => oneGradientGradient m (A z) g n
    let w := fun z => modelCoefficients (s z) (pairModel (s z) (y z)) (G z)
    let gv := fun z => G z+combine (y z) (w z)
    let d := fun z => conjugacyDirection (s z) (y z) (gv z)
    let tau := fun z => trial (oneGradientRun m (A z) g n)
    let Gn := fun z => oneGradientGradient m (A z) g (n+1)
    (∀ i : Fin n,(fun z => inner ℝ (s 0 i) (Gn z)-CG.length Q g n*
      inner ℝ (s 0 i) ((A z n-A z (n-1-i.val)) (CG.direction Q g n))) =O[𝓝 0] (fun z => ‖z‖^2)) ∧
      (fun z => inner ℝ (CG.direction Q g n) (Gn z)+
        lastLaunchTrialError (tau z) (d z) (gv z) (A z n)*‖CG.gradient Q g n‖^2)
        =O[𝓝 0] (fun z => ‖z‖^2) := by
  let Q := cgOperator base
  let m := xrfcBasisMethod directions trial
  let s := fun z => xrfcNativeColumns directions trial (A z) g n
  let y := fun z => xrfcNativeImages directions trial (A z) g n
  let G := fun z => oneGradientGradient m (A z) g n
  let tau := fun z => trial (oneGradientRun m (A z) g n)
  let w := fun z => modelCoefficients (s z) (pairModel (s z) (y z)) (G z)
  let gv := fun z => G z+combine (y z) (w z)
  let d := fun z => conjugacyDirection (s z) (y z) (gv z)
  let next := fun z => G z+A z n (combine (s z) (w z)+tau z • d z)
  let Gn := fun z => oneGradientGradient m (A z) g (n+1)
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n+1,CG.gradient Q g i≠0 := fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hreg := calibrated_native_prefix_contDiff directions trial base hb g (n+1) hpre hcal hT A hA hA0
  have hs : ∀ i : Fin n,ContDiffAt ℝ 1 (fun z => s z i) 0 := fun i => (hreg.2.1 n (by omega) i).1
  have hy : ∀ i : Fin n,ContDiffAt ℝ 1 (fun z => y z i) 0 := fun i => (hreg.2.1 n (by omega) i).2
  have hG : ContDiffAt ℝ 1 G 0 := hreg.1 n (by omega)
  have htau : ContDiffAt ℝ 1 tau 0 := hreg.2.2 n (by omega)
  have hGref : G 0=CG.gradient Q g n := by
    dsimp only [G]
    rw [hA0]
    exact calibrated_native_reference_gradient directions trial Q hp.1 hp.2 g (n+1) hpre hcal n (by omega)
  have hy0 (i : Fin n) : y 0 i=A 0 n (s 0 i) := by
    dsimp only [s,y]
    rw [hA0]
    exact calibrated_native_reference_image directions trial Q hp.1 hp.2 g (n+1) hpre hcal n (by omega) i
  have hdom : (crossGram (y 0) (s 0)).det≠0 ∧ (pairModel (s 0) (y 0)).det≠0 := by
    dsimp only [s,y]
    rw [hA0]
    exact calibrated_native_reference_domains directions trial Q hp.1 hp.2 g (n+1) hpre hcal n (by omega)
  have horth : coordinates (s 0) (G 0)=0 := by
    dsimp only [s,G]
    rw [hA0]
    exact calibrated_native_reference_orthogonal directions trial Q hp.1 hp.2 g (n+1) hpre hcal n (by omega)
  have hdir : conjugacyDirection (s 0) (y 0) (G 0)=CG.direction Q g n := by
    rw [hGref]
    dsimp only [s,y]
    rw [hA0]
    exact calibrated_native_reference_direction directions trial Q hp.1 hp.2 g (n+1) hpre hcal n (by omega)
  have htauref : tau 0=CG.length Q g n := by
    dsimp only [tau]
    rw [hA0]
    exact calibrated_native_reference_trial directions trial Q hp.1 hp.2 g (n+1) hpre hcal n (by omega)
  have hterm : CG.gradient Q g n+CG.length Q g n • Q (CG.direction Q g n)=0 := by
    rw [← CG.gradient_succ]
    have he := cg_terminates base hb g
    rw [hc] at he
    exact he
  have hterminal : G 0+tau 0 • A 0 n (conjugacyDirection (s 0) (y 0) (G 0))=0 := by
    rw [hdir,hGref,htauref,show A 0 n=Q from congrFun hA0 n]
    exact hterm
  have hsearch : inner ℝ (CG.direction Q g n) (CG.gradient Q g n)= -‖CG.gradient Q g n‖^2 :=
    (CG.invariant Q hp.1 hp.2 g n (fun i hi => hpre i (by omega))).search_pair
  have hdescent : inner ℝ (conjugacyDirection (s 0) (y 0) (G 0)) (G 0)≠0 := by
    rw [hdir,hGref,hsearch]
    exact neg_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hpre n (by omega))))
  have hrows := lastLaunch_primitive_rows s y G tau (fun z => A z n) (fun z i => A z (n-1-i.val))
    hs hy hG htau (hA n) (fun i => hA _) (fun _ => by rw [hA0]) hy0 (by rw [hA0];exact hp.1) (fun z i => hsym z (n-1-i.val)) hdom.2 hdom.1 horth hterminal hdescent
      (fun i => calibrated_native_image_error directions trial base hb g (n+1) hpre hcal hT A hA hA0 n (by omega) i)
  have hw0 : w 0=0 := modelCoefficients_zero _ _ _ horth
  have hgvref : gv 0=G 0 := by simp only [gv,hw0,combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero,add_zero]
  have hdref : d 0=CG.direction Q g n := by dsimp only [d];rw [hgvref,hdir]
  have hnext (z : X) : next z=Gn z := (xrfc_native_last_launch directions trial (A z) g n).symm
  refine ⟨fun i => (hrows.1 i).congr_left (fun z => ?_),?_⟩
  · change inner ℝ (s 0 i) (next z)-tau 0*inner ℝ (s 0 i) ((A z n-A z (n-1-i.val)) (d 0))=_
    rw [hnext,htauref,hdref]
  · apply hrows.2.congr_left
    intro z
    change inner ℝ (d 0) (next z)-lastLaunchTrialError (tau z) (d z) (gv z) (A z n)*inner ℝ (d 0) (gv 0)=_
    rw [hnext,hdref,hgvref,hGref,hsearch]
    ring

end
end krylov.OneGradient
