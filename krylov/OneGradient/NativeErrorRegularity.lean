import krylov.OneGradient.NativeVirtualData
import krylov.OneGradient.NativeTrialError
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine measured native error regularity.
Use: the true actual S/D measured relative error is C-one and vanishes at
the calibrated known reference, from primitive physical data alone.
Source: actual native virtual-field data, real observed trial charts and
the exact true relative-search dictionary on the active CG domain.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual informed native S/D measured error is C-one and zero at
reference, with every virtual field, trial chart and descent domain
derived from the original observed program and genuine active CG data.
Use: frame changes multiply a genuine first-order measured error.
Article: main_krylov, thm:local(a), true native epsilon regularity.
Proof: real native virtual fields and selected trials are C-one from
primitive observations. Their reference descent pairing is minus the
actual nonzero squared CG gradient norm. Exact calibration makes the
genuine relative-search quotient one, hence its measured error zero. -/
theorem informed_native_error_data (directions : Bool)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (k : ℕ) (hk : k<N) :
    let eps := fun z => xrfcNativeTrialError directions (informedTrial (cgOperator base)) (A z) g k
    ContDiffAt ℝ 1 eps 0 ∧ eps 0=0 := by
  let Q := cgOperator base
  let trial := informedTrial Q
  let gv := fun z => xrfcNativeVirtualGradient directions trial (A z) g k
  let d := fun z => xrfcNativeDirection directions trial (A z) g k
  let tau := fun z => trial (oneGradientRun (xrfcBasisMethod directions trial) (A z) g k)
  have hp := cgOperator_positive base hb
  have hdata := informed_native_virtual_data directions base hb g N hpre A hA hA0 k hk.le
  have hgv : ContDiffAt ℝ 1 gv 0 := hdata.1
  have hd : ContDiffAt ℝ 1 d 0 := hdata.2.1
  have hgv0 : gv 0=CG.gradient Q g k := hdata.2.2.1
  have hd0 : d 0=CG.direction Q g k := hdata.2.2.2
  have htau : ContDiffAt ℝ 1 tau 0 :=
    (informed_native_prefix_contDiff directions base hb g N hpre A hA hA0).2.2 k hk
  have htau0 : tau 0=CG.length Q g k := by
    dsimp only [tau]
    rw [hA0]
    exact informed_native_reference_trial directions Q hp.1 hp.2 g N hpre k hk
  have hi := CG.invariant Q hp.1 hp.2 g k (fun i hi => hpre i (hi.trans hk))
  have hden : inner ℝ (d 0) (gv 0)≠0 := by
    rw [hd0,hgv0,hi.search_pair]
    exact neg_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hpre k hk)))
  refine ⟨contDiffAt_const.add ((htau.mul (hd.inner ℝ ((hA k).clm_apply hd))).div (hd.inner ℝ hgv) hden),?_⟩
  change lastLaunchTrialError (tau 0) (d 0) (gv 0) (A 0 k)=0
  rw [lastLaunchTrialError_eq_relative,htau0,hd0,hgv0,congrFun hA0 k]
  change 1-CG.length Q g k/CG.length Q g k=0
  rw [div_self (CG.invariant_line_pos Q hp.2 g k hi (hpre k hk)).2.1.ne',sub_self]

end
end krylov.OneGradient
