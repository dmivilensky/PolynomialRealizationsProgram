import krylov.OneGradient.InformedIncomingRows
import krylov.OneGradient.CanonicalIncomingRows
import krylov.OneGradient.NativeTrialError
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine canonical incoming S/D coordinates.
Use: the actual informed incoming gradient has precisely the original
canonical old-drift and actual relative last-pivot coefficients.
Source: proved native physical rows, true reference CG column scales,
exact root transport and genuine positive reference normalization.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- The original actual full-cycle informed S/D incoming gradient has
the genuine canonical old-direction drift coordinates and last-direction
trial-error coordinate, each with a quadratic full-parameter remainder.
The last-step norm and actual relative trial error retain their true
native meanings; every varying operator difference is kept actual.
Use: the complete true CG frame reconstructs the source incoming vector
before substitution into the genuine native cubic output formulas.
Article: main_krylov, thm:local(a), actual canonical incoming coefficients.
Proof: derive the real native physical incoming rows from primitive C-one
operators. The actual reference old columns are genuine scaled CG
directions with positive nonzero scales. Exact canonical row transport
normalizes these physical remainders; true CG energy normalizes the final
row and identifies the actual relative-trial-error coefficient. -/
theorem informed_native_canonical_rows (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (A : X → ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (hsym : ∀ z j,(A z j).toLinearMap.IsSymmetric) :
    let trial := informedTrial (cgOperator base)
    let m := xrfcBasisMethod directions trial
    let Gn := fun z => oneGradientGradient m (A z) g (n+1)
    let R := cgOperator (metricRoot base)⁻¹
    let sigma := ‖canonicalCGStep base g n‖
    (∀ i : Fin n,(fun z =>
      inner ℝ (canonicalCGUnitStep base g (n-1-i.val)) (R (Gn z))-
        sigma*inner ℝ (canonicalCGUnitStep base g (n-1-i.val))
          ((R*(A z n-A z (n-1-i.val))*R) (canonicalCGUnitStep base g n)))
        =O[𝓝 0] (fun z => ‖z‖^2)) ∧
      (fun z => inner ℝ (canonicalCGUnitStep base g n) (R (Gn z))+
        sigma*xrfcNativeTrialError directions trial (A z) g n) =O[𝓝 0] (fun z => ‖z‖^2) := by
  let Q := cgOperator base
  let trial := informedTrial Q
  let m := xrfcBasisMethod directions trial
  let s := fun z => xrfcNativeColumns directions trial (A z) g n
  let Gn := fun z => oneGradientGradient m (A z) g (n+1)
  let eps := fun z => xrfcNativeTrialError directions trial (A z) g n
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n+1,CG.gradient Q g i≠0 := fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hk : n<referenceAtomCount base hb g := by rw [hc];omega
  have hrows := informed_native_incoming_rows directions base hb g hc A hA hA0 hsym
  change (∀ i : Fin n,(fun z => inner ℝ (s 0 i) (Gn z)-CG.length Q g n*
      inner ℝ (s 0 i) ((A z n-A z (n-1-i.val)) (CG.direction Q g n))) =O[𝓝 0] (fun z => ‖z‖^2)) ∧
    (fun z => inner ℝ (CG.direction Q g n) (Gn z)+eps z*‖CG.gradient Q g n‖^2) =O[𝓝 0] (fun z => ‖z‖^2) at hrows
  refine ⟨fun i => ?_,canonical_incoming_last_row base hb g n hk Gn eps hrows.2⟩
  let j := n-1-i.val
  let c := if directions then (1 : ℝ) else CG.length Q g j
  have hj : j<referenceAtomCount base hb g := by rw [hc];dsimp only [j];omega
  have hc' : c≠0 := by
    dsimp only [c]
    split_ifs
    · exact one_ne_zero
    · exact (cgLength_pos base hb g j hj).ne'
  have hsref : s 0 i=c • CG.direction Q g j := by
    dsimp only [s]
    rw [hA0]
    exact informed_native_reference_column directions Q hp.1 hp.2 g (n+1) hpre n (by omega) i
  have hphysical : (fun z => inner ℝ (c • CG.direction Q g j) (Gn z)-CG.length Q g n*
      inner ℝ (c • CG.direction Q g j) ((A z n-A z j) (CG.direction Q g n))) =O[𝓝 0] (fun z => ‖z‖^2) := by
    apply (hrows.1 i).congr_left
    intro z
    rw [hsref]
  exact canonical_incoming_old_row base hb g j n hj hk c hc' Gn (fun z => A z n-A z j) hphysical

end
end krylov.OneGradient
