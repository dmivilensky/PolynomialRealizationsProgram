import krylov.Envelope.SolveJets
import krylov.Methods.VirtualTrajectory
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, actual XRFC virtual-solve first jets.
Use: derive genuine computed virtual-correction and effective-gradient direction jet coherence from actual stored-step jets on the true reference domains.
Source: real full-memory observation arrays, native finite-solve jet closure and actual primitive smooth virtual block calculus.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual XRFC correction and effective-gradient conjugacy direction preserve genuine stored-step jet coherence through their real computed finite solves.
Use: The actual XRFC correction and effective-gradient conjugacy direction preserve genuine stored-step jet coherence through their real computed finite solves.
Article: main_krylov, thm:E1, actual XRFC virtual-solve first jets.
Proof: Identify actual full-memory arrays, derive native coefficient regularity on true finite model domains and apply the proved genuine solve jet rules. -/
theorem xrfc_virtual_block_jet (trial : History E → ℝ) (A : ℝ → ℕ → E →L[ℝ] E)
    (g : E) (k : ℕ) (K : Submodule ℝ E) (L : E →ₗ[ℝ] E)
    (hA : ∀ i<k,ContDiffAt ℝ 1 (fun t => A t i) 0)
    (hs : ∀ i<k,ContDiffAt ℝ 1 (fun t => oneGradientStep (xrfcMethod fullMemory trial) (A t) g i) 0)
    (hg : ContDiffAt ℝ 1 (fun t => oneGradientGradient (xrfcMethod fullMemory trial) (A t) g k) 0)
    (hM : (pairModel
      (fun i : Fin k => oneGradientStep (xrfcMethod fullMemory trial) (A 0) g (k-1-i.val))
      (fun i : Fin k => A 0 (k-1-i.val) (oneGradientStep (xrfcMethod fullMemory trial) (A 0) g (k-1-i.val)))).det≠0)
    (hC : (crossGram
      (fun i : Fin k => A 0 (k-1-i.val) (oneGradientStep (xrfcMethod fullMemory trial) (A 0) g (k-1-i.val)))
      (fun i : Fin k => oneGradientStep (xrfcMethod fullMemory trial) (A 0) g (k-1-i.val))).det≠0)
    (hj : ∀ i<k,(oneGradientStep (xrfcMethod fullMemory trial) (A 0) g i,
      deriv (fun t => oneGradientStep (xrfcMethod fullMemory trial) (A t) g i) 0)∈jetSubspace K L) :
    let m := xrfcMethod fullMemory trial (E := E)
    let H := fun t => oneGradientRun m (A t) g k
    (m.output (H 0),deriv (fun t => m.output (H t)) 0)∈jetSubspace K L ∧
      ((xrfcVirtualGradient trial (A 0) g k,deriv (fun t => xrfcVirtualGradient trial (A t) g k) 0)∈jetSubspace K L →
        (windowDirection (selectedWindow fullMemory (H 0)) (xrfcVirtualGradient trial (A 0) g k),
          deriv (fun t => windowDirection (selectedWindow fullMemory (H t)) (xrfcVirtualGradient trial (A t) g k)) 0)∈
            jetSubspace K L) := by
  -- Work with actual computed model arrays and true smooth scalar coefficients, without requiring ordinary returned gradients to have the effective-gradient jet.
  let m := xrfcMethod fullMemory trial (E := E)
  let H := fun t => oneGradientRun m (A t) g k
  let S := fun t (i : Fin k) => oneGradientStep m (A t) g (k-1-i.val)
  let Y := fun t (i : Fin k) => A t (k-1-i.val) (S t i)
  let G := fun t => oneGradientGradient m (A t) g k
  have hS (i : Fin k) : ContDiffAt ℝ 1 (fun t => S t i) 0 := hs _ (by omega)
  have hY (i : Fin k) : ContDiffAt ℝ 1 (fun t => Y t i) 0 := (hA _ (by omega)).clm_apply (hS i)
  have hModel (i j : Fin k) : ContDiffAt ℝ 1 (fun t => pairModel (S t) (Y t) i j) 0 :=
    (hS (max i j)).inner ℝ (hY (min i j))
  have hSj (i : Fin k) : (S 0 i,deriv (fun t => S t i) 0)∈jetSubspace K L := hj _ (by omega)
  have hc := model_solve_jet K L S (fun t => pairModel (S t) (Y t)) G hS hModel hg hM hSj
  have he : (fun t => m.output (H t))=(fun t => combine (S t)
      (modelCoefficients (S t) (pairModel (S t) (Y t)) (G t))) := by
    funext t
    exact (oneGradient_full_virtual_coordinates m (A t) g k).1
  constructor
  · change (m.output (H 0),deriv (fun t => m.output (H t)) 0)∈_
    have h0 : m.output (H 0)=combine (S 0) (modelCoefficients (S 0) (pairModel (S 0) (Y 0)) (G 0)) := congrFun he 0
    rw [h0,he]
    exact hc
  · intro hgj
    have hblock := oneGradient_virtualBlock_contDiffAt m A (fun _ => g) 0 k hA hs hg hM hC
    have hvirt : ContDiffAt ℝ 1 (fun t => xrfcVirtualGradient trial (A t) g k) 0 := hblock.2.1
    have hd := conjugacy_solve_jet K L S Y (fun t => xrfcVirtualGradient trial (A t) g k)
      hS hY hvirt hC hSj hgj
    have he : (fun t => windowDirection (selectedWindow fullMemory (H t)) (xrfcVirtualGradient trial (A t) g k))=
        fun t => conjugacyDirection (S t) (Y t) (xrfcVirtualGradient trial (A t) g k) := by
      funext t
      exact oneGradient_full_direction_coordinates m (A t) g _ k
    have h0 := congrFun he 0
    rw [h0,he]
    exact hd
end
end krylov.Envelope
