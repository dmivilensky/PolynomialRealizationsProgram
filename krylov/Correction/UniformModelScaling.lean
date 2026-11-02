import krylov.Correction.UniformModelBounds
import krylov.Correction.RFCHistoryScaling
import krylov.Correction.SpectralHistoryScaling
import krylov.Correction.GatedHomogeneousDomains

/-!
Article: main_krylov, thm:UCq, actual normalized-model scale covariance.
Use: Remove initial-gradient normalization from the genuine observed-model,
inverse and measured-gate conclusions while preserving their uniform constants.
Source: the proved complete actual RFC field scaling, genuine finite observed
coordinates, spectral-test covariance and diagonal coefficient normalization.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- Genuine common positive scaling of all physical observed columns preserves their actual reference-metric normalized model exactly.
Use: Restore original initial-gradient units in uniform model estimates.
Article: main_krylov, thm:UCq.
Proof: The measured model scales quadratically, and each true linear image norm scales by the same positive factor. Cancel only that common nonzero factor, allowing individual columns to be zero.
-/
theorem measured_model_normalization_scalar
    (s y : Fin p → EuclideanSpace ℝ (Fin n))
    (R : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {c : ℝ} (hc : 0<c) :
    rescaleModel (pairModel (fun i => c • s i) (fun i => c • y i))
      (fun i => ‖R (c • s i)‖⁻¹)=rescaleModel (pairModel s y) (fun i => ‖R (s i)‖⁻¹) := by
  rw [pairModel_scalar]
  ext i j
  simp only [rescaleModel,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.smul_apply,
    smul_eq_mul,map_smul,norm_smul,Real.norm_of_nonneg hc.le,_root_.mul_inv_rev]
  calc
    _ = ((c⁻¹*c)*(c*c⁻¹))*(‖R (s i)‖⁻¹*pairModel s y i j*‖R (s j)‖⁻¹) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hc.ne',mul_inv_cancel₀ hc.ne',one_mul,one_mul]

/-- The actual physical step-normalized model distance is its genuine fixed-coordinate measured model distance.
Use: Preserve the original observed matrix and its spectral norm under the true retained-age dictionary.
Article: main_krylov, thm:UCq.
Proof: Eliminate the pure finite length cast and substitute the real step and image coordinates; both actual norm expressions coincide.
-/
theorem canonicalObservedModel_norm_coordinates (base : Matrix (Fin n) (Fin n) ℝ)
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (h : W.length=p) (s y : Fin p → EuclideanSpace ℝ (Fin n))
    (hs : windowSteps W=s ∘ finCongr h) (hy : windowImages W=y ∘ finCongr h) :
    ‖canonicalObservedModel base W-1‖=
      ‖rescaleModel (pairModel s y)
        (fun i => ‖cgOperator (metricRoot base) (s i)‖⁻¹)-1‖ := by
  subst p
  have hs' : windowSteps W=s := hs
  have hy' : windowImages W=y := hy
  simp only [canonicalObservedModel,← pairModel_window,hs',hy']
  rfl

/-- Every genuine ordinary-RFC active normalized-model distance is invariant under positive initial-gradient scaling.
Use: Transfer the actual uniform model bound to arbitrary physical initial data.
Article: main_krylov, thm:UCq.
Proof: The genuine augmented-window dictionary puts both actual models in the same finite coordinates. True RFC homogeneity scales their real current probes and recorded pairs; exact normalized-model covariance cancels that common scale.
-/
theorem actual_observed_model_norm_scalar
    (base : Matrix (Fin n) (Fin n) ℝ)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc : 0<c) (k : ℕ) :
    let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
    let Hc := methodRun m A B (c • g) k
    let H := methodRun m A B g k
    ‖canonicalObservedModel base ((m.direction Hc,A k (m.direction Hc))::selectedWindow fullMemory Hc)-1‖=
      ‖canonicalObservedModel base ((m.direction H,A k (m.direction H))::selectedWindow fullMemory H)-1‖ := by
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
  let S : Fin (min (fullMemory k) k) → EuclideanSpace ℝ (Fin n) :=
    fun i => probedStep m A B g (k-1-i.val)
  let Y : Fin (min (fullMemory k) k) → EuclideanSpace ℝ (Fin n) :=
    fun i => probedSecant m A B g (k-1-i.val)
  let d := m.direction (methodRun m A B g k)
  let U : Fin (min (fullMemory k) k+1) → EuclideanSpace ℝ (Fin n) := Fin.cons d S
  let Z : Fin (min (fullMemory k) k+1) → EuclideanSpace ℝ (Fin n) := Fin.cons (A k d) Y
  have hscale := rfc_scalar fullMemory 1 A B g c hc.ne' (k+1)
  have hd : m.direction (methodRun m A B (c • g) k)=c • d := (hscale.2 k (by omega)).1
  have hs : (fun i : Fin (min (fullMemory k) k) => probedStep m A B (c • g) (k-1-i.val))=
      fun i => c • S i := by
    funext i
    exact (hscale.2 _ (by omega)).2.1
  have hy : (fun i : Fin (min (fullMemory k) k) => probedSecant m A B (c • g) (k-1-i.val))=
      fun i => c • Y i := by
    funext i
    exact (hscale.2 _ (by omega)).2.2
  have hU : (Fin.cons (c • d) (fun i => c • S i) : Fin (min (fullMemory k) k+1) → _)=fun i => c • U i := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  have hZ : (Fin.cons (c • A k d) (fun i => c • Y i) : Fin (min (fullMemory k) k+1) → _)=fun i => c • Z i := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  dsimp only
  rw [selectedWindow_methodRun,selectedWindow_methodRun]
  rw [canonicalObservedModel_norm_coordinates base _ _ _ _
    (augmentedWindow_coordinates _ _ _ _ _ _).1 (augmentedWindow_coordinates _ _ _ _ _ _).2]
  rw [canonicalObservedModel_norm_coordinates base _ _ _ _
    (augmentedWindow_coordinates _ _ _ _ _ _).1 (augmentedWindow_coordinates _ _ _ _ _ _).2]
  rw [hd,map_smul,hs,hy,hU,hZ,measured_model_normalization_scalar U Z _ hc]

/-- The real retained-history defect norm of ordinary RFC is invariant under every nonzero initial-gradient scale.
Use: Restore genuine defect-gate acceptance in original physical units.
Article: main_krylov, thm:UCq.
Proof: The exact finite observed dictionary and true RFC step/secant homogeneity reduce both actual defect norms to the existing pair-defect scaling identity.
-/
theorem actual_old_defect_norm_scalar
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc : c≠0) (k : ℕ) :
    let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
    ‖windowDefect (selectedWindow fullMemory (methodRun m A B (c • g) k))‖=
      ‖windowDefect (selectedWindow fullMemory (methodRun m A B g k))‖ := by
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
  have hscale := rfc_scalar fullMemory 1 A B g c hc (k+1)
  have hs : (fun i : Fin (min (fullMemory k) k) => probedStep m A B (c • g) (k-1-i.val))=
      fun i => c • probedStep m A B g (k-1-i.val) := by
    funext i
    exact (hscale.2 _ (by omega)).2.1
  have hy : (fun i : Fin (min (fullMemory k) k) => probedSecant m A B (c • g) (k-1-i.val))=
      fun i => c • probedSecant m A B g (k-1-i.val) := by
    funext i
    exact (hscale.2 _ (by omega)).2.2
  dsimp only
  rw [selectedWindow_methodRun,selectedWindow_methodRun]
  rw [windowDefect_norm_of_coordinates _ _ _ _
    (retainedWindow_coordinates _ _ _ _).1 (retainedWindow_coordinates _ _ _ _).2]
  rw [windowDefect_norm_of_coordinates _ _ _ _
    (retainedWindow_coordinates _ _ _ _).1 (retainedWindow_coordinates _ _ _ _).2]
  rw [hs,hy,pairDefect_scalar _ _ c hc]

/-- Positive initial-gradient scaling preserves every actual active ordinary-RFC inverse, spectral test, defect test and normalized-model bound with the same constants.
Use: Remove the normalized-initial-error restriction from the original uniform model theorem.
Article: main_krylov, thm:UCq.
Proof: Exact actual RFC field scaling transfers nonzero directions and gives a nonzero common factor in the genuine observed conjugacy determinant. Apply the proved exact measured spectral, defect and normalized-model scale identities to those same actual windows.
-/
theorem ordinary_active_models_scalar (base : Matrix (Fin n) (Fin n) ℝ)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc : 0<c) (N : ℕ) (γ C ε : ℝ)
    (hmodels : activeObservedModelBounds base (rfcMethod fullMemory 1) A B g N γ C ε) :
    activeObservedModelBounds base (rfcMethod fullMemory 1) A B (c • g) N γ C ε := by
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
  dsimp only [activeObservedModelBounds]
  intro k hk hdc
  have hscale := rfc_scalar fullMemory 1 A B g c hc.ne' (k+1)
  have hd := (hscale.2 k (by omega)).1
  have hd0 : m.direction (methodRun m A B g k)≠0 := by
    intro hz
    rw [hz,smul_zero] at hd
    exact hdc hd
  have ht := hmodels k hk hd0
  have hs : (fun i : Fin (min (fullMemory k) k) => probedStep m A B (c • g) (k-1-i.val))=
      fun i => c • probedStep m A B g (k-1-i.val) := by
    funext i
    exact (hscale.2 _ (by omega)).2.1
  have hy : (fun i : Fin (min (fullMemory k) k) => probedSecant m A B (c • g) (k-1-i.val))=
      fun i => c • probedSecant m A B g (k-1-i.val) := by
    funext i
    exact (hscale.2 _ (by omega)).2.2
  refine ⟨?_,?_,?_,?_⟩
  · have hu := ht.1
    rw [full_probed_conjugacy_det] at hu ⊢
    rw [hs,hy,crossGram_scalar,Matrix.det_smul]
    exact isUnit_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero _ (mul_ne_zero hc.ne' hc.ne')) (isUnit_iff_ne_zero.mp hu))
  · exact (actual_spectralGate_scalar_of_fields m fullMemory A B g k γ c hc.ne' hd
      (fun i hi => (hscale.2 i (by omega)).2.1) (fun i hi => (hscale.2 i (by omega)).2.2)).mpr ht.2.1
  · rw [actual_old_defect_norm_scalar A B g hc.ne' k]
    exact ht.2.2.1
  · rw [actual_observed_model_norm_scalar base A B g hc k]
    exact ht.2.2.2

end
end krylov.Correction
