import krylov.Methods.ObservedHistoryCharts
import krylov.Stability.ObservedGate

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, actual primitive observed gate neighborhoods.
Use: prove the genuine RFC observed gate persists on its real finite-data
neighborhood from the actual positive retained model and strict reference
defect bound, preserving every true query-history boundary.
Source: true finite-coordinate model invariance and standard continuity of
real inner products, square roots and the actual spectral matrix norm.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The actual reconstructed retained-window gate defect has exactly its true fixed-coordinate spectral norm.
Use: The actual reconstructed retained-window gate defect has exactly its true fixed-coordinate spectral norm.
Article: main_krylov, def:classes and cor:lm, actual primitive observed gate neighborhoods.
Proof: Use the true retained-window length and genuine physical getter-array coordinates in proved defect norm invariance. -/
theorem chartWindow_defect_norm (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E) :
    ‖windowDefect (chartWindow memory shape data)‖=
      ‖pairDefect (chartSteps memory shape data) (chartImages memory shape data)‖ :=
  windowDefect_norm_of_coordinates _ (chartWindow_length memory shape data) _ _
    (windowSteps_getD_array _ _ (chartWindow_length memory shape data))
    (windowImages_getD_array _ _ (chartWindow_length memory shape data))

/-- The genuine primitive observed retained coordinates have positive true energies whenever their actual history conjugacy matrix is positive definite.
Use: The genuine primitive observed retained coordinates have positive true energies whenever their actual history conjugacy matrix is positive definite.
Article: main_krylov, def:classes and cor:lm, actual primitive observed gate neighborhoods.
Proof: Read its actual positive diagonal through the genuine finite index equivalence and true complete-history reconstruction. -/
theorem chartWindow_positive_energy (memory : ℕ → ℕ) (H : History E) (data : Fin n → E)
    (hdata : H.observationList=List.ofFn data)
    (hC : (crossGram (windowImages (selectedWindow memory H)) (windowSteps (selectedWindow memory H))).PosDef)
    (i : Fin (min (memory H.queryShape.length) H.queryShape.length)) :
    0 < inner ℝ (chartSteps memory H.queryShape data i) (chartImages memory H.queryShape data i) := by
  -- Transfer genuine positive model diagonal entries to their actual primitive observed-data coordinates.
  let W := selectedWindow memory H
  have hW := chartWindow_of_array memory H data hdata
  have hlen : W.length=min (memory H.queryShape.length) H.queryShape.length := by
    change (selectedWindow memory H).length=_
    rw [← hW,chartWindow_length]
  have hp := hC.diag_pos (i := (finCongr hlen).symm i)
  rw [windowSteps_getD_array W _ hlen,windowImages_getD_array W _ hlen] at hp
  simp only [chartSteps,chartImages,hW]
  change 0 < inner ℝ ((W.getD i.val (0,0)).1) ((W.getD i.val (0,0)).2)
  simpa only [crossGram,Function.comp_apply,Equiv.apply_symm_apply,real_inner_comm] using hp

/-- The genuine reconstructed RFC gate stays accepted on a true primitive observed-data neighborhood of every positive-energy strict accepted reference.
Use: The genuine reconstructed RFC gate stays accepted on a true primitive observed-data neighborhood of every positive-energy strict accepted reference.
Article: main_krylov, def:classes and cor:lm, actual primitive observed gate neighborhoods.
Proof: The actual finite defect norm is continuous on true positive energies; the real retained length is fixed by the genuine query shape, so both actual acceptance conditions persist. -/
theorem chartWindow_gate_eventually (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E)
    (he : ∀ i : Fin (min (memory shape.length) shape.length),
      0 < inner ℝ (chartSteps memory shape data i) (chartImages memory shape data i))
    (hgate : chartWindow memory shape data≠[] ∧ ‖windowDefect (chartWindow memory shape data)‖<1) :
    ∀ᶠ p in 𝓝 data, chartWindow memory shape p≠[] ∧ ‖windowDefect (chartWindow memory shape p)‖<1 := by
  -- The real finite gate norm is continuous at positive true energies, while actual nonemptiness depends only on the genuine fixed shape.
  have hfields := chartSteps_regular memory shape (fun p : Fin n → E => p) data (r := 0) contDiffAt_id
  have hc := (pairDefect_continuousAt (fun p : Fin n → E => chartSteps memory shape p)
    (fun p => chartImages memory shape p) data (fun i => (hfields i).1.continuousAt)
    (fun i => (hfields i).2.continuousAt) he).norm
  have hlt : ‖pairDefect (chartSteps memory shape data) (chartImages memory shape data)‖<1 := by
    rw [← chartWindow_defect_norm]
    exact hgate.2
  have hn : 0<min (memory shape.length) shape.length := by
    rw [← chartWindow_length memory shape data]
    exact List.length_pos_iff_ne_nil.mpr hgate.1
  filter_upwards [hc.eventually (Iio_mem_nhds hlt)] with p hp
  refine ⟨?_,?_⟩
  · apply List.length_pos_iff_ne_nil.mp
    rwa [chartWindow_length]
  · rwa [chartWindow_defect_norm]
end
end krylov.Methods
