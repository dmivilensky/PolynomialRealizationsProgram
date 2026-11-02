import krylov.Tensor.BinaryFibreDictionary
import krylov.LinearAlgebra.InformationRadius

/-!
Article: main_krylov, thm:Fplanar, exact information radius of the remaining
binary coefficient.
Use: take the actual supremum over every admissible completion and the true
infimum over every common vector output. Prove that centring the observed
coefficient interval attains precisely |P1|*h2*norm(v).
Source: the existing two-scenario half-distance theorem and the proved actual
compact interval fibres; no method-specific centre is imposed on competitors.
-/

namespace krylov.Tensor.BinaryCubic
noncomputable section
open krylov.LinearAlgebra
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- All actual residual norms of one common output over the entire observed fibre.
Article: main_krylov, thm:Fplanar. -/
def fibreErrorValues (r : ℝ) (O : Observation) (v u : V) : Set ℝ :=
  {e | ∃ q∈coefficientFibre r O, e=‖u+(O.P*q) • v‖}

/-- The genuine worst error of a common vector output on one actual fibre.
Article: main_krylov, thm:Fplanar. -/
def fibreWorstError (r : ℝ) (O : Observation) (v u : V) : ℝ :=
  sSup (fibreErrorValues r O v u)

/-- The explicit output depending only on observed data, not on hidden q.
Article: main_krylov, thm:Fplanar, centre correction. -/
def fibreCentreCorrection (r : ℝ) (O : Observation) (v : V) : V :=
  -(O.P*fibreCentre r O) • v

/-- Every actual fibre error set has a finite bound for every common output.
Article: main_krylov, thm:Fplanar. -/
theorem fibreErrorValues_bddAbove (r : ℝ) (O : Observation) (v u : V) :
    BddAbove (fibreErrorValues r O v u) := by
  refine ⟨‖u‖+|O.P| * ‖v‖,?_⟩
  rintro e ⟨q,hq,rfl⟩
  have hq1 := coefficientFibre_abs_le hq
  calc
    ‖u+(O.P*q) • v‖ ≤ ‖u‖+‖(O.P*q) • v‖ := norm_add_le _ _
    _ = ‖u‖+|O.P| * |q| * ‖v‖ := by rw [norm_smul,Real.norm_eq_abs,abs_mul,mul_assoc]
    _ ≤ ‖u‖+|O.P| * 1*‖v‖ := by gcongr
    _ = ‖u‖+|O.P| * ‖v‖ := by ring

/-- Every true completion's error is dominated by the full fibre worst error.
Article: main_krylov, thm:Fplanar. -/
theorem error_le_fibreWorst {r : ℝ} {O : Observation} (v u : V) {q : ℝ}
    (hq : q∈coefficientFibre r O) : ‖u+(O.P*q) • v‖≤fibreWorstError r O v u :=
  le_csSup (fibreErrorValues_bddAbove r O v u) ⟨q,hq,rfl⟩

/-- The exact interval radius obstructs every arbitrary common output.
Article: main_krylov, thm:Fplanar, lower bound on each true data fibre.
Proof: use the two actual attained endpoints, then reuse the existing
half-distance theorem for their residuals at the common vector output. -/
theorem fibre_radius_lower (r : ℝ) (O : Observation) (v u : V)
    (hne : (coefficientFibre r O).Nonempty) :
    fibreProduct r O*‖v‖≤fibreWorstError r O v u := by
  have hc := coefficientFibre_isCompact r O
  have hlo := hc.sInf_mem hne
  have hhi := hc.sSup_mem hne
  have horder := csInf_le hc.bddBelow hhi
  let lo := sInf (coefficientFibre r O)
  let hi := sSup (coefficientFibre r O)
  have he : (O.P*hi) • v-(O.P*lo) • v=(O.P*(hi-lo)) • v := by module
  have h := two_scenario_distance ((O.P*hi) • v) ((O.P*lo) • v) u
  rw [he,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (sub_nonneg.mpr horder)] at h
  have hr : |O.P| * (hi-lo)*‖v‖/2=fibreProduct r O*‖v‖ := by
    unfold fibreProduct fibreHalfWidth
    dsimp only [lo,hi]
    ring
  rw [hr] at h
  apply h.trans
  apply max_le
  · simpa only [add_comm] using error_le_fibreWorst v u hhi
  · simpa only [add_comm] using error_le_fibreWorst v u hlo

/-- The data-only centre output controls every true completion by the exact radius.
Article: main_krylov, thm:Fplanar, centring attains the minimax value. -/
theorem fibre_centre_error {r : ℝ} {O : Observation} (v : V) {q : ℝ}
    (hq : q∈coefficientFibre r O) :
    ‖fibreCentreCorrection r O v+(O.P*q) • v‖≤fibreProduct r O*‖v‖ := by
  have he : fibreCentreCorrection r O v+(O.P*q) • v=(O.P*(q-fibreCentre r O)) • v := by
    unfold fibreCentreCorrection
    module
  rw [he,norm_smul,Real.norm_eq_abs,abs_mul]
  have h := mul_le_mul_of_nonneg_left (fibreCentre_bound hq) (abs_nonneg O.P)
  exact mul_le_mul_of_nonneg_right h (norm_nonneg v)

/-- The genuine whole-fibre worst error of the explicit centre is exactly
its information radius. Article: main_krylov, thm:Fplanar. -/
theorem fibre_centre_worst (r : ℝ) (O : Observation) (v : V)
    (hne : (coefficientFibre r O).Nonempty) :
    fibreWorstError r O v (fibreCentreCorrection r O v)=fibreProduct r O*‖v‖ := by
  apply le_antisymm
  · apply csSup_le
    · obtain ⟨q,hq⟩ := hne
      exact ⟨_,q,hq,rfl⟩
    · rintro e ⟨q,hq,rfl⟩
      exact fibre_centre_error v hq
  · exact fibre_radius_lower r O v _ hne

/-- The actual minimax value over all common vector outputs on one observed fibre.
Article: main_krylov, thm:Fplanar. -/
def fibreRadius (r : ℝ) (O : Observation) (v : V) : ℝ :=
  sInf (Set.range (fibreWorstError r O v))

/-- The full infimum over arbitrary common outputs equals the exact hidden
coefficient radius and is attained by the data-only centre correction.
Article: main_krylov, thm:Fplanar, exact fibre minimax.
Proof: the lower bound quantifies over every possible output, while the
explicit centre achieves its opposite inequality on all completions. -/
theorem fibreRadius_eq (r : ℝ) (O : Observation) (v : V)
    (hne : (coefficientFibre r O).Nonempty) :
    fibreRadius r O v=fibreProduct r O*‖v‖ := by
  have hb : BddBelow (Set.range (fibreWorstError r O v)) := by
    refine ⟨fibreProduct r O*‖v‖,?_⟩
    rintro e ⟨u,rfl⟩
    exact fibre_radius_lower r O v u hne
  apply le_antisymm
  · have h := csInf_le hb (Set.mem_range_self (fibreCentreCorrection r O v))
    rwa [fibre_centre_worst r O v hne] at h
  · apply le_csInf (Set.range_nonempty _)
    rintro e ⟨u,rfl⟩
    exact fibre_radius_lower r O v u hne

end
end krylov.Tensor.BinaryCubic
