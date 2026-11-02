import krylov.Correction.IncomingResidual
import krylov.Methods.ProbedModelBasis

/-!
Article: main_krylov, thm:C and apD:lem-model, the actual final model error.
Use: derive the leading model-error matrix from genuine measured images,
including the quadratic discrepancy of earlier correction-contaminated pairs.
Source: the latest-information entry identity, genuine RFC pair orders and
the proved frozen-outer-factor pairing calculus in the actual spectral norm.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {p : ℕ}

/-- Every actual latest-model error entry splits into fresh operator drift and the actual measured-image discrepancy.
Use: no fictitious exact secant replaces a correction-contaminated observed pair.
Article: main_krylov, thm:C, UᵀBU−H in actual newest-first coordinates.
Proof: choose the newer observation by the actual storage order and move its
symmetric operator across the real pairing in the lower triangle. -/
theorem observed_model_error_entry (s y : Fin p → E) (A : Fin p → E →L[ℝ] E)
    (hA : ∀ i, (A i).toLinearMap.IsSymmetric) (B : E →L[ℝ] E) (i j : Fin p) :
    (correctionCompression s B-pairModel s y) i j=
      inner ℝ (s i) ((B-A (min i j)) (s j))-
      inner ℝ (s (max i j)) (y (min i j)-A (min i j) (s (min i j))) := by
  -- Retain the true measured-image discrepancy while selecting the newer operator in each triangle.
  simp only [correctionCompression,crossGram,pairModel,Matrix.sub_apply,
    _root_.sub_apply,inner_sub_right]
  rcases le_total i j with hij | hji
  · simp only [min_eq_left hij,max_eq_right hij]
    have hs := hA i (s j) (s i)
    change inner ℝ (A i (s j)) (s i)=inner ℝ (s j) (A i (s i)) at hs
    rw [real_inner_comm] at hs
    linarith
  · simp only [min_eq_right hji,max_eq_left hji]
    ring

/-- Actual analytic model columns may be frozen to quadratic order once the observed image discrepancies are quadratic.
Use: a reusable bridge from exact measured data to the leading curvature-error matrix.
Article: main_krylov, thm:C, the normalized model-error first-order factor.
Proof: each exact entry splits by the previous identity. Frozen outer-factor
replacement costs quadratic order; the remaining actual image discrepancy
is paired with a locally bounded real model column. -/
theorem observed_model_error_order (s y : X → Fin p → E)
    (A : X → Fin p → E →L[ℝ] E) (B : X → E →L[ℝ] E)
    (hs : ∀ i, AnalyticAt ℝ (fun z => s z i) 0)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0) (hB : AnalyticAt ℝ B 0)
    (hAsym : ∀ z i, (A z i).toLinearMap.IsSymmetric)
    (hbase : ∀ i, B 0=A 0 i)
    (hxi : ∀ i, (fun z => y z i-A z i (s z i)) =O[𝓝 (0 : X)] (fun z => ‖z‖^2)) :
    (fun z => correctionCompression (s z) (B z)-pairModel (s z) (y z)-
      (Matrix.of fun i j => inner ℝ (s 0 i) ((B z-A z (min i j)) (s 0 j)))) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^2) := by
  -- Work entrywise through the proved spectral-norm coordinate equivalence.
  apply (krylov.LinearAlgebra.matrix_bigO_iff_entry _ _).mpr
  intro i j
  let T := fun z => B z-A z (min i j)
  have hT : T =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    have hr := analytic_reference_order T (hB.sub (hA (min i j)))
    have hz : T 0=0 := by dsimp only [T]; rw [hbase,sub_self]
    simpa only [hz,sub_zero] using hr
  have hf := pairing_reference_order (fun z => s z i) (fun z => s z j) (s 0 i) (s 0 j) T
    (fun z => ‖z‖) (by simpa only [norm_zero] using continuous_norm.tendsto (0 : X))
      (analytic_reference_order _ (hs i)) (analytic_reference_order _ (hs j)) hT
  have hb := inner_order (fun z => s z (max i j))
    (fun z => y z (min i j)-A z (min i j) (s z (min i j))) (fun _ => 1) (fun z => ‖z‖^2)
    ((hs (max i j)).continuousAt.tendsto.isBigO_one ℝ) (hxi (min i j))
  have hb' : (fun z => inner ℝ (s z (max i j))
      (y z (min i j)-A z (min i j) (s z (min i j)))) =O[𝓝 (0 : X)] (fun z => ‖z‖^2) := by
    simpa only [one_mul] using hb
  exact (hf.sub hb').congr_left fun z => by
    rw [Matrix.sub_apply,observed_model_error_entry (s z) (y z) (A z) (hAsym z) (B z) i j]
    dsimp only [T,Matrix.of_apply]
    ring

/-- Every actual full augmented RFC observed image has a quadratic discrepancy from its own probe-time operator.
Use: discharge the image-defect premise of the model-error expansion from real repeated RFC execution.
Article: main_krylov, thm:C and apD:eq:pairs, augmented actual pair discrepancies.
Proof: the current image is its actual probe and has zero discrepancy; each
older coordinate is a real recorded pair covered by the proved quadratic RFC pair order. -/
theorem full_image_discrepancy_order (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) (j : Fin (k+1)) :
    let m := rfcMethod fullMemory count (E := E)
    (fun z => probedImageBasis m (A z) (B z) (g z) k j-
      A z (k-j.val) (probedStepBasis m (A z) (B z) (g z) k j)) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^2) := by
  -- The head is the actual exact probe; only genuine older recorded pairs carry a discrepancy.
  refine Fin.cases ?_ (fun l => ?_) j
  · apply IsBigO.of_bound 0
    filter_upwards [] with z
    simp only [probedImageBasis,probedStepBasis,Fin.cons_zero,Fin.val_zero,Nat.sub_zero,
      probedProbe,probedDirection,sub_self,norm_zero,zero_mul,le_refl]
  · have hm : ∀ a, CG.gradient Q (g 0) a≠0 → 0<a → 0<fullMemory a := fun _ _ ha => ha
    have hx := (quadraticRFC_pair_orders fullMemory count A B g hA hB hg Q hA0 hB0 hQ hpos hm
      (k-1-l.val) (fun a ha => hpre a (by omega))).2
    simpa only [probedImageBasis,probedStepBasis,Fin.cons_succ,Fin.val_succ,
      show k-(l.val+1)=k-1-l.val by omega] using hx

/-- The actual full-memory RFC model error has its frozen operator-difference coefficient with a quadratic remainder.
Use: the first-order factor in the second-order terminal residual is proved
for the true executed model, its real current probe and its actual stored secants.
Article: main_krylov, thm:C, UᵀBU−H=U₀ᵀ𝓛U₀+O(ω²) before reference normalization.
Proof: actual prefix analyticity supplies each true augmented column; the
current and old operator times have the same genuine quadratic base. The
preceding actual image-discrepancy theorem discharges the quadratic error
premise of the measured-model expansion. -/
theorem full_model_error_order (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (hAsym : ∀ z i, (A z i).toLinearMap.IsSymmetric)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let m := rfcMethod fullMemory count (E := E)
    let U := fun z => probedStepBasis m (A z) (B z) (g z) k
    let Z := fun z => probedImageBasis m (A z) (B z) (g z) k
    (fun z => correctionCompression (U z) (B z k)-pairModel (U z) (Z z)-
      (Matrix.of fun i j => inner ℝ (U 0 i) ((B z k-A z (k-(min i j).val)) (U 0 j)))) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^2) := by
  -- Discharge regularity and discrepancy from the actual RFC trajectory before applying the generic pairing calculus.
  have hm : ∀ a, CG.gradient Q (g 0) a≠0 → 0<a → 0<fullMemory a := fun _ _ ha => ha
  have ht := quadraticRFC_prefix_analytic fullMemory count A B g 0 hA hB hg Q hA0 hB0 hQ hpos hm
    (k+1) (fun a ha => hpre a (by omega))
  apply observed_model_error_order _ _ (fun z (i : Fin (k+1)) => A z (k-i.val)) (fun z => B z k)
  · intro i
    refine Fin.cases (ht.2 k (by omega)).1 (fun j => ?_) i
    exact (ht.2 (k-1-j.val) (by omega)).2.1
  · intro i
    exact hA (k-i.val)
  · exact hB k
  · intro z i
    exact hAsym z (k-i.val)
  · intro i
    rw [hA0,hB0]
  · exact full_image_discrepancy_order count A B g hA hB hg Q hA0 hB0 hQ hpos k hpre

end
end krylov.Correction
