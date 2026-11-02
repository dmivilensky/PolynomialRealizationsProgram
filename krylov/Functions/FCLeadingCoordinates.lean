import krylov.Functions.MetricFCLeadingGradient
import krylov.Variation.FCResponse
import krylov.Nonlinear.MetricCoordinates

/-!
Article: main_krylov, thm:Htransfer, the actual FC derivative equals the printed response.
Use: identify the genuine terminal derivative used by native function transfer
with the established CG flag/tail formula. Common segment perturbations cancel
by the actual differentiated staircase, rather than by an assumed invariance.
Source: thm:A, actual FC first-variation coordinates and true metric pairing.
-/

namespace krylov.Functions
noncomputable section
open Set Metric Matrix Finset krylov.Methods krylov.Reference krylov.Nonlinear krylov.Variation krylov.Secant
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual finite operator perturbation extended by zero past the executed prefix.
Article: main_krylov, lem:cycle-transfer, finite FC operator chart. -/
def fcFiniteDrift (N : ℕ) (W : Fin N → E →L[ℝ] E) (k : ℕ) : E →L[ℝ] E :=
  if h : k < N then W ⟨k, h⟩ else 0

/-- The actual finite FC derivative equals its genuine directional derivative along the real affine operator path.
Article: main_krylov, thm:Htransfer, identification of the actual first jet. -/
theorem fcLeadingOperator_hasDerivAt (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (g : E) (hpre : ∀ i < N, CG.gradient Q g i ≠ 0)
    (W : Fin N → E →L[ℝ] E) :
    HasDerivAt (fun t : ℝ => fcGradient fullMemory (fun k => Q + t • fcFiniteDrift N W k) g N)
      (fcLeadingOperator Q N g W) 0 := by
  have hW : HasDerivAt (fun t : ℝ => t • W) W 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).smul_const W using 1
    simp only [one_smul]
  have hline := (hasDerivAt_const (0 : ℝ) g).prodMk hW
  have hdf : HasFDerivAt (fcFiniteTerminal Q N) (fderiv ℝ (fcFiniteTerminal Q N) (g, 0)) (g, (0 : ℝ) • W) := by
    simpa only [zero_smul] using (fcFiniteTerminal_analytic Q hQ hpos N g hpre).differentiableAt.hasFDerivAt
  have hd := hdf.comp_hasDerivAt 0 hline
  have heq (t : ℝ) : fcFiniteOperatorPath Q N (t • W) = fun k => Q + t • fcFiniteDrift N W k := by
    funext k
    by_cases hk : k < N
    · simp only [fcFiniteOperatorPath, fcFiniteDrift, dite_eq_left hk, Pi.smul_apply]
    · simp only [fcFiniteOperatorPath, fcFiniteDrift, dite_eq_right hk, smul_zero, add_zero]
  change HasDerivAt (fun t : ℝ => fcFiniteTerminal Q N (g, t • W)) (fcLeadingOperator Q N g W) 0 at hd
  simpa only [fcFiniteTerminal, heq] using hd

variable {n : ℕ}

/-- The real finite FC first jet satisfies the printed staircase coordinates, including arbitrary common secant drift.
Article: main_krylov, thm:A and thm:Htransfer, the genuine compatible response. -/
theorem fcLeadingOperator_coordinates
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (g : EuclideanSpace ℝ (Fin n))
    (hpre : ∀ i < N, CG.gradient Q g i ≠ 0) (hstop : CG.gradient Q g N = 0)
    (W : Fin N → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hW : ∀ i, (W i).toLinearMap.IsSymmetric) {i : ℕ} (hi : i < N) :
    inner ℝ (referenceStep Q g i) (fcLeadingOperator Q N g W) =
      ∑ j ∈ Ico (i + 1) N, inner ℝ (referenceStep Q g i)
        ((fcFiniteDrift N W j - fcFiniteDrift N W i) (referenceStep Q g j)) := by
  let A := fun (t : ℝ) k => Q + t • fcFiniteDrift N W k
  have hA k : AnalyticAt ℝ (fun t => A t k) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hAD k : HasDerivAt (fun t => A t k) (fcFiniteDrift N W k) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const (fcFiniteDrift N W k)).const_add Q using 1
    simp only [one_smul]
  have hsym t k : (A t k).toLinearMap.IsSymmetric := by
    have hw : (fcFiniteDrift N W k).toLinearMap.IsSymmetric := by
      by_cases hk : k < N
      · simpa only [fcFiniteDrift, dite_eq_left hk] using hW ⟨k, hk⟩
      · simp only [fcFiniteDrift, dite_eq_right hk]
        exact LinearMap.IsSymmetric.zero
    change (Q.toLinearMap + t • (fcFiniteDrift N W k).toLinearMap).IsSymmetric
    exact hQ.add (LinearMap.IsSymmetric.smul (by rfl) hw)
  have hA₀ : A 0 = fun _ => Q := by funext k; simp only [A, zero_smul, add_zero]
  have hc := fullFC_firstVariation_coordinates A (fcFiniteDrift N W) g hA hAD hsym Q hA₀
    hQ hpos N hpre hstop hi
  rw [(fcLeadingOperator_hasDerivAt Q hQ hpos N g hpre W).deriv] at hc
  exact hc

/-- The actual canonical matrix of an arbitrary physical segment perturbation.
Article: main_krylov, thm:Htransfer, true inverse-root congruence. -/
def physicalCanonicalMatrix (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (coordinateCongruence (metricCoordinates base hb) W)

/-- The canonical perturbation matrix acts by the genuine physical inverse-root congruence.
Article: main_krylov, thm:Htransfer, exact canonical tensor transport. -/
theorem physicalCanonicalMatrix_operator (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (physicalCanonicalMatrix base hb W) =
      coordinateCongruence (metricCoordinates base hb) W :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply _

/-- The true canonical perturbation construction is linear on differences.
Article: main_krylov, thm:Htransfer, actual secant increments. -/
theorem physicalCanonicalMatrix_sub (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (U W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    physicalCanonicalMatrix base hb (U - W) = physicalCanonicalMatrix base hb U - physicalCanonicalMatrix base hb W := by
  simp only [physicalCanonicalMatrix, map_sub]

/-- The actual inverse-root congruence preserves the original physical bilinear pairing.
Article: main_krylov, thm:Htransfer, the real canonical response dictionary. -/
theorem physicalCanonicalMatrix_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s t : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (cgOperator (metricRoot base) s)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (physicalCanonicalMatrix base hb W)
        (cgOperator (metricRoot base) t)) = inner ℝ s (W t) := by
  rw [physicalCanonicalMatrix_operator]
  change inner ℝ ((metricCoordinates base hb) s)
    ((metricCoordinates base hb).symm (W ((metricCoordinates base hb).symm ((metricCoordinates base hb) t)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact metric_primal_dual_pairing (metricCoordinates base hb) (metricCoordinates_inverse_symmetric base hb) s (W t)

/-- The actual first FC derivative is exactly the printed full-cycle response on the genuine canonical consecutive increments.
Article: main_krylov, thm:A and thm:Htransfer, full derivative/response identification.
Proof: the differentiated actual staircase kills every common segment drift.
Canonical consecutive increments telescope, and the complete true CG frame
identifies the terminal vector from its genuine physical step pairings. -/
theorem fcLeadingOperator_eq_fullCycleResponse (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g = n)
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hW : ∀ i < n, (W i).toLinearMap.IsSymmetric) :
    cgOperator (metricRoot base)⁻¹ (fcLeadingOperator (cgOperator base) n g (fun i => W i.val)) =
      fullCycleResponse base g (range n)
        (fun l => physicalCanonicalMatrix base hb (W (l + 1)) - physicalCanonicalMatrix base hb (W l)) := by
  obtain ⟨hQ, hpos⟩ := cgOperator_positive base hb
  have hpre := cg_nonstagnation_of_full_atoms base hb g hcount
  apply canonical_step_inner_ext base hb g hcount
  intro i hi
  have hc := fcLeadingOperator_coordinates (cgOperator base) hQ hpos n g hpre
    (by simpa only [hcount] using cg_terminates base hb g) (fun i => W i.val) (fun i => hW i.val i.isLt) hi
  rw [canonical_search_pairing base hb] at hc
  change inner ℝ (canonicalCGStep base g i)
    (cgOperator (metricRoot base)⁻¹ (fcLeadingOperator (cgOperator base) n g (fun i => W i.val))) = _ at hc
  rw [fullCycleResponse_coordinates base hb g hcount _ hi]
  refine hc.trans (sum_congr rfl (fun j hj => ?_))
  have hj' := mem_Ico.mp hj
  rw [sum_Ico_sub (fun k => physicalCanonicalMatrix base hb (W k)) (by omega : i ≤ j),
    ← physicalCanonicalMatrix_sub]
  simp only [fcFiniteDrift, dite_eq_left hi, dite_eq_left hj'.2]
  exact (physicalCanonicalMatrix_pairing base hb (W j - W i) (referenceStep (cgOperator base) g i)
    (referenceStep (cgOperator base) g j)).symm

end
end krylov.Functions
