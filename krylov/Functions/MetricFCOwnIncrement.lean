import krylov.Functions.MetricFCOwnReference
import krylov.Functions.MetricFCQuadraticJet
import krylov.Functions.MidpointReferenceJet

/-!
Article: main_krylov, thm:Htransfer, original own-A₀ compatible midpoint increments.
Use: express actual function secants using the true CG reference generated
by the actual first segment secant and actual initial gradient. The same
genuine third derivative controls all increments, uniformly on the original
compact nondegenerate reference set.
Source: actual own-reference trajectory comparison and genuine midpoint Taylor.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original physical CG reference midpoint, retaining the original initial point and measured gradient.
Article: main_krylov, thm:Htransfer, original A₀-reference geometry. -/
def fcOwnReferenceMidpoint (A : E →L[ℝ] E) (g u : E) (i : ℕ) : E :=
  u + CG.displacement A g i + (1 / 2 : ℝ) • referenceStep A g i

/-- Consecutive original reference midpoints differ by exactly half the sum of their two true CG steps.
Article: main_krylov, thm:Htransfer, ξ_l=(σ_l+σ_(l+1))/2. -/
theorem fcOwnReferenceMidpoint_sub (A : E →L[ℝ] E) (g u : E) (i : ℕ) :
    fcOwnReferenceMidpoint A g u (i + 1) - fcOwnReferenceMidpoint A g u i =
      (1 / 2 : ℝ) • (referenceStep A g i + referenceStep A g (i + 1)) := by
  unfold fcOwnReferenceMidpoint
  rw [CG.displacement_succ]
  unfold referenceStep
  module

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Every actual FC secant has its genuine compact-uniform third-derivative jet at the original own-A₀ reference midpoint.
Article: main_krylov, thm:Htransfer, original reference transfer.
Proof: original compact nondegeneracy gives derived quadratic errors of the
entire actual trajectory relative to its own first-secant CG reference. The
real objective localizes every actual segment. Apply genuine midpoint Taylor
and the proved reference replacement lemma. -/
theorem metricFCOperator_own_reference_jet (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (N : ℕ) (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v : E, v ≠ 0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i < N, CG.gradient z.1 z.2 i ≠ 0)
    (B : ℝ) (hB : 0 < B) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B →
      let A := metricFCOperator T f G H fullMemory r (ε • u)
      let g := ε⁻¹ • G (ε • u)
      (A 0, g) ∈ K → ∀ i : ℕ, i < N →
      ‖A i - Q - ε • D (fcOwnReferenceMidpoint (A 0) g u i)‖ ≤ η * ε := by
  intro η hη
  obtain ⟨εp, C, hεp, hC, hpoints⟩ := metricFCPoint_own_reference_points T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG N K hK hquad B hB
  obtain ⟨εq, M, hεq, hM, hquery⟩ := metricFCPoint_physical_bound T hT f G H hr hG₀ hHc₀ hLr hH hF hG B hB
  obtain ⟨εj, hεj, hjet⟩ := averagedHessian_reference_jet H D
    (by positivity : 0 < r / (‖T.toContinuousLinearMap‖ + 1))
    (metric_hessian_continuous_ball T H hH) hD M C hM hC.le η hη
  refine ⟨min εp (min εq εj), lt_min hεp (lt_min hεq hεj), ?_⟩
  intro ε hε he u hu
  dsimp only
  let A := metricFCOperator T f G H fullMemory r (ε • u)
  let g := ε⁻¹ • G (ε • u)
  intro hKref i hi
  let x := metricFCPoint T f G fullMemory r (ε • u)
  let a := x i
  let b := x (i + 1)
  let y := fun j => u + CG.displacement (A 0) g j
  have hq j := hquery ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu j
  have hp j (hj : j ≤ N) := hpoints ε hε (he.trans_le (min_le_left _ _)) u hu hKref j hj
  have hseg t (ht : t ∈ Icc (0 : ℝ) 1) : ‖a + t • (b - a)‖ ≤ M * ε := by
    have ha : a ∈ closedBall (0 : E) (M * ε) := by simpa only [mem_closedBall, dist_zero_right] using (hq i).1
    have hb : a + (b - a) ∈ closedBall (0 : E) (M * ε) := by
      simpa only [add_sub_cancel, mem_closedBall, dist_zero_right] using (hq (i + 1)).1
    simpa only [mem_closedBall, dist_zero_right] using (convex_closedBall (0 : E) (M * ε)).add_smul_mem ha hb ht
  have hmid : ‖a + (1 / 2 : ℝ) • (b - a) - ε • fcOwnReferenceMidpoint (A 0) g u i‖ ≤ C * ε ^ 2 := by
    have hm := midpoint_error_bound a b (ε • y i) (ε • y (i + 1))
    have hy : y (i + 1) - y i = referenceStep (A 0) g i := by
      dsimp only [y]
      rw [CG.displacement_succ]
      unfold referenceStep
      module
    have heq : ε • fcOwnReferenceMidpoint (A 0) g u i =
        ε • y i + (1 / 2 : ℝ) • (ε • y (i + 1) - ε • y i) := by
      rw [← smul_sub, hy]
      dsimp only [fcOwnReferenceMidpoint, y]
      module
    rw [heq]
    exact hm.trans (by nlinarith only [hp i (by omega), hp (i + 1) (by omega)])
  simpa only [A, metricFCOperator, a, b, x, hH₀] using
    hjet ε hε (he.trans_le ((min_le_right _ _).trans (min_le_right _ _))) a (b - a)
      (fcOwnReferenceMidpoint (A 0) g u i) hseg hmid

/-- Actual consecutive FC secants are compatible slices at the original first-secant reference midpoint increments.
Article: main_krylov, thm:Htransfer, original-A₀ increment identity.
Proof: subtract the two genuine own-reference secant jets; linearity of the
one true Hessian derivative yields exactly the printed half-sum of CG steps. -/
theorem metricFCOperator_own_reference_increment (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (N : ℕ) (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v : E, v ≠ 0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i < N, CG.gradient z.1 z.2 i ≠ 0)
    (B : ℝ) (hB : 0 < B) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B →
      let A := metricFCOperator T f G H fullMemory r (ε • u)
      let g := ε⁻¹ • G (ε • u)
      (A 0, g) ∈ K → ∀ i : ℕ, i + 1 < N →
      ‖A (i + 1) - A i - ε • D ((1 / 2 : ℝ) •
        (referenceStep (A 0) g i + referenceStep (A 0) g (i + 1)))‖ ≤ η * ε := by
  intro η hη
  obtain ⟨ε₀, hε₀, hjet⟩ := metricFCOperator_own_reference_jet T hT f G H Q D hD hr hG₀ hH₀ hHc₀
    hLr hH hF hG N K hK hquad B hB (η / 2) (by positivity)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε he u hu
  dsimp only
  let A := metricFCOperator T f G H fullMemory r (ε • u)
  let g := ε⁻¹ • G (ε • u)
  intro hKref i hi
  have h₀ := hjet ε hε he u hu hKref i (by omega)
  have h₁ := hjet ε hε he u hu hKref (i + 1) hi
  let m := fcOwnReferenceMidpoint (A 0) g u
  have heq : A (i + 1) - A i - ε • D ((1 / 2 : ℝ) •
      (referenceStep (A 0) g i + referenceStep (A 0) g (i + 1))) =
      (A (i + 1) - Q - ε • D (m (i + 1))) - (A i - Q - ε • D (m i)) := by
    rw [← fcOwnReferenceMidpoint_sub (A 0) g u i, map_sub, smul_sub]
    dsimp only [m]
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add h₁ h₀).trans_eq (by ring))

end
end krylov.Functions
