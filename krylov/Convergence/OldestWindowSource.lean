import krylov.Convergence.SS1LocalBounds
import krylov.Secant.OldestAsymptotics

/-!
Article: main_krylov, thm:Ip, sharp oldest-pair constant.
Use: isolate the genuine oldest observed diagonal before estimating the
actual SS1 query. The exact distance amplification is Δ^-2; only the newer
observations pay the uniform whole-window conditioning factor.
Source: the source's sharp endpoint FTC estimate and the already proved
oldest-dual distance identity in LinearAlgebra.OldestPair.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Secant krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The radius of only the newer actual observed segments. -/
def newerWindowRadius {E : Type*} [NormedAddCommGroup E]
    (a b : Fin (n+1) → E) : ℝ := ∑ i : Fin n, (‖a i.succ‖+‖b i.succ‖)

theorem newerWindowRadius_nonneg {E : Type*} [NormedAddCommGroup E]
    (a b : Fin (n+1) → E) : 0≤newerWindowRadius a b :=
  Finset.sum_nonneg fun i _=>add_nonneg (norm_nonneg (a i.succ)) (norm_nonneg (b i.succ))

/-- The normalized error in one real secant retains its individual endpoint
radii, rather than a common window envelope. -/
theorem source_unit_window_error_at
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) {L : ℝ≥0}
    (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S, HasFDerivAt G (H z) z)
    (a b : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)))
    (ha : ∀ i,a i∈S) (hb : ∀ i,b i∈S) (hs : ∀ i,b i-a i≠0)
    (i : Fin (n+1)) :
    ‖unitWindowImages (fun j=>b j-a j) (fun j=>G (b j)-G (a j)) i-
      unitWindow (fun j=>b j-a j) i‖≤(L:ℝ)/2*(‖a i‖+‖b i‖) := by
  have hh := secant_image_endpoint_bound G H S hS h₀ hH hG (a i) (b i) (ha i) (hb i)
  rw [hH₀,ContinuousLinearMap.id_apply] at hh
  change ‖‖b i-a i‖⁻¹ • (G (b i)-G (a i))-‖b i-a i‖⁻¹ • (b i-a i)‖≤_
  rw [←smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (norm_nonneg _))).trans_eq
    (by field_simp [norm_ne_zero_iff.mpr (hs i)])

/-- Every actual normalized latest-model entry uses the newer real segment
and its sharp half-weighted endpoint budget. -/
theorem source_window_entry_bound
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) {L : ℝ≥0}
    (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S, HasFDerivAt G (H z) z)
    (a b : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)))
    (ha : ∀ i,a i∈S) (hb : ∀ i,b i∈S) (hs : ∀ i,b i-a i≠0)
    (i j : Fin (n+1)) :
    |windowDataError (unitWindow (fun k=>b k-a k))
      (unitWindowImages (fun k=>b k-a k) (fun k=>G (b k)-G (a k))) i j|≤
      (L:ℝ)/2*(‖a (max i j)‖+‖b (max i j)‖) := by
  rw [windowDataError_entry]
  have hh := norm_inner_le_norm (𝕜:=ℝ) (unitWindow (fun k=>b k-a k) (min i j))
    (unitWindowImages (fun k=>b k-a k) (fun k=>G (b k)-G (a k)) (max i j)-
      unitWindow (fun k=>b k-a k) (max i j))
  rw [unitWindow_norm _ hs,one_mul,Real.norm_eq_abs] at hh
  exact hh.trans (source_unit_window_error_at G H S hS h₀ hH hH₀ hG a b ha hb hs _)

/-- The entire actual error after deleting its oldest diagonal is controlled
solely by newer observed endpoints. This also covers dimension one, where
the remainder and its newer radius are exactly zero. -/
theorem source_window_newer_bound
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) {L : ℝ≥0}
    (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S, HasFDerivAt G (H z) z)
    (a b : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)))
    (ha : ∀ i,a i∈S) (hb : ∀ i,b i∈S) (hs : ∀ i,b i-a i≠0) :
    let X := windowDataError (unitWindow (fun k=>b k-a k))
      (unitWindowImages (fun k=>b k-a k) (fun k=>G (b k)-G (a k)))
    ‖X-X 0 0 • vecMulVec (Pi.single 0 1) (Pi.single 0 1)‖≤
      ((n+1:ℕ):ℝ)*((L:ℝ)/2*newerWindowRadius a b) := by
  apply windowDataError_newer_norm _ _ (unitWindow_norm _ hs)
    (mul_nonneg (by positivity) (newerWindowRadius_nonneg _ _))
  intro i hi
  obtain ⟨j,rfl⟩ := Fin.exists_succ_eq.mpr hi
  exact (source_unit_window_error_at G H S hS h₀ hH hH₀ hG a b ha hb hs j.succ).trans
    (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun k _=>add_nonneg (norm_nonneg (a k.succ)) (norm_nonneg (b k.succ)))
        (Finset.mem_univ j)) (by positivity))

/-- A finite, genuine SS1 query has the exact oldest-distance coefficient.
Only newer endpoints and the current radial curvature occur in its remaining
terms. Thus a superlinear trajectory leaves precisely L_H/(2Δ²). -/
theorem ss1_oldest_source_step_bound
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) {L : ℝ≥0}
    (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S, HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (a b : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)))
    (x : EuclideanSpace ℝ (Fin (n+1)))
    (ha : ∀ i,a i∈S) (hb : ∀ i,b i∈S) (hx : x∈S)
    (hV : IsUnit (windowMatrix (unitWindow (fun i=>b i-a i))).det) :
    let V := windowMatrix (unitWindow (fun i=>b i-a i))
    let M := inverseCongruence V (ss1Model (unitWindow (fun i=>b i-a i))
      (unitWindowImages (fun i=>b i-a i) (fun i=>G (b i)-G (a i))))
    IsUnit M.det →
    ‖ss1Point (fun i=>b i-a i) (fun i=>G (b i)-G (a i)) (G x) x‖≤‖M⁻¹‖*
      (((L:ℝ)/2*(‖a 0‖+‖b 0‖)) /
        (Metric.infDist (euclideanColumn V 0) (newerColumnSpan V:Set _))^2+
      (((n+1:ℕ):ℝ)*((L:ℝ)/2*newerWindowRadius a b))/(leastGain V)^2+
      (L:ℝ)/2*‖x‖)*‖x‖ := by
  dsimp only
  intro hM
  let s := fun i=>b i-a i
  let y := fun i=>G (b i)-G (a i)
  let V := windowMatrix (unitWindow s)
  let X := windowDataError (unitWindow s) (unitWindowImages s y)
  let M := inverseCongruence V (ss1Model (unitWindow s) (unitWindowImages s y))
  have hs (i : Fin (n+1)) : s i≠0 := by
    intro hi
    have hh := windowMatrix_step_ne_zero (unitWindow s) hV i
    apply hh
    simp only [unitWindow,rescaleWindow,hi,smul_zero]
  have hmodel : ‖M-1‖≤((L:ℝ)/2*(‖a 0‖+‖b 0‖)) /
      (Metric.infDist (euclideanColumn V 0) (newerColumnSpan V:Set _))^2+
      (((n+1:ℕ):ℝ)*((L:ℝ)/2*newerWindowRadius a b))/(leastGain V)^2 := by
    rw [window_model_error _ _ hV]
    apply (oldest_model_distance_bound V X hV).trans
    apply add_le_add
    · apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      simpa only [max_self] using source_window_entry_bound G H S hS h₀ hH hH₀ hG a b ha hb hs 0 0
    · exact div_le_div_of_nonneg_right
        (source_window_newer_bound G H S hS h₀ hH hH₀ hG a b ha hb hs) (sq_nonneg _)
  have hgrad := radial_gradient_endpoint_bound G H S hS h₀ hH hG hG₀ x hx
  rw [hH₀,ContinuousLinearMap.id_apply] at hgrad
  rw [←ss1Point_rescale s y (fun i=>‖s i‖⁻¹) (unitWindow_diagonal_unit s hs) (G x) x]
  change ‖ss1Point (unitWindow s) (unitWindowImages s y) (G x) x‖≤_
  rw [ss1Point_eq_model_step _ _ _ _ hV]
  apply (secant_query_error_bound M hM x (G x)).trans
  calc
    _ ≤ ‖M⁻¹‖*(_*‖x‖+(L:ℝ)/2*‖x‖^2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right hmodel (norm_nonneg _)) hgrad) (norm_nonneg _)
    _ = _ := by ring

end
end krylov.Convergence
