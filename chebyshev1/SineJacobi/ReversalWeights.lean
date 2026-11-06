import chebyshev1.Jacobi.WeightReversal
import chebyshev1.Jacobi.WeightCoordinates
import chebyshev1.SineJacobi.SpectralMeasure

/-! Reciprocal sine-square spectral weights and their stationary log-weight center. -/
namespace chebyshev1.SineJacobi
noncomputable section
open scoped BigOperators
open Polynomial Polynomial.Chebyshev
set_option backward.isDefEq.respectTransparency false

/-- On the Chebyshev nodes, the last endpoint has weights proportional to `sin²(theta)/w`. -/
theorem endpoint_weight_reversal (J : JacobiData) {n : ℕ}
    (B : SpectralBasis (J.matrix 0 (n + 1)))
    (hsq : ∀ t, 0 ≤ J.aSq t)
    (hpos : ∀ s, 0 < s → s < n + 1 → 0 < J.aSq s)
    (hi : Function.Injective B.eigenvalues)
    (ht : J.leading (n + 1) = C (2 / (2 : ℝ) ^ (n + 1)) * T ℝ (n + 1))
    (heig : ∀ j, B.eigenvalues j = node (n + 1) j) (j : Fin (n + 1)) :
    B.weight (Fin.last n) j =
      (Real.sin (nodeAngle (n + 1) j) ^ 2 / B.weight 0 j) /
        (∑ k, Real.sin (nodeAngle (n + 1) k) ^ 2 / B.weight 0 k) := by
  let c : ℝ := (2 / (2 : ℝ) ^ (n + 1)) * (n + 1 : ℕ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hd (k : Fin (n + 1)) :
      |(J.leading (n + 1)).derivative.eval (B.eigenvalues k)| =
        c / Real.sin (nodeAngle (n + 1) k) := by
    rw [show J.leading (n + 1) = (data (n + 1)).leading (n + 1) from
      ht.trans (terminal (n + 1) (by omega)).symm, heig k]
    exact terminal_derivative_abs (n + 1) (by omega) k
  have hw (k : Fin (n + 1)) : 0 < B.weight 0 k :=
    (J.spectral_endpoint_positive B hsq hpos hi k).1
  have hf (k : Fin (n + 1)) :
      1 / (B.weight 0 k * ((J.leading (n + 1)).derivative.eval (B.eigenvalues k)) ^ 2) =
        (1 / c ^ 2) * (Real.sin (nodeAngle (n + 1) k) ^ 2 / B.weight 0 k) := by
    rw [← sq_abs ((J.leading (n + 1)).derivative.eval (B.eigenvalues k)), hd k]
    field_simp [(hw k).ne', (node_sin_pos (n + 1) k).ne', hc.ne']
  rw [J.spectral_endpoint_weight_normalized B hsq hpos hi j]
  simp_rw [hf]
  rw [← Finset.mul_sum]
  have hs : (∑ k, Real.sin (nodeAngle (n + 1) k) ^ 2 / B.weight 0 k) ≠ 0 :=
    (Finset.sum_pos (fun k _ => div_pos (sq_pos_of_pos (node_sin_pos _ k)) (hw k))
      Finset.univ_nonempty).ne'
  field_simp [hc.ne', hs]

/-- The first weights of the reversed chain obey the normalized sine-square reciprocal law. -/
theorem spectral_weight_reversal (J : JacobiData) {n : ℕ}
    (B : SpectralBasis (J.matrix 0 (n + 1)))
    (Brev : SpectralBasis ((J.reversed (n + 1)).matrix 0 (n + 1)))
    (hsq : ∀ t, 0 ≤ J.aSq t)
    (hpos : ∀ s, 0 < s → s < n + 1 → 0 < J.aSq s)
    (hi : Function.Injective B.eigenvalues)
    (ht : J.leading (n + 1) = C (2 / (2 : ℝ) ^ (n + 1)) * T ℝ (n + 1))
    (heig : ∀ j, B.eigenvalues j = node (n + 1) j)
    (hreig : ∀ j, Brev.eigenvalues j = B.eigenvalues j) (j : Fin (n + 1)) :
    Brev.weight 0 j =
      (Real.sin (nodeAngle (n + 1) j) ^ 2 / B.weight 0 j) /
        (∑ k, Real.sin (nodeAngle (n + 1) k) ^ 2 / B.weight 0 k) := by
  rw [J.spectral_weight_reversed B hsq hi Brev hreig j]
  exact endpoint_weight_reversal J B hsq hpos hi ht heig j

/-- Sine weights are a fixed point of the normalized reciprocal involution. -/
theorem sine_weights_reversal_fixed (N : ℕ) (hN : 0 < N) :
    WeightCoordinates.reverse (fun j : Fin N => Real.sin (nodeAngle N j))
      (sineWeight N) = sineWeight N := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact WeightCoordinates.reverse_fixed_weights _ (node_sin_pos N)

theorem sine_weights_reversal_fixed_iff (N : ℕ) (hN : 0 < N) (w : Fin N → ℝ)
    (hw : ∀ j, 0 < w j) (hwsum : (∑ j, w j) = 1) :
    WeightCoordinates.reverse (fun j : Fin N => Real.sin (nodeAngle N j)) w = w ↔
      w = sineWeight N := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact WeightCoordinates.reverse_fixed_iff _ w (node_sin_pos N) hw hwsum

/-- Every differentiable reversal-invariant functional is critical at sine weights in log coordinates. -/
theorem sine_logWeights_stationary (N : ℕ) (hN : 0 < N)
    (F : (Fin N → ℝ) → ℝ) (L : (Fin N → ℝ) →L[ℝ] ℝ)
    (hF : HasFDerivAt (fun x =>
      F (WeightCoordinates.logWeights (fun j : Fin N => Real.sin (nodeAngle N j)) x)) L 0)
    (hinvariant : ∀ w, (∀ j, 0 < w j) → (∑ j, w j) = 1 →
      F (WeightCoordinates.reverse (fun j : Fin N => Real.sin (nodeAngle N j)) w) = F w) :
    L = 0 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact WeightCoordinates.stationary_logWeights _ (node_sin_pos N) F L hF hinvariant

end
end chebyshev1.SineJacobi
