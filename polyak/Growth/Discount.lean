import polyak.Growth.Rate
import polyak.Growth.Subexponential

/-!
Article: Appendix A, Lemma plateau.
Use: discounted energy along every actual normalized trajectory grows subexponentially.
Proof: every strict exponential majorant for Γ gives a matching arbitrarily small energy margin.
-/

namespace polyak.Growth
noncomputable section

/-- Article: discounted position energy. Use: the same normalization as the energy estimate. -/
def discountedEnergy {E : Type*} [NormedAddCommGroup E] (x : ℕ → E) (t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-2*k*t) * ‖x k‖^2

/-- Article: discounted energy is nonnegative. Use: apply finite-window mass inequalities. -/
theorem discountedEnergy_nonneg {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (t : ℝ) (k : ℕ) : 0 ≤ discountedEnergy x t k := by
  exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

/-- Article: subexponential envelope factor. Use: all actual trajectories at the growth exponent.
No constant or rate estimate is assumed about the particular trajectory. -/
theorem discountedEnergy_subexponential {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {ψ : E → ℝ} (hψ : NormalizedSmooth ψ)
    {A B β : ℝ} (hB : B ≠ 0) (x : ℕ → E)
    (hrec : ∀ k, x (k+2) = A • x (k+1) + B • gradient ψ (x (k+1)) - β • x k) :
    Subexponential (discountedEnergy x (Real.log (growthRate A B β))) := by
  intro δ hδ
  let t := Real.log (growthRate A B β)
  let R := Real.exp (t+δ/2)
  have hR : growthRate A B β < R := by
    rw [← Real.exp_log (growthRate_pos A B β)]
    exact Real.exp_lt_exp.mpr (by dsimp [t]; linarith)
  obtain ⟨C,hC,hbound⟩ := exists_envelope_le_mul_pow hB hR
  let D := C*stateNorm x 0
  have hD : 0 ≤ D := mul_nonneg hC.le (stateNorm_nonneg x 0)
  refine ⟨D^2+1, by positivity, fun k => ?_⟩
  have hx : ‖x k‖ ≤ D*Real.exp ((k : ℝ)*(t+δ/2)) := by
    let s := Segment.ofNormalized hψ x k (fun j _ => hrec j)
    have hg := stateNorm_le_envelope_hilbert s
    have hnorm := norm_left_le_stateNorm x k
    calc
      ‖x k‖ ≤ stateNorm x k := hnorm
      _ ≤ envelope A B β k * stateNorm x 0 := hg
      _ ≤ (C*R^k)*stateNorm x 0 := by
        exact mul_le_mul_of_nonneg_right (hbound k) (stateNorm_nonneg x 0)
      _ = D*Real.exp ((k : ℝ)*(t+δ/2)) := by
        dsimp [D, R]
        rw [← Real.exp_nat_mul]
        ring
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (Real.exp_pos _).le)).mpr hx
  have he : Real.exp (-2*(k : ℝ)*t)*(D*Real.exp ((k : ℝ)*(t+δ/2)))^2 =
      D^2*Real.exp (δ*k) := by
    calc
      _ = D^2*(Real.exp (-2*(k : ℝ)*t)*Real.exp ((k : ℝ)*(t+δ/2))*
          Real.exp ((k : ℝ)*(t+δ/2))) := by ring
      _ = D^2*Real.exp ((-2*(k : ℝ)*t+(k : ℝ)*(t+δ/2))+(k : ℝ)*(t+δ/2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ = _ := by congr 2; ring
  change Real.exp (-2*(k : ℝ)*t)*‖x k‖^2 ≤ _
  calc
    _ ≤ Real.exp (-2*(k : ℝ)*t)*(D*Real.exp ((k : ℝ)*(t+δ/2)))^2 :=
      mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = D^2*Real.exp (δ*k) := he
    _ ≤ (D^2+1)*Real.exp (δ*k) := by nlinarith [Real.exp_pos (δ*k)]

end
end polyak.Growth
