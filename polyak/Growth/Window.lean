import polyak.Growth.Boundary
import polyak.Growth.Tail

/-!
Article: Appendix A, Lemma plateau.
Use: turn one strict-certificate window estimate into a uniform discounted tail bound.
Proof: subexponential growth removes the right boundary, then shift the actual trajectory.
-/

namespace polyak.Growth
noncomputable section
open Finset

/-- Article: energy estimate on every actual trajectory. Use: preserve its quantifiers over dimensions. -/
def WindowEnergyBound (A B β t K : ℝ) (w : ℕ) : Prop :=
  ∀ d : ℕ, ∀ r : Run (EuclideanSpace ℝ (Fin d)) A B β, ∀ i j : ℕ,
    w ≤ i → i ≤ j →
      mass (discountedEnergy r.x t) i (j+1) ≤
        K*(energyWindow (discountedEnergy r.x t) w i+
          energyWindow (discountedEnergy r.x t) w j)

variable {E : Type*} [NormedAddCommGroup E]

/-- Article: exact shifted mass. Use: translating a trajectory loses no boundary factor. -/
theorem mass_discountedEnergy_shift (x : ℕ → E) (t : ℝ) (i m : ℕ) :
    mass (discountedEnergy (fun k => x (i+k)) t) 0 m =
      Real.exp (2*i*t)*mass (discountedEnergy x t) i (i+m) := by
  unfold mass
  simp_rw [discountedEnergy_shift]
  rw [← mul_sum]
  congr 1
  simpa only [zero_add, Nat.add_comm m i] using sum_Ico_add (discountedEnergy x t) 0 m i

/-- Article: discounted pair norm. Use: connect the ℓ² free state to the two scalar energies. -/
theorem discounted_stateNorm (x : ℕ → E) (t : ℝ) (i : ℕ) :
    Real.exp (-2*i*t)*stateNorm x i^2 =
      discountedEnergy x t i+Real.exp (2*t)*discountedEnergy x t (i+1) := by
  have he : Real.exp (2*t)*Real.exp (-2*(i+1 : ℕ)*t) = Real.exp (-2*i*t) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [stateNorm_sq]
  simp only [discountedEnergy, mul_add, ← mul_assoc, he]

/-- Article: uniform discounted tail bound. Use: all starts and all dimensions share one D>1. -/
theorem windowEnergyBound_tail {A B β K : ℝ} {w : ℕ} (hB : B ≠ 0) (hK : 0 < K)
    (henergy : WindowEnergyBound A B β (Real.log (growthRate A B β)) K w) :
    ∃ D : ℝ, 1 < D ∧ ∀ d : ℕ, ∀ r : Run (EuclideanSpace ℝ (Fin d)) A B β,
      ∀ i j : ℕ, i ≤ j →
        mass (discountedEnergy r.x (Real.log (growthRate A B β))) i j ≤
          D*(discountedEnergy r.x (Real.log (growthRate A B β)) i+
            discountedEnergy r.x (Real.log (growthRate A B β)) (i+1)) := by
  let t := Real.log (growthRate A B β)
  let C := (1+2*K)*boundaryConstant A B β t (2*w+1)
  have hC : 0 < C := mul_pos (by linarith) (boundaryConstant_pos _ _ _ _ _)
  let D := 2+C*(1+Real.exp (2*t))
  have hD : 1 < D := by
    dsimp [D]
    nlinarith [mul_pos hC (show 0 < 1+Real.exp (2*t) by positivity)]
  refine ⟨D,hD,fun d r i j hij => ?_⟩
  let q := r.shift i
  have hsub := discountedEnergy_subexponential q.normalized hB q.x q.recurrence
  have hmass := mass_zero_le_boundary (discountedEnergy_nonneg q.x t) hsub hK w
    (fun l hl => henergy d q w l le_rfl hl) (j-i)
  have hbound := q.mass_le_boundaryConstant t (2*w+1)
  have hs : mass (discountedEnergy q.x t) 0 (j-i) ≤ C*stateNorm q.x 0^2 := by
    calc
      _ ≤ (1+2*K)*mass (discountedEnergy q.x t) 0 (2*w+1) := hmass
      _ ≤ (1+2*K)*(boundaryConstant A B β t (2*w+1)*stateNorm q.x 0^2) :=
        mul_le_mul_of_nonneg_left hbound (by linarith)
      _ = _ := by dsimp [C]; ring
  have hshift : mass (discountedEnergy q.x t) 0 (j-i) =
      Real.exp (2*i*t)*mass (discountedEnergy r.x t) i j := by
    change mass (discountedEnergy (fun k => r.x (i+k)) t) 0 (j-i) = _
    rw [mass_discountedEnergy_shift, Nat.add_sub_of_le hij]
  rw [hshift] at hs
  have hcancel : Real.exp (-2*i*t)*Real.exp (2*i*t) = 1 := by
    rw [← Real.exp_add]
    have he : -2*(i : ℝ)*t+2*i*t=0 := by ring
    rw [he, Real.exp_zero]
  have hstate : Real.exp (-2*i*t)*stateNorm q.x 0^2 =
      discountedEnergy r.x t i+Real.exp (2*t)*discountedEnergy r.x t (i+1) := by
    have hx : stateNorm q.x 0 = stateNorm r.x i := by simp [q, Run.shift, stateNorm]
    rw [hx, discounted_stateNorm]
  have hb₀ := discountedEnergy_nonneg r.x t i
  have hb₁ := discountedEnergy_nonneg r.x t (i+1)
  calc
    mass (discountedEnergy r.x t) i j =
        Real.exp (-2*i*t)*(Real.exp (2*i*t)*mass (discountedEnergy r.x t) i j) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ Real.exp (-2*i*t)*(C*stateNorm q.x 0^2) :=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ = C*(discountedEnergy r.x t i+Real.exp (2*t)*discountedEnergy r.x t (i+1)) := by
      rw [mul_left_comm, hstate]
    _ ≤ D*(discountedEnergy r.x t i+discountedEnergy r.x t (i+1)) := by
      dsimp [D]
      nlinarith [mul_nonneg (Real.exp_pos (2*t)).le hb₀,
        mul_nonneg hC.le hb₀, mul_nonneg hC.le hb₁,
        mul_nonneg hC.le (mul_nonneg (Real.exp_pos (2*t)).le hb₀)]

end
end polyak.Growth
