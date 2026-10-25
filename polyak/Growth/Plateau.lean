import polyak.Growth.Extension
import polyak.Growth.Discount
import polyak.Growth.Tail
import polyak.Growth.Window

/-!
Article: Appendix A, Lemma plateau.
Use: a uniform discounted-energy estimate is impossible at the exact growth exponent.
Proof: finite-tail contraction would make one root of Γ strictly smaller than its infimum.
-/

namespace polyak.Growth
noncomputable section
open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Article: discounted state. Use: two discounted positions control the genuine ℓ² state. -/
theorem discounted_state_le_pair (x : ℕ → E) (t : ℝ) (n : ℕ) :
    Real.exp (-2*n*t)*stateNorm x n^2 ≤
      (1+Real.exp (2*t))*(discountedEnergy x t n+discountedEnergy x t (n+1)) := by
  have he : Real.exp (-2*(n : ℝ)*t) =
      Real.exp (2*t)*Real.exp (-2*(n+1 : ℕ)*t) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [stateNorm_sq]
  have h0 := discountedEnergy_nonneg x t n
  have h1 := discountedEnergy_nonneg x t (n+1)
  have hi : Real.exp (-2*n*t)*(‖x n‖^2+‖x (n+1)‖^2) =
      discountedEnergy x t n+Real.exp (2*t)*discountedEnergy x t (n+1) := by
    simp only [discountedEnergy, he]
    ring
  rw [hi]
  nlinarith [Real.exp_pos (2*t)]

omit [InnerProductSpace ℝ E] in
/-- Article: initial discounted state. Use: a uniform scalar conversion factor. -/
theorem discounted_pair_zero_le_state (x : ℕ → E) (t : ℝ) :
    discountedEnergy x t 0+discountedEnergy x t 1 ≤
      (1+Real.exp (-2*t))*stateNorm x 0^2 := by
  simp only [discountedEnergy, Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero, one_mul,
    Nat.cast_one, mul_one, stateNorm_sq, zero_add]
  nlinarith [sq_nonneg ‖x 0‖, sq_nonneg ‖x 1‖, Real.exp_pos (-2*t)]

/-- Article: Lemma plateau, contradiction at the growth exponent.
Use: the estimate is uniform in the dimension and in the original interpolating function. -/
theorem not_uniform_mass_bound {A B β D : ℝ} (hB : B ≠ 0) (hD : 1 < D)
    (hbound : ∀ d : ℕ, ∀ r : Run (EuclideanSpace ℝ (Fin d)) A B β,
      ∀ i j : ℕ, i ≤ j →
        mass (discountedEnergy r.x (Real.log (growthRate A B β))) i j ≤
          D*(discountedEnergy r.x (Real.log (growthRate A B β)) i+
            discountedEnergy r.x (Real.log (growthRate A B β)) (i+1))) : False := by
  let t := Real.log (growthRate A B β)
  let θ := 1-1/D
  let H := (1+Real.exp (2*t))*D*(1+Real.exp (-2*t))
  have hDp : 0 < D := zero_lt_one.trans hD
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    have hh := (div_le_one hDp).2 hD.le
    linarith
  have hθ1 : θ < 1 := by
    dsimp [θ]
    linarith [one_div_pos.mpr hDp]
  have hH : 0 < H := by dsimp [H]; positivity
  have hlim : Tendsto (fun p : ℕ => H*θ^p) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul H
  obtain ⟨p,hp,hp0⟩ := ((hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))).and
    (eventually_gt_atTop 0)).exists
  have hsegment {d : ℕ} (s : Segment (EuclideanSpace ℝ (Fin d)) A B β (2*p)) :
      stateNorm s.x (2*p) ≤ (1/2 : ℝ)*Real.exp ((2*p : ℕ)*t)*stateNorm s.x 0 := by
    obtain ⟨r,hr⟩ := s.exists_run
    have hpair := pair_le_geometric (discountedEnergy_nonneg r.x t) hD (hbound d r) p
    have hs := discounted_state_le_pair r.x t (2*p)
    have hinit := discounted_pair_zero_le_state r.x t
    have hraw : Real.exp (-2*(2*p : ℕ)*t)*stateNorm r.x (2*p)^2 ≤
        H*θ^p*stateNorm r.x 0^2 := by
      calc
        _ ≤ (1+Real.exp (2*t))*(discountedEnergy r.x t (2*p)+
            discountedEnergy r.x t (2*p+1)) := hs
        _ ≤ (1+Real.exp (2*t))*(θ^p*D*(discountedEnergy r.x t 0+
            discountedEnergy r.x t 1)) :=
          mul_le_mul_of_nonneg_left hpair (by positivity)
        _ ≤ (1+Real.exp (2*t))*(θ^p*D*((1+Real.exp (-2*t))*stateNorm r.x 0^2)) := by
          gcongr
        _ = _ := by dsimp [H]; ring
    have he : Real.exp (2*(2*p : ℕ)*t)*Real.exp (-2*(2*p : ℕ)*t) = 1 := by
      rw [← Real.exp_add]
      have hz : 2*(↑(2*p) : ℝ)*t + -2*(↑(2*p) : ℝ)*t = 0 := by ring
      rw [hz, Real.exp_zero]
    have he2 : Real.exp (2*(2*p : ℕ)*t) = Real.exp ((2*p : ℕ)*t)^2 := by
      calc
        _ = Real.exp (((2*p : ℕ) : ℝ)*t+((2*p : ℕ) : ℝ)*t) := by congr 1; ring
        _ = _ := by rw [Real.exp_add, pow_two]
    have hm := mul_le_mul_of_nonneg_left hraw (Real.exp_pos (2*(2*p : ℕ)*t)).le
    rw [← mul_assoc, he, one_mul, he2] at hm
    have hsq : stateNorm r.x (2*p)^2 ≤
        ((1/2 : ℝ)*Real.exp ((2*p : ℕ)*t)*stateNorm r.x 0)^2 := by
      have hsmall : H*θ^p ≤ (1/4 : ℝ) := hp.le
      have hnon : 0 ≤ Real.exp ((2*p : ℕ)*t)^2*stateNorm r.x 0^2 := by positivity
      have hh := mul_le_mul_of_nonneg_right hsmall hnon
      nlinarith [hm]
    have hnon : 0 ≤ (1/2 : ℝ)*Real.exp ((2*p : ℕ)*t)*stateNorm r.x 0 :=
      mul_nonneg (by positivity) (stateNorm_nonneg _ _)
    have hn := (sq_le_sq₀ (stateNorm_nonneg r.x (2*p)) hnon).mp hsq
    have hnorm (k : ℕ) (hk : k ≤ 2*p) : stateNorm r.x k = stateNorm s.x k := by
      simp only [stateNorm, hr k (by omega), hr (k+1) (by omega)]
    simpa only [hnorm (2*p) le_rfl, hnorm 0 (by omega)] using hn
  have hΓ : envelope A B β (2*p) ≤ (1/2 : ℝ)*Real.exp ((2*p : ℕ)*t) := by
    apply csSup_le (insert_nonempty _ _)
    intro v hv
    rcases hv with rfl | ⟨d,s,hs,rfl⟩
    · positivity
    · apply (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hs))).2
      exact hsegment s
  have hlo := growthRate_pow_le_envelope (A := A) (β := β) hB (2*p)
  have hexp : growthRate A B β^(2*p) = Real.exp ((2*p : ℕ)*t) := by
    rw [← Real.exp_log (growthRate_pos A B β), ← Real.exp_nat_mul]
  rw [hexp] at hlo
  linarith [Real.exp_pos ((2*p : ℕ)*t)]

/-- Article: Lemma plateau, exact-growth incompatibility.
Use: the finite-window energy estimate cannot hold at log ρΓ. -/
theorem not_windowEnergyBound_at_growth {A B β K : ℝ} {w : ℕ}
    (hB : B ≠ 0) (hK : 0 < K) :
    ¬ WindowEnergyBound A B β (Real.log (growthRate A B β)) K w := by
  intro henergy
  obtain ⟨D,hD,hbound⟩ := windowEnergyBound_tail hB hK henergy
  exact not_uniform_mass_bound hB hD hbound

end
end polyak.Growth
