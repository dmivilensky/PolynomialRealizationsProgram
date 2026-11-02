import jacobi.Jacobi.ZeroModel
import jacobi.Jacobi.HalfSpectrumGeometry

/-!
Article: jacobi, Proposition B.1.
The unconditional original Bessel frequency comparison and exact leading
Bessel phase give one uniform inverse-index angular error on the full
first-half range. This also absorbs the finite set of small indices in
the later sharp angular theorem.
Use: the true source primitive Lipschitz bound applies simultaneously to the actual angle and its explicit model value.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original model angles remain in the comparison interval uniformly over the entire growing first half at large degree.
Use: the true source primitive Lipschitz bound applies simultaneously to the actual angle and its explicit model value.
Article: jacobi, Proposition B.1.
Proof: the exact first-half phase is at most pi*N/2 plus a fixed parameter
constant. Once N exceeds four times that constant offset, divide by N. -/
theorem firstHalf_modelAngle_cap (a b : ℝ) :
    ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧ ∀ k,2*k<n → modelAngle a b n k≤3*Real.pi/4 := by
  -- The model cap follows directly from its literal phase grid, independently of any unproved sharp zero approximation.
  let S := |a|+|b|+2
  filter_upwards [(frequency_tendsto a b).eventually (eventually_ge_atTop (4*S+1))] with n hn
  have hS : 0<S := by dsimp [S]; positivity
  have hN : 0<frequency a b n := by linarith
  refine ⟨hN,?_⟩
  intro k hk
  have hp := firstHalf_phase_upper a b hk
  change phaseGrid a k/frequency a b n≤3*Real.pi/4
  apply (div_le_iff₀ hN).mpr
  have hh := mul_le_mul_of_nonneg_left hn Real.pi_pos.le
  dsimp [S] at hh
  nlinarith [Real.pi_pos]

/-- Original inverse-square scaled-root comparison and a leading inverse-index phase error imply a uniform inverse-index angular error on a growing finite range.
Use: applies the actual Bessel/Jacobi comparisons to the full first half without a fixed-index limit argument.
Article: jacobi, Proposition B.1.
Proof: divide the genuine scaled-root error by N and add the leading
phase error. The growing-range cap t<=2*N converts t/N^3 into 4/(N*t). -/
theorem coarse_angular_conversion {theta j v N t Q L A : ℝ} (hN : 0<N) (ht : 0<t)
    (htN : t≤2*N) (hQ : 0≤Q) (hL : 0≤L) (hupper : j≤L*t)
    (hroot : |N*theta-j|≤Q*j/N^2) (hphase : |j-v|≤A/t) :
    |theta-v/N|≤(4*Q*L+A)/(N*t) := by
  -- The t/N^3 term is controlled uniformly up to the true finite middle index.
  have hid : theta-v/N=(N*theta-j)/N+(j-v)/N := by field_simp [hN.ne']; ring
  have htail : Q*(L*t)/N^3≤4*Q*L/(N*t) := by
    apply (div_le_div_iff₀ (by positivity : 0<N^3) (mul_pos hN ht)).mpr
    have hh : t^2≤4*N^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh (show 0≤Q*L*N by positivity)]
  rw [hid]
  calc
    _ ≤ |(N*theta-j)/N|+|(j-v)/N| := abs_add_le _ _
    _ ≤ (Q*j/N^2)/N+(A/t)/N := by
      rw [abs_div,abs_div,abs_of_pos hN]
      exact add_le_add (div_le_div_of_nonneg_right hroot hN.le) (div_le_div_of_nonneg_right hphase hN.le)
    _ ≤ (Q*(L*t)/N^2)/N+(A/t)/N := add_le_add
      (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hupper hQ) (sq_nonneg N)) hN.le) le_rfl
    _ = Q*(L*t)/N^3+(A/t)/N := by ring
    _ ≤ 4*Q*L/(N*t)+(A/t)/N := add_le_add htail le_rfl
    _ = _ := by ring

/-- The complete actual first-half Jacobi angle list differs from its literal leading model by at most one uniform inverse-index inverse-frequency bound.
Use: handles all small indices in Proposition B.1 (a), replaces its true primitive argument, and bounds the original cosine Taylor displacement for part (b).
Article: jacobi, Proposition B.1.
Proof: combine the proved original scaled-root comparison, uniform linear
Bessel upper bound and indexed leading Weyl error. Degree-frequency
comparability supplies the actual growing-index cap needed by the scalar conversion. -/
theorem firstHalf_angle_coarse {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ A : ℝ,0<A ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧
      ∀ k,2*k<n → |finiteAngleAt a b ha hb n k-modelAngle a b n k|≤A/(frequency a b n*(k+1:ℝ)) := by
  -- These constants come from the original unconditional zero comparisons, not the still sharper angular assertion being proved.
  obtain ⟨Q,hQ,hcomp⟩ := firstHalf_bessel_comparison ha hb
  obtain ⟨A,hA,hphase⟩ := positiveZero_phase_bound ha
  obtain ⟨_,L,_,hL,hlinear⟩ := positiveZero_linear_bounds ha
  refine ⟨4*Q*L+A,by positivity,?_⟩
  filter_upwards [hcomp,frequency_degree_comparison a b] with n hn hdegree
  refine ⟨hn.1,?_⟩
  intro k hk
  have htN : (k+1:ℝ)≤2*frequency a b n := by
    have hh : k+1≤n := by omega
    exact (show (k+1:ℝ)≤n by exact_mod_cast hh).trans hdegree.2.1
  exact coarse_angular_conversion hn.1 (by positivity) htN hQ.le hL.le
    (hlinear k).2 (hn.2 k hk) (hphase k)

end
end jacobi.Jacobi
