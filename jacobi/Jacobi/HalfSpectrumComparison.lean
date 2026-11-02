import jacobi.Jacobi.FrequencyWindow

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
All explicit frequency-window hypotheses are discharged for every first-half
original zero once the actual degree is large. The resulting constants
depend only on alpha,beta. The growing index range is 2*k<n in zero-based
indexing, exactly the source range 1<=k<=ceil(n/2).
Use: chooses one uniform degree threshold for all literal coefficient bounds and first-half zero comparisons.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual Jacobi oscillation frequency tends to infinity with its original degree.
Use: chooses one uniform degree threshold for all literal coefficient bounds and first-half zero comparisons.
Article: jacobi, Proposition B.1.
Proof: add the fixed source parameter offset to the community natural-cast divergence theorem. -/
theorem frequency_tendsto (a b : ℝ) : Tendsto (frequency a b) atTop atTop :=
  tendsto_atTop_add_const_right atTop ((a+b+1)/2) tendsto_natCast_atTop_atTop

/-- Every original first-half Bessel reference phase lies below half the finite Jacobi frequency plus a fixed parameter constant.
Use: discharges the uniform comparison-interval cap for all growing first-half prefixes at once.
Article: jacobi, Proposition B.1.
Proof: 2*k<n bounds the index contribution; the two fixed parameter offsets are bounded by their absolute values. -/
theorem firstHalf_phase_upper (a b : ℝ) {n k : ℕ} (hk : 2*k<n) :
    phaseGrid a k≤Real.pi*frequency a b n/2+Real.pi*(|a|+|b|+2) := by
  have hkn : 2*(k:ℝ)<n := by exact_mod_cast hk
  have hh : (k:ℝ)+a/2+3/4≤frequency a b n/2+|a|+|b|+2 := by
    unfold frequency
    linarith [le_abs_self a,neg_le_abs b,abs_nonneg a,abs_nonneg b]
  unfold phaseGrid
  nlinarith [mul_le_mul_of_nonneg_left hh Real.pi_pos.le]

/-- Every first-half original Bessel zero obeys the actual lower-frequency cap beyond one uniform degree threshold.
Use: removes the only geometric cap premise of the genuine quantitative Sturm comparison.
Article: jacobi, Proposition B.1.
Proof: the actual leading inverse-index estimate bounds every Bessel zero
by its exact phase plus a constant. The first-half phase is pi*N/2 plus
a fixed constant. At large N this is at most 9*pi*N/16, while the lower
comparison frequency is at least 3*N/4, giving the required cap. -/
theorem firstHalf_bessel_cap {a b C : ℝ} (ha : -1<a) (hC : 0<C) :
    ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧ 4*(C+1)≤(frequency a b n)^2 ∧
      ∀ k,2*k<n → positiveZero a ha k/√((frequency a b n)^2-C-1)≤3*Real.pi/4 := by
  -- The cap is proved for the full increasing index range, using actual numbered Bessel zeros rather than a fixed-index limit.
  obtain ⟨A,hA,hfirst⟩ := positiveZero_phase_bound ha
  let T := Real.pi*(|a|+|b|+2)+A
  have hT : 0<T := by dsimp [T]; positivity
  have he := (frequency_tendsto a b).eventually (eventually_ge_atTop (4*(C+1)+16*T/Real.pi+1))
  filter_upwards [he] with n hn
  let N := frequency a b n
  have hdiv : 0≤16*T/Real.pi := by positivity
  have hN : 0<N := by dsimp [N]; linarith
  have hNlarge : 4*(C+1)≤N^2 := by
    have hh : 4*(C+1)+1≤N := by dsimp [N]; linarith
    nlinarith [sq_nonneg (N-1)]
  have hNT : T≤Real.pi*N/16 := by
    have hh : 16*T/Real.pi≤N := by dsimp [N]; linarith
    have hm := (div_le_iff₀ Real.pi_pos).mp hh
    linarith
  refine ⟨hN,hNlarge,?_⟩
  intro k hk
  have herr : |positiveZero a ha k-phaseGrid a k|≤A :=
    (hfirst k).trans (div_le_self hA.le (by linarith [Nat.cast_nonneg (α := ℝ) k]))
  have hj : positiveZero a ha k≤Real.pi*N/2+T := by
    have hh := firstHalf_phase_upper a b hk
    dsimp [T,N]
    linarith [(abs_le.mp herr).2]
  have hL2 : (√(N^2-C-1))^2=N^2-C-1 := Real.sq_sqrt (by linarith)
  have hL : 0<√(N^2-C-1) := Real.sqrt_pos.mpr (by linarith)
  have hhalf : 3*N/4≤√(N^2-C-1) := by nlinarith
  apply (div_le_iff₀ hL).mpr
  have hm := mul_le_mul_of_nonneg_left hhalf (show 0≤3*Real.pi/4 by positivity)
  nlinarith [Real.pi_pos]

/-- The entire first half of every sufficiently large original Jacobi spectrum has a uniform quantitative Bessel comparison, with all original-function premises discharged.
Use: supplies growing-index endpoint locations and gap bounds for Proposition B.1 and aligns the genuine finite and Bessel phases for its sharper parts.
Article: jacobi, Proposition B.1.
Proof: the true smooth regular potential has a genuine uniform compact
bound. The preceding actual cap theorem verifies the comparison geometry
for every first-half index. Apply the proved two-sided frequency error
with that original index as the end of its true finite nodal prefix. -/
theorem firstHalf_bessel_comparison {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧
      ∀ k,2*k<n → |frequency a b n*finiteAngleAt a b ha hb n k-positiveZero a ha k|≤
        C*positiveZero a ha k/(frequency a b n)^2 := by
  -- Every cap, equation, endpoint and zero-numbering premise has been proved for the actual original source families.
  obtain ⟨C,hC,hbound⟩ := regularPotential_C1_bound a b
  refine ⟨2*(C+1),by positivity,?_⟩
  filter_upwards [firstHalf_bessel_cap (b := b) ha hC] with n hn
  refine ⟨hn.1,?_⟩
  intro k hk
  exact finiteAngle_frequency_error ha hb hC (fun t ht => (hbound t ht).1)
    (by omega : k<n) hn.2.1 (hn.2.2 k hk) k le_rfl

end
end jacobi.Jacobi
