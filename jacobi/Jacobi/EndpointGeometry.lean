import jacobi.Jacobi.HalfSpectrumGeometry

/-!
Article: jacobi, Proposition B.1.
The genuine first-half comparison and exact ordered parameter reflection
supply the full uniform scale of the smaller endpoint distance at every
original finite node. No fixed-index compactness is substituted for the
article's growing-index uniform statement.
Use: bounds its opposite endpoint distance uniformly when converting the true one-edge comparison to Proposition B.1 (c).
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every original first-half Jacobi angle lies in the full comparison interval beyond one parameter-dependent degree threshold.
Use: bounds its opposite endpoint distance uniformly when converting the true one-edge comparison to Proposition B.1 (c).
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the true Bessel lower-frequency cap is already uniform. Reverse
actual Sturm comparison places each original finite angle below that cap. -/
theorem firstHalf_angle_cap {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∀ᶠ n : ℕ in atTop,∀ k,2*k<n → finiteAngleAt a b ha hb n k≤3*Real.pi/4 := by
  obtain ⟨C,hC,hbound⟩ := regularPotential_C1_bound a b
  filter_upwards [firstHalf_bessel_cap (b := b) ha hC] with n hn
  intro k hk
  have hwindow := finiteAngle_frequency_window ha hb hC (fun t ht => (hbound t ht).1)
    (by omega : k<n) (by linarith [hn.2.1]) (hn.2.2 k hk) k le_rfl
  exact hwindow.2.le.trans (hn.2.2 k hk)

/-- The actual frequency and degree are uniformly comparable beyond a fixed source-dependent threshold.
Use: converts source n and N endpoint scales and controls the finite growing index range by its actual frequency.
Article: jacobi, Proposition B.1.
Proof: the frequency tends to infinity and differs from the original degree by one fixed real offset. -/
theorem frequency_degree_comparison (a b : ℝ) :
    ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧ (n:ℝ)≤2*frequency a b n ∧ frequency a b n≤2*(n:ℝ) := by
  have he := (frequency_tendsto a b).eventually (eventually_ge_atTop (2*|a+b+1|+1))
  filter_upwards [he] with n hn
  dsimp [frequency] at hn ⊢
  constructor
  · linarith [abs_nonneg (a+b+1)]
  constructor <;> linarith [le_abs_self (a+b+1),neg_le_abs (a+b+1)]

/-- An actual first-half angle has a uniform positive smaller-endpoint scale once its true cap and degree comparison hold.
Use: applies the source's genuine first-half estimates to both distances before exact ordered reflection.
Article: jacobi, Proposition B.1.
Proof: use the given actual lower bound for theta and the cap pi-theta>=pi/4;
the latter dominates pi*(k+1)/(8*N) because k+1<=n<=2*N. -/
theorem min_endpoint_of_half {theta c N : ℝ} {n k : ℕ} (hN : 0<N) (hn : (n:ℝ)≤2*N)
    (hk : 2*k<n) (hlo : c*(k+1:ℝ)/N≤theta) (hcap : theta≤3*Real.pi/4) :
    min c (Real.pi/8)*(k+1:ℝ)/N≤min theta (Real.pi-theta) := by
  -- The finite index cap turns the opposite endpoint margin pi/4 into the same inverse-frequency scale.
  have hkN : (k+1:ℝ)≤2*N := by
    have hh : k+1≤n := by omega
    exact (show (k+1:ℝ)≤n by exact_mod_cast hh).trans hn
  apply le_min
  · exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)) hN.le).trans hlo
  · have hh : min c (Real.pi/8)*(k+1:ℝ)/N≤Real.pi/4 := by
      apply (div_le_iff₀ hN).mpr
      have hm := mul_le_mul_of_nonneg_right (min_le_right c (Real.pi/8)) (show 0≤(k+1:ℝ) by positivity)
      have hn' := mul_le_mul_of_nonneg_left hkN (show 0≤Real.pi/8 by positivity)
      nlinarith
    exact hh.trans (by linarith)

/-- Every original finite Jacobi angle has its full uniform two-edge distance scale, with all source-dependent constants and degree thresholds proved.
Use: gives the endpoint-distance assertion of Proposition B.1 (c), bounds the actual restoring coefficient, and supplies the geometric input to interpolation estimate (d).
Article: jacobi, Proposition B.1.
Proof: combine the genuine two parameter-ordered first-half bounds and
caps with frequency-degree comparability. For an original first-half
index use those bounds directly. Every other original index is the
reversal of a first-half index for the swapped source parameters; the
exact proved ordered reflection exchanges the two endpoint distances. -/
theorem angle_endpoint_bounds {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧
      ∀ i : Fin n,
        c*(min (i.val+1) (n-i.val):ℕ)/frequency a b n≤min (angle a b ha hb i) (Real.pi-angle a b ha hb i) ∧
        min (angle a b ha hb i) (Real.pi-angle a b ha hb i)≤C*(min (i.val+1) (n-i.val):ℕ)/frequency a b n := by
  -- Parameter reflection applies to the actual sorted finite zero list, including the middle index; no independently selected edge subsequence is used.
  obtain ⟨ca,Ca,hca,hCa,hA⟩ := firstHalf_angle_bounds ha hb
  obtain ⟨cb,Cb,hcb,hCb,hB⟩ := firstHalf_angle_bounds hb ha
  let d := min ca cb
  let c := min d (Real.pi/8)
  let C := max Ca Cb
  have hc : 0<c := lt_min (lt_min hca hcb) (by positivity)
  have hC : 0<C := lt_of_lt_of_le hCa (le_max_left _ _)
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hA,hB,firstHalf_angle_cap ha hb,firstHalf_angle_cap hb ha,
    frequency_degree_comparison a b] with n hAn hBn hcapA hcapB hdegree
  have hfreq : frequency b a n=frequency a b n := by unfold frequency; ring
  rw [hfreq] at hBn
  refine ⟨hdegree.1,?_⟩
  intro i
  by_cases hi : 2*i.val<n
  · have hmin : min (i.val+1) (n-i.val)=i.val+1 := min_eq_left (by omega)
    rw [hmin,Nat.cast_add,Nat.cast_one]
    have heq := finiteAngleAt_eq ha hb i.isLt
    change finiteAngleAt a b ha hb n i.val=angle a b ha hb i at heq
    have hlo := (hAn.2 i.val hi).1
    have hu := (hAn.2 i.val hi).2
    rw [heq] at hlo hu
    have hdlo : d*(i.val+1:ℝ)/frequency a b n≤angle a b ha hb i :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left ca cb) (by positivity)) hdegree.1.le).trans hlo
    refine ⟨min_endpoint_of_half hdegree.1 hdegree.2.1 hi hdlo (by rw [← heq]; exact hcapA i.val hi),?_⟩
    exact (min_le_left _ _).trans (hu.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left Ca Cb) (by positivity)) hdegree.1.le))
  · let j := i.rev
    have hj : 2*j.val<n := by dsimp [j,Fin.rev]; omega
    have hjval : j.val+1=n-i.val := by dsimp [j,Fin.rev]; omega
    have hmin : min (i.val+1) (n-i.val)=j.val+1 := by rw [min_eq_right (by omega : n-i.val≤ i.val+1),hjval]
    have href : angle a b ha hb i=Real.pi-angle b a hb ha j := by
      simpa only [j,Fin.rev_rev] using angle_reflection ha hb j
    rw [hmin,Nat.cast_add,Nat.cast_one,href,show Real.pi-(Real.pi-angle b a hb ha j)=angle b a hb ha j by ring,min_comm]
    have heq := finiteAngleAt_eq hb ha j.isLt
    change finiteAngleAt b a hb ha n j.val=angle b a hb ha j at heq
    have hlo := (hBn.2 j.val hj).1
    have hu := (hBn.2 j.val hj).2
    rw [heq] at hlo hu
    have hdlo : d*(j.val+1:ℝ)/frequency a b n≤angle b a hb ha j :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right ca cb) (by positivity)) hdegree.1.le).trans hlo
    refine ⟨min_endpoint_of_half hdegree.1 hdegree.2.1 hj hdlo (by rw [← heq]; exact hcapB j.val hj),?_⟩
    exact (min_le_left _ _).trans (hu.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right Ca Cb) (by positivity)) hdegree.1.le))

end
end jacobi.Jacobi
