import jacobi.Jacobi.FinitePhaseAveraging
import jacobi.Bessel.PhaseZeroDisplacement

/-!
Article: jacobi, Proposition B.1.
The fully instantiated true phase averaging and exact original zero
numbering give the actual angular correction -R(theta)/(2*N^2), with
one uniform cubic frequency remainder on the growing first-half range.
This is the analytic input to the printed angular expansion.
Use: combine with the proved actual McMahon expansion and the true primitive Lipschitz estimate to obtain precisely Proposition B.1 (a).
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel jacobi.Oscillation
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every sufficiently large-index original first-half Jacobi zero has its true Bessel zero plus the literal regular-potential correction, with a uniform cubic frequency error and no extra phase hypotheses.
Use: combine with the proved actual McMahon expansion and the true primitive Lipschitz estimate to obtain precisely Proposition B.1 (a).
Article: jacobi, Proposition B.1.
Proof: the genuine finite phase and Bessel phase have the same exact
numbered zero levels. Their proved uniform averaged difference therefore
evaluates at the actual finite zero. The actual Bessel phase-to-zero
remainder converts that true phase displacement to the original zero
displacement. Divide by the actual positive frequency. All original
potential bounds, phase bases and numbering premises are discharged. -/
theorem firstHalf_bessel_second_order {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ k1 : ℕ,∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧
      ∀ k : ℕ,k1≤k → 2*k<n →
        |finiteAngleAt a b ha hb n k-positiveZero a ha k/frequency a b n+
          regularPrimitive a b (finiteAngleAt a b ha hb n k)/(2*(frequency a b n)^2)|≤
            C/(frequency a b n)^3 := by
  -- The terminal phase is evaluated at the actual canonical finite zero, not at an assumed approximate or independently numbered level.
  obtain ⟨k0,K,hK,hs4,hs1,haverage⟩ := finite_phase_averaging ha hb
  obtain ⟨Q,hQ,hcomp⟩ := firstHalf_bessel_comparison ha hb
  obtain ⟨C0,hC0,hpot⟩ := regularPotential_C1_bound a b
  let s := positiveZero a ha k0
  let R := 4*|1/4-a^2| *Q/s
  have hs : 0<s := (positiveZero_properties ha k0).1
  have hR : 0≤R := by dsimp [R]; positivity
  refine ⟨k0+1,K+R,by linarith,?_⟩
  have hbase := (scaledAngle_tendsto ha hb k0).eventually (Ioi_mem_nhds (show s/2<s by linarith))
  have hnext := (scaledAngle_tendsto ha hb (k0+1)).eventually
    (Ioi_mem_nhds (show s<positiveZero a ha (k0+1) from positiveZero_strictMono ha (Nat.lt_succ_self k0)))
  have hlarge := (frequency_tendsto a b).eventually (eventually_ge_atTop (4*C0+2*Q+2))
  filter_upwards [haverage,hcomp,firstHalf_angle_cap ha hb,hbase,hnext,hlarge] with n hav hn hcap hb0 hbn hfreq
  have hN := hn.1
  let N := frequency a b n
  let Z := scaledAngle a b ha hb n
  let f := scaledPhase a b ha hb n hN (Z k0)
  let g := ordinaryPhase a ha s
  have hN2 : 4*C0≤N^2 ∧ 2*Q≤N^2 := by
    have hh : 4*C0+2*Q+2≤N := hfreq
    constructor <;> nlinarith [sq_nonneg (N-1)]
  refine ⟨hN,?_⟩
  intro k hk1 hkhalf
  have hk : k<n := by omega
  have hk0 : k0≤k := by omega
  have hmono : ∀ i j : ℕ,i≤j → j<n → Z i≤Z j := by
    intro i j hij hj
    rcases hij.eq_or_lt with heq | hlt
    · rw [heq]
    · exact (mul_lt_mul_of_pos_left (finiteAngleAt_lt ha hb hlt hj) hN).le
  have hXlo' : s≤Z k := hbn.le.trans (hmono (k0+1) k hk1 hk)
  have hXhi : Z k≤(3*Real.pi/4)*N := by
    have hh := mul_le_mul_of_nonneg_left (hcap k hkhalf) hN.le
    simpa only [Z,scaledAngle,N,mul_comm] using hh
  have havg := hav hN (Z k) ⟨hXlo',hXhi⟩
  have hfinite := scaledPhase_numbered_zero ha hb (fun t ht => (hpot t ht).1)
    (n := n) (k := k0) (M := k-k0) (by omega) hN hN2.1
    (by change 2*(a^2+1)≤Z k0; linarith)
    (by rw [Nat.add_sub_of_le hk0]; exact hcap k hkhalf)
  rw [Nat.add_sub_of_le hk0] at hfinite
  have hbessel := ordinaryPhase_numbered_zero ha k0 (by linarith : 2*(a^2+1)≤positiveZero a ha k0) (k-k0)
  rw [Nat.add_sub_of_le hk0] at hbessel
  have herr := hn.2 k hkhalf
  change |Z k-positiveZero a ha k|≤Q*positiveZero a ha k/N^2 at herr
  have hhalf : positiveZero a ha k/2≤Z k := by
    have hh : Q/N^2≤1/2 := (div_le_iff₀ (sq_pos_of_pos hN)).mpr (by linarith [hN2.2])
    have hm := mul_le_mul_of_nonneg_right hh (positiveZero_properties ha k).1.le
    have he : (Q/N^2)*positiveZero a ha k=Q*positiveZero a ha k/N^2 := by ring
    rw [he] at hm
    linarith [(abs_le.mp herr).1]
  have hdisp := ordinaryPhase_zero_displacement ha hN hQ.le hk0 hhalf herr
  change |(g (Z k)-g (positiveZero a ha k))-(Z k-positiveZero a ha k)|≤R/N^2 at hdisp
  change |f (Z k)-g (Z k)-scaledPrimitive a b N (Z k)/2|≤K/N^2 at havg
  change f (Z k)=((k-k0:ℕ):ℝ)*Real.pi at hfinite
  change g (positiveZero a ha k)=((k-k0:ℕ):ℝ)*Real.pi at hbessel
  rw [hfinite,← hbessel] at havg
  have hscaled : |Z k-positiveZero a ha k+scaledPrimitive a b N (Z k)/2|≤(K+R)/N^2 := by
    have hid : Z k-positiveZero a ha k+scaledPrimitive a b N (Z k)/2=
      -((g (positiveZero a ha k)-g (Z k))-scaledPrimitive a b N (Z k)/2)-
        ((g (Z k)-g (positiveZero a ha k))-(Z k-positiveZero a ha k)) := by ring
    rw [hid]
    calc
      _ ≤ |-((g (positiveZero a ha k)-g (Z k))-scaledPrimitive a b N (Z k)/2)|+
        |(g (Z k)-g (positiveZero a ha k))-(Z k-positiveZero a ha k)| := abs_sub _ _
      _ ≤ K/N^2+R/N^2 := by rw [abs_neg]; exact add_le_add havg hdisp
      _ = _ := by ring
  have hdiv := div_le_div_of_nonneg_right hscaled hN.le
  have harg : (Z k-positiveZero a ha k+scaledPrimitive a b N (Z k)/2)/N=
      finiteAngleAt a b ha hb n k-positiveZero a ha k/N+
        regularPrimitive a b (finiteAngleAt a b ha hb n k)/(2*N^2) := by
    dsimp [Z,scaledAngle,scaledPrimitive,N]
    rw [mul_div_cancel_left₀ _ hN.ne']
    field_simp [hN.ne']
  rw [← harg]
  rw [abs_div,abs_of_pos hN]
  convert hdiv using 1
  ring

end
end jacobi.Jacobi
