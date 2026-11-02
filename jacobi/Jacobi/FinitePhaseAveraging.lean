import jacobi.Jacobi.InitialPhase
import jacobi.Jacobi.EndpointGeometry
import Mathlib.Analysis.Real.Pi.Bounds
import jacobi.Oscillation.PhaseAveraging

/-!
Article: jacobi, Proposition B.1.
The complete quantitative ODE averaging theorem is instantiated with the
original scaled Jacobi wave, the actual Bessel wave and the literal
regular potential. Every domain, derivative, initial alignment and C1
bound is proved here. One fixed actual Bessel zero anchors all degrees.
Use: the genuine numbered finite and Bessel zero phases turn this unconditional estimate into the sharp original angular expansion of Proposition B.1 (a).
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel jacobi.Oscillation
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original finite Jacobi phase differs from the true Bessel phase by exactly half the literal regular primitive, up to one uniform inverse-square frequency error on the entire growing comparison interval.
Use: the genuine numbered finite and Bessel zero phases turn this unconditional estimate into the sharp original angular expansion of Proposition B.1 (a).
Article: jacobi, Proposition B.1.
Proof: choose one actual Bessel zero beyond the explicit restoring
threshold. Genuine finite-root comparison bounds its true scaled finite
counterpart and its actual initial phase discrepancy. The original smooth
potential and primitive provide all actual rescaled derivatives and C1
bounds. Apply the proved ordinary phase-averaging theorem with these
original functions on the full interval [s,3*pi*N/4]. -/
theorem finite_phase_averaging {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ k0 : ℕ,∃ K : ℝ,0<K ∧ 4*(a^2+1)≤positiveZero a ha k0 ∧ 1≤positiveZero a ha k0 ∧
      ∀ᶠ n : ℕ in atTop,∀ hN : 0<frequency a b n,
      ∀ x∈Icc (positiveZero a ha k0) ((3*Real.pi/4)*frequency a b n),
        |scaledPhase a b ha hb n hN (scaledAngle a b ha hb n k0) x-
          ordinaryPhase a ha (positiveZero a ha k0) x-scaledPrimitive a b (frequency a b n) x/2|≤
            K/(frequency a b n)^2 := by
  -- All smallness conditions are derived from the actual original potential and zero comparison, never supplied as finite phase certificates.
  obtain ⟨C,hC,hpot⟩ := regularPotential_C1_bound a b
  obtain ⟨Q,hQ,hcomp⟩ := firstHalf_bessel_comparison ha hb
  obtain ⟨k0,hk0⟩ := ((positiveZero_tendsto ha).eventually
    (eventually_ge_atTop (4*|endpointCorrection a|+4*(a^2+1)+2))).exists
  let s := positiveZero a ha k0
  have hs : 0<s := (positiveZero_properties ha k0).1
  have hs1 : 1≤s := by dsimp [s]; nlinarith [abs_nonneg (endpointCorrection a),sq_nonneg a]
  have hs4 : 4*(a^2+1)≤s := by dsimp [s]; linarith [abs_nonneg (endpointCorrection a)]
  have hsc : 4*|endpointCorrection a|≤s := by dsimp [s]; nlinarith [sq_nonneg a]
  let E := C+Q+1
  let D := 2+|endpointCorrection a|/(s/2)^2
  let B := D+3
  let T := B*s+s/2+2*(|endpointCorrection a| *B+1)+
    ((4*(endpointCorrection a)^2+2*|endpointCorrection a|)*B+2*|endpointCorrection a|+1)*(1+3*Real.pi/4)
  have hE : 0<E := by dsimp [E]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  have hB : 2<B := by dsimp [B]; linarith
  have hT : 0<T := by dsimp [T]; positivity
  refine ⟨k0,T*E,by positivity,hs4,hs1,?_⟩
  have hfreq := (frequency_tendsto a b).eventually (eventually_ge_atTop (s+2*E+2))
  filter_upwards [hcomp,firstHalf_angle_cap ha hb,hfreq,eventually_gt_atTop (2*k0)] with n hn hcap hlarge hindex
  intro hN
  let N := frequency a b n
  let eps := E/N^2
  let Y := scaledAngle a b ha hb n k0
  let f := scaledPhase a b ha hb n hN Y
  let g := ordinaryPhase a ha s
  have hk : k0<n := by omega
  have heps : 0<eps := by dsimp [eps]; positivity
  have hN1 : 1≤N := by dsimp [N]; linarith
  have hN2 : 2*Q≤N^2 := by
    have hh : 2*Q+1≤N := by dsimp [N,E] at *; linarith
    nlinarith [sq_nonneg (N-1)]
  have hepsN : eps≤1/N := by
    dsimp [eps]
    apply (div_le_div_iff₀ (sq_pos_of_pos hN) hN).mpr
    have hh : E≤N := by dsimp [N]; linarith
    nlinarith
  have heps1 : eps≤1 := hepsN.trans (div_le_self (by norm_num) hN1)
  have hroot : |Y-s|≤eps*s := by
    have hh := hn.2 k0 hindex
    change |Y-s|≤Q*s/N^2 at hh
    calc
      _ ≤ Q*s/N^2 := hh
      _ ≤ E*s/N^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by dsimp [E]; linarith : Q≤E) hs.le) (sq_nonneg N)
      _ = _ := by dsimp [eps]; ring
  have hrootHalf : |Y-s|≤s/2 := by
    have hh := hn.2 k0 hindex
    change |Y-s|≤Q*s/N^2 at hh
    have hratio : Q/N^2≤1/2 := (div_le_iff₀ (sq_pos_of_pos hN)).mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_right hratio hs.le
    exact hh.trans (by convert hm using 1 <;> ring)
  have hYlo : s/2≤Y := by linarith [(abs_le.mp hrootHalf).1]
  have hsCap : s/N≤3*Real.pi/4 := by
    have hsN : s≤N := by dsimp [N]; linarith
    have hh : s/N≤1 := (div_le_iff₀ hN).mpr (by simpa only [one_mul] using hsN)
    linarith [Real.pi_gt_three]
  have hbase := scaledAngle_zero ha hb hN hk
  have hYcap := hcap k0 hindex
  have hCeps : C/N^2≤eps := div_le_div_of_nonneg_right (by dsimp [E]; linarith) (sq_nonneg N)
  have hinitial := scaledPhase_initial_bound ha hb (fun t ht => (hpot t ht).1)
    hN hk hs hsCap hYlo hYcap (hCeps.trans heps1)
  have hinit : |f s-g s|≤B*eps*s := by
    have hg0 : g s=0 := (jacobi.Bessel.restoringState a ha).phase_self s
    rw [hg0,sub_zero]
    have hh : |s-Y|≤eps*s := by simpa only [abs_sub_comm] using hroot
    have hmul := mul_le_mul_of_nonneg_left hh hD.le
    have hBge : D≤B := by dsimp [B]; linarith
    exact hinitial.trans (hmul.trans (by nlinarith))
  intro x hx
  have htheta : ∀ t∈Icc s x,t/N∈Icc 0 (3*Real.pi/4) := by
    intro t ht
    exact ⟨(div_pos (hs.trans_le ht.1) hN).le,
      (div_le_iff₀ hN).mpr (ht.2.trans hx.2)⟩
  have hphys : ∀ t∈Icc s x,t∈Ioo 0 (N*Real.pi) := by
    intro t ht
    exact ⟨hs.trans_le ht.1,by nlinarith [ht.2.trans hx.2,mul_pos hN Real.pi_pos]⟩
  have heB : ∀ t∈Icc s x,|scaledRemainder a b N t|≤eps := by
    intro t ht
    change |regularPotential a b (t/N)/N^2|≤eps
    rw [abs_div,abs_of_pos (sq_pos_of_pos hN)]
    exact (div_le_div_of_nonneg_right (hpot (t/N) (htheta t ht)).1 (sq_nonneg N)).trans hCeps
  have he'B : ∀ t∈Icc s x,|scaledRemainderSlope a b N t|≤eps/N := by
    intro t ht
    change |deriv (regularPotential a b) (t/N)/N^3|≤eps/N
    rw [abs_div,abs_of_pos (by positivity : 0<N^3)]
    calc
      _ ≤ C/N^3 := div_le_div_of_nonneg_right (hpot (t/N) (htheta t ht)).2 (by positivity)
      _ ≤ E/N^3 := div_le_div_of_nonneg_right (by dsimp [E]; linarith) (by positivity)
      _ = _ := by dsimp [eps]; ring
  have hPinit : |scaledPrimitive a b N s|≤eps*s := by
    change |regularPrimitive a b (s/N)/N|≤eps*s
    rw [abs_div,abs_of_pos hN]
    have hR := regularPrimitive_linear a b C (fun t ht => (hpot t ht).1) ⟨(div_pos hs hN).le,hsCap⟩
    calc
      _ ≤ (C*(s/N))/N := div_le_div_of_nonneg_right hR hN.le
      _ ≤ (E*(s/N))/N := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by dsimp [E]; linarith : C≤E) (by positivity)) hN.le
      _ = _ := by dsimp [eps]; ring
  have h := phase_averaging (f := f) (g := g) (c := endpointCorrection a)
    (e := scaledRemainder a b N) (e' := scaledRemainderSlope a b N) (P := scaledPrimitive a b N)
    hs1 hsc hx.1 hN hx.2 heps hepsN hB
    (fun t ht => scaledPhase_hasDerivAt ha hb n hN hbase.1 (hphys t ht) hbase.2)
    (fun t ht => by
      simpa only [endpointCorrection] using
        (ordinaryPhase_hasDerivAt ha hs (hs.trans_le ht.1) (wave_positiveZero_zero ha k0)))
    (fun t ht => scaledRemainder_hasDerivAt a b (htheta t ht))
    (fun t ht => scaledPrimitive_hasDerivAt a b (htheta t ht)) heB he'B hinit hPinit
  convert h using 1
  dsimp [T,eps]
  ring

end
end jacobi.Jacobi
