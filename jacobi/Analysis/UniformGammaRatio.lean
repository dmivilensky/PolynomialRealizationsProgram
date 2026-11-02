import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
Article: jacobi, Lemma C.1.
Uniform Gamma-ratio bounds follow from the community log-convexity
theorem and the exact Gamma recurrence. No uniform Stirling expansion
is assumed. The tail bounds cover every positive exponent in a bounded
interval with constants independent of the exponent and the index.
Use: applies the community Bohr--Mollerup bounds to the actual reference norm Gamma ratio.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Finset
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The true positive-axis logarithmic Gamma function has the exact additive recurrence.
Use: applies the community Bohr--Mollerup bounds to the actual reference norm Gamma ratio.
Article: jacobi, Lemma C.1.
Source: Euler's Gamma recurrence, mathlib Gamma.Basic.
Proof: take the real logarithm of the genuine positive Gamma recurrence and commute the two logarithm summands. -/
theorem logGamma_recurrence {y : ℝ} (hy : 0<y) :
    Real.log (Real.Gamma (y+1))=Real.log (Real.Gamma y)+Real.log y := by
  rw [Real.Gamma_add_one hy.ne',Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne',add_comm]

/-- Logarithmic Gamma growth over any bounded positive shift has an upper tangent-scale bound uniform in that shift.
Use: gives the uniform real Gamma-ratio tail bound behind complex reference norm estimates.
Article: jacobi, Lemma C.1.
Source: Bohr--Mollerup log-convexity, proved in mathlib.
Proof: the exact integer shift is a sum of increasing logarithms, each
at most its last logarithm. Convexity places every intermediate shift
under the chord joining zero and that integer shift. -/
theorem logGamma_shift_upper {n M : ℕ} (hn : 0<n) (hM : 0<M) {s : ℝ}
    (hs : 0≤s) (hsM : s≤M) :
    Real.log (Real.Gamma ((n:ℝ)+s))≤Real.log (Real.Gamma n)+s*Real.log ((n:ℝ)+M) := by
  -- The convexity argument uses one fixed integer shift for the entire exponent interval.
  let f : ℝ → ℝ := fun x => Real.log (Real.Gamma x)
  have hnp : 0<(n:ℝ) := by exact_mod_cast hn
  have hMp : 0<(M:ℝ) := by exact_mod_cast hM
  have hsum : (∑ j∈range M,Real.log ((n:ℝ)+j))≤(M:ℝ)*Real.log ((n:ℝ)+M) := by
    calc
      _ ≤ ∑ _j∈range M,Real.log ((n:ℝ)+M) := sum_le_sum (fun j hj =>
        Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_left (mem_range.mp hj).le n))
      _ = _ := by simp
  have hshift : f ((n:ℝ)+M)≤f n+(M:ℝ)*Real.log ((n:ℝ)+M) := by
    rw [Real.BohrMollerup.f_add_nat_eq (f := f) (fun {_} hy => logGamma_recurrence hy) hnp M]
    exact add_le_add_right hsum _
  have hconv := Real.convexOn_log_Gamma.2 hnp (by positivity : (0:ℝ)<(n:ℝ)+M)
    (show 0≤1-s/(M:ℝ) by exact sub_nonneg.mpr ((div_le_one hMp).mpr hsM))
    (div_nonneg hs hMp.le) (by ring : (1-s/(M:ℝ))+s/(M:ℝ)=1)
  have hpoint : (1-s/(M:ℝ))*(n:ℝ)+(s/(M:ℝ))*((n:ℝ)+M)=(n:ℝ)+s := by
    field_simp [hMp.ne']
    ring
  simp only [smul_eq_mul,hpoint] at hconv
  change f ((n:ℝ)+s)≤f n+s*Real.log ((n:ℝ)+M)
  calc
    _ ≤ (1-s/(M:ℝ))*f n+(s/(M:ℝ))*f ((n:ℝ)+M) := hconv
    _ ≤ (1-s/(M:ℝ))*f n+(s/(M:ℝ))*(f n+(M:ℝ)*Real.log ((n:ℝ)+M)) := by
      have hh := mul_le_mul_of_nonneg_left hshift (div_nonneg hs hMp.le)
      linarith
    _ = _ := by field_simp [hMp.ne']; ring

/-- The normalized real Gamma ratio has two positive bounds uniform over every bounded positive exponent interval and every index at least two.
Use: the original complex reference norm scale is controlled without
assuming a uniform special-function asymptotic expansion.
Article: jacobi, Lemma C.1.
Source: Bohr--Mollerup log-convexity and Euler's Gamma recurrence.
Proof: the actual logarithmic Gamma shift lies between s*log(n-1)
and s*log(n+M), up to the same log Gamma(n). Normalize by the genuine
index power. The elementary ratios (n+1)/(n-1), (n+1)/n and
(n+M)/(n+1) are at most three, two and M+1 respectively. These give
one logarithmic bound independent of s and n; exponentiate it. -/
theorem real_gamma_ratio_tail_bound {S : ℝ} (hS : 0<S) :
    ∃ H : ℝ,0<H ∧ ∀ s : ℝ,0<s → s≤S → ∀ n : ℕ,2≤n →
      Real.exp (-H)≤Real.Gamma ((n:ℝ)+1)/Real.Gamma ((n:ℝ)+s)*(n+1:ℝ)^(s-1) ∧
      Real.Gamma ((n:ℝ)+1)/Real.Gamma ((n:ℝ)+s)*(n+1:ℝ)^(s-1)≤Real.exp H := by
  -- One integer upper shift and one constant work for the entire moving exponent interval.
  obtain ⟨M,hMS⟩ := exists_nat_gt S
  have hM : 0<M := by exact_mod_cast hS.trans hMS
  let H : ℝ := S*Real.log (M+1:ℝ)+Real.log 2+S*Real.log 3+1
  have hlM : 0≤Real.log (M+1:ℝ) := Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) M])
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hl3 : 0≤Real.log 3 := Real.log_nonneg (by norm_num)
  have hH : 0<H := by dsimp [H]; positivity
  refine ⟨H,hH,fun s hs hsS n hn => ?_⟩
  have hn2 : (2:ℝ)≤n := by exact_mod_cast hn
  have hnp : 0<(n:ℝ) := by linarith
  have hn1 : 0<(n+1:ℝ) := by positivity
  have hnm : 0<(n:ℝ)-1 := by linarith
  have hlo := Real.BohrMollerup.f_add_nat_ge (f := fun x => Real.log (Real.Gamma x))
    Real.convexOn_log_Gamma (fun {_} hy => logGamma_recurrence hy) hn hs
  have hup := logGamma_shift_upper (by omega : 0<n) hM hs.le (hsS.trans hMS.le)
  have hrec := logGamma_recurrence hnp
  have h3 : Real.log (n+1:ℝ)≤Real.log 3+Real.log ((n:ℝ)-1) := by
    rw [← Real.log_mul (by norm_num : (3:ℝ)≠0) hnm.ne']
    exact Real.log_le_log hn1 (by linarith)
  have h2 : Real.log (n+1:ℝ)≤Real.log 2+Real.log (n:ℝ) := by
    rw [← Real.log_mul (by norm_num : (2:ℝ)≠0) hnp.ne']
    exact Real.log_le_log hn1 (by linarith)
  have hMlog : Real.log ((n:ℝ)+M)≤Real.log (M+1:ℝ)+Real.log (n+1:ℝ) := by
    rw [← Real.log_mul (by positivity : (M+1:ℝ)≠0) hn1.ne']
    apply Real.log_le_log (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hmono : Real.log (n:ℝ)≤Real.log (n+1:ℝ) := Real.log_le_log hnp (by linarith)
  have h3mul : s*(Real.log (n+1:ℝ)-Real.log ((n:ℝ)-1))≤S*Real.log 3 :=
    (mul_le_mul_of_nonneg_left (by linarith : Real.log (n+1:ℝ)-Real.log ((n:ℝ)-1)≤Real.log 3) hs.le).trans
      (mul_le_mul_of_nonneg_right hsS hl3)
  have hMmul : s*(Real.log ((n:ℝ)+M)-Real.log (n+1:ℝ))≤S*Real.log (M+1:ℝ) :=
    (mul_le_mul_of_nonneg_left (by linarith : Real.log ((n:ℝ)+M)-Real.log (n+1:ℝ)≤Real.log (M+1:ℝ)) hs.le).trans
      (mul_le_mul_of_nonneg_right hsS hlM)
  let L : ℝ := Real.log (Real.Gamma ((n:ℝ)+1))-Real.log (Real.Gamma ((n:ℝ)+s))+
    (s-1)*Real.log (n+1:ℝ)
  have hL : -H≤L ∧ L≤H := by
    dsimp [L,H]
    constructor <;> nlinarith [mul_nonneg hS.le hlM,mul_nonneg hS.le hl3]
  have he : Real.exp L=Real.Gamma ((n:ℝ)+1)/Real.Gamma ((n:ℝ)+s)*(n+1:ℝ)^(s-1) := by
    dsimp [L]
    rw [Real.exp_add,Real.exp_sub,Real.exp_log (Real.Gamma_pos_of_pos hn1),
      Real.exp_log (Real.Gamma_pos_of_pos (by positivity : (0:ℝ)<(n:ℝ)+s)),Real.rpow_def_of_pos hn1]
    congr 2
    ring
  rw [← he]
  exact ⟨Real.exp_le_exp.mpr hL.1,Real.exp_le_exp.mpr hL.2⟩

end
end jacobi.Analysis
