import polyak.Spectral.AnalyticLimit
import polyak.Boundary.Tail
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
Article: Appendix A, compactified normalized lag symbols.
Use: normalized real lag polynomials admit holomorphic extensions with a
uniform geometric limit on a compact complex neighborhood of the frequency interval.
Proof: Euler bounds and the exact radial normalization.
-/

namespace polyak.Spectral
noncomputable section
open Set Filter
open scoped Topology

/-- Article: a compact complex window around all physical angles. -/
def lagWindow (s : ℝ) : Set ℂ :=
  Metric.closedBall 0 (Real.pi+1) ∩ {z | |z.im| ≤ s/2}

/-- Article: compactness of the complex window. -/
theorem isCompact_lagWindow (s : ℝ) : IsCompact (lagWindow s) :=
  (isCompact_closedBall (0 : ℂ) (Real.pi+1)).inter_right
    (isClosed_le Complex.continuous_im.abs continuous_const)

/-- Article: every physical angle has a complex neighborhood inside the window. -/
theorem real_mem_interior_lagWindow {s ω : ℝ} (hs : 0 < s) (hω : ω ∈ Icc 0 Real.pi) :
    (ω : ℂ) ∈ interior (lagWindow s) := by
  let U : Set ℂ := {z | ‖z‖ < Real.pi+1 ∧ |z.im| < s/2}
  have hU : IsOpen U := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt Complex.continuous_im.abs continuous_const)
  have hUK : U ⊆ lagWindow s := by
    intro z hz
    exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hz.1.le,hz.2.le⟩
  apply (interior_mono hUK)
  rw [hU.interior_eq]
  constructor
  · simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hω.1] using
      lt_of_le_of_lt hω.2 (lt_add_one Real.pi)
  · simpa using half_pos hs

/-- Article: Euler bound for complex cosines in a horizontal strip. -/
theorem norm_complex_cos_le_exp (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h₁ : ‖Complex.exp (z*Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  have h₂ : ‖Complex.exp (-z*Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  unfold Complex.cos
  rw [norm_div, Complex.norm_ofNat]
  exact (div_le_div_of_nonneg_right ((norm_add_le _ _).trans (add_le_add h₁ h₂))
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

/-- Article: Euler bound for complex sines in a horizontal strip. -/
theorem norm_complex_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h₁ : ‖Complex.exp (z*Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  have h₂ : ‖Complex.exp (-z*Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  unfold Complex.sin
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  exact (div_le_div_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add h₂ h₁))
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

/-- Article: the radial decay of the n+1 normalized lag. -/
def lagRadial (s : ℝ) (n : ℕ) : ℝ := Real.exp (-((n+1 : ℕ) : ℝ)*s)

/-- Article: the normalized lag at infinity. -/
def complexGap (u : ℝ) (z : ℂ) : ℂ := 1-Complex.cos z^2-(u : ℂ)^2

/-- Article: the exact holomorphic normalized lag; δ=1 is lower and δ=-1 is upper. -/
def complexLag (u s δ : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (complexGap u z*(1+(lagRadial s n : ℂ)^2-
      2*(lagRadial s n : ℂ)*Complex.cos ((n+1 : ℕ)*z))-
    4*(δ : ℂ)*(u : ℂ)*(lagRadial s n : ℂ)*Complex.sin z*
      Complex.sin ((n+1 : ℕ)*z))/(1-(lagRadial s n : ℂ)^2)

/-- Article: holomorphy of every finite normalized lag. -/
theorem differentiable_complexLag (u s δ : ℝ) (n : ℕ) :
    Differentiable ℂ (complexLag u s δ n) := by
  unfold complexLag complexGap
  fun_prop

/-- Article: holomorphy of the limiting minimizer symbol. -/
theorem differentiable_complexGap (u : ℝ) : Differentiable ℂ (complexGap u) := by
  unfold complexGap
  fun_prop

/-- Article: positivity and the uniform upper bound for each radial coefficient. -/
theorem lagRadial_bounds {s : ℝ} (hs : 0 < s) (n : ℕ) :
    0 < lagRadial s n ∧ lagRadial s n ≤ Real.exp (-s) ∧ Real.exp (-s) < 1 := by
  refine ⟨Real.exp_pos _,Real.exp_le_exp.mpr ?_,?_⟩
  · have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith
  · exact Real.exp_lt_one_iff.mpr (neg_neg_iff_pos.mpr hs)

/-- Article: the radial normalization never divides by zero. -/
theorem lagRadial_denominator_pos {s : ℝ} (hs : 0 < s) (n : ℕ) :
    0 < 1-lagRadial s n^2 := by
  obtain ⟨ha,hab,hb⟩ := lagRadial_bounds hs n
  nlinarith

/-- Article: a uniform bound on the limiting gap in a closed horizontal strip. -/
theorem norm_complexGap_le (u h : ℝ) {z : ℂ} (hz : |z.im| ≤ h) :
    ‖complexGap u z‖ ≤ 1+Real.exp h^2+u^2 := by
  have hc := (norm_complex_cos_le_exp z).trans (Real.exp_le_exp.mpr hz)
  calc
    _ ≤ ‖(1 : ℂ)-Complex.cos z^2‖+‖(u : ℂ)^2‖ := norm_sub_le _ _
    _ ≤ (‖(1 : ℂ)‖+‖Complex.cos z^2‖)+‖(u : ℂ)^2‖ := by gcongr; exact norm_sub_le _ _
    _ = 1+‖Complex.cos z‖^2+u^2 := by simp [norm_pow, Real.norm_eq_abs]
    _ ≤ _ := by gcongr

/-- Article: uniform geometric convergence of the normalized lag symbol.
Use: the estimate holds also at complex angles and is independent of the real part. -/
theorem norm_complexLag_sub_gap_le {s h δ : ℝ} (hs : 0 < s) (hh : 0 ≤ h)
    (hδ : |δ| ≤ 1) (u : ℝ) (n : ℕ) {z : ℂ} (hz : |z.im| ≤ h) :
    ‖complexLag u s δ n z-complexGap u z‖ ≤
      ((4*(1+Real.exp h^2+u^2)+4*|u| *Real.exp h)/(1-Real.exp (-s)^2))*
        Real.exp (h-s)^((n+1 : ℕ)) := by
  let a := lagRadial s n
  let b := Real.exp (-s)
  let N : ℝ := (n+1 : ℕ)
  let E := Real.exp (N*h)
  let M := 1+Real.exp h^2+u^2
  obtain ⟨ha,hab,hb⟩ := lagRadial_bounds hs n
  have hap : 0 < a := ha
  have hbp : 0 < b := Real.exp_pos _
  have hD : 0 < 1-b^2 := by dsimp [b] at *; nlinarith
  have ha1 : a ≤ 1 := hab.trans hb.le
  have hN : 0 ≤ N := by positivity
  have hN' : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by positivity
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (mul_nonneg hN hh)
  have haE : a^2 ≤ a*E := by nlinarith
  have hden : 0 < 1-a^2 := lagRadial_denominator_pos hs n
  have hdenle : 1-b^2 ≤ 1-a^2 := by nlinarith
  have hg : ‖complexGap u z‖ ≤ M := norm_complexGap_le u h hz
  have hc : ‖Complex.cos ((n+1 : ℕ)*z)‖ ≤ E := by
    apply (norm_complex_cos_le_exp _).trans
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
      abs_mul, abs_of_nonneg hN']
    exact mul_le_mul_of_nonneg_left hz hN
  have hsn : ‖Complex.sin ((n+1 : ℕ)*z)‖ ≤ E := by
    apply (norm_complex_sin_le_exp _).trans
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
      abs_mul, abs_of_nonneg hN']
    exact mul_le_mul_of_nonneg_left hz hN
  have hsz : ‖Complex.sin z‖ ≤ Real.exp h :=
    (norm_complex_sin_le_exp _).trans (Real.exp_le_exp.mpr hz)
  have he : complexLag u s δ n z-complexGap u z =
      (complexGap u z*(2*(a : ℂ)^2-2*(a : ℂ)*Complex.cos ((n+1 : ℕ)*z))-
        4*(δ : ℂ)*(u : ℂ)*(a : ℂ)*Complex.sin z*Complex.sin ((n+1 : ℕ)*z))/
          (1-(a : ℂ)^2) := by
    have hd : (1-(a : ℂ)^2) ≠ 0 := by exact_mod_cast ne_of_gt hden
    dsimp only [complexLag,a]
    dsimp only [a] at hd
    field_simp [hd]
    ring
  have hnormden : ‖(1 : ℂ)-(a : ℂ)^2‖ = 1-a^2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hden]
  have hfirst : ‖(2 : ℂ)*(a : ℂ)^2-2*(a : ℂ)*Complex.cos ((n+1 : ℕ)*z)‖ ≤
      2*a^2+2*a*E := by
    calc
      _ ≤ ‖(2 : ℂ)*(a : ℂ)^2‖+‖(2 : ℂ)*(a : ℂ)*Complex.cos ((n+1 : ℕ)*z)‖ := norm_sub_le _ _
      _ = 2*a^2+2*a*‖Complex.cos ((n+1 : ℕ)*z)‖ := by
        simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,
          Real.norm_eq_abs,abs_of_pos hap]
      _ ≤ _ := by gcongr
  have hsecond : ‖(4 : ℂ)*(δ : ℂ)*(u : ℂ)*(a : ℂ)*Complex.sin z*
      Complex.sin ((n+1 : ℕ)*z)‖ ≤ 4*|u| *a*Real.exp h*E := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hap]
    calc
      _ ≤ 4*1*|u| *a*Real.exp h*E := by gcongr
      _ = _ := by ring
  have hnum : ‖complexGap u z*(2*(a : ℂ)^2-2*(a : ℂ)*Complex.cos ((n+1 : ℕ)*z))-
      4*(δ : ℂ)*(u : ℂ)*(a : ℂ)*Complex.sin z*Complex.sin ((n+1 : ℕ)*z)‖ ≤
      (4*M+4*|u| *Real.exp h)*(a*E) := by
    calc
      _ ≤ ‖complexGap u z‖*‖(2 : ℂ)*(a : ℂ)^2-2*(a : ℂ)*Complex.cos ((n+1 : ℕ)*z)‖+
          ‖(4 : ℂ)*(δ : ℂ)*(u : ℂ)*(a : ℂ)*Complex.sin z*Complex.sin ((n+1 : ℕ)*z)‖ := by
        exact (norm_sub_le
          (complexGap u z*(2*(a : ℂ)^2-2*(a : ℂ)*Complex.cos ((n+1 : ℕ)*z)))
          (4*(δ : ℂ)*(u : ℂ)*(a : ℂ)*Complex.sin z*Complex.sin ((n+1 : ℕ)*z))).trans_eq
            (by rw [norm_mul])
      _ ≤ M*(2*a^2+2*a*E)+4*|u| *a*Real.exp h*E := by gcongr
      _ ≤ _ := by
        have hM : 0 ≤ M := by dsimp [M]; positivity
        nlinarith
  have hpow : a*E = Real.exp (h-s)^((n+1 : ℕ)) := by
    rw [← Real.exp_nat_mul]
    dsimp [a,E,lagRadial,N]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he,norm_div,hnormden]
  calc
    _ ≤ ((4*M+4*|u| *Real.exp h)*(a*E))/(1-a^2) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ ≤ ((4*M+4*|u| *Real.exp h)*(a*E))/(1-b^2) :=
      div_le_div_of_nonneg_left (by positivity) hD hdenle
    _ = _ := by rw [hpow]; dsimp [M,b]; ring

/-- Article: the closed complex frequency window is a compact carrier. -/
instance compactSpace_lagWindow (s : ℝ) : CompactSpace (lagWindow s) :=
  isCompact_iff_compactSpace.mp (isCompact_lagWindow s)

/-- Article: finite normalized lag as a continuous function on the complex window. -/
def complexLagMap (u s δ : ℝ) (n : ℕ) : C(lagWindow s,ℂ) :=
  ⟨fun z => complexLag u s δ n z,
    (differentiable_complexLag u s δ n).continuous.comp continuous_subtype_val⟩

/-- Article: minimizer limit as a continuous function on the complex window. -/
def complexGapMap (u s : ℝ) : C(lagWindow s,ℂ) :=
  ⟨fun z => complexGap u z,(differentiable_complexGap u).continuous.comp continuous_subtype_val⟩

/-- Article: uniform convergence on a complex neighborhood of the full frequency interval. -/
theorem tendsto_complexLagMap {s δ : ℝ} (hs : 0 < s) (hδ : |δ| ≤ 1) (u : ℝ) :
    Tendsto (complexLagMap u s δ) atTop (𝓝 (complexGapMap u s)) := by
  let B := (4*(1+Real.exp (s/2)^2+u^2)+4*|u| *Real.exp (s/2))/(1-Real.exp (-s)^2)
  let θ := Real.exp (s/2-s)
  have hb := (lagRadial_bounds hs 0).2.2
  have hD : 0 < 1-Real.exp (-s)^2 := by nlinarith [Real.exp_pos (-s)]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hθ0 : 0 ≤ θ := (Real.exp_pos _).le
  have hθ1 : θ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hnorm (n : ℕ) : ‖complexLagMap u s δ n-complexGapMap u s‖ ≤ B*θ^(n+1) := by
    apply (ContinuousMap.norm_le _ (mul_nonneg hB (pow_nonneg hθ0 _))).mpr
    intro z
    exact norm_complexLag_sub_gap_le hs (half_pos hs).le hδ u n z.property.2
  have hlim : Tendsto (fun n : ℕ => B*θ^(n+1)) atTop (𝓝 0) := by
    simpa only [pow_succ,mul_zero,zero_mul] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const θ).const_mul B
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) hnorm hlim

/-- Article: the normalized lag sequence extends continuously to the lag at infinity. -/
def compactifiedLagMap (u s δ : ℝ) (hs : 0 < s) (hδ : |δ| ≤ 1) :
    C(OnePoint ℕ,C(lagWindow s,ℂ)) :=
  OnePoint.continuousMapMkNat (complexLagMap u s δ) (complexGapMap u s)
    (tendsto_complexLagMap hs hδ u)

/-- Article: compactness of the actual normalized lag family including minimizer limits. -/
theorem isCompact_normalizedLagRange (u s δ : ℝ) (hs : 0 < s) (hδ : |δ| ≤ 1) :
    IsCompact (range (compactifiedLagMap u s δ hs hδ)) :=
  isCompact_range (compactifiedLagMap u s δ hs hδ).continuous

/-- Article: exact radial normalization of cosh and sinh. -/
theorem lagRadial_hyperbolic (s : ℝ) (n : ℕ) :
    2*lagRadial s n*Real.cosh ((n+1 : ℕ)*s) = 1+lagRadial s n^2 ∧
    2*lagRadial s n*Real.sinh ((n+1 : ℕ)*s) = 1-lagRadial s n^2 := by
  have he : lagRadial s n*Real.exp ((n+1 : ℕ)*s)=1 := by
    unfold lagRadial
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hn : Real.exp (-((n+1 : ℕ)*s))=lagRadial s n := by
    unfold lagRadial
    congr 1
    ring
  rw [Real.cosh_eq,Real.sinh_eq,hn]
  constructor <;> nlinarith [he]

/-- Article: normalized holomorphic extension agrees with the original hyperbolic lag. -/
theorem complexLag_hyperbolic (u s δ : ℝ) (n : ℕ) (hs : 0 < s) (z : ℂ) :
    complexLag u s δ n z =
      (complexGap u z*((Real.cosh ((n+1 : ℕ)*s) : ℂ)-Complex.cos ((n+1 : ℕ)*z))-
        2*(δ : ℂ)*(u : ℂ)*Complex.sin z*Complex.sin ((n+1 : ℕ)*z))/
          (Real.sinh ((n+1 : ℕ)*s) : ℂ) := by
  let a := lagRadial s n
  have hd : (1-(a : ℂ)^2) ≠ 0 := by exact_mod_cast ne_of_gt (lagRadial_denominator_pos hs n)
  have hsp : 0 < Real.sinh ((n+1 : ℕ)*s) := Real.sinh_pos_iff.mpr (by positivity)
  have hsn : (Real.sinh ((n+1 : ℕ)*s) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hsp
  have hh := lagRadial_hyperbolic s n
  have hc : 2*(a : ℂ)*(Real.cosh ((n+1 : ℕ)*s) : ℂ)=1+(a : ℂ)^2 := by
    exact_mod_cast hh.1
  have hsi : 2*(a : ℂ)*(Real.sinh ((n+1 : ℕ)*s) : ℂ)=1-(a : ℂ)^2 := by
    exact_mod_cast hh.2
  unfold complexLag
  change _/(1-(a : ℂ)^2) = _
  apply (div_eq_div_iff hd hsn).mpr
  rw [← hc,← hsi]
  ring

/-- Article: exact real trace of the complex normalized symbol. -/
theorem complexLag_real (u s δ ω : ℝ) (n : ℕ) (hs : 0 < s) :
    complexLag u s δ n (ω : ℂ) =
      (((1-Real.cos ω^2-u^2)*(Real.cosh ((n+1 : ℕ)*s)-Real.cos ((n+1 : ℕ)*ω))-
        2*δ*u*Real.sin ω*Real.sin ((n+1 : ℕ)*ω))/Real.sinh ((n+1 : ℕ)*s) : ℝ) := by
  rw [complexLag_hyperbolic u s δ n hs]
  have hc : ((n+1 : ℕ) : ℂ)*(ω : ℂ)=(((n+1 : ℕ) : ℝ)*ω : ℝ) := by push_cast; rfl
  rw [hc]
  simp only [complexGap,← Complex.ofReal_cos,← Complex.ofReal_sin]
  push_cast
  ring

/-- Article: the complex extension on cosine coordinates is exactly the actual normalized lag. -/
theorem complexLag_arccos (u s δ : ℝ) (n : ℕ) (hs : 0 < s) (c : Frequency) :
    complexLag u s δ n (Real.arccos c : ℂ) =
      ((lagA u s (n+1) c-δ*lagB u (n+1) c)/Real.sinh ((n+1 : ℕ)*s) : ℝ) := by
  rw [complexLag_real u s δ (Real.arccos c) n hs,
    Real.cos_arccos c.property.1 c.property.2, Boundary.lagB_trig u (n+1) (by omega) c]
  congr 1
  unfold lagA lagD g
  rw [Waves.chebT_arccos]
  ring

end
end polyak.Spectral
