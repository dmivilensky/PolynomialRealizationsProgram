import jacobi.Bessel.McMahonSquared

/-!
Article: jacobi, Proposition B.1.
The genuinely bounded original regular potential brackets each true
finite Jacobi angle between the same indexed Bessel zeros divided by
sqrt(N^2+C+1) and sqrt(N^2-C-1). An elementary denominator estimate gives
a uniform scaled-zero error, before the sharper phase correction is used.
Use: extracts a quantitative inverse-square error from the actual two strict Sturm frequency comparisons.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set jacobi.Bessel
set_option backward.isDefEq.respectTransparency false

/-- A strictly positive frequency perturbation has a controlled effect on every positive scaled zero.
Use: extracts a quantitative inverse-square error from the actual two strict Sturm frequency comparisons.
Article: jacobi, Proposition B.1.
Proof: multiply the scaled difference by D*(N+D). Its absolute value is
exactly j*|N^2-D^2|; the denominator is at least N^2/2. -/
theorem frequency_rescaling_error {N D j Q : ℝ} (hN : 0<N) (hD : 0<D)
    (hj : 0<j) (hhalf : N/2≤D) (hQ : |N^2-D^2|≤Q) :
    |N*(j/D)-j|≤2*Q*j/N^2 := by
  -- Difference of squares retains a full factor N+D, avoiding the loss of one inverse frequency.
  have he : (N*(j/D)-j)*(D*(N+D))=j*(N^2-D^2) := by
    field_simp [hD.ne']
    ring
  have heabs := congrArg abs he
  rw [abs_mul,abs_of_pos (mul_pos hD (add_pos hN hD)),abs_mul,abs_of_pos hj] at heabs
  have hd : N^2/2≤D*(N+D) := by nlinarith [mul_nonneg hD.le hD.le,mul_le_mul_of_nonneg_left hhalf hN.le]
  have hb : |N*(j/D)-j| *(N^2/2)≤j*Q := by
    calc
      _ ≤ |N*(j/D)-j| *(D*(N+D)) := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ = j*|N^2-D^2| := heabs
      _ ≤ j*Q := mul_le_mul_of_nonneg_left hQ hj.le
  apply (le_div_iff₀ (sq_pos_of_pos hN)).mpr
  nlinarith

/-- Actual Jacobi angles in a prescribed original prefix lie in the genuine two-sided Bessel frequency window.
Use: provides a uniform comparison for an increasing prefix, including the entire first half of every sufficiently large actual finite spectrum.
Article: jacobi, Proposition B.1.
Proof: use the true regular-potential bound on the full comparison interval.
Reverse comparison first puts the original Jacobi angles below its far
endpoint. Forward comparison then supplies the matching opposite bound;
canonical zero numbering in both directions was proved at the singular endpoint. -/
theorem finiteAngle_frequency_window {a b C : ℝ} (ha : -1<a) (hb : -1<b)
    (hC : 0<C) (hbound : ∀ t∈Icc 0 (3*Real.pi/4),|regularPotential a b t|≤C)
    {n K : ℕ} (hK : K<n) (hlarge : C+1<(frequency a b n)^2)
    (hcap : positiveZero a ha K/√((frequency a b n)^2-C-1)≤3*Real.pi/4) :
    ∀ k≤K,
      positiveZero a ha k/√((frequency a b n)^2+C+1)<finiteAngleAt a b ha hb n k ∧
      finiteAngleAt a b ha hb n k<positiveZero a ha k/√((frequency a b n)^2-C-1) := by
  -- Actual Bessel cap control first establishes the physical interval for the original finite angles, so no angle-location estimate is assumed.
  have hN : 0<frequency a b n := frequency_pos ha hb (by omega)
  have hL : 0<√((frequency a b n)^2-C-1) := Real.sqrt_pos.mpr (by linarith)
  have hU : 0<√((frequency a b n)^2+C+1) := Real.sqrt_pos.mpr (by positivity)
  have hR : 3*Real.pi/4<Real.pi := by linarith [Real.pi_pos]
  have hlow := angle_lt_bessel_zero ha hb hL hR hK hcap (by
    intro t ht
    rw [Real.sq_sqrt (by linarith : 0≤(frequency a b n)^2-C-1)]
    have hh := (abs_le.mp (hbound t ⟨ht.1.le,ht.2.le⟩)).1
    linarith)
  have hupp := bessel_zero_lt_angle ha hb hU hR hK ((hlow K le_rfl).le.trans hcap) (by
    intro t ht
    rw [Real.sq_sqrt (by positivity : 0≤(frequency a b n)^2+C+1)]
    have hh := (abs_le.mp (hbound t ⟨ht.1.le,ht.2.le⟩)).2
    linarith)
  exact fun k hk => ⟨hupp k hk,hlow k hk⟩

/-- The original scaled Jacobi zeros have an explicit inverse-square frequency error uniformly on every actual capped prefix.
Use: controls all first-half root locations and gaps in Proposition B.1 and aligns the true Bessel and Jacobi phase bases.
Article: jacobi, Proposition B.1.
Proof: the proved strict window brackets each actual angle. Both square
root frequencies have a squared difference C+1 from N; the smaller one
is at least N/2. The scalar rescaling bound then controls both sides. -/
theorem finiteAngle_frequency_error {a b C : ℝ} (ha : -1<a) (hb : -1<b)
    (hC : 0<C) (hbound : ∀ t∈Icc 0 (3*Real.pi/4),|regularPotential a b t|≤C)
    {n K : ℕ} (hK : K<n) (hlarge : 4*(C+1)≤(frequency a b n)^2)
    (hcap : positiveZero a ha K/√((frequency a b n)^2-C-1)≤3*Real.pi/4) :
    ∀ k≤K,|frequency a b n*finiteAngleAt a b ha hb n k-positiveZero a ha k|≤
      2*(C+1)*positiveZero a ha k/(frequency a b n)^2 := by
  -- This is a quantitative conclusion about the actual finite zero list, rather than a fixed-index limiting assertion.
  let N := frequency a b n
  let L := √(N^2-C-1)
  let U := √(N^2+C+1)
  have hN : 0<N := frequency_pos ha hb (by omega)
  have hstrict : C+1<N^2 := by dsimp [N]; linarith
  have hL : 0<L := Real.sqrt_pos.mpr (by linarith)
  have hU : 0<U := Real.sqrt_pos.mpr (by positivity)
  have hL2 : L^2=N^2-C-1 := Real.sq_sqrt (by linarith)
  have hU2 : U^2=N^2+C+1 := Real.sq_sqrt (by positivity)
  have hhalfL : N/2≤L := by nlinarith
  have hhalfU : N/2≤U := by nlinarith
  have hwindow := finiteAngle_frequency_window ha hb hC hbound hK hstrict hcap
  intro k hk
  have hlo := frequency_rescaling_error hN hU (positiveZero_properties ha k).1 hhalfU
    (show |N^2-U^2|≤C+1 by rw [hU2]; rw [show N^2-(N^2+C+1)= -(C+1) by ring,abs_neg,abs_of_pos (by positivity)])
  have hhi := frequency_rescaling_error hN hL (positiveZero_properties ha k).1 hhalfL
    (show |N^2-L^2|≤C+1 by rw [hL2]; rw [show N^2-(N^2-C-1)=C+1 by ring,abs_of_pos (by positivity)])
  have hww := hwindow k hk
  have hl := mul_lt_mul_of_pos_left hww.1 hN
  have hu := mul_lt_mul_of_pos_left hww.2 hN
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hlo).1],by linarith [(abs_le.mp hhi).2]⟩

end
end jacobi.Jacobi
