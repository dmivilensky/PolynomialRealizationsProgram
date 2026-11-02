import jacobi.Variational.FredholmKlein
import jacobi.Variational.GreenDiagonal
import jacobi.Young.PotentialRegularity
import jacobi.Variational.SecondKKT

/-!
Article: jacobi, Theorem D.7.
The actual resolvent diagonal is bounded by the original exponential
potential with an explicit spectral margin. This proves its genuine free
limit at both infinities for every finite-energy L1 density, before any
optimizer equation or profile shape is imposed.
Source: complete eigenbasis quadratic expansions and the already proved H1 potential decay.
Use: forces the optimizing Green diagonal to approach the free value at infinity.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young jacobi.Continuum
open chebyshev2.Continuum
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual resolvent quadratic remainder is dominated by the actual feature operator with its explicit pole margin.
Use: forces the optimizing Green diagonal to approach the free value at infinity.
Article: jacobi, Theorem D.7.
Proof: in the actual complete eigenbasis, compare s*lambda/(1-s*lambda)
with s*lambda/(1-s*lambda_top), then sum the nonnegative squared coefficients.
Both quadratic expansions are actual convergent series. -/
theorem resolvent_quadratic_bound (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (v : FeatureSpace) :
    inner ℝ v (m.fredholmResolvent s hs hp v)-‖v‖^2≤
      (s/(1-s*observe m .top))*inner ℝ v (densityOperator m.value v) := by
  -- The same complete actual basis is retained on both sides, including its kernel.
  let D := densitySpectralData m.integrable m.nonneg
  have htop := sub_pos.mpr hp
  have hR := eigenbasis_quadratic_hasSum D.basis (m.fredholmResolvent s hs hp)
    (fun i => m.fredholmResolvent_basis hs hp i) v
  have hI := basis_hasSum_sq D.basis v
  have hK := eigenbasis_quadratic_hasSum D.basis (densityOperator m.value) D.equation v
  apply hasSum_le _ (hR.sub hI) (hK.mul_left (s/(1-s*observe m .top)))
  intro i
  have he : D.eig i≤observe m .top := by
    have hh := eigenbasis_le_top D i
    rw [density_kernel_eigenvalue_eq m.integrable m.nonneg D] at hh
    exact hh
  have hden : 0<1-s*D.eig i := by nlinarith [mul_le_mul_of_nonneg_left he hs]
  have hscalar : (1-s*D.eig i)⁻¹-1≤s/(1-s*observe m .top)*D.eig i := by
    have hle := div_le_div_of_nonneg_left (mul_nonneg hs (D.nonneg i)) htop
      (show 1-s*observe m .top≤1-s*D.eig i by nlinarith [mul_le_mul_of_nonneg_left he hs])
    have hid : (1-s*D.eig i)⁻¹-1=s*D.eig i/(1-s*D.eig i) := by field_simp; ring
    rw [hid]
    convert hle using 1
    ring
  nlinarith [mul_le_mul_of_nonneg_right hscalar (sq_nonneg (inner ℝ (D.basis i) v))]

/-- The original feature quadratic form is exactly the actual exponent-two Green potential.
Use: applies the reused H1 convolution decay to the genuine Fredholm inverse diagonal.
Article: jacobi, Theorem D.7.
Proof: the actual feature pairing gives exp(-abs(x-y)) twice; combine the two exponentials inside the actual integral. -/
theorem feature_potential (m : Density) (x : ℝ) :
    inner ℝ (feature x) (densityOperator m.value (feature x))=potential m x := by
  -- The actual reproducing feature pairing gives the squared exponential potential kernel.
  rw [densityOperator_inner m.integrable,potential_kernel]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [feature_inner]
    rw [← exp_add]
    congr 2
    rw [abs_sub_comm y x]
    ring

/-- The actual Fredholm Green diagonal has an explicit original-potential bound at every point.
Use: proves its true free limit before deriving the conserved optimizer equation.
Article: jacobi, Theorem D.7.
Proof: apply the proved actual quadratic comparison to a unit point feature and identify the exact feature potential. -/
theorem green_diagonal_bound (m : Density) {s : ℝ} (hs : 0≤s) (hp : s*observe m .top<1) (x : ℝ) :
    0≤2*m.greenDiagonal s hs hp x-1 ∧
      2*m.greenDiagonal s hs hp x-1≤s/(1-s*observe m .top)*potential m x := by
  have hlow := (m.fredholmGreen_diagonal hs hp x).1
  change (1/2:ℝ)≤(1/2)*inner ℝ (m.fredholmResolvent s hs hp (feature x)) (feature x) at hlow
  rw [real_inner_comm] at hlow
  have hh := resolvent_quadratic_bound m.toL1Source hs hp (feature x)
  rw [feature_norm,one_pow,feature_potential m] at hh
  unfold L1Source.greenDiagonal L1Source.fredholmGreen
  rw [real_inner_comm]
  constructor <;> linarith

/-- Every actual nonzero source at positive subcritical coupling has diagonal strictly above the free value everywhere.
Use: excludes the spurious free turning state from every nonzero Fredholm optimizing trajectory.
Article: jacobi, Theorem D.7.
Proof: retain the first two nonnegative terms of the genuine Neumann
series. They give 2*g>=1+s*W_2, and the original nonzero density has W_2>0 everywhere. -/
theorem green_diagonal_strict (m : Density) (hm : 0<m.mass) {s : ℝ} (hs : 0<s)
    (hp : s*observe m .top<1) (x : ℝ) : (1/2:ℝ)<m.greenDiagonal s hs.le hp x := by
  -- The positive first operator power supplies strictness; no positivity-improving resolvent principle is assumed.
  have hv := (ContinuousLinearMap.apply ℝ FeatureSpace (feature x)).hasSum
    (m.fredholmResolvent_hasSum hs.le hp)
  have hi := (innerSL ℝ (feature x)).hasSum hv
  change HasSum (fun n : ℕ => inner ℝ (feature x)
    (((s • densityOperator m.value)^n) (feature x)))
    (inner ℝ (feature x) (m.fredholmResolvent s hs.le hp (feature x))) at hi
  have hb := hi.summable.sum_le_tsum ({0,1} : Finset ℕ) (fun n _ => m.feature_power_nonneg hs.le n x x)
  rw [hi.tsum_eq] at hb
  simp only [Finset.sum_insert,Finset.mem_singleton,zero_ne_one,not_false_eq_true,Finset.sum_singleton,
    pow_zero,one_apply_eq_self,pow_one,smul_apply,real_inner_smul_right,feature_inner,
    sub_self,abs_zero,neg_zero,exp_zero,feature_potential m] at hb
  have hpos := mul_pos hs (potential_pos m hm x)
  change (1/2:ℝ)<(1/2)*inner ℝ (m.fredholmResolvent s hs.le hp (feature x)) (feature x)
  rw [real_inner_comm]
  linarith

/-- The actual inverse Green diagonal approaches its free value at both infinities.
Use: fixes the first-integral constant of every genuine Fredholm optimizer.
Article: jacobi, Theorem D.7.
Proof: the exact original-potential bound squeezes the nonnegative diagonal
excess to zero; the original H1 potential decays at both ends. -/
theorem green_diagonal_limits (m : Density) {s : ℝ} (hs : 0≤s) (hp : s*observe m .top<1) :
    Tendsto (m.greenDiagonal s hs hp) atTop (𝓝 (1/2:ℝ)) ∧
      Tendsto (m.greenDiagonal s hs hp) atBot (𝓝 (1/2:ℝ)) := by
  -- No Jost or optimizer-profile asymptotic is assumed in this squeeze.
  have he (l : Filter ℝ) (h : Tendsto (potential m) l (𝓝 0)) :
      Tendsto (m.greenDiagonal s hs hp) l (𝓝 (1/2:ℝ)) := by
    have hh : Tendsto (fun x => 2*m.greenDiagonal s hs hp x-1) l (𝓝 0) :=
      squeeze_zero (fun x => (green_diagonal_bound m hs hp x).1)
        (fun x => (green_diagonal_bound m hs hp x).2) (by simpa only [mul_zero] using h.const_mul (s/(1-s*observe m .top)))
    have ht := (hh.add_const 1).div_const 2
    convert ht using 1
    · funext x; ring
    · norm_num
  exact ⟨he atTop (potential_sobolev m).tendsto_zero.1,he atBot (potential_sobolev m).tendsto_zero.2⟩

end
end jacobi.Fredholm
