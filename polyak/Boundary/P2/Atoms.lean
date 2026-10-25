import polyak.Certificates.P2Signs
import polyak.Certificates.P2Identities
import polyak.Waves.Finite

/-!
Article: Theorem p2arc(ii)–(iv), the actual atom roots and probability weights.
Use: every frequency lies strictly inside (-1,1), including the zero-weight spiral endpoint.
Proof: exact quadratic factorization, source sign certificates and the cubic endpoint equation.
-/

namespace polyak.Boundary.P2
noncomputable section
open Spectral
open scoped NNReal

/-- Article: the two atom roots are distinct on the entire sign interval. -/
theorem discriminant_pos {z : ℝ} (hz : z∈parameterInterval) : 0 < atomA z^2-4*atomB z := by
  have hb := b_negative_positive z hz
  nlinarith [sq_nonneg (atomA z)]

/-- Article: factorization of the actual quadratic, with the selected ordered square root. -/
theorem atomPolynomial_factor {z : ℝ} (hz : z∈parameterInterval) (c : ℝ) :
    atomPolynomial z c=(c-x z)*(c-y z) := by
  have hs := Real.sq_sqrt (discriminant_pos hz).le
  unfold atomPolynomial x y
  nlinarith [hs]

/-- Article: x<0<y and x<y throughout J. -/
theorem roots_order {z : ℝ} (hz : z∈parameterInterval) : x z<0 ∧ 0<y z ∧ x z<y z := by
  have hb := b_negative_positive z hz
  have habs : |atomA z|<Real.sqrt (atomA z^2-4*atomB z) := by
    rw [←Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have hs := abs_lt.mp habs
  dsimp [x,y]
  constructor
  · linarith [hs.1]
  · constructor
    · linarith [hs.2]
    · have hp := Real.sqrt_pos.mpr (discriminant_pos hz)
      linarith

/-- Article: the smaller atom is a genuine root. -/
theorem atomPolynomial_x {z : ℝ} (hz : z∈parameterInterval) : atomPolynomial z (x z)=0 := by
  rw [atomPolynomial_factor hz]
  ring

/-- Article: the larger atom is a genuine root. -/
theorem atomPolynomial_y {z : ℝ} (hz : z∈parameterInterval) : atomPolynomial z (y z)=0 := by
  rw [atomPolynomial_factor hz]
  ring

/-- Article: certified strict rational enclosure of the smaller atom. -/
theorem x_bounds {z : ℝ} (hz : z∈parameterInterval) : -101/200 < x z ∧ x z < -12/25 := by
  have hy := (roots_order hz).2.1
  have ho := root_minus_outer_positive z hz
  have hi := root_minus_inner_positive z hz
  rw [atomPolynomial_factor hz] at ho hi
  constructor
  · by_contra h
    have hprod : (-101/200-x z)*(-101/200-y z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  · rcases mul_neg_iff.mp (show (-12/25-x z)*(-12/25-y z)<0 by linarith [hi]) with h | h
    · linarith [h.1]
    · linarith [h.2]

/-- Article: certified strict rational enclosure of the larger atom. -/
theorem y_bounds {z : ℝ} (hz : z∈parameterInterval) : 1/4 < y z ∧ y z < 57/200 := by
  have hx := (roots_order hz).1
  have ho := root_plus_outer_positive z hz
  have hi := root_plus_inner_positive z hz
  rw [atomPolynomial_factor hz] at ho hi
  constructor
  · rcases mul_neg_iff.mp (show (1/4-x z)*(1/4-y z)<0 by linarith [hi]) with h | h
    · linarith [h.2]
    · linarith [h.1]
  · by_contra h
    have hprod : (57/200-x z)*(57/200-y z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith

/-- Article: exact mean location inside the roots, including equality at ζ₁. -/
theorem meanCosine_mem {z : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z) :
    x z ≤ meanCosine z ∧ meanCosine z < y z := by
  have hm := midpoint_positive z hz
  have hsum : x z+y z= -atomA z := by unfold x y; ring
  have hxy := (roots_order hz).2.2
  have hmy : meanCosine z<y z := by linarith
  have he := mean_root_identity hz
  have hf : meanRootFactor z<0 := by have hh:=mean_root_factor_positive z hz; linarith
  have hc := endpointCubic_nonneg hz h1
  have hq : atomPolynomial z (meanCosine z) ≤ 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hc hf.le]
  rw [atomPolynomial_factor hz] at hq
  refine ⟨?_,hmy⟩
  by_contra h
  have hp : 0 < (meanCosine z-x z)*(meanCosine z-y z) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  linarith

/-- Article: the proposed probability weight is nonnegative and strictly below one. -/
theorem p_mem {z : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z) :
    0 ≤ p z ∧ p z<1 := by
  have hm := meanCosine_mem hz h1
  have hxy : 0<y z-x z := sub_pos.mpr (roots_order hz).2.2
  unfold p
  constructor
  · exact div_nonneg (sub_nonneg.mpr hm.1) hxy.le
  · apply (div_lt_one hxy).mpr
    linarith [hm.2]

/-- Article: the weight is zero exactly at the spiral endpoint. -/
theorem p_eq_zero_iff {z : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z) : p z=0 ↔ z=zeta1 := by
  have hxy : y z-x z≠0 := ne_of_gt (sub_pos.mpr (roots_order hz).2.2)
  have hmy := (meanCosine_mem hz h1).2
  have hf : meanRootFactor z≠0 := by have hh:=mean_root_factor_positive z hz; linarith
  constructor
  · intro hp
    have hmx : meanCosine z=x z := by
      have hh : meanCosine z-x z=0 := (div_eq_zero_iff.mp hp).resolve_right hxy
      exact sub_eq_zero.mp hh
    have he := mean_root_identity hz
    rw [hmx,atomPolynomial_x hz] at he
    have hc : endpointCubic z=0 := by
      have he' : endpointCubic z*meanRootFactor z=0 := by linarith
      exact (mul_eq_zero.mp he').resolve_right hf
    exact endpointCubic_strictMonoOn.injOn hz zeta1_mem (hc.trans endpointCubic_zeta1.symm)
  · rintro rfl
    have he := mean_root_identity hz
    rw [endpointCubic_zeta1,zero_mul,sub_zero,atomPolynomial_factor hz] at he
    have hy : meanCosine zeta1-y zeta1≠0 := ne_of_lt (sub_neg.mpr hmy)
    have hx : meanCosine zeta1-x zeta1=0 := (mul_eq_zero.mp he).resolve_right hy
    unfold p
    rw [hx,zero_div]

/-- Article: the actual smaller cosine frequency. -/
def lowerFrequency (z : ℝ) (hz : z∈parameterInterval) : Frequency :=
  ⟨x z,⟨by linarith [(x_bounds hz).1],by linarith [(x_bounds hz).2]⟩⟩

/-- Article: the actual larger cosine frequency. -/
def upperFrequency (z : ℝ) (hz : z∈parameterInterval) : Frequency :=
  ⟨y z,⟨by linarith [(y_bounds hz).1],by linarith [(y_bounds hz).2]⟩⟩

/-- Article: the actual nonnegative probability masses, indexed by the two atoms. -/
def weights (z : ℝ) (hz : z∈parameterInterval) (h1 : zeta1 ≤ z) : Bool → ℝ≥0
  | false => ⟨1-p z,by linarith [(p_mem hz h1).2]⟩
  | true => ⟨p z,(p_mem hz h1).1⟩

/-- Article: the actual atom map. -/
def atoms (z : ℝ) (hz : z∈parameterInterval) : Bool → Frequency
  | false => lowerFrequency z hz
  | true => upperFrequency z hz

/-- Article: exact normalization of the actual probability masses. -/
theorem weights_sum (z : ℝ) (hz : z∈parameterInterval) (h1 : zeta1 ≤ z) : ∑ j,weights z hz h1 j=1 := by
  apply NNReal.coe_injective
  rw [Fintype.sum_bool]
  change p z+(1-p z)=(1 : ℝ)
  ring

/-- Article: the source P₂ probability spectrum. -/
def spectrum (z : ℝ) (hz : z∈parameterInterval) (h1 : zeta1 ≤ z) : Spectrum :=
  Waves.finiteSpectrum (weights z hz h1) (atoms z hz) (weights_sum z hz h1)

end
end polyak.Boundary.P2
