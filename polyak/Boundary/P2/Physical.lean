import polyak.Boundary.P2.Parameter

/-! Article: Lemma p2ends(b), exact physical endpoint and isolated Hₐ root. -/
namespace polyak.Boundary.P2
noncomputable section
open Polynomial LeanCert.Engine

/-- Article: a finer proved rational enclosure for ζₐ. -/
theorem zetaA_fine_bounds : (16989316152/10000000000 : ℝ)<zetaA ∧ zetaA<16989316153/10000000000 := by
  have hl : (16989316152/10000000000 : ℝ)∈parameterInterval := by norm_num [parameterInterval]
  have hu : (16989316153/10000000000 : ℝ)∈parameterInterval := by norm_num [parameterInterval]
  have hpl : 0<N12 (16989316152/10000000000 : ℝ) := by norm_num [N12]
  have hpu : N12 (16989316153/10000000000 : ℝ)<0 := by norm_num [N12]
  constructor
  · by_contra hn
    have h:=N12_strictAntiOn.antitoneOn zetaA_mem hl (le_of_not_gt hn)
    rw [N12_zetaA] at h
    linarith
  · by_contra hn
    have h:=N12_strictAntiOn.antitoneOn hu zetaA_mem (le_of_not_gt hn)
    rw [N12_zetaA] at h
    linarith

/-- Article: the printed exact bounds for the physical endpoint Gₐ. -/
theorem Ga_bounds : (51179/50000 : ℝ)<Ga ∧ Ga<102359/100000 := by
  have hl : (16989316152/10000000000 : ℝ)∈parameterInterval := by norm_num [parameterInterval]
  have hu : (16989316153/10000000000 : ℝ)∈parameterInterval := by norm_num [parameterInterval]
  have hlo : (51179/50000 : ℝ)<G (16989316153/10000000000) := by norm_num [G,rMinus]
  have hhi : G (16989316152/10000000000 : ℝ)<102359/100000 := by norm_num [G,rMinus]
  exact ⟨hlo.trans (G_strictAntiOn zetaA_mem hu zetaA_fine_bounds.2),
    (G_strictAntiOn hl zetaA_mem zetaA_fine_bounds.1).trans hhi⟩

/-- Article: independent rational polynomial Hₐ. -/
def HaPolynomial : ℚ[X] := Ha X

/-- Article: real source evaluation of Hₐ. -/
theorem HaPolynomial_eval (v : ℝ) : aeval v HaPolynomial=Ha v := by
  norm_num [HaPolynomial,Ha,Polynomial.aeval_def]

/-- Article: exact derivative coefficient annotation for Hₐ. -/
def HaDerivativeCode : Numerics.PolynomialCode HaPolynomial.derivative where
  code := ⟨#[0,25866224,0,-235287488,0,-37479272448,0,621349666816,0,-2386855198720,0,1950351360000]⟩
  exact := by
    change (C (0)+X*(C (25866224)+X*(C (0)+X*(C (-235287488)+X*(C (0)+X*(C (-37479272448)+X*(C (0)+X*(C (621349666816)+X*(C (0)+X*(C (-2386855198720)+X*(C (0)+X*(C (1950351360000)+X*0))))))))))))=HaPolynomial.derivative
    norm_num [HaPolynomial,Ha]
    simp only [Polynomial.C_ofNat]
    ring

/-- Article: physical root isolation interval. -/
def GaInterval : LeanCert.Core.IntervalRat := ⟨51179/50000,102359/100000,by norm_num⟩

/-- Article: Hₐ is strictly increasing on the entire printed enclosure. -/
theorem HaDerivative_positive {v : ℝ} (hv : v∈GaInterval) : 0<aeval v HaPolynomial.derivative := by
  apply HaDerivativeCode.positive_of_taylor (204717/200000) (1/200000) (by decide +kernel) v
  rw [LeanCert.Core.IntervalRat.mem_def] at hv
  norm_num [GaInterval] at hv
  apply abs_le.mpr
  constructor <;> linarith [hv.1,hv.2]

/-- Article: Gₐ is exactly the unique root of Hₐ in the printed rational interval. -/
def GaRoot : Numerics.IsolatedRoot HaPolynomial GaInterval where
  value := Ga
  mem := by
    rw [LeanCert.Core.IntervalRat.mem_def]
    norm_num [GaInterval]
    exact ⟨Ga_bounds.1.le,Ga_bounds.2.le⟩
  root := by rw [HaPolynomial_eval]; exact Ha_Ga
  unique v hv he := by
    have hm : StrictMonoOn (fun v : ℝ => aeval v HaPolynomial) (Set.Icc (GaInterval.lo : ℝ) GaInterval.hi) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _) HaPolynomial.continuous_aeval.continuousOn
      intro w hw
      rw [(HaPolynomial.hasDerivAt_aeval w).deriv]
      have hm : w∈Set.Icc (GaInterval.lo : ℝ) GaInterval.hi := interior_subset hw
      exact HaDerivative_positive hm
    apply hm.injOn hv (show Ga∈GaInterval from ?_)
    · exact he.trans (by change 0=aeval Ga HaPolynomial; rw [HaPolynomial_eval,Ha_Ga])
    · rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num [GaInterval]
      exact ⟨Ga_bounds.1.le,Ga_bounds.2.le⟩

/-- Article: ζ₁ is the unique real root of its source cubic, without an interval restriction. -/
theorem zeta1_unique_real {v : ℝ} (hv : endpointCubic v=0) : v=zeta1 := by
  have hpos : 1<v := by
    by_contra hh
    have hp:=mul_nonpos_of_nonneg_of_nonpos (sq_nonneg v) (sub_nonpos.mpr (le_of_not_gt hh))
    unfold endpointCubic at hv
    nlinarith
  have hz : 1<zeta1 := by linarith [zeta1_bounds.1]
  have hp : 0<v^2+v*zeta1+zeta1^2-v-zeta1 := by
    have hv2:=mul_pos (by linarith : 0<v) (by linarith : 0<v-1)
    have hz2:=mul_pos (by linarith : 0<zeta1) (by linarith : 0<zeta1-1)
    have hm:=mul_pos (by linarith : 0<v) (by linarith : 0<zeta1)
    nlinarith
  have he : (v-zeta1)*(v^2+v*zeta1+zeta1^2-v-zeta1)=0 := by
    have h:=endpointCubic_zeta1
    unfold endpointCubic at hv h
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hp.ne')

/-- Article: both source parameter roots are simple. -/
theorem parameter_roots_simple :
    aeval zeta1 Numerics.transitionCubic.derivative≠0 ∧
    aeval zetaA endpointPolynomial.derivative≠0 := by
  constructor
  · apply (Numerics.transition_derivative_positive zeta1 ?_).ne'
    rw [LeanCert.Core.IntervalRat.mem_def]
    norm_num [Numerics.transitionInterval]
    exact zeta1_mem
  · have h:=negativeEndpointDerivative_positive zetaA_mem
    rw [Polynomial.derivative_neg,map_neg] at h
    exact (neg_pos.mp h).ne

end
end polyak.Boundary.P2
