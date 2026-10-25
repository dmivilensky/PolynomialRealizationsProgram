import polyak.Boundary.P2.Algebra
import polyak.Boundary.P2.Check
import polyak.Boundary.SpiralArc

/-! Article: Lemma p2ends, actual isolated parameter roots and exact endpoint signs. -/
namespace polyak.Boundary.P2
noncomputable section
open Polynomial LeanCert.Engine

/-- Article: independent rational polynomial defining ζₐ. -/
def endpointPolynomial : ℚ[X] := N12 X

/-- Article: independent literal coefficients of the actual endpoint polynomial. -/
def endpointPolynomialCode : Numerics.PolynomialCode endpointPolynomial where
  code := ⟨#[1600,-10048,28224,-48736,59952,-57472,44832,-28736,14988,-6092,1764,-314,25]⟩
  exact := by
    change (C (1600)+X*(C (-10048)+X*(C (28224)+X*(C (-48736)+X*(C (59952)+X*(C (-57472)+X*(C (44832)+X*(C (-28736)+X*(C (14988)+X*(C (-6092)+X*(C (1764)+X*(C (-314)+X*(C (25)+X*0)))))))))))))=endpointPolynomial
    norm_num [endpointPolynomial,N12]
    simp only [Polynomial.C_ofNat]
    ring

/-- Article: the real source and its rational-polynomial evaluation agree. -/
theorem endpointPolynomial_eval (z : ℝ) : aeval z endpointPolynomial=N12 z := by
  norm_num [endpointPolynomial,N12,Polynomial.aeval_def]

/-- Article: literal coefficients of the positive derivative of −N₁₂. -/
def negativeEndpointDerivativeCode : Numerics.PolynomialCode ((-endpointPolynomial).derivative) where
  code := ⟨#[10048,-56448,146208,-239808,287360,-268992,201152,-119904,54828,-17640,3454,-300]⟩
  exact := by
    change (C (10048)+X*(C (-56448)+X*(C (146208)+X*(C (-239808)+X*(C (287360)+X*(C (-268992)+X*(C (201152)+X*(C (-119904)+X*(C (54828)+X*(C (-17640)+X*(C (3454)+X*(C (-300)+X*0)))))))))))) = (-endpointPolynomial).derivative
    norm_num [endpointPolynomial,N12]
    simp only [Polynomial.C_ofNat]
    ring

/-- Article: exact strict negative derivative of N₁₂ throughout J. -/
theorem negativeEndpointDerivative_positive {z : ℝ} (hz : z∈parameterInterval) :
    0 < aeval z (-endpointPolynomial).derivative := by
  have hc : signedPolynomialCheck negativeEndpointDerivativeCode.code 1=true := by decide +kernel
  have h := signedPolynomialCheck_positive hc hz
  rw [negativeEndpointDerivativeCode.exact] at h
  simpa only [Rat.cast_one,one_mul] using h

/-- Article: N₁₂ is strictly decreasing on the whole common certificate interval. -/
theorem N12_strictAntiOn : StrictAntiOn (N12 (R := ℝ)) parameterInterval := by
  have hmono : StrictMonoOn (fun z : ℝ => aeval z (-endpointPolynomial)) parameterInterval := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact (-endpointPolynomial).continuous_aeval.continuousOn
    · intro z hz
      rw [((-endpointPolynomial).hasDerivAt_aeval z).deriv]
      exact negativeEndpointDerivative_positive (interior_subset hz)
  intro z hz z' hz' hzz'
  have h := hmono hz hz' hzz'
  change aeval z (-endpointPolynomial)<aeval z' (-endpointPolynomial) at h
  rw [map_neg,map_neg,endpointPolynomial_eval,endpointPolynomial_eval] at h
  linarith

/-- Article: the exact enclosure used to select ζₐ. -/
def zetaAInterval : LeanCert.Core.IntervalRat := ⟨16989/10000,1699/1000,by norm_num⟩

/-- Article: an actual algebraic root, unique in the source enclosure. -/
theorem exists_zetaA : Nonempty (Numerics.IsolatedRoot (-endpointPolynomial) zetaAInterval) := by
  apply Numerics.exists_isolatedRoot zetaAInterval
  · norm_num [zetaAInterval,endpointPolynomial,N12,Polynomial.aeval_def]
  · norm_num [zetaAInterval,endpointPolynomial,N12,Polynomial.aeval_def]
  · intro z hz
    apply negativeEndpointDerivative_positive
    rw [LeanCert.Core.IntervalRat.mem_def] at hz
    norm_num [zetaAInterval] at hz
    constructor <;> linarith [hz.1,hz.2]

/-- Article: the designated P₂-to-P₅ algebraic parameter. -/
def zetaARoot : Numerics.IsolatedRoot (-endpointPolynomial) zetaAInterval := Classical.choice exists_zetaA

/-- Article: ζₐ. -/
def zetaA : ℝ := zetaARoot.value

/-- Article: its exact N₁₂ equation. -/
theorem N12_zetaA : N12 zetaA=0 := by
  have h := zetaARoot.root
  rw [map_neg,endpointPolynomial_eval] at h
  change -N12 zetaA=0 at h
  linarith

/-- Article: the printed strict rational bounds for ζₐ. -/
theorem zetaA_bounds : 16989/10000 < zetaA ∧ zetaA < 1699/1000 := by
  have hm := zetaARoot.mem
  rw [LeanCert.Core.IntervalRat.mem_def] at hm
  norm_num [zetaAInterval] at hm
  change 16989/10000 ≤ zetaA ∧ zetaA ≤ 1699/1000 at hm
  constructor
  · apply lt_of_le_of_ne hm.1
    intro he
    have h := N12_zetaA
    rw [←he] at h
    norm_num [N12] at h
  · apply lt_of_le_of_ne hm.2
    intro he
    have h := N12_zetaA
    rw [he] at h
    norm_num [N12] at h

/-- Article: ζₐ belongs to the interval of all finite source sign checks. -/
theorem zetaA_mem : zetaA∈parameterInterval := by
  constructor <;> linarith [zetaA_bounds.1,zetaA_bounds.2]

/-- Article: source numerator N₁₂ is nonnegative up to its unique endpoint. -/
theorem N12_nonneg {z : ℝ} (hz : z∈parameterInterval) (hza : z ≤ zetaA) : 0 ≤ N12 z := by
  rw [←N12_zetaA]
  exact N12_strictAntiOn.antitoneOn hz zetaA_mem hza

/-- Article: upper lag five is strictly inactive before ζₐ. -/
theorem N12_positive {z : ℝ} (hz : z∈parameterInterval) (hza : z < zetaA) : 0 < N12 z := by
  rw [←N12_zetaA]
  exact N12_strictAntiOn hz zetaA_mem hza

/-- Article: the spiral transition parameter already isolated by the concrete source certificate. -/
def zeta1 : ℝ := Numerics.transitionRoot.value

/-- Article: the exact cubic equation defining ζ₁. -/
theorem endpointCubic_zeta1 : endpointCubic zeta1=0 := by
  have h := Numerics.transitionRoot.root
  simpa [Numerics.transitionCubic,endpointCubic,zeta1,Polynomial.aeval_def] using h

/-- Article: the printed rational enclosure of the spiral endpoint is strict. -/
theorem zeta1_bounds : 4239/2500 < zeta1 ∧ zeta1 < 16957/10000 := by
  have hm := Numerics.transitionRoot.mem
  rw [LeanCert.Core.IntervalRat.mem_def] at hm
  norm_num [Numerics.transitionRootInterval] at hm
  change 4239/2500 ≤ zeta1 ∧ zeta1 ≤ 16957/10000 at hm
  constructor
  · apply lt_of_le_of_ne hm.1
    intro he
    have h := endpointCubic_zeta1
    rw [←he] at h
    norm_num [endpointCubic] at h
  · apply lt_of_le_of_ne hm.2
    intro he
    have h := endpointCubic_zeta1
    rw [he] at h
    norm_num [endpointCubic] at h

/-- Article: ζ₁ lies inside the common parameter interval. -/
theorem zeta1_mem : zeta1∈parameterInterval := by
  constructor <;> linarith [zeta1_bounds.1,zeta1_bounds.2]

/-- Article: the defining cubic is strictly increasing throughout the certificate interval. -/
theorem endpointCubic_strictMonoOn : StrictMonoOn (endpointCubic (R := ℝ)) parameterInterval := by
  have hm : StrictMonoOn (fun z : ℝ => aeval z Numerics.transitionCubic) parameterInterval := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact Numerics.transitionCubic.continuous_aeval.continuousOn
    · intro z hz
      rw [(Numerics.transitionCubic.hasDerivAt_aeval z).deriv]
      apply Numerics.transition_derivative_positive
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num [Numerics.transitionInterval]
      exact (interior_subset hz : z∈parameterInterval)
  intro z hz z' hz' hzz'
  have h := hm hz hz' hzz'
  simpa [Numerics.transitionCubic,endpointCubic,Polynomial.aeval_def] using h

/-- Article: the cubic factor is nonnegative from the spiral endpoint onward. -/
theorem endpointCubic_nonneg {z : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z) :
    0 ≤ endpointCubic z := by
  rw [←endpointCubic_zeta1]
  exact endpointCubic_strictMonoOn.monotoneOn zeta1_mem hz h1

/-- Article: the P₂ arc has distinct ordered endpoints. -/
theorem zeta1_lt_zetaA : zeta1 < zetaA := by linarith [zeta1_bounds.2,zetaA_bounds.1]

end
end polyak.Boundary.P2
