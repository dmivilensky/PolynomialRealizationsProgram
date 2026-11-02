import jacobi.Variational.RadialConvolution
import jacobi.Variational.SecondKKT

/-!
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
The literal exponent-two convolution is even and has strictly negative slope
at every positive radius for every nonzero radial finite-energy density.
Only its L1 source is used: spatial scaling reuses the proved full measurable
exponent-one convolution result, without density regularity assumptions.
Source: reflected convolution positivity and the exact exponent rescaling.
Use: centers the normalized elliptic optimizer's peak at the origin.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Real Filter Set jacobi.Variational
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual second-moment potential inherits the density's reflection symmetry.
Use: centers the normalized elliptic optimizer's peak at the origin.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: reflect the literal convolution variable and use the even density and exponential kernel. -/
theorem potential_even (m : Density) (hs : SymmetricDecreasing m.value) (x : ℝ) :
    potential m (-x)=potential m x := by
  rw [potential_kernel,potential_kernel,
    ← integral_neg_eq_self (fun y => m.value y*exp (-2*|-x-y|)) volume]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [hs.even,show -x- -y=-(x-y) by ring,abs_neg]

/-- The actual second-moment Green gradient has strictly negative slope at every positive radius.
Use: closes strict radial gradient monotonicity for the article's single-moment KKT shape theorem.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: the rescaled source is nonnegative, integrable and symmetric
decreasing, with mass twice the original positive mass. Apply the actual
exponent-one strict convolution slope theorem at the radius 2x. -/
theorem potentialSlope_radial_neg (m : Density) (hm : 0<m.mass)
    (hs : SymmetricDecreasing m.value) {x : ℝ} (hx : 0<x) : potentialSlope m x<0 := by
  -- Rescaling preserves the full measurable radial source class.
  have hs' : SymmetricDecreasing (source m) := by
    refine ⟨?_,?_⟩
    · intro y
      change m.value ((-y)/2)=m.value (y/2)
      rw [neg_div,hs.even]
    · intro y hy z hz hyz
      change m.value (z/2)≤m.value (y/2)
      have hyp : 0<y := hy
      have hzp : 0<z := hz
      exact hs.decreasing (show 0<y/2 by positivity) (show 0<z/2 by positivity) (by linarith)
  have hmass : (∫ y,source m y)=2*m.mass := by
    have hh := Measure.integral_comp_mul_left m.value (1/2:ℝ)
    simp only [smul_eq_mul] at hh
    norm_num at hh
    convert hh using 1 <;> simp only [source,div_eq_mul_inv,mul_comm,Density.mass,one_mul]
  exact convolutionSlope_radial_neg (source_integrable m) (fun y => m.nonneg (y/2))
    hs' (by rw [hmass]; positivity) (by positivity : 0<2*x)

/-- The actual exponent-two potential strictly decreases on the closed nonnegative half-line.
Use: proves the continuous strict shape of the second-moment KKT coefficient and its interval support.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: its genuine derivative is strictly negative throughout the interior of the positive half-line. -/
theorem potential_strictAnti (m : Density) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value) :
    StrictAntiOn (potential m) (Ici 0) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici 0) (potential_continuous m).1.continuousOn
    (fun y _ => (potential_hasDerivAt m y).hasDerivWithinAt)
  intro y hy
  exact potentialSlope_radial_neg m hm hs (by simpa only [interior_Ici,mem_Ioi] using hy)

end
end jacobi.Young
