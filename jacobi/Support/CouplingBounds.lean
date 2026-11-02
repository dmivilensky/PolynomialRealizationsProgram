import jacobi.Support.BirthDeathBounds
import jacobi.Support.BirthDeathError

/-!
Article: jacobi, Appendix C.3 (coefficient bounds).
The genuine positive square-root support coefficients have both the
printed uniform positive lower bound and full inverse-square error
from one half. Their original matrix coefficients are identified exactly.
Use: coupling_lower and coupling_error prove the printed original coefficient bounds; naturalChain_sqrt_coupling identifies this exact value with the actual original matrix recurrence.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The actual original positive adjacent support coefficient before its unused finite tail.
Use: coupling_lower and coupling_error prove the printed original coefficient bounds; naturalChain_sqrt_coupling identifies this exact value with the actual original matrix recurrence.
Article: jacobi, Appendix C.3 (coefficient bounds).
-/
def coupling (a b : ℝ) (n m : ℕ) : ℝ :=
  Real.sqrt (coefficientA a b n (m-1)*coefficientC a b n m/4)

/-- The original positive support coefficient is exactly the actual finite Jacobi recurrence coefficient at every genuine interior edge.
Use: coefficient_bounds proves the full printed estimates directly for the actual original finite chain, preserving its positive-coupling convention.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the actual squared coupling is the already proved original A_(m-1)*C_m/4, with the genuine positive square root taken on both sides. -/
theorem naturalChain_sqrt_coupling (a b : ℝ) (ha:-1<a) (hb:-1<b) {n m : ℕ}
    (hm:0<m) (hmn:m<n) :
    Real.sqrt ((naturalChain a b ha hb n).data.aSq m)=coupling a b n m := by
  rw [naturalChain_coupling a b ha hb hm hmn]
  rfl

/-- Taking the genuine nonnegative square root does not increase distance from one.
Use: coupling_error converts the actual proved squared-coefficient estimate into the original coefficient estimate with no assumed root perturbation bound.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: multiply the actual square-root difference by sqrt(x)+1; this equals x-1 exactly, and the genuine extra factor is at least one. -/
theorem sqrt_error_one {x : ℝ} (hx:0≤x) : |Real.sqrt x-1|≤|x-1| := by
  have he : (Real.sqrt x-1)*(Real.sqrt x+1)=x-1 := by nlinarith [Real.sq_sqrt hx]
  have hab := congrArg abs he
  rw [abs_mul,abs_of_pos (by positivity : 0<Real.sqrt x+1)] at hab
  nlinarith [Real.sqrt_nonneg x,abs_nonneg (Real.sqrt x-1)]

/-- The actual original adjacent support coefficients have a common strictly positive lower bound on the entire printed growing half chain.
Use: the original reduction-of-order kernel and oscillatory perturbation estimates divide only by these genuinely uniformly positive original coefficients.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: the proved actual birth/death product has a uniform positive lower bound at every original positive index. Monotonicity of the genuine square root and division by two give the same bound for the original coefficient. -/
theorem coupling_lower {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,0<m→2*m≤n+6→c≤coupling a b n m := by
  obtain ⟨c,C,hc,hC,hbound⟩ := birthDeath_bounds ha hb
  refine ⟨Real.sqrt (c/4),Real.sqrt_pos.mpr (by positivity),?_⟩
  filter_upwards [hbound] with n hn
  intro m hm hmn
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (hn m hm hmn).1 (by norm_num))

/-- The actual original adjacent support coefficients satisfy the full uniform inverse-square estimate from their free value one half.
Use: the original support wave has a summable O(m^-2) recurrence perturbation, which drives its oscillatory frequency envelope.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: the genuine birth/death product is nonnegative and its distance from one has the proved inverse-square bound. The elementary genuine square-root error bound, together with sqrt(x/4)=sqrt(x)/2, gives the printed estimate. -/
theorem coupling_error {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,0<m→2*m≤n+6→
      |coupling a b n m-1/2|≤C/(m:ℝ)^2 := by
  -- Both the true sign and the normalization are supplied by the same actual original birth/death product.
  obtain ⟨C,hC,herr⟩ := birthDeath_error ha hb
  obtain ⟨c,D,hc,hD,hbound⟩ := birthDeath_bounds ha hb
  refine ⟨C,hC,?_⟩
  filter_upwards [herr,hbound] with n hn he
  intro m hm hmn
  have hprod : 0≤coefficientA a b n (m-1)*coefficientC a b n m := hc.le.trans (he m hm hmn).1
  have hs := sqrt_error_one hprod
  have h := hn m hm hmn
  rw [coupling,Real.sqrt_div hprod,show Real.sqrt (4:ℝ)=2 by norm_num,
    show Real.sqrt (coefficientA a b n (m-1)*coefficientC a b n m)/2-1/2=
      (Real.sqrt (coefficientA a b n (m-1)*coefficientC a b n m)-1)/2 by ring,
    abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [abs_nonneg (Real.sqrt (coefficientA a b n (m-1)*coefficientC a b n m)-1)]

end
end jacobi.Support
