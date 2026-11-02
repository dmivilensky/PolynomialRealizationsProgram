import jacobi.RootMass.Polynomials
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
Article: jacobi, Theorem D.8.
The rational coordinate is proved unbounded by an explicit linear lower
bound. Intermediate values and strict monotonicity construct its actual
order isomorphism [1,infinity) to [0,infinity). The inverse is continuous,
with every defining equation and endpoint value proved, not postulated.
Source: the intermediate value theorem and continuity of order isomorphisms.
Use: proves its full unbounded range without asymptotic or numerical premises.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A uniform explicit linear lower bound for the true rational coordinate beyond n=2.
Use: proves its full unbounded range without asymptotic or numerical premises.
Article: jacobi, Theorem D.8.
Proof: p(n)<=(4+abs(a))*n² and n³*(n²-1)>=n⁵/2 for n>=2;
compare the actual positive-denominator rational functions. -/
theorem psi_linear_lower {a n : ℝ} (ha : -2*sqrt 3<a) (hn : 2≤n) :
    n/(2*(4+|a|)^2)≤psi a n := by
  -- Polynomial growth estimates give an actual bound on the whole tail.
  have hn1 : 1≤n := by linarith
  have hn0 : 0<n := by linarith
  have hC : 0<4+|a| := by positivity
  have hp := (p_bounds ha hn1).1.trans_le (p_bounds ha hn1).2.1
  have hP : p a n≤(4+|a|)*n^2 := by
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self a) hn0.le
    have h2 := mul_nonneg (abs_nonneg a) (show 0≤n^2-n by nlinarith)
    unfold p
    nlinarith
  have hP2 : (p a n)^2≤(4+|a|)^2*n^4 := by
    have hh := (sq_le_sq₀ hp.le (by positivity : 0≤(4+|a|)*n^2)).mpr hP
    simpa only [mul_pow,← pow_mul] using hh
  unfold psi
  apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
  calc
    _≤(n/(2*(4+|a|)^2))*((4+|a|)^2*n^4) :=
      mul_le_mul_of_nonneg_left hP2 (by positivity)
    _=n^5/2 := by field_simp
    _≤n^3*(n^2-1) := by nlinarith [mul_nonneg (pow_nonneg hn0.le 3) (show 0≤n^2-2 by nlinarith)]

/-- The actual inverse-profile coordinate tends to infinity on its positive tail.
Use: proves surjectivity onto every nonnegative target coordinate.
Article: jacobi, Theorem D.8.
Proof: its proved positive linear lower bound eventually exceeds any prescribed real target. -/
theorem psi_atTop {a : ℝ} (ha : -2*sqrt 3<a) : Tendsto (psi a) atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [eventually_ge_atTop (max (2:ℝ) (2*(4+|a|)^2*R))] with n hn
  have h2 : 2≤n := (le_max_left _ _).trans hn
  have hR : 2*(4+|a|)^2*R≤n := (le_max_right _ _).trans hn
  exact (by apply (le_div_iff₀ (by positivity : 0<2*(4+|a|)^2)).mpr; nlinarith :
    R≤n/(2*(4+|a|)^2)).trans (psi_linear_lower ha h2)

/-- Every nonnegative target has an actually attained unique inverse coordinate n>=1.
Use: constructs the inverse required in all quadrature definitions.
Article: jacobi, Appendix D.5 (root-mass coordinate and inverse).
Proof: choose a finite upper endpoint with coordinate above the target,
apply the actual continuous intermediate value theorem, and use strict monotonicity for uniqueness. -/
theorem psi_root {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0≤y) :
    ∃ n : ℝ,1≤n ∧ psi a n=y ∧ ∀ k : ℝ,1≤k → psi a k=y → k=n := by
  -- Surjectivity is proved before the inverse function is defined.
  obtain ⟨R,hR,hRy⟩ := ((eventually_ge_atTop (1:ℝ)).and
    ((psi_atTop ha).eventually (eventually_ge_atTop y))).exists
  have hc : ContinuousOn (psi a) (Icc 1 R) := fun n hn =>
    (psi_contDiffAt ((p_bounds ha hn.1).1.trans_le (p_bounds ha hn.1).2.1).ne').continuousAt.continuousWithinAt
  obtain ⟨n,hn,he⟩ := intermediate_value_Icc hR hc
    (show y∈Icc (psi a 1) (psi a R) by rw [psi_one]; exact ⟨hy,hRy⟩)
  exact ⟨n,hn.1,he,fun k hk hke => (psi_strictMono ha).injOn hk hn.1 (hke.trans he.symm)⟩

/-- The genuine order isomorphism determined by the actual rational coordinate.
Use: its inverse is continuous by the standard order-topology theorem, with no assumed inverse regularity.
Article: jacobi, Appendix D.5 (root-mass coordinate and inverse).
-/
def psiOrderIso (a : ℝ) (ha : -2*sqrt 3<a) : Ici (1:ℝ) ≃o Ici (0:ℝ) := by
  let f (n : Ici (1:ℝ)) : Ici (0:ℝ) := ⟨psi a n,by
    have hh := (psi_strictMono ha).monotoneOn (show (1:ℝ)∈Ici 1 by simp) n.property n.property
    simpa only [psi_one,mem_Ici] using hh⟩
  have hm : StrictMono f := fun x y hxy => psi_strictMono ha x.property y.property hxy
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨n,hn,he,_hu⟩ := psi_root ha y.property
    exact ⟨⟨n,hn⟩,Subtype.ext he⟩
  exact hm.orderIsoOfSurjective f hs

/-- The actual inverse profile coordinate, continuously extended by its boundary value below zero.
Use: evaluates n_u=psi^{-1}(y*(1-u²)) on the whole compact integration interval.
Article: jacobi, Appendix D.5 (root-mass coordinate and inverse).
-/
def inverse (a : ℝ) (ha : -2*sqrt 3<a) (y : ℝ) : ℝ :=
  ((psiOrderIso a ha).symm ⟨max y 0,mem_Ici.mpr (le_max_right _ _)⟩ : Ici (1:ℝ))

/-- The actual inverse always belongs to the original profile domain.
Use: every denominator estimate applies to every quadrature argument.
Article: jacobi, Theorem D.8.
Proof: the inverse order isomorphism takes values in the closed half-line n>=1. -/
theorem inverse_ge_one (a : ℝ) (ha : -2*sqrt 3<a) (y : ℝ) : 1≤ inverse a ha y :=
  ((psiOrderIso a ha).symm ⟨max y 0,mem_Ici.mpr (le_max_right _ _)⟩).property

/-- The original rational coordinate of the actual inverse is its exact nonnegative target.
Use: all substitution and inverse-derivative identities use a proved defining equation.
Article: jacobi, Theorem D.8.
Proof: the actual order isomorphism and its inverse cancel. -/
theorem psi_inverse {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0≤y) : psi a (inverse a ha y)=y := by
  have hh := congrArg Subtype.val ((psiOrderIso a ha).apply_symm_apply ⟨max y 0,mem_Ici.mpr (le_max_right _ _)⟩)
  simpa only [inverse,psiOrderIso,StrictMono.coe_orderIsoOfSurjective,max_eq_left hy] using hh

/-- The actual inverse cancels the rational coordinate at every n>=1.
Use: identifies actual optimizer states with the unique inverse-coordinate quadrature profile.
Article: jacobi, Theorem D.8.
Proof: the proved defining equation and strict injectivity identify the two profile-domain points. -/
theorem inverse_psi {a n : ℝ} (ha : -2*sqrt 3<a) (hn : 1≤n) : inverse a ha (psi a n)=n := by
  have hnon := (psi_strictMono ha).monotoneOn (show (1:ℝ)∈Ici 1 by simp) hn hn
  rw [psi_one] at hnon
  exact (psi_strictMono ha).injOn (inverse_ge_one a ha _) hn (psi_inverse ha hnon)

/-- The inverse coordinate has the exact lower endpoint value one.
Use: controls the apparently singular quadrature endpoint u=1.
Article: jacobi, Appendix D.5 (root-mass coordinate and inverse).
Proof: cancel psi(1)=0 in the genuine inverse identity. -/
theorem inverse_zero (a : ℝ) (ha : -2*sqrt 3<a) : inverse a ha 0=1 := by
  simpa only [psi_one] using inverse_psi ha (n := 1) le_rfl

/-- The actual inverse coordinate is continuous, including at the lower endpoint.
Use: every fixed-interval state quadrature has a continuous integrand on its compact domain.
Article: jacobi, Appendix D.5 (root-mass coordinate and inverse).
Proof: compose max(y,0), the continuous inverse order isomorphism, and subtype inclusion. -/
theorem inverse_continuous (a : ℝ) (ha : -2*sqrt 3<a) : Continuous (inverse a ha) :=
  continuous_subtype_val.comp ((psiOrderIso a ha).symm.continuous.comp
    ((continuous_id.max continuous_const).subtype_mk (fun _ => mem_Ici.mpr (le_max_right _ _))))

/-- The genuine inverse coordinate is strictly increasing on its actual nonnegative target domain.
Use: strict quadrature monotonicity is pointwise before integration.
Article: jacobi, Appendix D.5 (root-mass coordinate and inverse).
Proof: the inverse order isomorphism preserves strict order and max does not change nonnegative arguments. -/
theorem inverse_strictMono {a : ℝ} (ha : -2*sqrt 3<a) : StrictMonoOn (inverse a ha) (Ici (0:ℝ)) := by
  intro x hx y hy hxy
  change (((psiOrderIso a ha).symm ⟨max x 0,mem_Ici.mpr (le_max_right _ _)⟩ : Ici (1:ℝ)) : ℝ)<_
  apply (psiOrderIso a ha).symm.strictMono
  change max x 0<max y 0
  rwa [max_eq_left hx,max_eq_left hy]

/-- The actual inverse has a classical reciprocal derivative at every positive target.
Use: differentiates the fixed-interval state quadratures at every interior integration point.
Article: jacobi, Theorem D.8.
Proof: the already constructed continuous inverse cancels psi in a true
neighborhood of the positive target. The actual nonzero coordinate derivative gives the inverse chain rule. -/
theorem inverse_hasDerivAt {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) :
    HasDerivAt (inverse a ha) (psiSlope a (inverse a ha y))⁻¹ y := by
  have hn := inverse_ge_one a ha y
  have hp := (p_bounds ha hn).1.trans_le (p_bounds ha hn).2.1
  apply HasDerivAt.of_local_left_inverse (inverse_continuous a ha).continuousAt
    (psi_hasDerivAt hp.ne') (psiSlope_pos ha hn).ne'
  filter_upwards [eventually_gt_nhds hy] with z hz
  exact psi_inverse ha hz.le

end
end jacobi.RootMass
