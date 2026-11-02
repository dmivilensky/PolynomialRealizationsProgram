import jacobi.Variational.GreenReciprocal

/-!
Article: jacobi, Theorem D.7.
A positive fundamental pair with unit Wronskian spans every classical
solution. An L2 solution at either infinite end cannot contain the growing
branch: its quotient by that branch has a constant limit, and the square
of that quotient is integrable on a tail of infinite measure.
Source: classical reduction of order and the zero-limit theorem for integrable functions.
Use: upgrades the actual homogeneous Green factors to the precise classical regularity in their solution-space assertion.
-/
namespace jacobi.Continuum
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Every everywhere classical solution of an equation with continuous potential is genuinely C2.
Use: upgrades the actual homogeneous Green factors to the precise classical regularity in their solution-space assertion.
Article: jacobi, Theorem D.7.
Proof: the first equation gives differentiability, the second gives the
actual second derivative V*f, and this product is continuous. Apply the two derivative characterizations of C2. -/
theorem classical_ode_contDiff {f V : ℝ → ℝ} (hV : Continuous V)
    (hf : ∀ x,HasDerivAt f (deriv f x) x)
    (hd : ∀ x,HasDerivAt (deriv f) (V x*f x) x) : ContDiff ℝ 2 f := by
  -- Continuity of the actual second derivative follows from the equation itself.
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  change ContDiff ℝ (1+1) f
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x => (hf x).differentiableAt,by simp,?_⟩
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hd x).differentiableAt,?_⟩
  have he : deriv (deriv f)=fun x => V x*f x := funext fun x => (hd x).deriv
  rw [he]
  exact hV.mul hfc

/-- A positive unit-Wronskian pair spans every global classical solution of the same scalar equation.
Use: proves that the actual two positive Green factors form the full homogeneous solution space.
Article: jacobi, Theorem D.7.
Proof: the Wronskian of R and f is constant A. The quotient (f-A*L)/R
then has zero derivative and is constant B; positivity licenses division everywhere. -/
theorem positive_fundamental_pair {R L V f d : ℝ → ℝ}
    (hR : ∀ x,0<R x)
    (hRe : ∀ x,HasDerivAt R (deriv R x) x ∧ HasDerivAt (deriv R) (V x*R x) x)
    (hLe : ∀ x,HasDerivAt L (deriv L x) x ∧ HasDerivAt (deriv L) (V x*L x) x)
    (hW : ∀ x,R x*deriv L x-deriv R x*L x=1)
    (hf : ∀ x,HasDerivAt f (d x) x) (hd : ∀ x,HasDerivAt d (V x*f x) x) :
    ∃ A B : ℝ,∀ x,f x=A*L x+B*R x := by
  -- The first conserved Wronskian extracts the coefficient of the left factor.
  let W (x : ℝ) := R x*d x-deriv R x*f x
  have hWd (x : ℝ) : HasDerivAt W 0 x := by
    convert ((hRe x).1.mul (hd x)).sub ((hRe x).2.mul (hf x)) using 1
    ring
  have hw (x : ℝ) : W x=W 0 := is_const_of_deriv_eq_zero
    (fun y => (hWd y).differentiableAt) (fun y => (hWd y).deriv) x 0
  let q (x : ℝ) := (f x-W 0*L x)/R x
  have hqd (x : ℝ) : HasDerivAt q 0 x := by
    have hh := ((hf x).sub ((hLe x).1.const_mul (W 0))).div (hRe x).1 (hR x).ne'
    convert hh using 1
    apply Eq.symm
    apply (div_eq_zero_iff).mpr
    left
    have hwx := hw x
    have hWx := hW x
    change R x*d x-deriv R x*f x=W 0 at hwx
    change (d x-W 0*deriv L x)*R x-(f x-W 0*L x)*deriv R x=0
    linear_combination hwx-W 0*hWx
  refine ⟨W 0,q 0,fun x => ?_⟩
  have hq : q x=q 0 := is_const_of_deriv_eq_zero
    (fun y => (hqd y).differentiableAt) (fun y => (hqd y).deriv) x 0
  have hh := (div_eq_iff (hR x).ne').mp hq
  linarith

/-- An L2 solution cannot contain a nonzero coefficient of an eventually large positive branch at an infinite-measure end.
Use: proves both half-line uniqueness statements for the actual Green factors.
Article: jacobi, Theorem D.7.
Proof: f/L tends to A because R/L tends to zero. On a common tail L>=1,
so its square is dominated by the integrable f². Every neighborhood of the
end has infinite measure, forcing the limiting constant A² to be zero. -/
theorem l2_coefficient_vanishes {R L f : ℝ → ℝ} {A B : ℝ} {l : Filter ℝ}
    [l.NeBot] (hL : ∀ x,0<L x) (hLm : Measurable L) (hm : Measurable (fun x => (f x/L x)^2))
    (hlarge : ∀ᶠ x in l,1≤L x) (hratio : Tendsto (fun x => R x/L x) l (𝓝 0))
    (heq : ∀ x,f x=A*L x+B*R x) {S : Set ℝ} (hS : S∈l) (hSm : MeasurableSet S)
    (hi : MemLp f 2 (volume.restrict S)) (hinf : ∀ S∈l,volume S=∞) : A=0 := by
  -- Use a single common tail for square integrability and the lower bound on the growing factor.
  let T := S∩{x | 1≤L x}
  have hT : T∈l := inter_mem hS hlarge
  have hfiS : IntegrableOn (fun x => f x^2) S := hi.integrable_sq
  have hfi : IntegrableOn (fun x => f x^2) T := hfiS.mono_set inter_subset_left
  have hqi : IntegrableOn (fun x => (f x/L x)^2) T := by
    apply hfi.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (hSm.inter (measurableSet_le measurable_const hLm))] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),div_pow]
    have hxL : 1≤L x := hx.2
    exact div_le_self (sq_nonneg _) (by nlinarith)
  have hq : Tendsto (fun x => f x/L x) l (𝓝 A) := by
    have hh := (tendsto_const_nhds (x := A) (f := l)).add (hratio.const_mul B)
    simp only [mul_zero,add_zero] at hh
    apply hh.congr' (Eventually.of_forall fun x => ?_)
    rw [heq x]
    field_simp [(hL x).ne']
  have hz : A^2=0 := IntegrableAtFilter.eq_zero_of_tendsto ⟨T,hT,hqi⟩ hinf (hq.pow 2)
  nlinarith [sq_nonneg A]

end
end jacobi.Continuum
