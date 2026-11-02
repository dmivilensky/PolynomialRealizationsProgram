import jacobi.Variational.TopDilation
import jacobi.Variational.TopVariation

/-!
Article: jacobi, Lemma D.3.
Strict spectral dilation and its quadratic L1 remainder give an actual
mass-preserving admissible direction with strictly positive linearized
constraint. The second-moment and top-eigenvalue applications discharge
all constants and radii from the already proved actual variations.
Source: the article's dilation-based constraint qualification argument.
Use: excludes an abnormal zero objective multiplier in the cone separation argument.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real chebyshev2.Continuum chebyshev2.Sobolev
set_option backward.isDefEq.respectTransparency false

/-- Strict dilation and a quadratic L1 expansion construct a positive linearized feasible direction.
Use: excludes an abnormal zero objective multiplier in the cone separation argument.
Article: jacobi, Lemma D.3.
Proof: choose one explicit positive scale increment below the variation
radius and the ratio of linear gain to quadratic error; the latter then
uses at most half the strictly positive spectral gain. -/
theorem dilation_constraint_qualification_local (m : Density) (hm : 0<m.mass)
    (hrad : SymmetricDecreasing m.value) (Φ L : Density → ℝ)
    {C r k η : ℝ} (hC : 0<C) (hr : 0<r) (hk : 0<k) (hη : 0<η)
    (hvariation : ∀ q : Density,(∫ x,|q.value x-m.value x|)≤r →
      |Φ q-Φ m-L q|≤C*(∫ x,|q.value x-m.value x|)^2)
    (hgain : ∀ (t : ℝ) (ht : 1≤t),t≤1+η →
      Φ m+k*(t-1)≤Φ (m.dilate t (by linarith))) :
    ∃ q : Density,q.mass=m.mass ∧ 0<L q := by
  -- One explicit choice meets both the L1 radius and the strict gain budget.
  let ε := min η (min (r/(2*m.mass)) (k/(8*C*m.mass^2)))
  have hε : 0<ε := lt_min hη (lt_min (by positivity) (by positivity))
  have hεη : ε≤η := min_le_left _ _
  have hεr : ε≤r/(2*m.mass) := (min_le_right _ _).trans (min_le_left _ _)
  have hεk : ε≤k/(8*C*m.mass^2) := (min_le_right _ _).trans (min_le_right _ _)
  let q := m.dilate (1+ε) (by positivity)
  have hL : (∫ x,|q.value x-m.value x|)≤2*m.mass*ε := by
    convert! dilation_l1 m hrad (t := 1+ε) (by linarith) using 1
    simp only [add_sub_cancel_left]
    rfl
  have hsmall : (∫ x,|q.value x-m.value x|)≤r :=
    hL.trans (by nlinarith [(le_div_iff₀ (by positivity : 0<2*m.mass)).mp hεr])
  have hv := hvariation q hsmall
  have hg := hgain (1+ε) (by linarith) (by linarith)
  have hnon : 0≤∫ x,|q.value x-m.value x| := integral_nonneg fun _ => abs_nonneg _
  have hquad : C*(∫ x,|q.value x-m.value x|)^2≤4*C*m.mass^2*ε^2 := by
    calc
      _ ≤ C*(2*m.mass*ε)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnon hL 2) hC.le
      _ = _ := by ring
  have hkε : 8*C*m.mass^2*ε≤k := by
    nlinarith [(le_div_iff₀ (by positivity : 0<8*C*m.mass^2)).mp hεk]
  refine ⟨q,m.dilate_mass (by positivity),?_⟩
  have hrem := (le_abs_self (Φ q-Φ m-L q)).trans (hv.trans hquad)
  have hbudget := mul_le_mul_of_nonneg_right hkε hε.le
  have hpos := mul_pos hk hε
  nlinarith

/-- The common qualification theorem on the convenient moment dilation interval [1,2].
Use: retains the moment expansion interface while Fredholm uses a shorter pole-dependent interval.
Article: jacobi, Lemma D.3.
Proof: specialize the local dilation qualification to eta=1. -/
theorem dilation_constraint_qualification (m : Density) (hm : 0<m.mass)
    (hrad : SymmetricDecreasing m.value) (Φ L : Density → ℝ)
    {C r k : ℝ} (hC : 0<C) (hr : 0<r) (hk : 0<k)
    (hvariation : ∀ q : Density,(∫ x,|q.value x-m.value x|)≤r →
      |Φ q-Φ m-L q|≤C*(∫ x,|q.value x-m.value x|)^2)
    (hgain : ∀ (t : ℝ) (ht : 1≤t),t≤2 →
      Φ m+k*(t-1)≤Φ (m.dilate t (by linarith))) :
    ∃ q : Density,q.mass=m.mass ∧ 0<L q :=
  dilation_constraint_qualification_local m hm hrad Φ L hC hr hk zero_lt_one
    hvariation (by simpa only [one_add_one_eq_two] using hgain)

/-- Every nonzero radial density has an actual mass-preserving direction with positive linearized G_2.
Use: discharges the second-moment constraint qualification in the article's multiplier theorem.
Article: jacobi, Lemma D.3.
Proof: combine the full actual second variation with its proved strict dilation gain. -/
theorem second_constraint_qualified (m : Density) (hm : 0<m.mass)
    (hrad : SymmetricDecreasing m.value) :
    ∃ q : Density,q.mass=m.mass ∧ 0<2*secondPairing m.value (q.value-m.value) := by
  obtain ⟨k,hk,hgain⟩ := second_strict_dilation m hm
  exact dilation_constraint_qualification m hm hrad (fun q => observe q .second)
    (fun q => 2*secondPairing m.value (q.value-m.value))
    (C := 1) (r := 1) zero_lt_one zero_lt_one hk
    (fun q _ => by simpa only [one_mul] using second_expansion_remainder m q) hgain

/-- Every nonzero radial density has an actual top gradient and a mass-preserving direction on which it is positive.
Use: discharges the top-eigenvalue constraint qualification with its actual gap and actual gradient.
Article: jacobi, Lemma D.3.
Proof: use the proved actual simple-gap variation and strict top dilation,
then choose the explicit scale supplied by the common qualification argument. -/
theorem top_constraint_qualified (m : Density) (hm : 0<m.mass)
    (hrad : SymmetricDecreasing m.value) :
    ∃ e : H1,‖e‖=1 ∧ densityOperator m.value e=m.spectrum 0 • e ∧
      ∃ q : Density,q.mass=m.mass ∧ 0<∫ x,topGradient e x*(q.value x-m.value x) := by
  -- The variation constants are derived from this density's actual positive spectral gap.
  obtain ⟨e,he,hTe,hgap,_,_,hvariation⟩ := top_variation m hm
  obtain ⟨k,hk,hgain⟩ := top_strict_dilation m hm
  refine ⟨e,he,hTe,?_⟩
  apply dilation_constraint_qualification m hm hrad (fun q => observe q .top)
    (fun q => ∫ x,topGradient e x*(q.value x-m.value x))
    (C := 2/(m.spectrum 0-m.spectrum 1)) (r := (m.spectrum 0-m.spectrum 1)/4)
    (by positivity) (by positivity) hk
  · intro q hsmall
    have h := hvariation q hsmall
    change |observe q .top-observe m .top-(∫ x,topGradient e x*(q.value x-m.value x))|≤_ at h
    convert h using 1
    ring
  · exact hgain

end
end jacobi.Variational
