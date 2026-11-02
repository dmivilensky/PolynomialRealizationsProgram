import jacobi.Variational.FredholmKlein
import jacobi.Variational.FredholmPerturbation

/-!
Article: jacobi, Theorem D.7.
The actual regularized determinant has the printed Green-gradient expansion
and quadratic L1 remainder on the full subcritical spectral domain. Klein's
inequality in both orientations sandwiches the remainder; the proved actual
resolvent gradient modulus bounds its upper side. The perturbation radius
itself proves the perturbed operator remains below the spectral pole.
Source: the actual eigenbasis trace comparison and the resolvent identity.
Use: converts the uniform actual Fredholm gradient modulus to a quadratic scalar remainder.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter chebyshev2.Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- A bounded measurable coefficient pairs integrably with every signed L1 source, with its exact L1 bound.
Use: converts the uniform actual Fredholm gradient modulus to a quadratic scalar remainder.
Article: jacobi, Theorem D.7.
Proof: dominate the product norm by B*abs(delta), then integrate this majorant. -/
theorem bounded_signed_pairing {g d : ℝ → ℝ} (hg : AEStronglyMeasurable g volume)
    (hd : Integrable d) {B : ℝ} (hB : ∀ x,|g x|≤B) :
    Integrable (fun x => g x*d x) ∧ |∫ x,g x*d x|≤B*(∫ x,|d x|) := by
  -- The actual signed pairing is integrable before the integral inequality is applied.
  have hi : Integrable (fun x => g x*d x) := hd.bdd_mul hg
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x,|g x*d x| := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => g x*d x)
    _ ≤ ∫ x,B*|d x| := integral_mono_ae hi.abs (hd.abs.const_mul B)
      (Eventually.of_forall fun x => by
        change |g x*d x|≤B*|d x|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _))
    _ = _ := integral_const_mul _ _

/-- Every actual Fredholm gradient has an integrable pairing with every signed L1 perturbation.
Use: licenses subtraction and combination of the two genuine gradient trace integrals.
Article: jacobi, Theorem D.7.
Proof: evaluate the bounded derivative operator on a unit feature to bound the gradient uniformly. -/
theorem L1Source.fredholmGradient_integrable_mul (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) {d : ℝ → ℝ} (hd : Integrable d) :
    Integrable (fun x => m.fredholmGradient s hs hp x*d x) := by
  apply (bounded_signed_pairing (m.fredholmGradient_continuous hs hp).aestronglyMeasurable hd
    (B := ‖m.fredholmDerivativeOperator s hs hp‖) ?_).1
  intro x
  rw [← m.fredholmDerivativeOperator_feature hs hp]
  calc
    _ ≤ ‖m.fredholmDerivativeOperator s hs hp (feature x)‖*‖feature x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖m.fredholmDerivativeOperator s hs hp‖ := by
      simpa only [feature_norm,mul_one] using (m.fredholmDerivativeOperator s hs hp).le_opNorm (feature x)

/-- The actual determinant remainder is nonnegative and bounded by the product of its two actual pole margins.
Use: the printed epsilon-radius theorem follows after proving the perturbed spectral margin.
Article: jacobi, Theorem D.7.
Proof: Klein's inequality in both orientations bounds the remainder by the
pairing of the gradient difference with delta. The proved uniform gradient
modulus and signed L1 pairing bound give the stated quadratic expression. -/
theorem fredholm_remainder_margins (m q : L1Source) {s : ℝ} (hs : 0≤s)
    (hm : s*observe m .top<1) (hq : s*observe q .top<1) :
    0≤q.fredholmReal s-m.fredholmReal s-(∫ x,m.fredholmGradient s hs hm x*(q.value x-m.value x)) ∧
    |q.fredholmReal s-m.fredholmReal s-(∫ x,m.fredholmGradient s hs hm x*(q.value x-m.value x))|≤
      s^2*(∫ x,|q.value x-m.value x|)^2/((1-s*observe q .top)*(1-s*observe m .top)) := by
  -- Both trace comparisons use the actual finite subcritical Fredholm values.
  have hlo := fredholm_klein m q hs hm hq
  have hhi := fredholm_klein q m hs hq hm
  have hqm := q.fredholmGradient_integrable_mul hs hq (q.integrable.sub m.integrable)
  have hmm := m.fredholmGradient_integrable_mul hs hm (q.integrable.sub m.integrable)
  have hsign : (fun x => q.fredholmGradient s hs hq x*(m.value x-q.value x))=
      -(fun x => q.fredholmGradient s hs hq x*(q.value x-m.value x)) := by funext x; simp only [Pi.neg_apply]; ring
  rw [hsign,integral_neg'] at hhi
  have hdiff : (∫ x,(q.fredholmGradient s hs hq x-m.fredholmGradient s hs hm x)*(q.value x-m.value x))=
      (∫ x,q.fredholmGradient s hs hq x*(q.value x-m.value x))-
        (∫ x,m.fredholmGradient s hs hm x*(q.value x-m.value x)) := by
    change (∫ x,(q.fredholmGradient s hs hq x-m.fredholmGradient s hs hm x)*(q.value x-m.value x))=
      (∫ x,q.fredholmGradient s hs hq x*((q.value-m.value) x))-
        (∫ x,m.fredholmGradient s hs hm x*((q.value-m.value) x))
    rw [← integral_sub hqm hmm]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only [Pi.sub_apply]; ring
  have hbound := (bounded_signed_pairing
    (((q.fredholmGradient_continuous hs hq).sub (m.fredholmGradient_continuous hs hm)).aestronglyMeasurable)
      (q.integrable.sub m.integrable) (fun x => fredholmGradient_distance m q hs hm hq x)).2
  change |∫ x,(q.fredholmGradient s hs hq x-m.fredholmGradient s hs hm x)*(q.value x-m.value x)|≤
    (s^2*(∫ x,|q.value x-m.value x|)/((1-s*observe q .top)*(1-s*observe m .top)))*
      (∫ x,|q.value x-m.value x|) at hbound
  rw [hdiff] at hbound
  refine ⟨hlo,?_⟩
  rw [abs_of_nonneg hlo]
  have hlin := (le_abs_self _).trans hbound
  have he : (s^2*(∫ x,|q.value x-m.value x|)/((1-s*observe q .top)*(1-s*observe m .top)))*
      (∫ x,|q.value x-m.value x|)=
      s^2*(∫ x,|q.value x-m.value x|)^2/((1-s*observe q .top)*(1-s*observe m .top)) := by ring
  rw [he] at hlin
  linarith

/-- The full actual Fredholm first variation has the printed quadratic L1 remainder and perturbation radius.
Use: supplies the Fredholm multiplier theorem's expansion with every spectral pole premise discharged.
Article: jacobi, Theorem D.7.
Proof: actual top-eigenvalue L1 stability and the stated perturbation radius
give the perturbed margin epsilon/2. Apply the two-sided trace remainder
bound and compare its two positive pole margins with epsilon and epsilon/2. -/
theorem fredholm_variation (m : L1Source) {s ε : ℝ} (hs : 0<s) (hε : 0<ε)
    (hp : s*observe m .top≤1-ε) (q : L1Source)
    (hsmall : (∫ x,|q.value x-m.value x|)≤ε/(2*s)) :
    s*observe q .top<1 ∧
      |q.fredholmReal s-m.fredholmReal s-
        (∫ x,m.fredholmGradient s hs.le (by linarith) x*(q.value x-m.value x))|≤
          2*s^2*(∫ x,|q.value x-m.value x|)^2/ε^2 := by
  -- The radius proves the perturbed pole condition, rather than assuming it separately.
  let N := ∫ x,|q.value x-m.value x|
  have hN : 0≤N := integral_nonneg fun _ => abs_nonneg _
  have ht := kernel_top_distance q.integrable m.integrable q.nonneg m.nonneg
  change |observe q .top-observe m .top|≤N at ht
  have hsN : s*N≤ε/2 := by
    have h := (le_div_iff₀ (by positivity : 0<2*s)).mp hsmall
    nlinarith
  have hqmargin : s*observe q .top≤1-ε/2 := by
    have h := mul_le_mul_of_nonneg_left ((le_abs_self _).trans ht) hs.le
    nlinarith
  have hmq : s*observe q .top<1 := by linarith
  have hmp : s*observe m .top<1 := by linarith
  have h := (fredholm_remainder_margins m q hs.le hmp hmq).2
  have hdenpos : 0<(1-s*observe q .top)*(1-s*observe m .top) :=
    mul_pos (sub_pos.mpr hmq) (sub_pos.mpr hmp)
  have hden : ε^2/2≤(1-s*observe q .top)*(1-s*observe m .top) := by
    have hmarg : ε≤1-s*observe m .top := by linarith
    have hqarg : ε/2≤1-s*observe q .top := by linarith
    nlinarith [mul_le_mul hqarg hmarg hε.le (by linarith : 0≤1-s*observe q .top)]
  refine ⟨hmq,h.trans ?_⟩
  change s^2*N^2/((1-s*observe q .top)*(1-s*observe m .top))≤2*s^2*N^2/ε^2
  calc
    _ ≤ s^2*N^2/(ε^2/2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by ring

end
end jacobi.Variational
