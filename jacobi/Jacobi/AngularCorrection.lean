import jacobi.Jacobi.CoarseAngularError
import jacobi.Jacobi.RegularPrimitiveBounds

/-!
Article: jacobi, Proposition B.1.
The original cotangent/tangent correction is expressed through the actual
regular primitive, uniformly bounded, and identified with the exact
first-order change of the article's affine cosine model.
Use: the sharp original Jacobi angle expansion and exact corrected cosine model use this same correction.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual source angular correction in its genuine regular-primitive form.
Use: the sharp original Jacobi angle expansion and exact corrected cosine model use this same correction.
Article: jacobi, Proposition B.1.
-/
def modelCorrection (a b : ℝ) (n k : ℕ) : ℝ :=
  endpointCorrection a/(2*(frequency a b n)^2*modelAngle a b n k)-
    regularPrimitive a b (modelAngle a b n k)/(2*(frequency a b n)^2)

/-- The true primitive correction is exactly the printed cotangent/tangent expression at every valid original model angle.
Use: identifies the final sharp angular theorem with Proposition B.1 (a) as printed in the article.
Article: jacobi, Proposition B.1.
Proof: substitute the proved literal primitive and cancel its actual reciprocal-angle term; every denominator is nonzero on the true physical angle interval. -/
theorem modelCorrection_eq {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ} (hk : k<n) :
    modelCorrection a b n k=
      (endpointCorrection a*(cos (modelAngle a b n k/2)/sin (modelAngle a b n k/2))-
        endpointCorrection b*(sin (modelAngle a b n k/2)/cos (modelAngle a b n k/2)))/(4*(frequency a b n)^2) := by
  -- The apparent reciprocal-angle singularity cancels in the original explicit primitive, not in an assumed asymptotic identity.
  have hN := frequency_pos ha hb (show 0<n by omega)
  have hx := (modelAngle_endpoint_bounds ha hb hk).1
  obtain ⟨hs,hc⟩ := half_angle_positive hx
  unfold modelCorrection
  rw [regularPrimitive_eq a b hx]
  field_simp [hN.ne',hx.1.ne',hs.ne',hc.ne']
  ring

/-- The source angular correction times the original model sine is precisely the affine corrected-cosine displacement.
Use: cancels the first-order angular term when deriving the sharp actual node error in Proposition B.1 (b).
Article: jacobi, Proposition B.1.
Proof: substitute the exact original half-angle correction, use the
actual sine/cosine double-angle identities and the sine-square identity,
and collect the literal affine scale and shift coefficients. -/
theorem modelCorrection_sin {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ} (hk : k<n) :
    modelCorrection a b n k*sin (modelAngle a b n k)=cos (modelAngle a b n k)-modelNode a b n k := by
  -- The affine correction is obtained by an exact trigonometric identity for the literal original model.
  have hN := frequency_pos ha hb (show 0<n by omega)
  have hx := (modelAngle_endpoint_bounds ha hb hk).1
  obtain ⟨hs,hc⟩ := half_angle_positive hx
  let x := modelAngle a b n k
  have hsin : sin x=2*sin (x/2)*cos (x/2) := by simpa only [show 2*(x/2)=x by ring] using Real.sin_two_mul (x/2)
  have hcos : cos x=1-2*sin (x/2)^2 := by simpa only [show 2*(x/2)=x by ring] using Real.cos_two_mul_eq_one_sub (x/2)
  rw [modelCorrection_eq ha hb hk]
  change ((endpointCorrection a*(cos (x/2)/sin (x/2))-endpointCorrection b*(sin (x/2)/cos (x/2)))/(4*(frequency a b n)^2))*sin x=
    cos x-(modelScale a b n*cos x+modelShift a b n)
  rw [hsin,hcos]
  dsimp [modelScale,modelShift]
  have hs0 : sin (x/2)≠0 := hs.ne'
  have hc0 : cos (x/2)≠0 := hc.ne'
  field_simp [hN.ne',hs0,hc0]
  linear_combination 2*endpointCorrection a*Real.sin_sq_add_cos_sq (x/2)

/-- The exact source angular correction has a uniform inverse-index inverse-frequency bound on the full original first half.
Use: absorbs every finite small index in Proposition B.1 (a), without a missing special-case hypothesis.
Article: jacobi, Proposition B.1.
Proof: the exact leading model angle is at least pi*k/(4*N), controlling
its reciprocal term. The true primitive is bounded on the actual model
comparison interval. The original index cap k<=2*N converts its remaining
inverse-square term to the same inverse-index scale. -/
theorem firstHalf_modelCorrection_bound {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧
      ∀ k,2*k<n → |modelCorrection a b n k|≤M/(frequency a b n*(k+1:ℝ)) := by
  -- The bound is proved from the literal primitive and true model geometry, independently of the sharp actual-angle estimate.
  obtain ⟨C,hC,hbound⟩ := regularPotential_C1_bound a b
  let R := 3*Real.pi/4
  let M := 2*|endpointCorrection a|/Real.pi+C*R
  have hR : 0<R := by dsimp [R]; positivity
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  filter_upwards [firstHalf_modelAngle_cap a b,frequency_degree_comparison a b] with n hcap hdegree
  have hN := hcap.1
  refine ⟨hN,?_⟩
  intro k hk
  let N := frequency a b n
  let t : ℝ := k+1
  let x := modelAngle a b n k
  have ht : 0<t := by dsimp [t]; positivity
  have htN : t≤2*N := by
    have hh : k+1≤n := by omega
    have hhR : (k+1:ℝ)≤(n:ℝ) := by exact_mod_cast hh
    exact hhR.trans hdegree.2.1
  have hx := (modelAngle_endpoint_bounds ha hb (show k<n by omega)).1
  have hx0 : 0<x := hx.1
  have hxlower := (modelAngle_endpoint_bounds ha hb (show k<n by omega)).2.1
  have hRbound : |regularPrimitive a b x|≤C*R :=
    (regularPrimitive_linear a b C (fun t ht => (hbound t ht).1) ⟨hx.1.le,hcap.2 k hk⟩).trans
      (mul_le_mul_of_nonneg_left (hcap.2 k hk) hC.le)
  have hfirst : |endpointCorrection a/(2*N^2*x)|≤(2*|endpointCorrection a|/Real.pi)/(N*t) := by
    rw [abs_div,abs_of_pos (by positivity : 0<2*N^2*x)]
    calc
      _ = (|endpointCorrection a|/(2*N^2))/x := by ring
      _ ≤ (|endpointCorrection a|/(2*N^2))/((Real.pi/4)*t/N) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hxlower
      _ = _ := by field_simp [hN.ne',ht.ne',Real.pi_ne_zero]; ring
  have hsecond : |regularPrimitive a b x/(2*N^2)|≤C*R/(N*t) := by
    rw [abs_div,abs_of_pos (by positivity : 0<2*N^2)]
    exact (div_le_div_of_nonneg_right hRbound (by positivity)).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith))
  change |endpointCorrection a/(2*N^2*x)-regularPrimitive a b x/(2*N^2)|≤M/(N*t)
  calc
    _ ≤ |endpointCorrection a/(2*N^2*x)|+|regularPrimitive a b x/(2*N^2)| := abs_sub _ _
    _ ≤ (2*|endpointCorrection a|/Real.pi)/(N*t)+C*R/(N*t) := add_le_add hfirst hsecond
    _ = _ := by dsimp [M]; ring

end
end jacobi.Jacobi
