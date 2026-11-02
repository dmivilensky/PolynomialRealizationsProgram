import jacobi.GelfandLevitan.HalfReferenceParseval
import jacobi.GelfandLevitan.TransformationOperator

/-!
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
The original norming-weighted target reference waves differ from the
actual half-reference basis by a summable inverse-square perturbation.
All bounds come from the already proved original spectral and norming
estimates; there is no numerical or perturbation-size assumption.
Use: normalized_reference_pointwise_bound transfers the actual rho_k-1 estimate to the true sqrt(rho_k) factors in the source reference perturbation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Square-root normalization changes a positive weight by no more than its original deviation from one.
Use: normalized_reference_pointwise_bound transfers the actual rho_k-1 estimate to the true sqrt(rho_k) factors in the source reference perturbation.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: factor r-1=(sqrt(r)-1)*(sqrt(r)+1), whose second factor is at least one. -/
theorem sqrt_sub_one_bound {r : ℝ} (hr : 0≤r) : |Real.sqrt r-1|≤|r-1| := by
  calc
    _ ≤ |Real.sqrt r-1| * (Real.sqrt r+1) :=
      le_mul_of_one_le_right (abs_nonneg _) (by linarith [Real.sqrt_nonneg r])
    _ = |r-1| := by
      rw [← abs_of_nonneg (show 0≤Real.sqrt r+1 by positivity),← abs_mul]
      congr 1
      nlinarith [Real.sq_sqrt hr]

/-- The original source reference normalization at every genuine spectral index.
Use: normalizedSourceMap and normalizedReferenceMap use this same true norming constant.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def halfNormalization (a : ℝ) (k : ℕ) : ℝ := Real.sqrt 2/Real.sqrt (norming a k)

/-- The actual norming-weighted target reference wave on the common compact physical domain.
Use: its original half-space vector is the g_k system compactly perturbing the actual reference half basis.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def normalizedSourceMap (a : ℝ) (ha : -1<a) (k : ℕ) : C(Interval,ℝ) :=
  (halfNormalization a k*Real.sqrt (normingRatio a ha k)) •
    realHalfWave a ha (jacobi.Bessel.sigma a ha k)

/-- The actual normalized unperturbed half-reference wave on the original compact domain.
Use: its true L2 embedding is identified with halfReferenceVector before the compact perturbation construction.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def normalizedReferenceMap (a : ℝ) (ha : -1<a) (k : ℕ) : C(Interval,ℝ) :=
  halfNormalization a k • realHalfWave a ha (eigenvalue a k)

/-- The genuine reference normalization cancels its original spectral amplitude uniformly.
Use: normalized_reference_pointwise_bound absorbs the true f_k amplitude and spectral difference bounds into an inverse-square perturbation.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the original positive norm satisfies fn_k>=c*p_k^2. Taking true square roots gives sqrt(c)*p_k<=sqrt(fn_k), and division by the positive normalizing factors proves the bound. -/
theorem halfNormalization_amplitude_bound (a : ℝ) (ha : -1<a) :
    ∃ C:ℝ,0<C ∧ ∀ k,halfNormalization a k*(k+1:ℝ)^(-gamma a)≤C := by
  -- The lower norm estimate includes every genuine small index.
  obtain ⟨c,_,hc,_,hN⟩ := norming_bounds ha
  refine ⟨Real.sqrt 2/Real.sqrt c,by positivity,fun k => ?_⟩
  let p := (k+1:ℝ)^(-gamma a)
  have hp : 0<p := Real.rpow_pos_of_pos (by positivity) _
  have hpsq : p^2=1/(k+1:ℝ)^(2*gamma a) := by
    dsimp [p]
    rw [Real.rpow_neg (by positivity : 0≤(k+1:ℝ)),show 2*gamma a=gamma a*2 by ring,
      Real.rpow_mul (by positivity : 0≤(k+1:ℝ)),Real.rpow_two,inv_pow,one_div]
  have hn : c*p^2≤norming a k := by
    rw [hpsq]
    simpa only [mul_one_div] using (hN k).1
  have hs := Real.sqrt_le_sqrt hn
  rw [Real.sqrt_mul hc.le,Real.sqrt_sq hp.le] at hs
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hc)).mpr
  change (Real.sqrt 2/Real.sqrt (norming a k)*p)*Real.sqrt c≤Real.sqrt 2
  calc
    _ = (Real.sqrt 2/Real.sqrt (norming a k))*(Real.sqrt c*p) := by ring
    _ ≤ (Real.sqrt 2/Real.sqrt (norming a k))*Real.sqrt (norming a k) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := div_mul_cancel₀ _ (Real.sqrt_pos.mpr (norming_pos ha k)).ne'

/-- The true normalized target reference waves differ uniformly from the original reference waves by O(k^-2).
Use: normalized_reference_vector_bound gives summable true Hilbert perturbations in the two-bases compact-operator construction.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: split the actual difference into the normalized spectral displacement and the square-root weight displacement. The proved original f bounds and rho bounds, together with the true norm-amplitude cancellation, give one inverse-square constant. -/
theorem normalized_reference_pointwise_bound (a : ℝ) (ha : -1<a) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ k:ℕ in atTop,∀ t:Interval,
      |normalizedSourceMap a ha k t-normalizedReferenceMap a ha k t|≤C/(k+1:ℝ)^2 := by
  -- Every estimate is for the unchanged actual reference solutions and norming products.
  obtain ⟨A,B,hA,hB,hf⟩ := spectral_solution_bounds ha
  obtain ⟨_,R,D,_,hR,hD,hρ⟩ := normingRatio_bounds ha
  obtain ⟨L,hL,hN⟩ := halfNormalization_amplitude_bound a ha
  refine ⟨L*(Real.sqrt R*B+D*A),by positivity,?_⟩
  filter_upwards [hf] with k hk t
  let p := (k+1:ℝ)^(-gamma a)
  have hp : 0<p := Real.rpow_pos_of_pos (by positivity) _
  have hn : 0≤halfNormalization a k := by unfold halfNormalization; positivity
  have hr : Real.sqrt (normingRatio a ha k)≤Real.sqrt R := Real.sqrt_le_sqrt (hρ k).2.1
  have hdiff := (hk (halfTime t) (halfTime_mem t)).2.2
  have hτ := (hk (halfTime t) (halfTime_mem t)).2.1
  have hroot := (sqrt_sub_one_bound (normingRatio_properties ha k).2.le).trans (hρ k).2.2
  have he : normalizedSourceMap a ha k t-normalizedReferenceMap a ha k t=
      halfNormalization a k*(Real.sqrt (normingRatio a ha k)*
        (realSolution a (jacobi.Bessel.sigma a ha k) (halfTime t)-realSolution a (eigenvalue a k) (halfTime t))+
        (Real.sqrt (normingRatio a ha k)-1)*realSolution a (eigenvalue a k) (halfTime t)) := by
    change (halfNormalization a k*Real.sqrt (normingRatio a ha k))*
      realSolution a (jacobi.Bessel.sigma a ha k) (halfTime t)-
        halfNormalization a k*realSolution a (eigenvalue a k) (halfTime t)=_
    ring
  rw [he,abs_mul,abs_of_nonneg hn]
  calc
    _ ≤ halfNormalization a k*(|Real.sqrt (normingRatio a ha k)*
        (realSolution a (jacobi.Bessel.sigma a ha k) (halfTime t)-realSolution a (eigenvalue a k) (halfTime t))|+
        |(Real.sqrt (normingRatio a ha k)-1)*realSolution a (eigenvalue a k) (halfTime t)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hn
    _ ≤ halfNormalization a k*(Real.sqrt R*(B*p/(k+1:ℝ)^2)+(D/(k+1:ℝ)^2)*(A*p)) := by
      rw [abs_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul hr hdiff (abs_nonneg _) (Real.sqrt_nonneg _))
        (mul_le_mul hroot hτ (abs_nonneg _) (by positivity))) hn
    _ = (halfNormalization a k*p)*(Real.sqrt R*B+D*A)/(k+1:ℝ)^2 := by ring
    _ ≤ L*(Real.sqrt R*B+D*A)/(k+1:ℝ)^2 := by
      gcongr
      exact hN k

end
end jacobi.GelfandLevitan
