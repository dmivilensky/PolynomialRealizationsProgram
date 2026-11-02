import jacobi.Rearrangement.Approximation
import jacobi.Young.GeneralDensity

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Amplitude clipping makes the L1 approximation compatible with the energy:
on a bounded nonnegative range, the 3/2 power is Lipschitz. The simultaneous
spatial and amplitude cutoffs are reused from the proved general Young
inequality. Thus arbitrary finite-energy densities are approached by the
actual regular densities to which the rearrangement theorem applies.
Source: smooth compact approximation, the mean value theorem and dominated convergence.
Use: passes mass and energy limits from the proved regular density approximations.
-/
namespace jacobi.Rearrangement
noncomputable section
open Set Real MeasureTheory Filter Metric jacobi.Variational
open scoped NNReal ENNReal Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The absolute difference of two actual integrals is bounded by their L1 distance.
Use: passes mass and energy limits from the proved regular density approximations.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: subtract the integrable functions inside the integral and apply the integral norm bound. -/
theorem integral_distance {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    |(∫ x, f x)-(∫ x, g x)| ≤ ∫ x, |f x-g x| := by
  have h := norm_integral_le_integral_norm (μ := volume) (fun x => f x-g x)
  rw [integral_sub hf hg] at h
  simpa only [Real.norm_eq_abs] using h

/-- The energy integrand is Lipschitz on each bounded nonnegative range.
Use: bounded L1 approximation controls the full energy error, not only the mass.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: its derivative is continuous, hence bounded on the compact interval;
the one-dimensional mean value theorem gives the Lipschitz bound. -/
theorem energy_lipschitzOn {B : ℝ} (hB : 0 ≤ B) :
    ∃ L : ℝ≥0, LipschitzOnWith L (fun x : ℝ => x^(3/2 : ℝ)) (Icc 0 B) := by
  -- The derivative exists at zero as well, since the exponent is strictly larger than one.
  let d (x : ℝ) := (3/2 : ℝ)*x^((3/2 : ℝ)-1)
  have hc : Continuous d := continuous_const.mul (Real.continuous_rpow_const (by norm_num))
  obtain ⟨D,hD⟩ := isCompact_Icc.bddAbove_image (K := Icc 0 B) hc.norm.continuousOn
  have hD0 : 0 ≤ D := (norm_nonneg (d 0)).trans (hD (mem_image_of_mem _ ⟨le_refl 0,hB⟩))
  refine ⟨⟨D,hD0⟩,(convex_Icc 0 B).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x _ => (Real.hasDerivAt_rpow_const (x := x) (p := 3/2) (Or.inr (by norm_num))).hasDerivWithinAt) ?_⟩
  intro x hx
  exact hD (mem_image_of_mem _ hx)

/-- A bounded nonnegative density has a regular approximation with simultaneous L1 and energy error control.
Use: the density cutoff sequence can be rearranged without introducing any unproved energy bound.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: choose a small enough proved L1 approximation and clip its amplitude to
the original bound B. Clipping contracts the L1 error; the bounded-range energy
Lipschitz estimate controls the integral of the absolute energy error. -/
theorem exists_regular_energy_approx {m : ℝ → ℝ} (hm : Integrable m)
    (hn : ∀ x, 0 ≤ m x) {B : ℝ} (hb : ∀ x, m x ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : ℝ →ᵇ ℝ) (R : ℝ) (K : ℝ≥0),
      0 ≤ R ∧ f ∈ regularFamily R B K ∧
      (∫ x, |m x-f x|) ≤ ε ∧
      (∫ x, |m x^(3/2 : ℝ)-f x^(3/2 : ℝ)|) ≤ ε := by
  -- A common amplitude bound is restored after smoothing, so its support and Lipschitz bounds are retained.
  have hB : 0 ≤ B := (hn 0).trans (hb 0)
  obtain ⟨L,hL⟩ := energy_lipschitzOn hB
  let δ := ε/(1+(L : ℝ))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g,R,C,K,hR,hg,he⟩ := exists_regular_l1_approx hm hn hδ
  let f : ℝ →ᵇ ℝ := g ⊓ BoundedContinuousFunction.const ℝ B
  have hf : f ∈ regularFamily R B K := by
    refine ⟨hg.1.min_const B,fun x => ⟨le_min (hg.2.1 x).1 hB,min_le_right _ _⟩,fun x hx => ?_⟩
    change min (g x) B=0
    rw [hg.2.2 x hx,min_eq_left hB]
  have hc (x : ℝ) : |m x-f x| ≤ |m x-g x| := by
    change |m x-min (g x) B| ≤ |m x-g x|
    have h := hb x
    grind [abs_eq_max_neg]
  have hei : Integrable (fun x => |m x-f x|) := (hm.sub (regularDensity f hf).integrable).abs
  have herr : (∫ x, |m x-f x|) ≤ δ :=
    (integral_mono hei (hm.sub (regularDensity g hg).integrable).abs hc).trans he
  have hbound (x : ℝ) : |m x^(3/2 : ℝ)-f x^(3/2 : ℝ)| ≤ (L : ℝ)*|m x-f x| := by
    simpa only [Real.dist_eq] using hL.dist_le_mul (m x) ⟨hn x,hb x⟩ (f x) (hf.2.1 x)
  -- The energy error is itself integrable by the same L1 majorant; no energy premise is added to m.
  have heiE : Integrable (fun x => |m x^(3/2 : ℝ)-f x^(3/2 : ℝ)|) := by
    apply (hei.const_mul (L : ℝ)).mono'
    · exact ((Real.continuous_rpow_const (by norm_num)).measurable.comp_aemeasurable
        hm.aestronglyMeasurable.aemeasurable |>.aestronglyMeasurable).sub
          (regularDensity f hf).energy_integrable.aestronglyMeasurable |>.norm
    · exact Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs,abs_abs] using hbound x
  refine ⟨f,R,K,hR,hf,?_,?_⟩
  · exact herr.trans (by dsimp [δ]; exact div_le_self hε.le (by linarith [L.coe_nonneg]))
  · calc
      _ ≤ ∫ x, (L : ℝ)*|m x-f x| := integral_mono heiE (hei.const_mul _) hbound
      _ = (L : ℝ)*(∫ x, |m x-f x|) := integral_const_mul _ _
      _ ≤ (L : ℝ)*δ := mul_le_mul_of_nonneg_left herr L.coe_nonneg
      _ ≤ ε := by dsimp [δ]; rw [← mul_div_assoc,div_le_iff₀ (by positivity)]; nlinarith

/-- The existing simultaneous cutoff tends to the density in the actual L1 norm.
Use: removes the bounded-amplitude hypothesis from regular approximation.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: cutoffs eventually equal the original value at every point and their
absolute error is bounded by the original integrable nonnegative density. -/
theorem cutoff_l1_error (m : Density) :
    Tendsto (fun n => ∫ x, |m.value x- jacobi.Young.cutoff m.value n x|) atTop (𝓝 0) := by
  -- The same cutoff already used for the global Young inequality supplies the bounded approximating domain.
  have h := tendsto_integral_of_dominated_convergence m.value
    (fun n => by
      simpa only [Real.norm_eq_abs,Pi.sub_apply] using
        (m.measurable.sub (jacobi.Young.cutoff_measurable m.measurable n)).aestronglyMeasurable.norm)
    m.integrable (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_abs,abs_of_nonneg (sub_nonneg.mpr (jacobi.Young.cutoff_le m.nonneg n x))]
      exact sub_le_self _ (jacobi.Young.cutoff_nonneg m.nonneg n x))
    (Eventually.of_forall fun x => by
      simpa only [sub_self,abs_zero] using
        (jacobi.Young.cutoff_limit m.value x).const_sub (m.value x) |>.abs)
  simpa only [integral_zero] using h

/-- The same cutoff tends to the density with vanishing absolute energy-integrand error.
Use: transfers finite-energy regular approximation with the exact original limiting energy.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: use continuity of the 3/2 power and dominate its nonnegative cutoff
error by the original integrable energy integrand. -/
theorem cutoff_energy_error (m : Density) :
    Tendsto (fun n => ∫ x, |m.value x^(3/2 : ℝ)-
      jacobi.Young.cutoff m.value n x^(3/2 : ℝ)|) atTop (𝓝 0) := by
  -- Domination is by the given finite energy, without a bound on the original density's height.
  have hc : Continuous (fun x : ℝ => x^(3/2 : ℝ)) := Real.continuous_rpow_const (by norm_num)
  have h := tendsto_integral_of_dominated_convergence (fun x => m.value x^(3/2 : ℝ))
    (fun n => by
      simpa only [Real.norm_eq_abs,Pi.sub_apply,Function.comp_def] using
        ((hc.measurable.comp m.measurable).sub
          (hc.measurable.comp (jacobi.Young.cutoff_measurable m.measurable n))).aestronglyMeasurable.norm)
    m.energy_integrable (fun n => Eventually.of_forall fun x => by
      have hn := jacobi.Young.cutoff_nonneg m.nonneg n x
      have hl := rpow_le_rpow hn (jacobi.Young.cutoff_le m.nonneg n x) (by norm_num : (0 : ℝ) ≤ 3/2)
      rw [Real.norm_eq_abs,abs_abs,abs_of_nonneg (sub_nonneg.mpr hl)]
      exact sub_le_self _ (rpow_nonneg hn _))
    (Eventually.of_forall fun x => by
      simpa only [Function.comp_def,sub_self,abs_zero] using
        ((hc.tendsto (m.value x)).comp (jacobi.Young.cutoff_limit m.value x)).const_sub
          (m.value x^(3/2 : ℝ)) |>.abs)
  simpa only [integral_zero] using h

/-- Every actual finite-energy density has regular approximations controlling both mass and energy integrands.
Use: the proved regular rearrangement theorem now applies to approximations of every variational input.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: first choose an existing cutoff with small L1 and energy errors; then
apply the bounded regular approximation theorem. The two integral triangle
inequalities give the requested errors for the original literal density. -/
theorem exists_regular_finite_energy_approx (m : Density) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : ℝ →ᵇ ℝ) (R C : ℝ) (K : ℝ≥0),
      0 ≤ R ∧ f ∈ regularFamily R C K ∧
      (∫ x, |m.value x-f x|) ≤ ε ∧
      (∫ x, |m.value x^(3/2 : ℝ)-f x^(3/2 : ℝ)|) ≤ ε := by
  -- A single cutoff index controls both errors before any regular approximation is chosen.
  have hhalf : 0 < ε/2 := half_pos hε
  have hcut := ((cutoff_l1_error m).eventually (gt_mem_nhds hhalf)).and
    ((cutoff_energy_error m).eventually (gt_mem_nhds hhalf))
  obtain ⟨n,hn,hE⟩ := hcut.exists
  let b := jacobi.Young.cutoffDensity m.measurable m.nonneg m.energy_integrable n
  have hb (x : ℝ) : b.value x ≤ (n+1 : ℝ) := by
    by_cases hx : x ∈ Icc (-(n+1 : ℝ)) (n+1 : ℝ)
    · change (Icc (-(n+1 : ℝ)) (n+1 : ℝ)).indicator (fun x => min (m.value x) (n+1 : ℝ)) x ≤ _
      rw [indicator_of_mem hx]
      exact min_le_right _ _
    · simp only [b,jacobi.Young.cutoffDensity,jacobi.Young.cutoff,indicator_of_notMem hx]
      positivity
  obtain ⟨f,R,K,hR,hf,hf1,hfE⟩ := exists_regular_energy_approx b.integrable b.nonneg hb hhalf
  let q := regularDensity f hf
  refine ⟨f,R,(n+1 : ℝ),K,hR,hf,?_,?_⟩
  · have hi := integral_mono (m.integrable.sub q.integrable).abs
      (((m.integrable.sub b.integrable).abs).add ((b.integrable.sub q.integrable).abs))
      (fun x => abs_sub_le (m.value x) (b.value x) (f x))
    have ha := integral_add (m.integrable.sub b.integrable).abs (b.integrable.sub q.integrable).abs
    simp only [Pi.add_apply,Pi.sub_apply] at hi ha
    rw [ha] at hi
    change (∫ x, |m.value x-f x|) ≤
      (∫ x, |m.value x-b.value x|)+(∫ x, |b.value x-f x|) at hi
    change (∫ x, |m.value x-b.value x|) < ε/2 at hn
    linarith
  · have hi := integral_mono (m.energy_integrable.sub q.energy_integrable).abs
      (((m.energy_integrable.sub b.energy_integrable).abs).add
        ((b.energy_integrable.sub q.energy_integrable).abs))
      (fun x => abs_sub_le (m.value x^(3/2 : ℝ)) (b.value x^(3/2 : ℝ)) (f x^(3/2 : ℝ)))
    have ha := integral_add (m.energy_integrable.sub b.energy_integrable).abs
      (b.energy_integrable.sub q.energy_integrable).abs
    simp only [Pi.add_apply,Pi.sub_apply] at hi ha
    rw [ha] at hi
    change (∫ x, |m.value x^(3/2 : ℝ)-f x^(3/2 : ℝ)|) ≤
      (∫ x, |m.value x^(3/2 : ℝ)-b.value x^(3/2 : ℝ)|)+
        (∫ x, |b.value x^(3/2 : ℝ)-f x^(3/2 : ℝ)|) at hi
    change (∫ x, |m.value x^(3/2 : ℝ)-b.value x^(3/2 : ℝ)|) < ε/2 at hE
    linarith

end
end jacobi.Rearrangement
