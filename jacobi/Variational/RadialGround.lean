import jacobi.Variational.ACCalculus
import jacobi.Variational.Tails
import chebyshev2.GroundState.Article

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
The actual positive spectral ground state is even for every even L1 density.
For a symmetric decreasing nonzero density its derivative is strictly negative
on the positive half-line. No continuity or boundedness of the density is used.
Source: the one-dimensional Wronskian and the ground-state differential equation.
Use: supplies the initial slope for the strict radial ground-state argument.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Set Filter Real chebyshev2.Sobolev
open chebyshev2.GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every actual positive ground state of an even integrable density is even and has zero central slope.
Use: supplies the initial slope for the strict radial ground-state argument.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the reflected Wronskian has a.e. zero derivative. Its L1 integrability
forces its constant value to be zero; the reflected-to-original quotient is
then constant and equals one at the origin. -/
theorem ground_even {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (heven : ∀ x,m (-x)=m x) :
    (∀ x,H1.rep G.u (-x)=H1.rep G.u x) ∧ G.d 0=0 := by
  -- Reflection preserves null sets; the two a.e. ODEs therefore hold together.
  let u := H1.rep G.u
  let W (x : ℝ) := G.d x*u (-x)+u x*G.d (-x)
  have hrefl := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
  have hud (x : ℝ) : HasDerivAt u (G.d x) x := G.derivative x
  have hur (x : ℝ) : HasDerivAt (fun y => u (-y)) (-G.d (-x)) x := by
    simpa only [Function.comp_def,mul_neg_one] using
      (hud (-x)).comp x (hasDerivAt_neg x)
  have hWac (a b : ℝ) : AbsolutelyContinuousOnInterval W a b :=
    ((G.d_locallyAC a b).mul ((G.c1.comp contDiff_neg).contDiffOn.absolutelyContinuousOnInterval)).add
      ((G.c1.contDiffOn.absolutelyContinuousOnInterval).mul (locallyAC_reflect G.d_locallyAC G.ode a b))
  have hWd : ∀ᵐ x,HasDerivAt W 0 x := by
    filter_upwards [G.ode,hrefl.ae G.ode] with x hx hr
    have hdr := hr.comp x (hasDerivAt_neg x)
    convert (hx.mul (hur x)).add ((hud x).mul hdr) using 1
    · rfl
    · dsimp only [u,Function.comp_def]
      rw [heven]
      ring
  have hWi : Integrable W :=
    (l2_product_integrable G.d_memLp
      ((H1.regular G.u).value_memLp.comp_measurePreserving (Measure.measurePreserving_neg volume))).add
      (l2_product_integrable (H1.regular G.u).value_memLp
        (G.d_memLp.comp_measurePreserving (Measure.measurePreserving_neg volume)))
  have hWconst (x : ℝ) : W x=W 0 := locallyAC_const hWac hWd x 0
  have hWzero : W 0=0 := by
    have hc : Integrable (fun _ : ℝ => W 0) := hWi.congr (Eventually.of_forall hWconst)
    simpa only [integrable_const_iff,isFiniteMeasure_iff,Real.volume_univ,
      lt_self_iff_false,or_false] using hc
  have hW (x : ℝ) : W x=0 := (hWconst x).trans hWzero
  have hquot (x : ℝ) : HasDerivAt (fun y => u (-y)/u y) 0 x := by
    convert (hur x).div (hud x) (G.positive x).ne' using 1
    symm
    apply (div_eq_zero_iff).mpr
    left
    have hw := hW x
    dsimp only [W] at hw
    nlinarith
  have he (x : ℝ) : u (-x)/u x=1 := by
    have h := is_const_of_deriv_eq_zero (fun y => (hquot y).differentiableAt)
      (fun y => (hquot y).deriv) x 0
    simpa only [neg_zero,div_self (show u 0≠0 from (G.positive 0).ne')] using h
  refine ⟨fun x => (div_eq_one_iff_eq (G.positive x).ne').mp (he x),?_⟩
  have hw := hW 0
  simp only [W,neg_zero] at hw
  have hp : 0<u 0 := G.positive 0
  nlinarith

/-- The actual positive ground state has strictly negative derivative at every positive radius.
Use: proves the strict decrease of the top-eigenvalue gradient used in the KKT profiles.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: where 1-kappa*m is negative, integrate its negative upper bound from
the zero central slope. Where it is nonnegative, radial monotonicity makes
the slope nondecreasing thereafter; a nonnegative slope would contradict
positivity and decay of the ground state. -/
theorem ground_slope_neg {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hs : SymmetricDecreasing m) {x : ℝ} (hx : 0<x) :
    G.d x<0 := by
  -- The coefficient can cross zero only from negative to nonnegative.
  let c := groundParameter hm hn
  let u := H1.rep G.u
  have hc : 0<c := G.coupling_positive
  have hzero : G.d 0=0 := (ground_even G hs.even).2
  by_cases hxcoef : 1-c*m x<0
  · have hi : IntervalIntegrable (fun y => (1-c*m y)*u y) volume 0 x :=
      (G.d_locallyAC 0 x).intervalIntegrable_deriv.congr_ae
        (ae_restrict_of_ae (G.ode.mono fun _ h => h.deriv))
    have hui : IntervalIntegrable u volume 0 x := (H1.continuous_rep G.u).intervalIntegrable 0 x
    have hb : (∫ y in (0:ℝ)..x, (1-c*m y)*u y) ≤
        (1-c*m x)*(∫ y in (0:ℝ)..x, u y) := by
      rw [← intervalIntegral.integral_const_mul,
        intervalIntegral.integral_of_le hx.le,intervalIntegral.integral_of_le hx.le]
      apply integral_mono_ae hi.1 (hui.const_mul _).1
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact mul_le_mul_of_nonneg_right
        (by nlinarith [hs.decreasing hy.1 hx hy.2]) (G.positive y).le
    have hp : 0<∫ y in (0:ℝ)..x,u y := intervalIntegral.integral_pos hx
      (H1.continuous_rep G.u).continuousOn (fun y _ => (G.positive y).le)
      ⟨0,⟨le_rfl,hx.le⟩,G.positive 0⟩
    rw [locallyAC_integral_eq_sub G.d_locallyAC G.ode,hzero,sub_zero] at hb
    exact hb.trans_lt (mul_neg_of_neg_of_pos hxcoef hp)
  · have hcoeff : 0≤1-c*m x := le_of_not_gt hxcoef
    have hdmono {y : ℝ} (hxy : x≤y) : G.d x≤G.d y := by
      apply locallyAC_le_of_derivative_nonneg G.d_locallyAC G.ode hxy
      exact Eventually.of_forall fun z hz => mul_nonneg
        (by nlinarith [hs.decreasing hx (hx.trans_le hz.1) hz.1]) (G.positive z).le
    by_contra hnot
    have hdx : 0≤G.d x := le_of_not_gt hnot
    have humono : MonotoneOn u (Ici x) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici x)
        (H1.continuous_rep G.u).continuousOn
        (fun y _ => (G.derivative y).hasDerivWithinAt)
        (fun y hy => hdx.trans (hdmono (by
          have hh : x<y := by simpa only [interior_Ici,mem_Ioi] using hy
          exact hh.le)))
    have ht : u x≤0 := ge_of_tendsto (H1.rep_tendsto_zero G.u).1
      ((eventually_ge_atTop x).mono fun y hy => humono (by simp) hy hy)
    exact (G.positive x).not_ge ht

/-- The ground state is strictly decreasing on the entire closed nonnegative half-line.
Use: the squared ground state gives the continuous even strictly decreasing top gradient.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the derivative is strictly negative at every interior point of the half-line. -/
theorem ground_strictAnti {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hs : SymmetricDecreasing m) :
    StrictAntiOn (H1.rep G.u) (Ici 0) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici 0) (H1.continuous_rep G.u).continuousOn
    (fun y _ => (G.derivative y).hasDerivWithinAt)
  intro y hy
  exact ground_slope_neg G hs (by simpa only [interior_Ici,mem_Ioi] using hy)

/-- The actual positive ground state has the radial shape asserted for every nonzero radial density.
Use: closes the ground-state clause of Rearrangement (c), with a strictly stronger conclusion.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: combine reflected Wronskian symmetry with strict half-line monotonicity. -/
theorem ground_symmetricDecreasing {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hs : SymmetricDecreasing m) :
    SymmetricDecreasing (H1.rep G.u) where
  even := (ground_even G hs.even).1
  decreasing := (ground_strictAnti G hs).antitoneOn.mono (Ioi_subset_Ici_self)

end
end jacobi.Variational
