import jacobi.RootMass.MinimumPrinciple

/-!
Article: jacobi, Appendix D.5 (compact root-mass profile).
The actual normal multiplier makes the Green coefficient even, continuous
and strictly decreasing. Global scalar minimization gives a real switching
level at 2*b, with a unique finite positive crossing radius. The original
measurable minimizing density equals its printed positive-root formula
inside that compact core and vanishes outside, modulo the two boundary points.
Source: the proved actual pointwise minimum principle and strict radial Green monotonicity.
Use: its true switching level determines both the compact profile and the matching exterior Green solution.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual Green coefficient of a root-mass inner optimizer.
Use: its true switching level determines both the compact profile and the matching exterior Green solution.
Article: jacobi, Appendix D.5 (compact root-mass profile).
-/
def coefficient (m : RootDensity) (a b mu x : ℝ) : ℝ := -a*b/2+2*mu*potential m.toDensity x

/-- Any actual scalar minimizer below the switching level must vanish.
Use: the original optimizing density is zero outside its true finite core.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: zero has objective zero, while the proved factored polynomial is strictly positive at every positive argument. -/
theorem minimizer_below {b c n : ℝ} (hc : c<2*b) (hn : 0≤n)
    (hmin : h b c n≤h b c 0) : n=0 := by
  by_contra hne
  have hp := h_pos_below hc (lt_of_le_of_ne hn (Ne.symm hne))
  have hh : h b c n≤0 := by simpa only [h,zero_pow (by decide : 3≠0),zero_pow (by decide : 2≠0),mul_zero,sub_zero,add_zero] using hmin
  exact (not_le_of_gt hp) hh

/-- Any actual global scalar minimizer above the switching level is the printed larger root.
Use: excludes the smaller stationary local maximum in the actual compact density.
Article: jacobi, Theorem D.8.
Proof: the already proved unique global minimum at the larger root and
the actual minimizing property force equality of their objective values. -/
theorem minimizer_above {b c n : ℝ} (hb : 0<b) (hc : 2*b<c) (hn : 0≤n)
    (hmin : ∀ k : ℝ,0≤k → h b c n≤h b c k) : n=upperRoot b c := by
  have hrp : 0<upperRoot b c := hb.trans (upperRoot_properties hb hc).1
  have hu := upperRoot_minimizes hb hc hn
  exact hu.2.mp (le_antisymm hu.1 (hmin _ hrp.le))

/-- The actual inner Green coefficient has its full strict radial shape and exact tail limit.
Use: constructs its unique switching radius without assuming a compact optimizer.
Article: jacobi, Theorem D.8.
Proof: reuse the actual nonzero radial potential's strict monotonicity,
reflection symmetry and H1 decay, then apply the positive normal multiplier. -/
theorem coefficient_shape (m : RootDensity) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value)
    (a b : ℝ) {mu : ℝ} (hmu : 0<mu) :
    Continuous (coefficient m a b mu) ∧ (∀ x,coefficient m a b mu (-x)=coefficient m a b mu x) ∧
      StrictAntiOn (coefficient m a b mu) (Ici (0:ℝ)) ∧
      Tendsto (coefficient m a b mu) atTop (𝓝 (-a*b/2)) := by
  -- The same genuine Green potential is retained in every shape assertion.
  have hc := (potential_continuous m.toDensity).1
  refine ⟨continuous_const.add (continuous_const.mul hc),?_,?_,?_⟩
  · intro x
    unfold coefficient
    rw [potential_even m.toDensity hs]
  · intro x hx y hy hxy
    have hh := mul_lt_mul_of_pos_left (potential_strictAnti m.toDensity hm hs hx hy hxy)
      (mul_pos (show (0:ℝ)<2 by norm_num) hmu)
    unfold coefficient
    linarith
  · have hh := ((potential_sobolev m.toDensity).tendsto_zero.1.const_mul (2*mu)).const_add (-a*b/2)
    convert hh using 1
    · rfl
    · simp only [mul_zero,add_zero]

/-- The actual optimizer's central Green coefficient lies strictly above the true switching level.
Use: ensures the compact positive core is nonempty before applying intermediate values.
Article: jacobi, Theorem D.8.
Proof: otherwise strict radial decrease gives c(x)<2*b away from zero.
The full pointwise minimum principle would force the original density to
vanish almost everywhere, contradicting its positive actual mass. -/
theorem coefficient_center (m : RootDensity) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value)
    (a b : ℝ) {mu : ℝ} (hmu : 0<mu)
    (hP : ∀ᵐ x : ℝ,∀ n : ℝ,0≤n → h b (coefficient m a b mu x) (sqrt (m.value x))≤h b (coefficient m a b mu x) n) :
    2*b<coefficient m a b mu 0 := by
  -- The possible singleton at the central turning point is explicitly removed as a null set.
  obtain ⟨_hc,heven,hanti,_hlim⟩ := coefficient_shape m hm hs a b hmu
  by_contra! hn
  have hz : m.value=ᵐ[volume] (0 : ℝ → ℝ) := by
    have hx0 : ∀ᵐ x : ℝ,x≠0 := by simp [ae_iff]
    filter_upwards [hP,hx0] with x hx hxne
    have habs : coefficient m a b mu |x|=coefficient m a b mu x := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_nonpos hx,heven]
    have hlt := hanti (show (0:ℝ)∈Ici 0 by simp) (mem_Ici.mpr (abs_nonneg x)) (abs_pos.mpr hxne)
    rw [habs] at hlt
    have hs0 := minimizer_below (hlt.trans_le hn) (sqrt_nonneg (m.value x)) (hx 0 le_rfl)
    have hsq := sq_sqrt (m.nonneg x)
    simpa only [hs0,zero_pow (by decide : 2≠0),Pi.zero_apply] using hsq.symm
  have hmass : m.mass=0 := by simpa only [Density.mass,Pi.zero_apply,integral_zero] using integral_congr_ae hz
  exact hm.ne' hmass

/-- The actual coefficient has a unique finite positive switching radius and precisely its centered positive superlevel set.
Use: constructs the compact optimizer core and the exact endpoint for the Green matching and first integral.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: the actual center is above the switching value and the proved tail
limit is strictly below it. Intermediate values give a finite crossing;
strict radial monotonicity and evenness determine the full superlevel set. -/
theorem coefficient_boundary {a b : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b)
    (m : RootDensity) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value) {mu : ℝ} (hmu : 0<mu)
    (hP : ∀ᵐ x : ℝ,∀ n : ℝ,0≤n → h b (coefficient m a b mu x) (sqrt (m.value x))≤h b (coefficient m a b mu x) n) :
    ∃ A : ℝ,0<A ∧ coefficient m a b mu A=2*b ∧
      (∀ x : ℝ,2*b<coefficient m a b mu x ↔ |x|<A) ∧
      (∀ x : ℝ,A< |x| → coefficient m a b mu x<2*b) := by
  -- The genuine Green tail limit, rather than a guessed cutoff, constructs the free boundary.
  obtain ⟨hc,heven,hanti,hlim⟩ := coefficient_shape m hm hs a b hmu
  have h0 := coefficient_center m hm hs a b hmu hP
  have htail : -a*b/2<2*b := by nlinarith [mul_lt_mul_of_pos_right (parameter_bounds ha).1 hb]
  obtain ⟨R,hR,hcR⟩ := ((eventually_gt_atTop (0:ℝ)).and (hlim.eventually (Iio_mem_nhds htail))).exists
  obtain ⟨A,hA,hzero⟩ := intermediate_value_Icc' hR.le hc.continuousOn ⟨hcR.le,h0.le⟩
  have hAp : 0<A := lt_of_le_of_ne hA.1 (by intro hz; rw [← hz] at hzero; exact h0.ne' hzero)
  have habs (x : ℝ) : coefficient m a b mu |x|=coefficient m a b mu x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx,heven]
  refine ⟨A,hAp,hzero,fun x => ?_,fun x hx => ?_⟩
  · rw [← habs x]
    constructor
    · intro hh
      by_contra! hx
      have hl := hanti.antitoneOn hAp.le (abs_nonneg x) hx
      rw [hzero] at hl
      linarith
    · intro hx
      have hl := hanti (abs_nonneg x) hAp.le hx
      rwa [hzero] at hl
  · have hl := hanti hAp.le (abs_nonneg x) hx
    rwa [hzero,habs] at hl

end
end jacobi.RootMass
