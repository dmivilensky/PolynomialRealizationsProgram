import jacobi.RootMass.Existence

/-!
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Throughout the stated inner parameter range the cubic root objective is
strictly increasing in its nonnegative scalar argument. Actual amplitude
descent therefore makes every genuine inner minimizer meet G_2=T exactly.
This replaces the source's support-removal argument with an exact rescaling
of the same admissible problem, reusing the proved spectral scaling law.
Source: polynomial derivative positivity and actual integral comparison.
Use: strict amplitude descent is valid even when the original mass multiplier is negative.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
set_option backward.isDefEq.respectTransparency false

/-- The derivative polynomial of the actual scalar inner objective.
Use: strict amplitude descent is valid even when the original mass multiplier is negative.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: differentiate the three literal polynomial terms and collect their coefficients. -/
theorem f_hasDerivAt (a b n : ℝ) : HasDerivAt (f a b) (3*n^2+a*b*n+b^2) n := by
  convert (((hasDerivAt_id n).pow 3).add (((hasDerivAt_id n).pow 2).const_mul (a*b/2))).add
    ((hasDerivAt_id n).const_mul (b^2)) using 1
  · rfl
  · norm_num
    ring

/-- The actual scalar derivative is strictly positive on the nonnegative domain for every inner parameter.
Use: justifies global scalar monotonicity rather than relying on a false convexity claim in m.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: for nonnegative a each term is nonnegative with b²>0. Otherwise
12*f'(n)=(6*n+a*b)²+(12-a²)*b² is strictly positive. -/
theorem f_derivative_pos {a b n : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b) (hn : 0≤n) :
    0<3*n^2+a*b*n+b^2 := by
  by_cases han : 0≤a
  · have hp := mul_nonneg (mul_nonneg han hb.le) hn
    nlinarith [sq_pos_of_pos hb]
  · have ha2 := (parameter_bounds ha).2 (by linarith)
    have hp := mul_pos (show 0<12-a^2 by linarith) (sq_pos_of_pos hb)
    nlinarith [sq_nonneg (6*n+a*b)]

/-- The actual inner polynomial strictly increases on its full nonnegative argument domain.
Use: every nonzero density undergoes strict objective descent under an amplitude decrease.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the polynomial is continuous and its proved actual derivative is positive; apply the mean value theorem. -/
theorem f_strictMono {a b : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b) : StrictMonoOn (f a b) (Ici (0:ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · unfold f
    fun_prop
  · intro n hn
    rw [(f_hasDerivAt a b n).deriv]
    exact f_derivative_pos ha hb (interior_subset hn)

/-- Actual root-amplitude scaling, with density multiplied by r².
Use: preserves the genuine finite root-energy domain in exact spectral normalization and localized variation.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
-/
def RootDensity.scaleRoot (m : RootDensity) (r : ℝ) (hr : 0≤r) : RootDensity where
  toDensity := m.toDensity.scale (r^2) (sq_nonneg r)
  root_integrable := by
    change Integrable (fun x => sqrt (r^2*m.value x))
    simp_rw [sqrt_mul (sq_nonneg r),sqrt_sq hr]
    exact m.root_integrable.const_mul r

/-- Root-amplitude scaling has exactly its declared pointwise square root.
Use: compares actual objectives and computes exact polynomial amplitude variations.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: positive square-root multiplication and the nonnegative scalar branch. -/
theorem RootDensity.scaleRoot_sqrt (m : RootDensity) (r : ℝ) (hr : 0≤r) (x : ℝ) :
    sqrt ((m.scaleRoot r hr).value x)=r*sqrt (m.value x) := by
  change sqrt (r^2*m.value x)=_
  rw [sqrt_mul (sq_nonneg r),sqrt_sq hr]

/-- Every genuine nonzero finite root-energy density has strict objective descent under a strict root-amplitude decrease.
Use: discharges the activity argument for all actual inner minimizers.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: scalar monotonicity gives integral comparison. Equality of integrals
would give equality of scalar arguments almost everywhere, forcing the
original density to vanish and contradicting its positive mass. -/
theorem RootDensity.scaleRoot_objective_lt (m : RootDensity) {a b r : ℝ}
    (ha : -2*sqrt 3<a) (hb : 0<b) (hm : 0<m.mass) (hr : 0<r) (hr1 : r<1) :
    (m.scaleRoot r hr.le).objective a b<m.objective a b := by
  -- Integral equality is excluded for the actual measurable density, not only for a proposed positive profile.
  let q := m.scaleRoot r hr.le
  have hmono (x : ℝ) : f a b (sqrt (q.value x))≤f a b (sqrt (m.value x)) := by
    rw [m.scaleRoot_sqrt]
    exact (f_strictMono ha hb).monotoneOn (mul_nonneg hr.le (sqrt_nonneg _)) (sqrt_nonneg _)
      (mul_le_of_le_one_left (sqrt_nonneg _) hr1.le)
  have hle := integral_mono (q.f_integrable a b) (m.f_integrable a b) hmono
  by_contra! hn
  have he : q.objective a b=m.objective a b := le_antisymm hle hn
  have hae := (integral_eq_iff_of_ae_le (q.f_integrable a b) (m.f_integrable a b)
    (Eventually.of_forall hmono)).mp he
  have hz : m.value=ᵐ[volume] (0 : ℝ → ℝ) := by
    filter_upwards [hae] with x hx
    have hh := (f_strictMono ha hb).injOn (sqrt_nonneg (q.value x)) (sqrt_nonneg (m.value x)) hx
    rw [m.scaleRoot_sqrt] at hh
    have hs : sqrt (m.value x)=0 := by nlinarith [sqrt_nonneg (m.value x)]
    have hsq := sq_sqrt (m.nonneg x)
    simpa only [hs,zero_pow (by decide : 2≠0),Pi.zero_apply] using hsq.symm
  have hmass : m.mass=0 := by simpa only [Density.mass,Pi.zero_apply,integral_zero] using integral_congr_ae hz
  exact hm.ne' hmass

/-- Every actual inner minimizer has its true spectral constraint active.
Use: the pointwise minimum principle and profile quadratures evaluate the same prescribed G_2=T.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: if G_2>T, the exact fourth-root root-amplitude normalization reaches
T and strictly decreases the actual objective, contradicting the genuine
inner infimum. All square-root signs and original spectral scaling identities are proved. -/
theorem inner_constraint_active {a b T : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b) (hT : 0<T)
    (m : RootDensity) (hG : T≤observe m.toDensity .second) (hmin : m.cost a b=inner a b T) :
    observe m.toDensity .second=T := by
  -- The constructed competitor belongs to the original inner admissible set.
  apply le_antisymm _ hG
  by_contra! hslack
  let G := observe m.toDensity .second
  have hGp : 0<G := hT.trans_le hG
  let c := sqrt (T/G)
  have hc : 0<c := sqrt_pos.mpr (div_pos hT hGp)
  have hc1 : c<1 := (sqrt_lt' zero_lt_one).mpr (by simpa only [one_pow] using (div_lt_one hGp).mpr hslack)
  have hc2 : c^2=T/G := sq_sqrt (div_nonneg hT.le hGp.le)
  let r := sqrt c
  have hr : 0<r := sqrt_pos.mpr hc
  have hr1 : r<1 := (sqrt_lt' zero_lt_one).mpr (by simpa only [one_pow] using hc1)
  have hr2 : r^2=c := sq_sqrt hc.le
  let q := m.scaleRoot r hr.le
  have hqG : observe q.toDensity .second=T := by
    change observe (m.toDensity.scale (r^2) (sq_nonneg r)) .second=T
    rw [Density.scale_second,hr2,hc2]
    exact div_mul_cancel₀ _ hGp.ne'
  have hm := mass_pos_of_observe_pos m.toDensity .second hGp
  have hqF := m.scaleRoot_objective_lt ha hb hm hr hr1
  have hlo : inner a b T≤q.cost a b := sInf_le ⟨q,hqG.ge,rfl⟩
  rw [← hmin] at hlo
  have hlt : q.cost a b<m.cost a b :=
    (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (q.objective_nonneg ha hb.le) hqF)).mpr hqF
  exact (not_lt_of_ge hlo) hlt

end
end jacobi.RootMass
