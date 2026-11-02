import jacobi.Fredholm.InverseProfile

/-!
Article: jacobi, Theorem D.7.
Every constructed physical candidate has a global exponential density
bound. The free case follows from the actual zero first integral near
the free Green limit; the compact case uses the proved finite support.
Source: the integrating-factor proof of the scalar differential inequality.
Use: proves the source's asserted decay for arbitrary free candidates.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every genuine full-support Fredholm optimizer has an exponential density bound outside a finite radius.
Use: proves the source's asserted decay for arbitrary free candidates.
Article: jacobi, Theorem D.7.
Proof: the actual Green diagonal tends to one half. Beyond a finite
radius its zero phase is at least (g-1/2)^2, hence g'<=-(g-1/2).
The integrating factor (g-1/2)*exp(x) decreases there. Squaring the
resulting bound in the actual clipped density formula gives exp(-2*x);
evenness gives the same estimate at the other end. -/
theorem Optimizer.free_density_tail {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s)
    (ht : P.tau hs=1) :
    ∃ a C : ℝ,0<a ∧ 0<C ∧ ∀ x : ℝ,a≤ |x| → P.density.value x≤C*exp (-2*|x|) := by
  -- The exponential rate is derived from the true first integral, not postulated from convergence.
  let g := P.g hs.le
  have he : P.edge=(1/2:ℝ) := (P.free_iff hs).1.mp ht
  have hg := (green_diagonal_limits P.density hs.le P.pole).1
  change Tendsto g atTop (𝓝 (1/2:ℝ)) at hg
  have hlim : Tendsto (fun x => P.A^2*g x*(g x-(1/2:ℝ))) atTop (𝓝 0) := by
    have h := (hg.const_mul (P.A^2)).mul (hg.sub_const (1/2:ℝ))
    simpa only [sub_self,mul_zero] using h
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1)))
  let a := max R 1
  have ha : 0<a := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right R 1)
  have hpos (x : ℝ) : 0<g x-(1/2:ℝ) :=
    sub_pos.mpr (green_diagonal_strict P.density P.mass_pos hs P.pole x)
  have hslope (x : ℝ) (hx : a≤x) : deriv g x≤-(g x-(1/2:ℝ)) := by
    have hp := hR x ((le_max_left R 1).trans hx)
    have hphase : (g x-(1/2:ℝ))^2≤phase P.A P.edge (g x) := by
      unfold phase
      rw [he,max_eq_left (hpos x).le]
      nlinarith [mul_le_mul_of_nonneg_right hp.le (sq_nonneg (g x-(1/2:ℝ)))]
    have hroot := sqrt_le_sqrt hphase
    rw [sqrt_sq (hpos x).le] at hroot
    have hbranch := (P.green_jacobian hs (ha.trans_le hx)).deriv
    change deriv g x= -sqrt (phase P.A P.edge (g x)) at hbranch
    linarith
  let W := fun x => (g x-(1/2:ℝ))*exp x
  have hgc : ContDiff ℝ 2 g := P.density.greenDiagonal_contDiff P.continuous hs.le P.pole
  have hd (x : ℝ) : HasDerivAt W ((deriv g x+g x-(1/2:ℝ))*exp x) x := by
    convert (((hgc.differentiable (by norm_num) x).hasDerivAt.sub_const (1/2:ℝ)).mul
      (Real.hasDerivAt_exp x)) using 1
    ring
  have hanti : AntitoneOn W (Ici a) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
      ((hgc.continuous.sub continuous_const).mul continuous_exp).continuousOn
      (fun x _ => (hd x).hasDerivWithinAt)
    intro x hx
    have h := hslope x (interior_subset hx)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (exp_pos x).le
  have hWa : 0<W a := mul_pos (hpos a) (exp_pos a)
  have hbound (x : ℝ) (hx : a≤x) : g x-(1/2:ℝ)≤W a*exp (-x) := by
    have hh := mul_le_mul_of_nonneg_right
      (hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx) (exp_pos (-x)).le
    have hcancel : W x*exp (-x)=g x-(1/2:ℝ) := by
      dsimp only [W]
      rw [mul_assoc,← exp_add,add_neg_cancel,exp_zero,mul_one]
    rwa [hcancel] at hh
  let C := P.A^2/(2*s)*(W a)^2
  have hA := (P.parameter_signs hs).2
  have hC : 0<C := mul_pos (div_pos (sq_pos_of_pos hA) (by positivity)) (sq_pos_of_pos hWa)
  refine ⟨a,C,ha,hC,?_⟩
  intro x hx
  have hsq := pow_le_pow_left₀ (hpos |x|).le (hbound |x| hx) 2
  have hExp : (W a*exp (-|x|))^2=(W a)^2*exp (-2*|x|) := by
    rw [mul_pow]
    congr 1
    rw [pow_two,← exp_add]
    congr 1
    ring
  rw [hExp] at hsq
  have hden : 0<2*s := by positivity
  have hformula := P.density_formula hs |x|
  rw [he,max_eq_left (hpos |x|).le,P.radial.abs_eq] at hformula
  have hh : P.density.value x*(2*s)≤P.A^2*((W a)^2*exp (-2*|x|)) := by
    rw [mul_comm, hformula]
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg P.A)
  have hdiv := (le_div_iff₀ hden).mpr hh
  convert hdiv using 1
  dsimp only [C]
  ring

/-- A continuous nonnegative density with an exponential tail has a global exponential bound.
Use: turns both actual support regimes into the source's single global decay assertion.
Article: jacobi, Theorem D.7.
Proof: compactness bounds the density on the remaining centered
interval. Increase the tail constant by that compact bound times
exp(2*a); monotonicity of exp supplies the same estimate inside. -/
theorem exponential_tail_global {m : ℝ → ℝ} (hm : Continuous m)
    {a B : ℝ} (hB : 0<B)
    (htail : ∀ x : ℝ,a≤ |x| → m x≤B*exp (-2*|x|)) :
    ∃ C : ℝ,0<C ∧ ∀ x : ℝ,m x≤C*exp (-2*|x|) := by
  -- Compactness controls the part of the actual function not covered by the tail estimate.
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hm.continuousOn : ContinuousOn m (Icc (-a) a))
  let C := B+(|K|+1)*exp (2*a)
  have hC : 0<C := by dsimp [C]; positivity
  have hBC : B≤C := by
    dsimp only [C]
    nlinarith [mul_pos (by positivity : 0< |K|+1) (exp_pos (2*a))]
  have hKC : (|K|+1)*exp (2*a)≤C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro x
  by_cases hx : a≤ |x|
  · exact (htail x hx).trans (mul_le_mul_of_nonneg_right
      hBC (exp_pos _).le)
  · have hxa : |x|≤a := (not_le.mp hx).le
    have hmx : m x≤ |K|+1 := by
      have hh := (le_norm_self (m x)).trans (hK x (abs_le.mp hxa))
      exact hh.trans ((le_abs_self K).trans (by linarith))
    have hexp : (1:ℝ)≤exp (2*a-2*|x|) := one_le_exp_iff.mpr (by linarith)
    have hbound : |K|+1≤((|K|+1)*exp (2*a))*exp (-2*|x|) := by
      rw [mul_assoc,← exp_add]
      have he : 2*a+-2*|x|=2*a-2*|x| := by ring
      rw [he]
      exact (mul_le_mul_of_nonneg_left hexp (by positivity)).trans_eq' (mul_one _)
    apply hmx.trans (hbound.trans _)
    exact mul_le_mul_of_nonneg_right hKC (exp_pos _).le

/-- Every arbitrary physical Fredholm candidate has a genuine global exponential density bound.
Use: completes the decay assertion in the source construction and justifies all spatial integral interpretations.
Article: jacobi, Theorem D.7.
Proof: at full support the actual first integral gives an exponential
tail. Below full support the actual density vanishes beyond its proved
finite support radius, giving an immediate tail bound. Continuity and
compactness extend either tail bound to the whole line. -/
theorem candidate_exponential_decay {s t c : ℝ} (hs : 0<s)
    (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    ∃ C : ℝ,0<C ∧ ∀ x : ℝ,(candidate s t c hs ht hc).density.value x≤C*exp (-2*|x|) := by
  -- Both regimes concern the original constructed density and its actual operator.
  let P := candidate s t c hs ht hc
  have hp := candidate_parameters hs ht hc
  change P.tau hs=t ∧ P.chi hs=c at hp
  rcases lt_or_eq_of_le ht.2 with hti | hte
  · obtain ⟨a,ha,_,hpos,_⟩ := P.compact_exterior hs (by rw [hp.1]; exact hti)
    apply exponential_tail_global P.continuous (by norm_num : (0:ℝ)<1)
    intro x hx
    have hn : ¬0<P.density.value x := by rw [hpos x]; exact not_lt.mpr hx
    have hz : P.density.value x=0 := le_antisymm (not_lt.mp hn) (P.density.nonneg x)
    rw [hz]
    positivity
  · obtain ⟨a,B,ha,hB,htail⟩ := P.free_density_tail hs (hp.1.trans hte)
    exact exponential_tail_global P.continuous hB htail

end
end jacobi.Fredholm
