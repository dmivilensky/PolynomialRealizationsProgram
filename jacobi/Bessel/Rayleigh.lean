import jacobi.Bessel.StieltjesDecay
import jacobi.Bessel.SpectralBounds

/-!
Article: jacobi, Lemma 1.3.
The genuine finite Stieltjes defect has a summable inverse-square bound,
so its full limit is the actual Bessel logarithmic-derivative defect.
The actual Riccati decay excludes any escaped first trace and proves
the exact printed infinite first Rayleigh sum, without a product premise.
Source: dominated convergence for genuine finite and infinite resolvent observations.
Use: it has a summable inverse-square majorant even before the full infinite first mass is identified.
-/
namespace jacobi.Bessel
noncomputable section
open Set Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The exact difference between mass and a positive Stieltjes resolvent term.
Use: it has a summable inverse-square majorant even before the full infinite first mass is identified.
Article: jacobi, Lemma 1.3.
-/
def resolventDefect (s x : ℝ) : ℝ := s*x^2/(1+s*x)

/-- The genuine scalar resolvent defect is nonnegative and at most its quadratic numerator.
Use: uniform inverse-square control permits the actual finite-to-infinite defect limit.
Article: jacobi, Lemma 1.3.
Proof: its denominator is at least one, and the original numerator is nonnegative. -/
theorem resolventDefect_bounds {s x : ℝ} (hs : 0≤s) (hx : 0≤x) :
    0≤resolventDefect s x ∧ resolventDefect s x≤s*x^2 := by
  have hd : 1≤1+s*x := by linarith [mul_nonneg hs hx]
  exact ⟨div_nonneg (mul_nonneg hs (sq_nonneg x)) (by linarith),
    div_le_self (mul_nonneg hs (sq_nonneg x)) hd⟩

/-- The true scalar resolvent remainder is exactly the difference between its mass and Stieltjes summand.
Use: the actual finite defect sum equals the original finite trace minus its genuine logarithmic derivative.
Article: jacobi, Lemma 1.3.
Proof: the nonnegative parameter and entry give a strictly positive denominator, so ordinary field algebra applies. -/
theorem resolventDefect_difference {s x : ℝ} (hs : 0≤s) (hx : 0≤x) :
    x-x/(1+s*x)=resolventDefect s x := by
  unfold resolventDefect
  have hd : 1+s*x≠0 := ne_of_gt (by nlinarith [mul_nonneg hs hx] : 0<1+s*x)
  field_simp [hd]
  ring

/-- The original Bessel logarithmic-derivative defect equals the actual convergent infinite spectral defect series.
Use: excludes a hidden constant first-trace defect after taking the large-parameter limit.
Article: jacobi, Lemma 1.3.
Proof: each finite defect is its genuine trace minus its actual
Stieltjes logarithmic derivative. The finite spectral entries converge
and their defects are bounded by a summable inverse-square majorant.
Pass both genuine finite observations to their independently proved limits. -/
theorem stieltjes_defect_identity {a s : ℝ} (ha : -1<a) (hs : 0≤s) :
    stieltjes a 0-stieltjes a s=∑' k,resolventDefect s (edgeValue a ha k) := by
  -- The reference beta=0 chooses one actual finite approximation and adds no hypothesis to the Bessel result.
  have hb : (-1:ℝ)<0 := by norm_num
  let C := jacobi.Jacobi.traceBound a 0
  have hpoint (k : ℕ) : Tendsto
      (fun n : ℕ => resolventDefect s (jacobi.Jacobi.finiteLambdaAt a 0 ha hb n k)) atTop
      (𝓝 (resolventDefect s (edgeValue a ha k))) := by
    have hd : 1+s*edgeValue a ha k≠0 := ne_of_gt (by
      nlinarith [mul_nonneg hs ((edgeValue_properties ha).1 k).le])
    have hc : ContinuousAt (resolventDefect s) (edgeValue a ha k) := by
      unfold resolventDefect
      fun_prop (disch := exact hd)
    exact hc.tendsto.comp (jacobi.Jacobi.finiteLambdaAt_tendsto ha hb k)
  have h := tendsto_tsum_of_dominated_convergence
    ((inverse_square_majorant_summable C).mul_left s) hpoint (by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn k
      rw [Real.norm_eq_abs,abs_of_nonneg (resolventDefect_bounds hs
        (jacobi.Jacobi.finiteLambdaAt_nonneg ha hb n k)).1]
      apply (resolventDefect_bounds hs (jacobi.Jacobi.finiteLambdaAt_nonneg ha hb n k)).2.trans
      have hp := pow_le_pow_left₀ (jacobi.Jacobi.finiteLambdaAt_nonneg ha hb n k)
        (jacobi.Jacobi.finiteLambdaAt_index_bound ha hb hn k) 2
      simpa only [div_pow] using mul_le_mul_of_nonneg_left hp hs)
  have he (n : ℕ) : (∑' k,resolventDefect s (jacobi.Jacobi.finiteLambdaAt a 0 ha hb n k))=
      (∑ i:Fin n,jacobi.Jacobi.finiteLambda a 0 ha hb n i)- jacobi.Jacobi.finiteStieltjes a 0 ha hb n s := by
    rw [jacobi.Jacobi.finiteLambdaAt_tsum ha hb n (resolventDefect s) (by simp [resolventDefect])]
    unfold jacobi.Jacobi.finiteStieltjes
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hx := jacobi.Jacobi.finiteLambdaAt_nonneg ha hb n i.val
    rw [jacobi.Jacobi.finiteLambdaAt_eq ha hb i.isLt] at hx
    exact (resolventDefect_difference hs hx).symm
  have hfun : (fun n : ℕ => ∑' k,resolventDefect s (jacobi.Jacobi.finiteLambdaAt a 0 ha hb n k))=
      fun n : ℕ => (∑ i:Fin n,jacobi.Jacobi.finiteLambda a 0 ha hb n i)- jacobi.Jacobi.finiteStieltjes a 0 ha hb n s :=
    funext he
  rw [hfun] at h
  have hlim := (jacobi.Jacobi.finiteLambda_sum_tendsto ha hb).sub
    (jacobi.Jacobi.finiteStieltjes_tendsto ha hb hs)
  rw [stieltjes_zero ha]
  exact (tendsto_nhds_unique h hlim).symm

/-- For every genuine positive Bessel edge value, its scalar Stieltjes defect tends to that entire value at large positive parameter.
Use: dominated convergence then recovers the full actual infinite first spectral mass.
Article: jacobi, Lemma 1.3.
Proof: divide numerator and denominator by the positive parameter.
Its inverse tends to zero and the remaining denominator tends to the
actual nonzero positive edge value. -/
theorem resolventDefect_tendsto {x : ℝ} (hx : 0<x) :
    Tendsto (fun s : ℝ => resolventDefect s x) atTop (𝓝 x) := by
  -- The parameter is eventually positive, so the rescaling cancels only genuine nonzero factors.
  have h : Tendsto (fun s : ℝ => x^2/(s⁻¹+x)) atTop (𝓝 (x^2/x)) :=
    tendsto_const_nhds.div (by simpa only [zero_add] using tendsto_inv_atTop_zero.add_const x) hx.ne'
  rw [show x^2/x=x by rw [pow_two,mul_div_cancel_right₀ _ hx.ne']] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
  unfold resolventDefect
  have hd : 1+s*x≠0 := ne_of_gt (by positivity)
  field_simp [hs.ne',hx.ne',hd]

/-- The genuine infinite Bessel edge spectrum has exactly the printed first Rayleigh sum.
Use: discharges the actual edge mass, enables the full L1 spectral limit and fixes the canonical-product normalization without an escaped exponential factor.
Article: jacobi, Lemma 1.3.
Proof: the actual Bessel spectrum is already genuinely summable.
Each scalar Stieltjes defect is bounded by its edge value and tends
to that whole value. Dominated convergence identifies the full defect
limit with the actual mass. The proved genuine Riccati decay makes the
same limit the original central logarithmic derivative, already evaluated exactly. -/
theorem first_rayleigh_sum {a : ℝ} (ha : -1<a) :
    (∑' k,edgeValue a ha k)=1/(2*(a+1)) := by
  -- Summability and decay were established independently of this exact mass identity.
  have h := tendsto_tsum_of_dominated_convergence (edgeValue_summable ha)
    (fun k => resolventDefect_tendsto ((edgeValue_properties ha).1 k)) (by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs k
      rw [Real.norm_eq_abs,abs_of_nonneg (resolventDefect_bounds hs ((edgeValue_properties ha).1 k).le).1]
      unfold resolventDefect
      have hx := (edgeValue_properties ha).1 k
      apply (div_le_iff₀ (show 0<1+s*edgeValue a ha k by nlinarith [mul_nonneg hs hx.le])).mpr
      nlinarith)
  have he : (fun s : ℝ => ∑' k,resolventDefect s (edgeValue a ha k))=ᶠ[atTop]
      fun s : ℝ => stieltjes a 0-stieltjes a s := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    exact (stieltjes_defect_identity ha hs).symm
  have hlim := (tendsto_const_nhds (x := stieltjes a 0)).sub (stieltjes_tendsto_zero ha)
  simp only [sub_zero] at hlim
  exact (tendsto_nhds_unique (h.congr' he) hlim).trans (stieltjes_zero ha)

end
end jacobi.Bessel
