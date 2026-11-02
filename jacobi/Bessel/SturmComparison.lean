import jacobi.Bessel.Oscillation
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Article: jacobi, Proposition B.1.
Strict comparison on ordinary nodal intervals is proved directly from the
actual Wronskian. The singular first interval uses a separately discharged
zero Wronskian limit; its endpoint exponents need not be positive.
Source: the classical Sturm comparison argument, including its singular endpoint form.
Use: fixes the left Wronskian sign in Sturm comparison without an unproved simple-zero orientation.
-/
namespace jacobi.Bessel
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Positivity to the right of a zero forces a nonnegative actual derivative at that endpoint.
Use: fixes the left Wronskian sign in Sturm comparison without an unproved simple-zero orientation.
Article: jacobi, Proposition B.1.
Proof: all right-hand difference quotients are nonnegative, and their genuine derivative limit preserves the inequality. -/
theorem derivative_at_left_zero_nonneg {f : ℝ → ℝ} {a b d : ℝ} (hab : a<b)
    (hd : HasDerivAt f d a) (hz : f a=0) (hp : ∀ x∈Ioo a b,0≤f x) : 0≤d := by
  have ht := hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE a)
  apply ge_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx
  simp only [slope,vsub_eq_sub,hz,sub_zero,smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hx.1.le)) (hp x hx)

/-- Positivity to the left of a zero forces a nonpositive actual derivative at that endpoint.
Use: fixes the right Wronskian sign in both ordinary and singular Sturm comparisons.
Article: jacobi, Proposition B.1.
Proof: the actual left-hand difference quotients are nonpositive; take their genuine derivative limit. -/
theorem derivative_at_right_zero_nonpos {f : ℝ → ℝ} {a b d : ℝ} (hab : a<b)
    (hd : HasDerivAt f d b) (hz : f b=0) (hp : ∀ x∈Ioo a b,0≤f x) : d≤0 := by
  have ht := hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE b)
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsLT hab] with x hx
  simp only [slope,vsub_eq_sub,hz,sub_zero,smul_eq_mul]
  exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr (sub_nonpos.mpr hx.2.le)) (hp x hx)

/-- The genuine Wronskian derivative cancels the two cross terms exactly.
Use: supplies the same actual derivative in ordinary and singular Sturm comparison.
Article: jacobi, Proposition B.1.
Proof: apply the ordinary product rule twice and cancel the equal cross terms. -/
theorem wronskian_hasDerivAt {f f' g g' : ℝ → ℝ} {x a b c d : ℝ}
    (hf : HasDerivAt f a x) (hf' : HasDerivAt f' b x)
    (hg : HasDerivAt g c x) (hg' : HasDerivAt g' d x)
    (he : a=f' x) (he' : c=g' x) :
    HasDerivAt (fun t => f' t*g t-f t*g' t) (b*g x-f x*d) x := by
  convert (hf'.mul hg).sub (hf.mul hg') using 1
  rw [he,he']
  ring

/-- Two positive ordinary-interval solutions with strictly ordered restoring coefficients cannot span a nodal interval of the less oscillatory solution.
Use: proves a genuine comparison zero between successive actual zeros, preserving their canonical numbering.
Article: jacobi, Proposition B.1.
Proof: the actual Wronskian strictly increases because its derivative is
(q1-q0)*u*v. Its left endpoint is nonnegative and its right endpoint is
nonpositive, from the true one-sided derivatives and positive interior signs.
Continuity extends the comparator's sign to both endpoints, giving a contradiction. -/
theorem not_positive_sturm_comparison {f f' f'' g g' g'' q0 q1 : ℝ → ℝ} {a b : ℝ}
    (hab : a<b) (hf : ∀ x∈Icc a b,HasDerivAt f (f' x) x)
    (hf' : ∀ x∈Icc a b,HasDerivAt f' (f'' x) x)
    (hg : ∀ x∈Icc a b,HasDerivAt g (g' x) x)
    (hg' : ∀ x∈Icc a b,HasDerivAt g' (g'' x) x)
    (he0 : ∀ x∈Ioo a b,f'' x+q0 x*f x=0)
    (he1 : ∀ x∈Ioo a b,g'' x+q1 x*g x=0)
    (hq : ∀ x∈Ioo a b,q0 x<q1 x)
    (hfa : f a=0) (hfb : f b=0)
    (hp : ∀ x∈Ioo a b,0<f x) : ¬∀ x∈Ioo a b,0<g x := by
  -- No zero orientation is assumed: the two required endpoint slope signs follow from actual derivative limits.
  intro hgp
  let W : ℝ → ℝ := fun x => f' x*g x-f x*g' x
  have hW x (hx : x∈Icc a b) : HasDerivAt W (f'' x*g x-f x*g'' x) x := by
    exact wronskian_hasDerivAt (hf x hx) (hf' x hx) (hg x hx) (hg' x hx) rfl rfl
  have hmono : StrictMonoOn W (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
      (fun x hx => (hW x hx).continuousAt.continuousWithinAt)
    intro x hx
    have hxi : x∈Ioo a b := by simpa only [interior_Icc] using hx
    rw [(hW x ⟨hxi.1.le,hxi.2.le⟩).deriv]
    have he : f'' x*g x-f x*g'' x=(q1 x-q0 x)*f x*g x := by
      linear_combination g x*he0 x hxi-f x*he1 x hxi
    rw [he]
    exact mul_pos (mul_pos (sub_pos.mpr (hq x hxi)) (hp x hxi)) (hgp x hxi)
  have hga : 0≤g a := by
    have ht : Tendsto g (𝓝[>] a) (𝓝 (g a)) :=
      (hg a ⟨le_rfl,hab.le⟩).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx using (hgp x hx).le
  have hgb : 0≤g b := by
    have ht : Tendsto g (𝓝[<] b) (𝓝 (g b)) :=
      (hg b ⟨hab.le,le_rfl⟩).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx using (hgp x hx).le
  have hleft := derivative_at_left_zero_nonneg hab (hf a ⟨le_rfl,hab.le⟩) hfa (fun x hx => (hp x hx).le)
  have hright := derivative_at_right_zero_nonpos hab (hf b ⟨hab.le,le_rfl⟩) hfb (fun x hx => (hp x hx).le)
  have hinc := hmono ⟨le_rfl,hab.le⟩ ⟨hab.le,le_rfl⟩ hab
  dsimp [W] at hinc
  rw [hfa,hfb,zero_mul,zero_mul,sub_zero,sub_zero] at hinc
  linarith [mul_nonneg hleft hga,mul_nonpos_of_nonpos_of_nonneg hright hgb]

/-- Strict Sturm comparison also holds on the first nodal interval with a singular left endpoint, provided its actual Wronskian tends to zero.
Use: compares the first genuine Jacobi and Bessel zeros for the whole alpha>-1 range, including negative singular powers.
Article: jacobi, Proposition B.1.
Proof: on (0,b] the actual Wronskian strictly increases. Its genuine zero
limit at the singular endpoint makes its value at b/2 nonnegative, hence
its value at b strictly positive. Positivity of the original nodal branch
makes its endpoint slope nonpositive and continuity gives the comparator
nonnegative endpoint value, forcing the same Wronskian value nonpositive. -/
theorem not_positive_singular_sturm {f f' f'' g g' g'' q0 q1 : ℝ → ℝ} {b : ℝ}
    (hb : 0<b) (hf : ∀ x∈Ioc 0 b,HasDerivAt f (f' x) x)
    (hf' : ∀ x∈Ioc 0 b,HasDerivAt f' (f'' x) x)
    (hg : ∀ x∈Ioc 0 b,HasDerivAt g (g' x) x)
    (hg' : ∀ x∈Ioc 0 b,HasDerivAt g' (g'' x) x)
    (he0 : ∀ x∈Ioo 0 b,f'' x+q0 x*f x=0)
    (he1 : ∀ x∈Ioo 0 b,g'' x+q1 x*g x=0)
    (hq : ∀ x∈Ioo 0 b,q0 x<q1 x)
    (hlim : Tendsto (fun x => f' x*g x-f x*g' x) (𝓝[>] 0) (𝓝 0))
    (hfb : f b=0) (hp : ∀ x∈Ioo 0 b,0<f x) : ¬∀ x∈Ioo 0 b,0<g x := by
  -- No value or continuity of the possibly divergent original solutions is assumed at the singular endpoint.
  intro hgp
  let W : ℝ → ℝ := fun x => f' x*g x-f x*g' x
  have hW x (hx : x∈Ioc 0 b) : HasDerivAt W (f'' x*g x-f x*g'' x) x :=
    wronskian_hasDerivAt (hf x hx) (hf' x hx) (hg x hx) (hg' x hx) rfl rfl
  have hmono : StrictMonoOn W (Ioc 0 b) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc 0 b)
      (fun x hx => (hW x hx).continuousAt.continuousWithinAt)
    intro x hx
    have hxi : x∈Ioo 0 b := by simpa only [interior_Ioc] using hx
    rw [(hW x ⟨hxi.1,hxi.2.le⟩).deriv]
    have he : f'' x*g x-f x*g'' x=(q1 x-q0 x)*f x*g x := by
      linear_combination g x*he0 x hxi-f x*he1 x hxi
    rw [he]
    exact mul_pos (mul_pos (sub_pos.mpr (hq x hxi)) (hp x hxi)) (hgp x hxi)
  have hmid : b/2∈Ioc 0 b := ⟨by linarith,by linarith⟩
  have hnon : 0≤W (b/2) := by
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT hmid.1] with x hx
    exact hmono.monotoneOn ⟨hx.1,hx.2.le.trans hmid.2⟩ hmid hx.2.le
  have hpos : 0<W b := hnon.trans_lt (hmono hmid ⟨hb,le_rfl⟩ (by linarith))
  have hgb : 0≤g b := by
    have ht : Tendsto g (𝓝[<] b) (𝓝 (g b)) :=
      (hg b ⟨hb,le_rfl⟩).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsLT hb] with x hx using (hgp x hx).le
  have hright := derivative_at_right_zero_nonpos hb (hf b ⟨hb,le_rfl⟩) hfb (fun x hx => (hp x hx).le)
  dsimp [W] at hpos
  rw [hfb,zero_mul,sub_zero] at hpos
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hright hgb)) hpos

end
end jacobi.Bessel
