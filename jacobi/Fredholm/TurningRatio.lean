import jacobi.Fredholm.FirstIntegral

/-!
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
The true rational turning ratio is continuous from its switching endpoint,
strictly increases above it and tends to infinity. Its one actual positive
root determines the complete sign pattern and simple upper turning zero of
the original Fredholm first integral.
Source: the exact rational derivative and the intermediate value theorem.
Use: the sign of the original phase polynomial is the sign of 1-(4/3)*A²*turningRatio.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual rational ratio determining the unique upper Fredholm turning zero.
Use: the sign of the original phase polynomial is the sign of 1-(4/3)*A²*turningRatio.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
-/
def turningRatio (e g : ℝ) : ℝ := g*(g-e)^3/(2*g-1)^2

/-- The actual rational turning ratio has its explicit classical derivative above the free diagonal.
Use: proves strict uniqueness and simplicity of the true upper turning root.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: differentiate the literal rational function and factor its cubic denominator exactly. -/
theorem turningRatio_hasDerivAt (e : ℝ) {g : ℝ} (hg : (1/2:ℝ)<g) :
    HasDerivAt (turningRatio e)
      ((g-e)^2*(4*g^2+(2*e-4)*g+e)/(2*g-1)^3) g := by
  have hden : 2*g-1≠0 := by linarith
  convert ((hasDerivAt_id g).mul (((hasDerivAt_id g).sub_const e).pow 3)).div
    ((((hasDerivAt_id g).const_mul 2).sub_const 1).pow 2) (pow_ne_zero 2 hden) using 1
  · rfl
  · dsimp only [Pi.pow_apply,Pi.mul_apply,id_eq]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    field_simp
    ring

/-- The actual turning-ratio derivative is strictly positive above its switching level.
Use: gives the unique source upper turning level for every actual positive amplitude.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: the derivative numerator has the positive decomposition
4*(gamma-1/2)²+(gamma-1/2)+2*(g_e-1/2)*(gamma+1/2). -/
theorem turningRatio_derivative_pos {e g : ℝ} (he : (1/2:ℝ)≤e) (hg : e<g) :
    0<(g-e)^2*(4*g^2+(2*e-4)*g+e)/(2*g-1)^3 := by
  have hgp : (1/2:ℝ)<g := he.trans_lt hg
  have hpoly : 0<4*g^2+(2*e-4)*g+e := by
    have hh := mul_nonneg (show 0≤e-1/2 by linarith) (show 0≤g+1/2 by linarith)
    nlinarith [sq_nonneg (g-1/2)]
  exact div_pos (mul_pos (sq_pos_of_pos (sub_pos.mpr hg)) hpoly) (pow_pos (by linarith) 3)

/-- The apparent ratio singularity at the full-support switching level is actually removable.
Use: includes g_e=1/2 in the actual upper-turning existence theorem.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: the zero-denominator value is zero on both sides; elsewhere cancel the exact quadratic factor. -/
theorem turningRatio_half (g : ℝ) : turningRatio (1/2) g=g*(g-1/2)/4 := by
  by_cases hg : g=1/2
  · subst g
    norm_num [turningRatio]
  · have hd : 2*g-1≠0 := by intro hz; apply hg; linarith
    unfold turningRatio
    field_simp
    ring

/-- The actual turning ratio is continuous on the complete closed switching ray.
Use: genuine intermediate values construct its root, including the full-support branch.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: above one half its denominator never vanishes. At the limiting
switching level one half, the proved removable-factor identity is a polynomial. -/
theorem turningRatio_continuousOn {e : ℝ} (he : (1/2:ℝ)≤e) :
    ContinuousOn (turningRatio e) (Ici e) := by
  rcases lt_or_eq_of_le he with hlt | heq
  · intro g hg
    exact (turningRatio_hasDerivAt e (hlt.trans_le hg)).continuousAt.continuousWithinAt
  · rw [← heq]
    have hh : turningRatio (1/2)=fun g : ℝ => g*(g-1/2)/4 := funext turningRatio_half
    rw [hh]
    fun_prop

/-- The actual turning ratio is strictly increasing on its full closed switching ray.
Use: the source phase polynomial has precisely one upper positive zero.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: use the exact positive derivative on the interior and the proved continuity at the possible removable endpoint. -/
theorem turningRatio_strictMono {e : ℝ} (he : (1/2:ℝ)≤e) : StrictMonoOn (turningRatio e) (Ici e) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici e) (turningRatio_continuousOn he)
  intro g hg
  have hge : e<g := by simpa only [interior_Ici,mem_Ioi] using hg
  rw [(turningRatio_hasDerivAt e (he.trans_lt hge)).deriv]
  exact turningRatio_derivative_pos he hge

/-- The actual rational turning ratio tends to infinity.
Use: ensures existence of the upper turning level for every positive actual amplitude.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: divide the exact rational expression by gamma². Its remaining factor
converges to one quarter, so the positive quadratic factor forces divergence. -/
theorem turningRatio_atTop (e : ℝ) : Tendsto (turningRatio e) atTop atTop := by
  -- The true rational expression has its actual asymptotic factor, not an assumed equivalent.
  have hdiv : Tendsto (fun g : ℝ => e/g) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hinv : Tendsto (fun g : ℝ => (1:ℝ)/g) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hf : Tendsto (fun g : ℝ => (1-e/g)^3/(2-1/g)^2) atTop (𝓝 (1/4:ℝ)) := by
    convert ((hdiv.const_sub 1).pow 3).div ((hinv.const_sub 2).pow 2) (by norm_num) using 1
    norm_num
  have hh := (tendsto_pow_atTop (by decide : (2:ℕ)≠0)).atTop_mul_pos (by norm_num : (0:ℝ)<1/4) hf
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with g hg
  unfold turningRatio
  field_simp

/-- Every actual positive amplitude and admissible switching level determine one unique genuine upper turning ratio root.
Use: supplies the true Fredholm phase turning level before any parameter normalization.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: actual continuity, zero endpoint, strict increase and unbounded range
give a genuine positive target root; strict monotonicity proves uniqueness. -/
theorem turningRatio_root {A e : ℝ} (hA : 0<A) (he : (1/2:ℝ)≤e) :
    ∃ g0 : ℝ,e<g0 ∧ turningRatio e g0=3/(4*A^2) ∧
      ∀ z : ℝ,e<z → turningRatio e z=3/(4*A^2) → z=g0 := by
  -- The true upper root is obtained by intermediate values of the original rational ratio.
  have htarget : 0<3/(4*A^2) := by positivity
  have hzero : turningRatio e e=0 := by simp [turningRatio]
  obtain ⟨g0,hg0,hroot⟩ := intermediate_value_Ici (turningRatio_continuousOn he) (turningRatio_atTop e)
    (show 3/(4*A^2)∈Ici (turningRatio e e) by rw [hzero]; exact htarget.le)
  have hgt : e<g0 := lt_of_le_of_ne hg0 (by intro hz; rw [← hz,hzero] at hroot; exact htarget.ne hroot)
  exact ⟨g0,hgt,hroot,fun z hz heq => (turningRatio_strictMono he).injOn hz.le hg0 (heq.trans hroot.symm)⟩

end
end jacobi.Fredholm
