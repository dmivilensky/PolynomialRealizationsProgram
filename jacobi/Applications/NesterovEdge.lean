import jacobi.Applications.ResidualPolynomials
import jacobi.Analysis.VanishingPower
import jacobi.Jacobi.CosineMehlerHeine

/-!
Article: jacobi, Proposition A.1.
This retains full complex local uniformity, including the origin.
Use: degree_ratio and nesterov_landweber_joint_limit control the actual source scaling denominator.
-/
namespace jacobi.Applications
noncomputable section
open Complex Set Filter Polynomial jacobi.Jacobi
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The exact Nesterov iteration count grows to infinity along each parity subsequence.
Use: degree_ratio and nesterov_landweber_joint_limit control the actual source scaling denominator.
Article: jacobi, Proposition A.1.
Proof: the iteration count is at least its growing Jacobi degree. -/
theorem iterationCount_tendsto (e : ℕ) :
    Tendsto (fun m : ℕ => 2*m+1+e) atTop atTop := by
  refine tendsto_atTop.mpr (fun N => ?_)
  filter_upwards [eventually_ge_atTop N] with m hm
  omega

/-- The ratio of the Jacobi degree to the exact Nesterov count tends to one half in either parity.
Use: nesterov_factor_joint_limit matches the already proved Jacobi squared scaling; the same ratio controls the Landweber power.
Article: jacobi, Proposition A.1.
Proof: divide the affine count by the positive degree and use reciprocal degree tending to zero. -/
theorem degree_ratio (e : ℕ) :
    Tendsto (fun m : ℕ => (m:ℂ)/((2*m+1+e:ℕ):ℂ)) atTop (𝓝 (1/2)) := by
  -- Only the finite initial degree zero is discarded in the algebraic cancellation.
  have h := ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).const_mul (1+(e:ℂ))).const_add 2
  norm_num only [mul_zero,add_zero] at h
  have hi := h.inv₀ (by norm_num : (2:ℂ)≠0)
  norm_num only [one_div] at hi ⊢
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hn : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp
  ring

/-- The genuine growing Landweber factor tends to one jointly in the degree and the complex hard-edge argument.
Use: nesterov_hard_edge multiplies this limit by the genuine Jacobi factor limit, preserving local uniformity.
Article: jacobi, Proposition A.1.
Proof: reciprocal k tends to zero and m/k tends to one half. Thus both z^2/k^2 and (m+1+e)*z^2/k^2 tend to zero on the joint filter. Apply the logarithmic variable-power lemma. -/
theorem nesterov_landweber_joint_limit (e : ℕ) (z : ℂ) :
    Tendsto (fun p : ℕ × ℂ => (1-p.2^2/((2*p.1+1+e:ℕ):ℂ)^2)^(p.1+1+e))
      (atTop×ˢ𝓝 z) (𝓝 1) := by
  -- The varying complex argument is bounded by its actual neighborhood limit, not fixed in advance.
  have hi : Tendsto (fun p : ℕ × ℂ => (((2*p.1+1+e:ℕ):ℂ))⁻¹)
      (atTop×ˢ𝓝 z) (𝓝 0) :=
    ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).comp (iterationCount_tendsto e)).comp tendsto_fst
  have hr := (degree_ratio e).comp (tendsto_fst (β := ℂ) (g := 𝓝 z))
  have hz := (tendsto_snd (α := ℕ) (f := atTop) (g := 𝓝 z)).pow 2
  apply jacobi.Analysis.vanishing_power
  · simpa only [div_eq_mul_inv,inv_pow,zero_pow (by omega : 2≠0),mul_zero] using hz.mul (hi.pow 2)
  · have h := ((hr.add (hi.const_mul (1+(e:ℂ)))).mul hi).mul hz
    norm_num only [mul_zero,add_zero,zero_mul] at h
    convert h using 1
    funext p
    dsimp only [Function.comp_def]
    have hk : ((2*p.1+1+e:ℕ):ℂ)≠0 := by exact_mod_cast (by omega : 2*p.1+1+e≠0)
    field_simp [hk]
    push_cast
    ring

/-- The genuine Nesterov Jacobi factor has the full joint complex Bessel limit at the actual iteration-count scale.
Use: nesterov_hard_edge proves compact-uniform convergence of the original entire residual rather than only a fixed-argument limit.
Article: jacobi, Proposition A.1.
Proof: m/k tends to one half, so the Jacobi squared spectral argument 4*m^2*z^2/k^2 tends jointly to z^2. Compose the previously verified locally uniform Mehler--Heine theorem with this varying argument. -/
theorem nesterov_factor_joint_limit {b : ℝ} (hb : -1<b) (e : ℕ) (z : ℂ) :
    Tendsto (fun p : ℕ × ℂ => aeval (p.2^2/((2*p.1+1+e:ℕ):ℂ)^2)
        (nesterovFactor b p.1 e)) (atTop×ˢ𝓝 z)
      (𝓝 (jacobi.Bessel.normalized ((b/2:ℝ):ℂ) (z^2))) := by
  -- Reuse the genuine Jacobi limit on exactly the squared source spectral coordinate.
  have hr := (degree_ratio e).comp (tendsto_fst (β := ℂ) (g := 𝓝 z))
  have hz := (tendsto_snd (α := ℕ) (f := atTop) (g := 𝓝 z)).pow 2
  have hw : Tendsto (fun p : ℕ × ℂ => 4*(p.1:ℂ)^2*p.2^2/
      ((2*p.1+1+e:ℕ):ℂ)^2) (atTop×ˢ𝓝 z) (𝓝 (z^2)) := by
    have h := ((hr.const_mul 2).pow 2).mul hz
    norm_num only [mul_one_div_cancel,mul_one,one_pow,one_mul] at h
    convert h using 1
    funext p
    dsimp only [Function.comp_def]
    have hk : ((2*p.1+1+e:ℕ):ℂ)≠0 := by exact_mod_cast (by omega : 2*p.1+1+e≠0)
    field_simp [hk]
    ring
  have hfamily : TendstoLocallyUniformly
      (fun p : ℕ × ℂ => fun w : ℂ => normalized ((b/2:ℝ):ℂ) (((e:ℝ)-1/2):ℂ)
        p.1 (1-w/(2*(p.1:ℂ)^2)))
      (jacobi.Bessel.normalized ((b/2:ℝ):ℂ)) (atTop×ˢ𝓝 z) := by
    intro U hU w
    obtain ⟨T,hT,hE⟩ := mehler_heine_locallyUniform
      (a := ((b/2:ℝ):ℂ)) (b := (((e:ℝ)-1/2):ℂ))
      (by norm_num; linarith) U hU w
    exact ⟨T,hT,tendsto_fst.eventually hE⟩
  have h := hfamily.tendsto_comp (jacobi.Bessel.normalized_analytic _ _).continuousAt hw
  apply h.congr'
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop (0:ℕ))] with p hp
  rw [nesterovFactor,shiftedPolynomial_aeval]
  push_cast
  congr 1
  have hn : (p.1:ℂ)≠0 := by exact_mod_cast hp.ne'
  field_simp [hn]
  ring

/-- The entire original Nesterov residual has the printed Bessel hard-edge limit locally uniformly on the complex plane in either parity.
Use: nesterov_hard_edge_uniform and the full iteration-index limit identify the actual residual asymptotics used by the application.
Article: jacobi, Proposition A.1.
Proof: the two actual factors have joint limits, the Landweber factor tending to one. Compare the resulting value with the continuous Bessel value at the varying argument; the joint-limit criterion gives genuine local uniform convergence. -/
theorem nesterov_hard_edge {b : ℝ} (hb : -1<b) (e : ℕ) :
    TendstoLocallyUniformly (fun m : ℕ => fun z : ℂ =>
        aeval (z^2/((2*m+1+e:ℕ):ℂ)^2) (nesterovResidual b m e))
      (fun z => jacobi.Bessel.normalized ((b/2:ℝ):ℂ) (z^2)) atTop := by
  -- The criterion keeps both degree and argument variable throughout the proof.
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro z
  have h := (nesterov_landweber_joint_limit e z).mul (nesterov_factor_joint_limit hb e z)
  simp only [one_mul] at h
  have hbessel := (jacobi.Bessel.normalized_analytic ((b/2:ℝ):ℂ) (z^2)).continuousAt.tendsto.comp
    ((tendsto_snd : Tendsto (fun p : ℕ × ℂ => p.2) (atTop×ˢ𝓝 z) (𝓝 z)).pow 2)
  have hres : Tendsto (fun p : ℕ × ℂ =>
      aeval (p.2^2/((2*p.1+1+e:ℕ):ℂ)^2) (nesterovResidual b p.1 e))
      (atTop×ˢ𝓝 z) (𝓝 (jacobi.Bessel.normalized ((b/2:ℝ):ℂ) (z^2))) := by
    simpa only [nesterovResidual,map_mul,map_pow,map_sub,map_one,aeval_X] using h
  exact (hbessel.prodMk hres).mono_right (by rw [← nhds_prod_eq]; exact nhds_le_uniformity _)

/-- The original Nesterov hard-edge limit is uniform on each compact complex set.
Use: the source's compact-uniform formulation and stability of actual small complex zeros have their full uniformity.
Article: jacobi, Proposition A.1.
Proof: restrict the proved locally uniform limit to the compact set. -/
theorem nesterov_hard_edge_uniform {b : ℝ} (hb : -1<b) (e : ℕ)
    {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun m : ℕ => fun z : ℂ =>
        aeval (z^2/((2*m+1+e:ℕ):ℂ)^2) (nesterovResidual b m e))
      (fun z => jacobi.Bessel.normalized ((b/2:ℝ):ℂ) (z^2)) atTop K := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  exact (tendstoLocallyUniformlyOn_univ.mpr (nesterov_hard_edge hb e)).mono (subset_univ K)

end
end jacobi.Applications
