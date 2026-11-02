import jacobi.Jacobi.MehlerHeine
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
Article: jacobi, Proposition A.1.
The actual Jacobi polynomials at cos(z/n) have the printed complex
compact-uniform Mehler--Heine limit. The passage from the proved squared
scaling uses the genuine derivative of sine at zero and joint limits.
Source: sin(z)/z tends to one and locally uniform convergence with varying arguments.
Use: converts cosine edge scaling to squared edge scaling uniformly near every complex argument.
-/
namespace jacobi.Jacobi
noncomputable section
open Complex Set Filter
open scoped Nat Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine removable extension of sin(z)/z, expressed by the community differential slope.
Use: converts cosine edge scaling to squared edge scaling uniformly near every complex argument.
Article: jacobi, Proposition A.1.
-/
def sineSlope : ℂ → ℂ := dslope Complex.sin 0

/-- The removable sine quotient has its genuine value one at the origin.
Use: identifies the limit of the cosine-to-squared scaling correction.
Article: jacobi, Proposition A.1.
Proof: the differential slope at its own base is the actual sine derivative, namely cos(0)=1. -/
theorem sineSlope_zero : sineSlope 0=1 := by
  rw [sineSlope,dslope_same,Complex.deriv_sin,Complex.cos_zero]

/-- The removable sine quotient is genuinely continuous at zero.
Use: its composition with z/(2*n) has the required joint limit.
Article: jacobi, Proposition A.1.
Proof: continuity of the differential slope at its base is equivalent to differentiability of sine there. -/
theorem sineSlope_continuous_zero : ContinuousAt sineSlope 0 :=
  continuousAt_dslope_same.mpr (Complex.differentiable_sin 0)

/-- The removable sine quotient obeys its original multiplicative identity even at zero.
Use: the finite cosine-to-squared scaling identity needs no nonzero-argument hypothesis.
Article: jacobi, Proposition A.1.
Proof: the differential-slope identity gives the sine increment; its base value is zero. -/
theorem sineSlope_identity (z : ℂ) : z*sineSlope z=Complex.sin z := by
  simpa only [sub_zero,Complex.sin_zero,smul_eq_mul,sineSlope] using sub_smul_dslope Complex.sin 0 z

/-- The exact finite cosine scaling equals the squared argument times the genuine removable sine correction.
Use: translates the actual finite Jacobi polynomial from one source scaling to the other.
Article: jacobi, Proposition A.1.
Proof: the cosine double-angle identity gives twice the squared sine.
Use its actual removable-quotient identity and cancel only the positive natural degree. -/
theorem cosine_scaling_identity {n : ℕ} (hn : 0<n) (z : ℂ) :
    2*(n:ℂ)^2*(1-Complex.cos (z/n))=z^2*(sineSlope (z/(2*n)))^2 := by
  -- This identity remains exact at z=0.
  have hn0 : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  have harg : z/(n:ℂ)=2*(z/(2*n)) := by ring
  rw [harg,Complex.cos_two_mul_eq_one_sub,← sineSlope_identity (z/(2*n))]
  field_simp [hn0]
  ring

/-- The cosine-to-squared spectral scaling has its genuine joint limit as degree grows and the complex argument varies.
Use: preserves local uniformity, rather than proving only a fixed-argument Mehler--Heine limit.
Article: jacobi, Proposition A.1.
Proof: reciprocal degree tends to zero while the argument tends to z.
The actual removable sine correction therefore tends to one. Its exact
finite scaling identity gives the joint limit z^2. -/
theorem cosine_scaling_joint_limit (z : ℂ) :
    Tendsto (fun p : ℕ × ℂ => 2*(p.1:ℂ)^2*(1-Complex.cos (p.2/p.1)))
      (atTop×ˢ𝓝 z) (𝓝 (z^2)) := by
  -- The argument is permitted to vary together with the growing degree.
  have hinv : Tendsto (fun p : ℕ × ℂ => (p.1:ℂ)⁻¹) (atTop×ˢ𝓝 z) (𝓝 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).comp tendsto_fst
  have hz : Tendsto (fun p : ℕ × ℂ => p.2) (atTop×ˢ𝓝 z) (𝓝 z) := tendsto_snd
  have hsmall : Tendsto (fun p : ℕ × ℂ => p.2/(2*p.1)) (atTop×ˢ𝓝 z) (𝓝 0) := by
    have h := hz.mul (hinv.div_const 2)
    convert h using 1
    · funext p
      simp only [div_eq_mul_inv,mul_inv_rev]
    · simp
  have hS := sineSlope_continuous_zero.tendsto.comp hsmall
  rw [sineSlope_zero] at hS
  have h := (hz.pow 2).mul (hS.pow 2)
  simp only [one_pow,mul_one] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop (0:ℕ))] with p hp
  exact cosine_scaling_identity hp p.2

/-- The genuine squared-edge Jacobi scaling converges locally uniformly on the entire complex plane.
Use: permits the actual degree-dependent cosine argument in the Mehler--Heine theorem.
Article: jacobi, Proposition A.1.
Proof: around any point use a closed unit neighborhood inside a
sufficiently large origin-centered ball and restrict the already proved uniform limit. -/
theorem mehler_heine_locallyUniform {a b : ℂ} (ha : -1<a.re) :
    TendstoLocallyUniformly (fun n : ℕ => fun z : ℂ => normalized a b n (1-z/(2*(n:ℂ)^2)))
      (jacobi.Bessel.normalized a) atTop := by
  -- Every local neighborhood inherits a genuine uniform majorant from one fixed complex ball.
  intro U hU z
  have h := mehler_heine_uniform (b := b) ha (R := ‖z‖+1) (by positivity)
  refine ⟨Metric.closedBall z 1,Metric.closedBall_mem_nhds z (by norm_num),?_⟩
  filter_upwards [h U hU] with n hn w hw
  apply hn w
  rw [Metric.mem_closedBall,dist_zero_right]
  have hd : ‖w-z‖≤1 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hh := norm_add_le (w-z) z
  rw [sub_add_cancel] at hh
  linarith

/-- The actual Jacobi family at its printed cosine scaling has the genuine locally uniform Bessel limit.
Use: supplies the source Mehler--Heine formula with the uniformity required for complex zero transfer.
Article: jacobi, Proposition A.1.
Proof: the squared family converges locally uniformly, and the cosine
spectral argument has the proved joint limit z^2. Reindex the local
uniform convergence by the degree component and apply its varying-argument
limit theorem. Both coordinates tend to the same continuous Bessel value,
which is precisely the local uniform convergence criterion. -/
theorem mehler_heine_cos_locallyUniform {a b : ℂ} (ha : -1<a.re) :
    TendstoLocallyUniformly (fun n : ℕ => fun z : ℂ => normalized a b n (Complex.cos (z/n)))
      (fun z => jacobi.Bessel.normalized a (z^2)) atTop := by
  -- Joint parameter limits retain the complete complex local uniformity.
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro z
  have hsquared : TendstoLocallyUniformly
      (fun p : ℕ × ℂ => fun w : ℂ => normalized a b p.1 (1-w/(2*(p.1:ℂ)^2)))
      (jacobi.Bessel.normalized a) (atTop×ˢ𝓝 z) := by
    intro U hU w
    obtain ⟨T,hT,hE⟩ := mehler_heine_locallyUniform (b := b) ha U hU w
    exact ⟨T,hT,tendsto_fst.eventually hE⟩
  have hlimit := hsquared.tendsto_comp (jacobi.Bessel.normalized_analytic a (z^2)).continuousAt
    (cosine_scaling_joint_limit z)
  have heq : (fun p : ℕ × ℂ => normalized a b p.1
      (1-(2*(p.1:ℂ)^2*(1-Complex.cos (p.2/p.1)))/(2*(p.1:ℂ)^2)))=ᶠ[atTop×ˢ𝓝 z]
      fun p : ℕ × ℂ => normalized a b p.1 (Complex.cos (p.2/p.1)) := by
    filter_upwards [tendsto_fst.eventually (eventually_gt_atTop (0:ℕ))] with p hp
    congr 1
    have hn0 : (p.1:ℂ)≠0 := by exact_mod_cast hp.ne'
    field_simp [hn0]
    ring
  have hcos := hlimit.congr' heq
  have hbase := (jacobi.Bessel.normalized_analytic a (z^2)).continuousAt.tendsto.comp
    ((tendsto_snd : Tendsto (fun p : ℕ × ℂ => p.2) (atTop×ˢ𝓝 z) (𝓝 z)).pow 2)
  exact (hbase.prodMk hcos).mono_right (by
    rw [← nhds_prod_eq]
    exact nhds_le_uniformity _)

/-- The printed cosine Mehler--Heine formula holds uniformly on every complex compact set.
Use: the complete compact-uniform limit in the article's Bessel edge argument.
Article: jacobi, Proposition A.1.
Proof: the genuine locally uniform limit restricts to the compact set,
where local uniform convergence is equivalent to uniform convergence. -/
theorem mehler_heine_cos_uniform {a b : ℂ} (ha : -1<a.re) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n : ℕ => fun z : ℂ => normalized a b n (Complex.cos (z/n)))
      (fun z => jacobi.Bessel.normalized a (z^2)) atTop K := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  exact (tendstoLocallyUniformlyOn_univ.mpr (mehler_heine_cos_locallyUniform ha)).mono (subset_univ K)

end
end jacobi.Jacobi
