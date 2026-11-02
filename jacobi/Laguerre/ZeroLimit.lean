import jacobi.Laguerre.MehlerHeine
import jacobi.Laguerre.Roots
import jacobi.Bessel.OrderedApproximation
import jacobi.Jacobi.LocalZeros
import Mathlib.Analysis.RCLike.Lemmas

/-!
Article: jacobi, Proposition 6.1.
The actual complex Mehler--Heine limit gives derivative convergence,
local uniqueness, compact zero exclusion and real zero existence.
The general ordered-zero theorem is then applied with every premise
proved for the original positive simple Laguerre spectrum.
Use: finiteSigmaAt_limit applies genuine complex zero stability to exactly this polynomial family.
-/
namespace jacobi.Laguerre
noncomputable section
open Polynomial Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original finite Laguerre polynomial in its squared hard-edge coordinate.
Use: finiteSigmaAt_limit applies genuine complex zero stability to exactly this polynomial family.
Article: jacobi, Proposition 6.1.
-/
def scaled (a:ℝ) (n:ℕ) (z:ℂ) : ℂ :=
  Polynomial.aeval (z/(4*(n:ℂ))) (polynomial a n)

/-- The genuine real restriction of the same finite Laguerre hard-edge polynomial.
Use: real zero existence follows from the actual Bessel sign changes and the intermediate value theorem.
Article: jacobi, Proposition 6.1.
-/
def scaledReal (a:ℝ) (n:ℕ) (x:ℝ) : ℝ :=
  (polynomial a n).eval (x/(4*(n:ℝ)))

/-- The real scaled Laguerre polynomial is exactly the real-field inclusion of the original complex polynomial.
Use: finiteSigmaAt_limit transfers genuine real sign-change zeros into the same complex family used for local uniqueness.
Article: jacobi, Proposition 6.1.
Proof: polynomial evaluation commutes with the real algebra map and the literal affine scale. -/
theorem scaled_cast (a x:ℝ) (n:ℕ) : scaled a n (x:ℂ)=(scaledReal a n x:ℂ) := by
  unfold scaled scaledReal
  have hcast:(x:ℂ)/(4*(n:ℂ))=((x/(4*(n:ℝ)):ℝ):ℂ) := by push_cast; rfl
  rw [hcast]
  exact (Polynomial.ofReal_eval (K:=ℂ) (polynomial a n) (x/(4*(n:ℝ)))).symm

/-- Every original finite scaled Laguerre function is entire.
Use: the complex Weierstrass derivative theorem supplies actual derivative convergence in scaled_injective_near_zero.
Article: jacobi, Proposition 6.1.
Proof: the affine complex coordinate is analytic, and evaluation of the actual finite polynomial preserves analyticity. -/
theorem scaled_analytic (a:ℝ) (n:ℕ) (z:ℂ) : AnalyticAt ℂ (scaled a n) z := by
  have h:AnalyticAt ℂ (fun w:ℂ=>w/(4*(n:ℂ))) z:=analyticAt_id.div_const
  exact h.aeval_polynomial (polynomial a n)

/-- The original finite Laguerre hard-edge functions converge locally uniformly on the whole complex plane.
Use: scaled_deriv_uniform and compact zero exclusion retain the required complex uniformity.
Article: jacobi, Proposition 6.1.
Proof: a closed unit neighborhood of each point lies inside one
finite origin-centered ball, where the actual uniform limit is proved. -/
theorem mehler_heine_locallyUniform {a:ℝ} (ha:-1 < a) :
    TendstoLocallyUniformly (scaled a) (jacobi.Bessel.normalized (a:ℂ)) atTop := by
  -- The neighborhood bound is for the original polynomial throughout the complex ball.
  intro U hU z
  have h:=mehler_heine_uniform ha (R:=‖z‖+1) (by positivity)
  refine ⟨Metric.closedBall z 1,Metric.closedBall_mem_nhds z (by norm_num),?_⟩
  filter_upwards [h U hU] with n hn w hw
  apply hn w
  rw [Metric.mem_closedBall,dist_zero_right]
  have hd:‖w-z‖≤1:=by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hh:=norm_add_le (w-z) z
  rw [sub_add_cancel] at hh
  linarith

/-- The genuine derivatives of the original scaled Laguerre polynomials converge uniformly on every complex compact set.
Use: scaled_injective_near_zero excludes extra finite zeros around each actual simple Bessel zero.
Article: jacobi, Proposition 6.1.
Source: the community Weierstrass differentiation theorem.
Proof: the actual finite functions are entire and have the proved
locally uniform limit. Differentiate that limit and restrict it to the compact set. -/
theorem scaled_deriv_uniform {a:ℝ} (ha:-1 < a) {K:Set ℂ} (hK:IsCompact K) :
    TendstoUniformlyOn (fun n:ℕ=>deriv (scaled a n))
      (deriv (jacobi.Bessel.normalized (a:ℂ))) atTop K := by
  have h:=(tendstoLocallyUniformlyOn_univ.mpr (mehler_heine_locallyUniform ha)).deriv
    (Eventually.of_forall (fun n z _=>(scaled_analytic a n z).differentiableAt.differentiableWithinAt))
    isOpen_univ
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  exact h.mono (subset_univ K)

/-- Near every actual simple Bessel zero, the genuine Laguerre hard-edge polynomials are eventually injective on one fixed complex disk.
Use: finiteSigmaAt_limit rules out an extra finite root near a preceding limiting root, fixing the original finite numbering.
Article: jacobi, Proposition 6.1.
Proof: derivative continuity near the original simple zero and actual
uniform derivative convergence make the finite derivative close to a
fixed nonzero scalar. Reuse the proved convex-domain mean-value
injectivity theorem from the Jacobi zero argument. -/
theorem scaled_injective_near_zero {a:ℝ} (ha:-1 < a) (k:ℕ) :
    ∃r:ℝ,0 < r ∧ ∀ᶠn:ℕ in atTop,
      InjOn (scaled a n) (Metric.closedBall (jacobi.Bessel.sigma a ha k:ℂ) r) := by
  -- The central derivative is that of the same actual entire Bessel function used in Mehler--Heine.
  let z:ℂ:= jacobi.Bessel.sigma a ha k
  let d:=deriv (jacobi.Bessel.normalized (a:ℂ)) z
  have hd:0 < ‖d‖:=norm_pos_iff.mpr
    (jacobi.Bessel.normalized_zero_simple (by simpa using ha) (jacobi.Bessel.sigma_mem ha k))
  have hD:=(jacobi.Bessel.normalized_analytic (a:ℂ) z).deriv.continuousAt
  have hN:∀ᶠw in 𝓝 z,‖deriv (jacobi.Bessel.normalized (a:ℂ)) w-d‖ < ‖d‖/4 := by
    exact (hD.sub_const d).norm.eventually (Iio_mem_nhds
      (show ‖d-d‖ < ‖d‖/4 from by rw [sub_self,norm_zero]; positivity))
  obtain ⟨r,hr,hball⟩:=Metric.nhds_basis_closedBall.mem_iff.mp hN
  have herr:=(Metric.tendstoUniformlyOn_iff.mp (scaled_deriv_uniform ha (isCompact_closedBall z r)))
    (‖d‖/4) (by positivity)
  refine ⟨r,hr,?_⟩
  filter_upwards [herr] with n hn
  apply jacobi.Jacobi.injective_on_of_deriv_close (convex_closedBall z r)
    (fun w _=>(scaled_analytic a n w).differentiableAt.hasDerivAt)
    (d:=d) (C:=‖d‖/2) ?_ (by linarith)
  intro w hw
  have he:‖deriv (scaled a n) w-deriv (jacobi.Bessel.normalized (a:ℂ)) w‖ < ‖d‖/4 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hn w hw
  have hb:‖deriv (jacobi.Bessel.normalized (a:ℂ)) w-d‖ < ‖d‖/4:=hball hw
  have hh:=norm_add_le (deriv (scaled a n) w-deriv (jacobi.Bessel.normalized (a:ℂ)) w)
    (deriv (jacobi.Bessel.normalized (a:ℂ)) w-d)
  rw [sub_add_sub_cancel] at hh
  linarith

/-- A genuine Bessel zero-free real compact interval eventually contains no original finite scaled Laguerre zero.
Use: finiteSigmaAt_limit excludes premature finite zeros in every intervening actual Bessel gap.
Article: jacobi, Proposition 6.1.
Proof: the actual Bessel norm has a positive minimum on the compact
complex embedding of the interval. The original uniform approximation
eventually differs by less than half that positive minimum. -/
theorem scaled_nonvanishing_interval {a:ℝ} (ha:-1 < a) (A B:ℝ)
    (hgap:∀x∈Icc A B,jacobi.Bessel.normalized (a:ℂ) (x:ℂ)≠0) :
    ∀ᶠn:ℕ in atTop,∀x∈Icc A B,scaled a n (x:ℂ)≠0 := by
  -- Actual compact nonvanishing supplies the margin, with no numerical tolerance.
  let K:=Complex.ofReal '' Icc A B
  have hK:IsCompact K:=isCompact_Icc.image Complex.continuous_ofReal
  have hc:ContinuousOn (fun z=>‖jacobi.Bessel.normalized (a:ℂ) z‖) K :=
    fun z _=>(jacobi.Bessel.normalized_analytic (a:ℂ) z).continuousAt.norm.continuousWithinAt
  have hpos:∀z∈K,0 < ‖jacobi.Bessel.normalized (a:ℂ) z‖ := by
    rintro z ⟨x,hx,rfl⟩
    exact norm_pos_iff.mpr (hgap x hx)
  obtain ⟨d,hd,hbound⟩:=hK.exists_forall_le' hc hpos
  have hu:=(tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((tendstoLocallyUniformlyOn_univ.mpr (mehler_heine_locallyUniform ha)).mono (subset_univ K))
  have he:=(Metric.tendstoUniformlyOn_iff.mp hu) (d/2) (by positivity)
  filter_upwards [he] with n hn x hx hz
  have hh:=hn (x:ℂ) ⟨x,hx,rfl⟩
  rw [hz,dist_zero_right] at hh
  linarith [hbound (x:ℂ) ⟨x,hx,rfl⟩]

/-- Every actual Bessel spectral zero is approached by true real zeros of the original finite Laguerre polynomials.
Use: finiteSigmaAt_limit obtains existence near every limit before using the genuine original finite ordering.
Article: jacobi, Proposition 6.1.
Proof: actual simple Bessel zeros have opposite signs arbitrarily
nearby. Mehler--Heine preserves both real signs eventually, and the
intermediate value theorem supplies a genuine finite real zero between them. -/
theorem scaled_zero_approximation {a:ℝ} (ha:-1 < a) (k:ℕ) {e:ℝ} (he:0 < e) :
    ∀ᶠn:ℕ in atTop,∃x:ℝ,|x- jacobi.Bessel.sigma a ha k| < e ∧ scaled a n (x:ℂ)=0 := by
  -- The existence argument uses the real restriction of the same original complex polynomial.
  have hpoint (x:ℝ) : Tendsto (fun n:ℕ=>scaledReal a n x) atTop
      (𝓝 (jacobi.Bessel.realNormalized a x)) := by
    have hh:=(mehler_heine_uniform ha (R:=|x|) (abs_nonneg x)).tendsto_at (x:=(x:ℂ)) (by
      simp only [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,le_refl])
    have hh':Tendsto (fun n:ℕ=>scaled a n (x:ℂ)) atTop
      (𝓝 (jacobi.Bessel.normalized (a:ℂ) (x:ℂ))) := hh
    simpa only [Function.comp_def,scaled_cast,Complex.ofReal_re,jacobi.Bessel.realNormalized] using
      Complex.continuous_re.continuousAt.tendsto.comp hh'
  obtain ⟨⟨u,hu,huneg⟩,⟨v,hv,hvpos⟩⟩:=
    jacobi.Bessel.realNormalized_signs ha (jacobi.Bessel.sigma_mem ha k) he
  filter_upwards [(hpoint u).eventually (Iio_mem_nhds huneg),
    (hpoint v).eventually (Ioi_mem_nhds hvpos)] with n hnU hnV
  have hc:Continuous (scaledReal a n):=
    (polynomial a n).continuous.comp (continuous_id.div_const _)
  have hzero:(0:ℝ)∈uIcc (scaledReal a n u) (scaledReal a n v):=Icc_subset_uIcc ⟨hnU.le,hnV.le⟩
  obtain ⟨x,hx,hval⟩:=intermediate_value_uIcc hc.continuousOn hzero
  have hnear:=ordConnected_Ioo.uIcc_subset hu hv hx
  refine ⟨x,abs_lt.mpr ⟨by linarith [hnear.1],by linarith [hnear.2]⟩,?_⟩
  rw [scaled_cast,hval,Complex.ofReal_zero]

/-- The actual squared hard-edge zeros of the original Laguerre polynomial, in increasing order.
Use: finiteSigmaAt_limit proves the printed 4*n*y_(n,k)->j_(a,k)^2 with the original finite indexing.
Article: jacobi, Proposition 6.1.
-/
def finiteSigma (a:ℝ) (ha:-1 < a) (n:ℕ) (i:Fin n) : ℝ :=
  4*(n:ℝ)*roots a ha n i

/-- The actual scaled Laguerre function vanishes exactly at the original canonically ordered squared hard-edge zeros.
Use: finiteSigmaAt_limit identifies every locally transferred zero with an actual finite spectral index.
Article: jacobi, Proposition 6.1.
Proof: restriction to real coordinates is exact; the complete genuine
Laguerre zero theorem and its nonzero finite scale give the equivalence. -/
theorem finiteSigma_zero_iff {a:ℝ} (ha:-1 < a) {n:ℕ} (hn:0 < n) (x:ℝ) :
    scaled a n (x:ℂ)=0 ↔ ∃i:Fin n,finiteSigma a ha n i=x := by
  rw [scaled_cast,Complex.ofReal_eq_zero]
  change (polynomial a n).eval (x/(4*(n:ℝ)))=0 ↔ _
  rw [roots_zero_iff ha]
  apply exists_congr
  intro i
  unfold finiteSigma
  rw [eq_div_iff (by positivity : 4*(n:ℝ)≠0),mul_comm]

/-- Every canonically ordered original Laguerre zero has the printed fixed-index squared hard-edge limit.
Use: the complete Laguerre l1 resolvent-spectrum limit in Proposition 6.1 combines this theorem with the exact total trace.
Article: jacobi, Proposition 6.1.
Proof: actual positivity and strict ordering come from the unchanged
finite matrix. Genuine real zero existence, compact gap exclusion and
complex local injectivity are proved above. Apply the shared ordered-zero
argument with all its original polynomial premises discharged. -/
theorem finiteSigmaAt_limit {a:ℝ} (ha:-1 < a) (k:ℕ) :
    Tendsto (fun n:ℕ=> jacobi.Bessel.finiteZeroAt (finiteSigma a ha) n k)
      atTop (𝓝 (jacobi.Bessel.sigma a ha k)) := by
  -- This fixes the true finite numbering; it is stronger than unindexed existence of nearby zeros.
  apply jacobi.Bessel.ordered_zero_limit ha (finiteSigma a ha) (scaled a)
  · intro n
    constructor
    · intro i
      have hn:0 < n:=by have hh:=i.isLt; omega
      exact mul_pos (by positivity) (roots_pos ha i)
    · intro i j hij
      have hn:0 < n:=by have hh:=i.isLt; omega
      exact mul_lt_mul_of_pos_left ((roots a ha n).strictMono hij) (by positivity)
  · intro n i
    have hn:0 < n:=by have hh:=i.isLt; omega
    exact (finiteSigma_zero_iff ha hn _).mpr ⟨i,rfl⟩
  · intro j e he
    filter_upwards [scaled_zero_approximation ha j he,eventually_gt_atTop (0:ℕ)] with n hn hnpos
    obtain ⟨x,hx,hzero⟩:=hn
    obtain ⟨i,hi⟩:=(finiteSigma_zero_iff ha hnpos x).mp hzero
    exact ⟨i,hi ▸ hx⟩
  · exact scaled_nonvanishing_interval ha
  · exact scaled_injective_near_zero ha

end
end jacobi.Laguerre
