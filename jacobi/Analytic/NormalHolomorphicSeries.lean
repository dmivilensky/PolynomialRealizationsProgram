import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
Article: jacobi, Lemma C.1.
Normal convergence of genuinely jointly holomorphic summands implies
joint complex differentiability. Scalar Cauchy estimates along complex
lines bound the full Frechet derivative, so the community differentiable
series theorem applies on a smaller ball in any complex normed space.
Source: Weierstrass' theorem and the Cauchy derivative estimate.
Use: supplies a summable Frechet derivative majorant for the joint reference energy series.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A bounded genuine holomorphic function on a complex Banach ball has a bounded full derivative on its inner half ball.
Use: supplies a summable Frechet derivative majorant for the joint reference energy series.
Article: jacobi, Lemma C.1.
Source: Cauchy's derivative estimate restricted to complex affine lines.
Proof: every unit direction gives a holomorphic scalar slice on the radius R/2 disk. Its radius R/4 Cauchy circle stays inside the original ball. The chain rule identifies its derivative with the full derivative applied to that same unit direction; take the operator norm. -/
theorem holomorphic_fderiv_bound {f : E → ℂ} {p x : E} {R M : ℝ} (hR : 0<R) (hM : 0≤M)
    (hf : ∀ y∈ball p R,DifferentiableAt ℂ f y)
    (hb : ∀ y∈ball p R,‖f y‖≤M) (hx : x∈ball p (R/2)) :
    ‖fderiv ℂ f x‖≤M/(R/4) := by
  -- Unit-direction slices control the actual full complex Frechet derivative.
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let g : ℂ → ℂ := fun z => f (x+z • v)
  have hmap (z:ℂ) (hz:z∈ball 0 (R/2)) : x+z • v∈ball p R := by
    rw [mem_ball,dist_eq_norm] at hx hz ⊢
    have hh := norm_add_le (x-p) (z • v)
    rw [norm_smul,hv,mul_one] at hh
    rw [sub_zero] at hz
    have he : x+z • v-p=(x-p)+z • v := by abel
    rw [he]
    linarith
  have hd : DifferentiableOn ℂ g (ball 0 (R/2)) := by
    intro z hz
    exact ((hf _ (hmap z hz)).comp z (by fun_prop)).differentiableWithinAt
  have hr : 0<R/4 := by linarith
  have hc : closedBall (0:ℂ) (R/4)⊆ball 0 (R/2) :=
    closedBall_subset_ball (by linarith)
  have hb' : ∀ z∈sphere (0:ℂ) (R/4),‖g z‖≤M :=
    fun z hz => hb _ (hmap z (hc (sphere_subset_closedBall hz)))
  have hdx := hf x (ball_subset_ball (by linarith) hx)
  have hl : HasDerivAt (fun z:ℂ => x+z • v) v 0 := by
    convert! ((hasDerivAt_id (0:ℂ)).smul_const v).const_add x using 1
    simp only [one_smul]
  have hf0 : HasFDerivAt f (fderiv ℂ f x) (x+(0:ℂ) • v) := by
    simpa only [zero_smul,add_zero] using hdx.hasFDerivAt
  have he := hf0.comp_hasDerivAt 0 hl
  have he' : deriv g 0=fderiv ℂ f x v := by
    convert! he.deriv using 1
  rw [← he',← _root_.Complex.cderiv_eq_deriv isOpen_ball hd hr hc]
  exact _root_.Complex.norm_cderiv_le hr hb'

/-- A normally bounded series of jointly holomorphic functions is jointly holomorphic at the centre of its actual bounding ball.
Use: proves joint order/energy holomorphy of the literal reference series, rather than only holomorphy along curves.
Article: jacobi, Lemma C.1.
Source: Weierstrass' theorem; mathlib hasFDerivAt_tsum_of_isPreconnected.
Proof: scalar Cauchy slices give a summable bound for the genuine Frechet derivatives on the inner half ball. The summands are norm summable at the centre by the original majorant. Apply the community differentiable-series theorem on the convex inner ball. -/
theorem normal_series_differentiableAt {F : ℕ → E → ℂ} {p : E} {R : ℝ} {M : ℕ → ℝ}
    (hR : 0<R) (hM : ∀ n,0≤M n) (hs : Summable M)
    (hF : ∀ n x,x∈ball p R → DifferentiableAt ℂ (F n) x)
    (hb : ∀ n x,x∈ball p R → ‖F n x‖≤M n) :
    DifferentiableAt ℂ (fun x => ∑' n,F n x) p := by
  -- The full derivative series, not merely coordinatewise derivatives, is controlled on one common ball.
  have hsum : Summable (fun n => M n/(R/4)) := hs.div_const _
  have hder (n:ℕ) (x:E) (hx:x∈ball p (R/2)) : ‖fderiv ℂ (F n) x‖≤M n/(R/4) :=
    holomorphic_fderiv_bound hR (hM n) (hF n) (hb n) hx
  have hbase : Summable (fun n => F n p) := hs.of_norm_bounded
    (fun n => hb n p (mem_ball_self hR))
  exact (hasFDerivAt_tsum_of_isPreconnected hsum isOpen_ball (convex_ball p (R/2)).isPreconnected
    (fun n x hx => (hF n x (ball_subset_ball (by linarith) hx)).hasFDerivAt)
    hder (mem_ball_self (half_pos hR)) hbase (mem_ball_self (half_pos hR))).differentiableAt

end
end jacobi.Analytic
