import jacobi.Analytic.ReferenceEnergyAnalytic
import jacobi.Analytic.NormalHolomorphicSeries

/-!
Article: jacobi, Lemma C.1.
The original square-root-free Gauss energy series is jointly complex
differentiable in its order and energy. The same actual coefficient
majorant used for analytic curves now controls its full Frechet
derivative through the multivariate normal-series theorem.
Use: supplies jointly holomorphic summands for the original reference series.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Metric Filter jacobi.Hankel
open scoped Topology
attribute [local fun_prop] analyticAt_fst analyticAt_snd
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Each actual energy coefficient is jointly analytic in the genuine complex order and energy.
Use: supplies jointly holomorphic summands for the original reference series.
Article: jacobi, Lemma C.1.
Proof: its numerator is a finite polynomial expression in both coordinates. The denominator is a rising-factorial polynomial at a positive-real-part argument, so its analytic inverse is legitimate. -/
theorem energyCoefficient_joint_analytic {a z : ℂ} (ha : 0<(gamma a).re) (n : ℕ) :
    AnalyticAt ℂ (fun p: ℂ × ℂ => energyCoefficient p.1 n p.2) (a,z) := by
  have hg : AnalyticAt ℂ (fun p: ℂ × ℂ => gamma p.1+1/2) (a,z) := by unfold gamma; fun_prop
  have hd := (AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ n) _ (mem_univ _)).comp hg
  have hn : AnalyticAt ℂ (fun p: ℂ × ℂ => (n.factorial:ℂ)⁻¹*
      (∏ j∈Finset.range n,((gamma p.1+j)^2-(p.2-besselCoefficient p.1)/(Real.pi:ℂ)^2))) (a,z) := by
    unfold gamma besselCoefficient
    fun_prop
  exact hn.mul (hd.inv (jacobi.Reference.Hypergeometric.pochhammer_ne_zero (by norm_num; linarith) n))

/-- The actual original reference energy core is jointly holomorphic in complex order and energy at every physical Gauss argument in the convergence disk.
Use: closes the multivariate parameter assertion of fboundC(a), including the frequency branch point.
Article: jacobi, Lemma C.1.
Proof: choose one genuine product neighborhood with positive denominator margin and bounded order and shifted energy. The actual finite coefficient bound gives a summable Gauss majorant on a ball inside that neighborhood. Apply the full Frechet normal-series theorem to the jointly analytic actual coefficients. -/
theorem energyCore_joint_differentiable {a z x : ℂ} (ha : 0<(gamma a).re) (hx : ‖x‖<1) :
    DifferentiableAt ℂ (fun p: ℂ × ℂ => energyCore p.1 p.2 x) (a,z) := by
  -- One genuine two-dimensional neighborhood controls all terms and their full complex derivatives.
  let δ : ℝ := (gamma a).re/2
  let G : ℝ := ‖gamma a‖+1
  let E : ℝ := ‖z-besselCoefficient a‖+1
  let r : ℝ := (‖x‖+1)/2
  let D : ℝ := G+(E+1)/Real.pi+1
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hG : 0<G := by dsimp [G]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hr : 0<r := by dsimp [r]; positivity
  have hr1 : r<1 := by dsimp [r]; linarith
  have hg : Continuous (fun p: ℂ × ℂ => gamma p.1) := by unfold gamma; fun_prop
  have he : Continuous (fun p: ℂ × ℂ => p.2-besselCoefficient p.1) := by unfold besselCoefficient; fun_prop
  have hm : ∀ᶠ p: ℂ × ℂ in 𝓝 (a,z),δ<(gamma p.1).re ∧ ‖gamma p.1‖<G ∧ ‖p.2-besselCoefficient p.1‖<E :=
    ((Complex.continuous_re.comp hg).continuousAt.eventually_const_lt (by dsimp [δ]; linarith)).and
      ((hg.continuousAt.norm.eventually_lt_const (by dsimp [G]; linarith)).and
        (he.continuousAt.norm.eventually_lt_const (by dsimp [E]; linarith)))
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hm
  let M := fun n => ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) (δ:ℂ) n‖*r^n
  have hM : Summable M := by
    have hh := jacobi.Reference.Hypergeometric.summable_norm
      (u := (D:ℂ)) (v := (D:ℂ)) (c := (δ:ℂ)) (x := (r:ℂ))
      (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]; exact hr1)
    convert! hh using 1
    ext n
    simp only [M,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  apply jacobi.Analytic.normal_series_differentiableAt hR (fun n => by dsimp [M]; positivity) hM
  · intro n p hp
    exact ((energyCoefficient_joint_analytic (hδ.trans (hball hp).1) n).mul analyticAt_const).differentiableAt
  · intro n p hp
    obtain ⟨hmargin,hgu,heu⟩ := hball hp
    have hc : δ≤(gamma p.1+1/2).re := by norm_num; linarith
    rw [norm_mul,norm_pow]
    exact mul_le_mul (energyCoefficient_bound hG hδ hE hgu.le hc heu.le n)
      (pow_le_pow_left₀ (norm_nonneg _) (by dsimp [r]; linarith) n) (by positivity) (norm_nonneg _)

/-- The literal original energy solution is jointly holomorphic in its complex order and energy throughout the admissible half-plane.
Use: completes the joint holomorphy statement used in fboundC(a) and complex reference norm continuation.
Article: jacobi, Lemma C.1.
Proof: multiply the jointly holomorphic actual energy core by the fixed-spatial sine prefactor, which is an exponential of an affine order function in the physical interior. -/
theorem solution_joint_holomorphic {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) :
    DifferentiableOn ℂ (fun p: ℂ × ℂ => solution p.1 p.2 t) {p | 0<(gamma p.1).re} := by
  -- The genuine energy series supplies the full derivative; the sine power is an analytic affine-order exponential.
  intro p hp
  have hw : AnalyticAt ℂ (fun q: ℂ × ℂ => weight q.1 t) p := by
    have hne : ((Real.sin (Real.pi*t)/Real.pi:ℝ):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (div_pos (jacobi.Reference.sine_pos ht) Real.pi_pos).ne'
    have heq : (fun q: ℂ × ℂ => weight q.1 t)=
      fun q => Complex.exp (Complex.log ((Real.sin (Real.pi*t)/Real.pi:ℝ):ℂ)*gamma q.1) :=
      funext (fun q => Complex.cpow_def_of_ne_zero hne _)
    rw [heq]
    unfold gamma
    fun_prop
  exact (hw.differentiableAt.mul (energyCore_joint_differentiable hp
    (jacobi.Reference.coordinate_norm_lt_one_of_nonneg ⟨ht.1.le,ht.2⟩))).differentiableWithinAt

end
end jacobi.ComplexReference
