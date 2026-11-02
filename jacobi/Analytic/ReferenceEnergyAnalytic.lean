import jacobi.Analytic.ReferenceEnergySeries

/-!
Article: jacobi, Lemma C.1.
The actual reference energy series remains holomorphic when order,
energy and spatial Gauss argument vary along analytic curves. All
coefficient and denominator estimates are proved for that same series,
including the frequency branch point.
Use: proves actual order holomorphy of f(t,sigma_k) and f(t,tau_k), and genuine entire energy dependence without differentiating a square root.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Filter jacobi.Hankel
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The original regular energy core is analytic along every analytic order, energy and Gauss-argument curve in its genuine convergence domain.
Use: proves actual order holomorphy of f(t,sigma_k) and f(t,tau_k),
and genuine entire energy dependence without differentiating a square root.
Article: jacobi, Lemma C.1.
Proof: on one common neighborhood retain a positive exponent margin,
a bounded exponent, bounded shifted energy and a spatial radius below
one. The proved exact coefficient comparison gives one summable Gauss
majorant. Sum the actual analytic energy-polynomial terms by the
community Weierstrass theorem. -/
theorem energyCore_comp_analytic {A Z X : ℂ → ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ A p) (hZ : AnalyticAt ℂ Z p) (hX : AnalyticAt ℂ X p)
    (ha : 0<(gamma (A p)).re) (hx : ‖X p‖<1) :
    AnalyticAt ℂ (fun u => energyCore (A u) (Z u) (X u)) p := by
  -- The original energy polynomials have one actual majorant across the frequency branch point.
  have hg : AnalyticAt ℂ (fun u => gamma (A u)) p := by unfold gamma; fun_prop
  have he : AnalyticAt ℂ (fun u => Z u-besselCoefficient (A u)) p := by
    unfold besselCoefficient
    fun_prop
  let δ : ℝ := (gamma (A p)).re/2
  let G : ℝ := ‖gamma (A p)‖+1
  let E : ℝ := ‖Z p-besselCoefficient (A p)‖+1
  let r : ℝ := (‖X p‖+1)/2
  let D : ℝ := G+(E+1)/Real.pi+1
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hG : 0<G := by dsimp [G]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hr : 0<r := by dsimp [r]; positivity
  have hr1 : r<1 := by dsimp [r]; linarith
  have hm : ∀ᶠ u in 𝓝 p,δ<(gamma (A u)).re :=
    (Complex.continuous_re.continuousAt.comp hg.continuousAt).eventually_const_lt (by dsimp [δ]; linarith)
  have hgm : ∀ᶠ u in 𝓝 p,‖gamma (A u)‖<G := hg.continuousAt.norm.eventually_lt_const (by dsimp [G]; linarith)
  have hem : ∀ᶠ u in 𝓝 p,‖Z u-besselCoefficient (A u)‖<E :=
    he.continuousAt.norm.eventually_lt_const (by dsimp [E]; linarith)
  have hxm : ∀ᶠ u in 𝓝 p,‖X u‖<r := hX.continuousAt.norm.eventually_lt_const (by dsimp [r]; linarith)
  obtain ⟨U,hUsub,hUopen,hpU⟩ := eventually_nhds_iff.mp
    ((hA.eventually_analyticAt.and hZ.eventually_analyticAt).and
      (hX.eventually_analyticAt.and (hm.and (hgm.and (hem.and hxm)))))
  let M := fun n => ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) (δ:ℂ) n‖*r^n
  have hM : Summable M := by
    have hh := jacobi.Reference.Hypergeometric.summable_norm
      (u := (D:ℂ)) (v := (D:ℂ)) (c := (δ:ℂ)) (x := (r:ℂ))
      (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]; exact hr1)
    convert! hh using 1
    ext n
    simp only [M,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  have hterms (n : ℕ) : DifferentiableOn ℂ (fun u => energyCoefficient (A u) n (Z u)*(X u)^n) U := by
    intro u hu
    obtain ⟨⟨hAu,hZu⟩,hXu,hmargin,_⟩ := hUsub u hu
    exact ((energyCoefficient_comp_analytic hAu hZu (hδ.trans hmargin) n).mul (hXu.pow n)).differentiableAt.differentiableWithinAt
  have hbound (n : ℕ) (u : ℂ) (hu : u∈U) :
      ‖energyCoefficient (A u) n (Z u)*(X u)^n‖≤M n := by
    obtain ⟨_,_,hmargin,hgu,heu,hxu⟩ := hUsub u hu
    have hc : δ≤(gamma (A u)+1/2).re := by norm_num; linarith
    rw [norm_mul,norm_pow]
    exact mul_le_mul (energyCoefficient_bound hG hδ hE hgu.le hc heu.le n)
      (pow_le_pow_left₀ (norm_nonneg _) hxu.le n) (by positivity) (norm_nonneg _)
  have hd := Complex.differentiableOn_tsum_of_summable_norm hM hterms hUopen hbound
  exact hd.analyticOnNhd hUopen p hpU

/-- The actual original reference solution is analytic along every analytic order-and-energy curve at all physical half-interval points, including zero and the energy branch point.
Use: supplies the genuine holomorphic reference factors in the analytic GL kernel and profile constructions.
Article: jacobi, Lemma C.1.
Proof: multiply the proved genuine analytic energy core, at its actual
physical coordinate inside the Gauss disk, by the independently proved
analytic original sine normalization. -/
theorem solution_comp_analytic {A Z : ℂ → ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ A p) (hZ : AnalyticAt ℂ Z p) (ha : 0<(gamma (A p)).re)
    {t : ℝ} (ht : t∈Ico 0 1) : AnalyticAt ℂ (fun u => solution (A u) (Z u) t) p :=
  (weight_comp_analytic hA ha t).mul (energyCore_comp_analytic hA hZ analyticAt_const ha
    (jacobi.Reference.coordinate_norm_lt_one_of_nonneg ht))

/-- The genuine complex-order reference solution is entire in the original energy at every physical half-interval point.
Use: actual energy Cauchy estimates and complex spectral-segment bounds in the analytic GL series have no excluded branch point.
Article: jacobi, Lemma C.1.
Proof: specialize the proved order-and-energy curve theorem to constant order and identity energy. -/
theorem solution_energy_analytic {a : ℂ} (ha : 0<(gamma a).re)
    {t : ℝ} (ht : t∈Ico 0 1) (z : ℂ) : AnalyticAt ℂ (fun w => solution a w t) z :=
  solution_comp_analytic analyticAt_const analyticAt_id ha ht

end
end jacobi.ComplexReference
