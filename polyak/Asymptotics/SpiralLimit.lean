import polyak.Spiral.Regularity

/-!
Article: Proposition spiral and Appendix C, the limiting quartic as q tends to one.
Use: the limiting constant is specified by its unique positive root and an exact
rational enclosure. The limit is a genuine one-sided limit of the selected spiral root.
-/

namespace polyak.Asymptotics
noncomputable section
open Set Filter
open scoped Topology ContDiff

/-- Article: the printed limiting quartic. -/
def limitingQuartic (r : ℝ) : ℝ := r^4-2*r^3+2*r^2-2*r-1

theorem limitingQuartic_eq (r : ℝ) :
    limitingQuartic r=Spiral.spiralPolynomial r 1 := by
  unfold limitingQuartic Spiral.spiralPolynomial
  ring

private theorem limitingQuartic_strictMono : StrictMonoOn limitingQuartic (Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1)
  · exact (by unfold limitingQuartic; fun_prop : Continuous limitingQuartic).continuousOn
  · intro r hr
    have hr1 : 1<r := by simpa only [interior_Ici,mem_Ioi] using hr
    have hh : HasDerivAt limitingQuartic (Spiral.spiralDerivative r 1) r := by
      simpa only [show limitingQuartic=(fun r => Spiral.spiralPolynomial r 1) from
        funext limitingQuartic_eq] using Spiral.hasDerivAt_spiralPolynomial r 1
    rw [hh.deriv]
    unfold Spiral.spiralDerivative
    have hp : 0<2*(r-1)*(r^2+1) := by positivity
    have hn : 0≤2*r*(r-1)^2 := by positivity
    nlinarith

/-- Article: the quartic has exactly one positive root. -/
theorem existsUnique_limitingQuartic_root :
    ∃! r : ℝ, 0<r ∧ limitingQuartic r=0 := by
  have hcont : Continuous limitingQuartic := by unfold limitingQuartic; fun_prop
  have hneg : limitingQuartic 1<0 := by norm_num [limitingQuartic]
  have hpos : 0<limitingQuartic 2 := by norm_num [limitingQuartic]
  obtain ⟨r,hr,hroot⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ)≤2)
    hcont.continuousOn ⟨hneg.le,hpos.le⟩
  refine ⟨r,⟨by linarith [hr.1],hroot⟩,?_⟩
  intro s hs
  have hs1 : 1<s := by
    by_contra hn
    have hsle : s≤1 := le_of_not_gt hn
    have hprod : 0<s*(2-s) := mul_pos hs.1 (by linarith)
    have habs : (s-1)^2<1 := by nlinarith
    have hsq : s^2+1≤2 := by nlinarith
    have hp : (s-1)^2*(s^2+1)<2 := by
      calc
        _ < 1*(s^2+1) := mul_lt_mul_of_pos_right habs (by positivity)
        _ ≤ 2 := by linarith
    have he : limitingQuartic s=(s-1)^2*(s^2+1)-2 := by unfold limitingQuartic; ring
    rw [hs.2] at he
    linarith
  exact limitingQuartic_strictMono.injOn (by exact hs1.le) hr.1 (hs.2.trans hroot.symm)

/-- Article: the limiting rate constant r*=1.71298.... -/
def limitingFactor : ℝ := Classical.choose existsUnique_limitingQuartic_root

theorem limitingFactor_spec : 0<limitingFactor ∧ limitingQuartic limitingFactor=0 :=
  (Classical.choose_spec existsUnique_limitingQuartic_root).1

/-- Article: an exact enclosure of the printed decimal, checked by rational arithmetic. -/
theorem limitingFactor_bounds :
    (171298 : ℝ)/100000<limitingFactor ∧ limitingFactor<(171299 : ℝ)/100000 := by
  have hge : 1≤limitingFactor := by
    have hu := (Classical.choose_spec existsUnique_limitingQuartic_root).2
    have hcont : Continuous limitingQuartic := by unfold limitingQuartic; fun_prop
    obtain ⟨r,hr,hroot⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ)≤2)
      hcont.continuousOn (show (0 : ℝ)∈Icc (limitingQuartic 1) (limitingQuartic 2) by
        norm_num [limitingQuartic])
    have heq := hu r ⟨by linarith [hr.1],hroot⟩
    rw [heq] at hr
    exact hr.1
  have hl : limitingQuartic ((171298 : ℝ)/100000)<0 := by norm_num [limitingQuartic]
  have hu : 0<limitingQuartic ((171299 : ℝ)/100000) := by norm_num [limitingQuartic]
  constructor
  · by_contra hn
    have hh := limitingQuartic_strictMono.monotoneOn hge (by norm_num) (le_of_not_gt hn)
    rw [limitingFactor_spec.2] at hh
    linarith
  · by_contra hn
    have hh := limitingQuartic_strictMono.monotoneOn (by norm_num) hge (le_of_not_gt hn)
    rw [limitingFactor_spec.2] at hh
    linarith

/-- Article: the spiral's exact selected positive root tends to the unique quartic constant. -/
theorem spiral_factor_tendsto_one :
    Tendsto Spiral.factor (𝓝[<] (1 : ℝ)) (𝓝 limitingFactor) := by
  let r := limitingFactor
  let f : ℝ×ℝ → ℝ := fun p => Spiral.spiralPolynomial p.2 p.1
  have hf : ContDiffAt ℝ ω f (1,r) := by
    dsimp only [f,Spiral.spiralPolynomial]
    fun_prop
  have hderiv : 0<Spiral.spiralDerivative r 1 := by
    have hr : 1<r := by linarith [limitingFactor_bounds.1]
    unfold Spiral.spiralDerivative
    have hp : 0<2*(r-1)*(r^2+1) := by positivity
    have hn : 0≤2*r*(r-1)^2 := by positivity
    nlinarith
  have hn : (ω : ℕ∞ω)≠0 := by simp
  have hd := chebyshev2.Calculus.scalar_derivative_invertible
    (hf.differentiableAt (by simp)) (Spiral.hasDerivAt_spiralPolynomial r 1) hderiv.ne'
  let g := hf.implicitFunction hn hd
  have hg : ContDiffAt ℝ ω g 1 := hf.contDiffAt_implicitFunction hn hd
  have hself : g 1=r := hf.implicitFunction_apply_self hn hd
  have hpos : ∀ᶠ q in 𝓝 (1 : ℝ),0<g q := by
    exact hg.continuousAt.eventually (lt_mem_nhds (by rw [hself]; exact limitingFactor_spec.1))
  have hroot : ∀ᶠ q in 𝓝 (1 : ℝ), f (q,g q)=0 := by
    have hh := hf.eventually_apply_implicitFunction hn hd
    have hz : f (1,r)=0 := by simpa only [f,← limitingQuartic_eq] using limitingFactor_spec.2
    simpa only [hz] using hh
  have hdomain : ∀ᶠ q in 𝓝[<] (1 : ℝ),0<q ∧ q<1 :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds
      |>.and self_mem_nhdsWithin
  have heq : Spiral.factor=ᶠ[𝓝[<] (1 : ℝ)] g := by
    filter_upwards [hpos.filter_mono nhdsWithin_le_nhds,
      hroot.filter_mono nhdsWithin_le_nhds,hdomain] with q hq hz hdom
    have hu := (Classical.choose_spec (Spiral.existsUnique_spiral_root hdom.1 hdom.2)).2
    exact (hu (Spiral.factor q) (Spiral.factor_spec hdom.1 hdom.2)).trans
      (hu (g q) ⟨hq,hz⟩).symm
  have hlim : Tendsto g (𝓝[<] (1 : ℝ)) (𝓝 r) := by
    rw [← hself]
    exact hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact hlim.congr' heq.symm

end
end polyak.Asymptotics
