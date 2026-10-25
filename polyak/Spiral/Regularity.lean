import polyak.Spiral.Threshold
import chebyshev2.Calculus.ImplicitScalar

/-!
Article: Appendix B, analyticity of the positive spiral root.
Use: the source factor is genuinely real analytic on 0<q<1.
Proof: the analytic implicit function theorem and positivity of Fρ; uniqueness
identifies its local positive branch with the already defined quartic root.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace polyak.Spiral

/-- Article: analytic regularity of the actual selected root, without assuming its continuity. -/
theorem factor_contDiffAt {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ContDiffAt ℝ ω factor q := by
  let f : ℝ×ℝ → ℝ := fun p => spiralPolynomial p.2 p.1
  have hf : ContDiffAt ℝ ω f (q,factor q) := by
    dsimp [f,spiralPolynomial]
    fun_prop
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hdp := spiralDerivative_pos hq hq1 (q_lt_factor hq hq1).le
  have hd := chebyshev2.Calculus.scalar_derivative_invertible
    (hf.differentiableAt (by simp)) (hasDerivAt_spiralPolynomial (factor q) q) hdp.ne'
  let g := hf.implicitFunction hn hd
  have hg : ContDiffAt ℝ ω g q := hf.contDiffAt_implicitFunction hn hd
  have hself : g q=factor q := hf.implicitFunction_apply_self hn hd
  have hpos : ∀ᶠ y in 𝓝 q, 0 < g y := by
    have hp : 0 < g q := by rw [hself]; exact (factor_spec hq hq1).1
    exact hg.continuousAt (lt_mem_nhds hp)
  have hroot : ∀ᶠ y in 𝓝 q, f (y,g y)=0 := by
    have hh := hf.eventually_apply_implicitFunction hn hd
    have hz : f (q,factor q)=0 := (factor_spec hq hq1).2
    simpa only [hz] using hh
  have hdomain : ∀ᶠ y in 𝓝 q, 0 < y ∧ y < 1 :=
    isOpen_Ioo.mem_nhds ⟨hq,hq1⟩
  have heq : factor =ᶠ[𝓝 q] g := by
    filter_upwards [hpos,hroot,hdomain] with y hy hz hdom
    have hu := (Classical.choose_spec (existsUnique_spiral_root hdom.1 hdom.2)).2
    have h₁ := hu (factor y) (factor_spec hdom.1 hdom.2)
    have h₂ := hu (g y) ⟨hy,hz⟩
    exact h₁.trans h₂.symm
  exact hg.congr_of_eventuallyEq heq

/-- Article: analyticity is the actual analytic predicate, not just finite differentiability. -/
theorem factor_analyticAt {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    AnalyticAt ℝ factor q := (factor_contDiffAt hq hq1).analyticAt

end polyak.Spiral
