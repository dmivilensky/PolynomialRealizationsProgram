import krylov.XR.PracticalQuadraticRun

/-!
# Fresh-secant quadratic execution

Theorem 7.1 (`thm:XR`): the actual fresh-secant ModelStep inherits the
proved Krylov induction for nonzero computed trial scalars. Accepted and
rejected oracle observations retain their genuine caches and transported
secants. The full-window query is proved separately from its Armijo
acceptance. Raw outer recursion below uses the executor's totalized search
index; its algebraic identities do not assert search existence for an
arbitrary trial policy. Source: the generic quadratic event/flag argument.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Reference
open scoped InnerProductSpace
/-- Literal no-safeguard outer recursion with the fresh-secant model. The
underlying search index is the executor's totalized backtracking index. -/
def rawPracticalRun {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds := none) :
    ℕ → State (EuclideanSpace ℝ (Fin n)) :=
  rawRun P n (practicalModel P) f G (algorithmInitialState P f G x₀ bounds)

/-- On full-atom positive quadratics, the totalized no-safeguard outer
recursion reaches the true minimizer. This algebraic statement includes
rejected-probe updates and assumes only the stated computed nonzero
trials. Existence of an Armijo search is not inferred from its total index. -/
theorem rawPracticalRun_quadratic_terminates {n : ℕ} (P : Parameters)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ) (bounds : SpectralBounds)
    (hinitial : P.initialCapacity = n) (hmaximum : P.maximumCapacity = n) (hn : 0 < n)
    (hatoms : referenceAtomCount base hb g₀ = n) (hsigma : P.armijo < 1 / 2)
    (htrials : ∀ i,
      let S := rawPracticalRun P (quadraticObjective (cgOperator base) g₀ constant)
        (quadraticGradient (cgOperator base) g₀) 0 bounds i
      S.gradient ≠ 0 →
        (S.pairs.length < n → practicalTrialParameter P S ≠ 0) ∧
        (let probe := rawObservationEvent (practicalModel P)
          (quadraticObjective (cgOperator base) g₀ constant) (quadraticGradient (cgOperator base) g₀) 1 false S
         probe.pairs.length < n → practicalTrialParameter P probe ≠ 0)) :
    let S := rawPracticalRun P (quadraticObjective (cgOperator base) g₀ constant)
      (quadraticGradient (cgOperator base) g₀) 0 bounds (n + 1)
    S.gradient = 0 ∧ quadraticGradient (cgOperator base) g₀ S.point = 0 ∧
      S.point = CG.displacement (cgOperator base) g₀ n := by
  let Q := cgOperator base
  let f := quadraticObjective Q g₀ constant
  let G := quadraticGradient Q g₀
  have hQ := cgOperator_positive base hb
  have hg : ∀ k < n, CG.gradient Q g₀ k ≠ 0 := by
    simpa only [hatoms] using cg_nonstagnation base hb g₀
  have ht : CG.gradient Q g₀ n = 0 := by simpa only [hatoms] using cg_terminates base hb g₀
  have hz := practical_quadratic_rawRun_terminates P Q hQ.1 hQ.2 g₀ constant
    (‖WithLp.ofLp (G 0)‖⁻¹) bounds hinitial hmaximum hn hg ht hsigma htrials
  have hc := rawRun_cache P n (practicalModel P) f G (algorithmInitialState P f G 0 bounds) rfl rfl (n + 1)
  change (rawPracticalRun P f G 0 bounds (n + 1)).gradient = 0 at hz
  change (rawPracticalRun P f G 0 bounds (n + 1)).value = _ ∧
    (rawPracticalRun P f G 0 bounds (n + 1)).gradient = _ at hc
  have htrue : G (rawPracticalRun P f G 0 bounds (n + 1)).point = 0 := hc.2.symm.trans hz
  refine ⟨hz, htrue, quadratic_critical_unique Q hQ.2 g₀ _ _ htrue ?_⟩
  change g₀ + Q (CG.displacement Q g₀ n) = 0
  rw [← CG.gradient_displacement, ht]

end
end krylov.XR
