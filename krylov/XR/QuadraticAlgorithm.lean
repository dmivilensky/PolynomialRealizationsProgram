import krylov.XR.QuadraticRun

/-!
Article: main_krylov, thm:XR, literal full-atom quadratic theorem.
Use: instantiate the actual raw algorithm, including its infinity-norm
initialization, real spectral atom condition, rejected probes and capacity
bookkeeping. The actual terminal point equals the genuine CG minimizer;
no exact output or gate-success premise occurs. Source: the proved full
quadratic executor invariant and existing exact CG atom-count theorem.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive definite true quadratic gradients have exactly one critical
point. This identifies an actually stopped state with the true minimizer. -/
theorem quadratic_critical_unique (Q : E →L[ℝ] E)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g₀ x y : E)
    (hx : quadraticGradient Q g₀ x = 0) (hy : quadraticGradient Q g₀ y = 0) : x = y := by
  have hQ : Q (x - y) = 0 := by
    change g₀ + Q x = 0 at hx
    change g₀ + Q y = 0 at hy
    rw [map_sub]
    have hxy : Q x = Q y := add_left_cancel (hx.trans hy.symm)
    rw [hxy, sub_self]
  by_contra hne
  have h := hpos (x - y) (sub_ne_zero.mpr hne)
  rw [hQ, inner_zero_right] at h
  exact h.false

/-- Full-atom positive quadratics are solved by the literal no-(G) XR
algorithm, including its prescribed rejected-probe update and true stopping
test. Only the original nonzero actual-trial restriction is required. -/
theorem rawAlgorithmRun_quadratic_terminates {n : ℕ} (P : Parameters)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ) (bounds : SpectralBounds)
    (hinitial : P.initialCapacity = n) (hmaximum : P.maximumCapacity = n) (hn : 0 < n)
    (hatoms : referenceAtomCount base hb g₀ = n) (hsigma : P.armijo < 1 / 2)
    (htrials : ∀ i,
      let S := rawAlgorithmRun P (quadraticObjective (cgOperator base) g₀ constant)
        (quadraticGradient (cgOperator base) g₀) 0 bounds i
      S.gradient ≠ 0 →
        (S.pairs.length < n → algorithmTrialParameter P S ≠ 0) ∧
        (let probe := rawObservationEvent (algorithmModel P)
          (quadraticObjective (cgOperator base) g₀ constant) (quadraticGradient (cgOperator base) g₀) 1 false S
         probe.pairs.length < n → algorithmTrialParameter P probe ≠ 0)) :
    let S := rawAlgorithmRun P (quadraticObjective (cgOperator base) g₀ constant)
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
  have hz := quadratic_rawRun_terminates P Q hQ.1 hQ.2 g₀ constant
    (‖WithLp.ofLp (G 0)‖⁻¹) bounds hinitial hmaximum hn hg ht hsigma htrials
  have hc := rawRun_cache P n (algorithmModel P) f G (algorithmInitialState P f G 0 bounds) rfl rfl (n + 1)
  change (rawAlgorithmRun P f G 0 bounds (n + 1)).gradient = 0 at hz
  change (rawAlgorithmRun P f G 0 bounds (n + 1)).value = _ ∧
    (rawAlgorithmRun P f G 0 bounds (n + 1)).gradient = _ at hc
  have htrue : G (rawAlgorithmRun P f G 0 bounds (n + 1)).point = 0 := hc.2.symm.trans hz
  refine ⟨hz, htrue, quadratic_critical_unique Q hQ.2 g₀ _ _ htrue ?_⟩
  change g₀ + Q (CG.displacement Q g₀ n) = 0
  rw [← CG.gradient_displacement, ht]

end
end krylov.XR
