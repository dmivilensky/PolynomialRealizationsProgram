import krylov.Stability.SmoothMetricCompact
import krylov.Envelope.Geometry
import krylov.Variation.ReferenceFlags

/-!
Article: main_krylov, thm:E, actual compact orthogonal first-jet decomposition.
Use: derive the real compact weighted quadratic norm-envelope remainder for
every actually executed smooth CG-consistent raw method, splitting its true
derivative by the genuine reference CG flag. Identification of the common
unexplored component with the frozen injection formula is a separate filtration
result; this intermediate theorem assumes no expansion.
Source: the proved real varying-metric compact Taylor theorem, actual static
CG execution and true reference orthogonality, followed by Pythagoras.
-/

namespace krylov.Envelope
noncomputable section
open Set Matrix Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- Every actual smooth CG-consistent raw trajectory has the true compact-uniform orthogonal derivative envelope with its actual reference CG flag and genuine initial-error weight.
Use: Every actual smooth CG-consistent raw trajectory has the true compact-uniform orthogonal derivative envelope with its actual reference CG flag and genuine initial-error weight.
Article: main_krylov, thm:E, actual compact orthogonal first-jet decomposition.
Proof: The actual active count discharges nonstagnation and the nonzero initial gradient. The true quadratic transcript identifies the base output; actual reference orthogonality and projection give Pythagoras. The previously proved varying-metric compact Taylor remainder bounds the genuine executed output. -/
theorem smoothProbed_compact_orthogonal_jet (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A B : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : ℕ) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hA : ∀ x∈K, ∀ k<N, ContDiffAt ℝ 2 (fun p => A p k) x)
    (hB : ∀ x∈K, ∀ k<N, ContDiffAt ℝ 2 (fun p => B p k) x) (hg : ∀ x∈K, ContDiffAt ℝ 2 g x)
    (hconsistent : CGConsistent m)
    (hAx : ∀ x∈K, A x=fun _ => cgOperator (base x)) (hBx : ∀ x∈K, B x=fun _ => cgOperator (base x))
    (hsmooth : ∀ x∈K, SmoothProbedCycleAt m 2 (cgOperator (base x)) (g x) N)
    (hN : 0 < N) (hcount : ∀ x (hx : x∈K), N ≤ referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x)) :
    let Φ := fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹
      (probedGradient m (A p) (B p) (g p) N)
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ x∈K, ∀ h : X, ‖h‖ ≤ δ →
      let D := fderiv ℝ Φ x h
      let P := oldFlag (base x) (g x) (N-1)
      let ν := P.starProjection D
      |‖Φ (x+h)‖-Real.sqrt (‖cgCanonicalError (base x) (g x) N+(D-ν)‖^2+‖ν‖^2)| ≤
        C*‖h‖^2*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖ := by
  -- Work with the genuine variable-metric output of the actual raw executor.
  let Φ := fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹
    (probedGradient m (A p) (B p) (g p) N)
  have hpre : ∀ x∈K, ∀ k<N, CG.gradient (cgOperator (base x)) (g x) k≠0 := by
    intro x hx k hk
    exact cg_nonstagnation (base x) ((hpos x hx).self_of_nhds) (g x) k (hk.trans_le (hcount x hx))
  have hgnz : ∀ x∈K, g x≠0 := fun x hx => hpre x hx 0 hN
  obtain ⟨δ,C,hδ,hC,hbound⟩ := smoothProbed_metric_compact_taylor m base g A B N 2 K hK hb hpos hgnz
    hA hB hg hconsistent hAx hBx hpre hsmooth
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx h hh
  let D := fderiv ℝ Φ x h
  let P := oldFlag (base x) (g x) (N-1)
  let ν := P.starProjection D
  let e := cgCanonicalError (base x) (g x) N
  let R := Φ (x+h)-(Φ x+D)
  -- Identify the actual base run before applying any reference flag orthogonality.
  have href : Φ x=e := by
    dsimp only [Φ,e,cgCanonicalError]
    rw [hAx x hx,hBx x hx]
    exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹)
      (quadratic_gradient_eq_cg m hconsistent _ (cgOperator_positive _ ((hpos x hx).self_of_nhds)).1
        (cgOperator_positive _ ((hpos x hx).self_of_nhds)).2 (g x) N)
  have hE : e∈Pᗮ := by
    have ht := remainingTail_orthogonal (base x) ((hpos x hx).self_of_nhds) (g x) (N-1)
      (show N-1 < referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x) by have := hcount x hx;omega)
    have heq : N-1+1=N := by omega
    simpa only [remainingTail,heq,neg_neg] using Pᗮ.neg_mem ht
  have hD : D-ν∈Pᗮ := P.sub_starProjection_mem_orthogonal D
  have hν : ν∈P := P.starProjection_apply_mem D
  have horth : inner ℝ (e+(D-ν)) ν=0 := by
    rw [real_inner_comm]
    exact (Pᗮ.add_mem hE hD) ν hν
  -- The true Taylor remainder controls the actual orthogonal envelope norm in every regime.
  have hn := orthogonal_envelope_norm (e+(D-ν)) ν R horth
  have hid : e+(D-ν)+ν+R=Φ (x+h) := by rw [← href];dsimp only [R];abel
  rw [hid] at hn
  apply hn.trans
  have htwo : taylorPolynomial Φ 2 x h=Φ x+D := by
    simp [taylorPolynomial,Finset.sum_range_succ,iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,D]
  have ht := hbound x hx h hh 2 (by omega) le_rfl
  change ‖Φ (x+h)-taylorPolynomial Φ 2 x h‖ ≤ _ at ht
  rw [htwo] at ht
  exact ht
end
end krylov.Envelope
