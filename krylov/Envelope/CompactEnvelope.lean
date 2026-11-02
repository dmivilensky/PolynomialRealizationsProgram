import krylov.Envelope.CanonicalDirectionalFiltration
import krylov.Envelope.Geometry

set_option autoImplicit false
/-!
Article: main_krylov, thm:E, genuine compact common-response envelope.
Use: derive the actual vector decomposition, common unexplored frozen
response, real explored method component and weighted quadratic remainder
uniformly over genuine compact reference families, including exhaustion.
Source: complete actual raw-method canonical filtration and the proved
primitive-coefficient varying-metric compact Taylor theorem, followed by
true CG reference orthogonality and actual Pythagoras.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- Every genuine compact family of smooth source-admissible globally CG-consistent raw methods has the actual common-frozen-response vector and norm envelope with a true uniform weighted quadratic remainder.
Use: Every genuine compact family of smooth source-admissible globally CG-consistent raw methods has the actual common-frozen-response vector and norm envelope with a true uniform weighted quadratic remainder.
Article: main_krylov, thm:E, genuine compact common-response envelope.
Proof: The true active count derives all actual nonstagnation domains and the real positive initial-error weight. Apply the genuine varying-metric compact Taylor theorem, identify the actual base execution by global CG consistency and use the proved full raw observation filtration along real reference-preserving perturbations. The genuine canonical CG flag separates the actual common frozen response and the real method-dependent projection; true orthogonality gives the actual norm envelope in every regime. -/
theorem actual_compact_envelope (memory : ℕ → ℕ) (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (hm : CGConsistent m) (hspan : ProbedSpanRestricted memory m)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A B : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : ℕ) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hA : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 2 (fun p => A p i) x)
    (hB : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 2 (fun p => B p i) x) (hg : ∀ x∈K, ContDiffAt ℝ 2 g x)
    (hAx : ∀ x∈K, A x=fun _ => cgOperator (base x)) (hBx : ∀ x∈K, B x=fun _ => cgOperator (base x))
    (hsmooth : ∀ x∈K, SmoothProbedCycleAt m 2 (cgOperator (base x)) (g x) N)
    (hN : 0<N) (hcount : ∀ x (hx : x∈K), N≤referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x)) :
    let Φ := fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹
      (probedGradient m (A p) (B p) (g p) N)
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      (∀ t : ℝ, base (x+t • h)=base x) → (∀ t : ℝ, g (x+t • h)=g x) →
      let e := cgCanonicalError (base x) (g x) N
      let P := exploredFlag (base x) (g x) N
      let ι := commonTransverseResponse (base x) (g x) (fun t => A (x+t • h)) N
      let ν := P.starProjection (fderiv ℝ Φ x h)
      let ρ := Φ (x+h)-(e+ι+ν)
      ‖ρ‖≤C*‖h‖^2*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖ ∧
        (e+ι∈Pᗮ) ∧ (ν∈P) ∧
        |‖Φ (x+h)‖-Real.sqrt (‖e+ι‖^2+‖ν‖^2)|≤‖ρ‖ := by
  -- Use the genuine varying-metric output of the actual raw executor on the real ambient reference and perturbation space.
  let Φ := fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹
    (probedGradient m (A p) (B p) (g p) N)
  have hpre (x : X) (hx : x∈K) (i : ℕ) (hi : i<N) : CG.gradient (cgOperator (base x)) (g x) i≠0 :=
    cg_nonstagnation (base x) ((hpos x hx).self_of_nhds) (g x) i (hi.trans_le (hcount x hx))
  have hgnz (x : X) (hx : x∈K) : g x≠0 := hpre x hx 0 hN
  obtain ⟨δ,C,hδ,hC,ht⟩ := smoothProbed_metric_compact_taylor m base g A B N 2 K hK hb hpos hgnz hA hB hg hm hAx hBx hpre hsmooth
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx h hh hbl hgl
  let e := cgCanonicalError (base x) (g x) N
  let P := exploredFlag (base x) (g x) N
  let D := fderiv ℝ Φ x h
  let ι := commonTransverseResponse (base x) (g x) (fun t => A (x+t • h)) N
  let ν := P.starProjection D
  let ρ := Φ (x+h)-(e+ι+ν)
  change ‖ρ‖≤_ ∧ e+ι∈Pᗮ ∧ ν∈P ∧ |‖Φ (x+h)‖-Real.sqrt (‖e+ι‖^2+‖ν‖^2)|≤‖ρ‖
  have href : Φ x=e := by
    dsimp only [Φ,e,cgCanonicalError]
    rw [hAx x hx,hBx x hx]
    exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹)
      (quadratic_gradient_eq_cg m hm _ (cgOperator_positive _ ((hpos x hx).self_of_nhds)).1
        (cgOperator_positive _ ((hpos x hx).self_of_nhds)).2 (g x) N)
  -- The actual primitive-method filtration identifies the common frozen unexplored derivative, rather than assuming that decomposition.
  have hcommon : D-ν=ι := actual_fderiv_common_transverse memory m hm hspan base g A B x h N
    (hb x hx) (hpos x hx) (hA x hx) (hB x hx) (hg x hx) (hAx x hx) (hBx x hx) (hpre x hx) (hsmooth x hx) hbl hgl
  have hsum : e+ι+ν=Φ x+D := by rw [← hcommon,href];abel
  have hρ : ρ=Φ (x+h)-(Φ x+D) := by rw [← hsum]
  -- Retain the same true compact Taylor constants and actual initial-error weight when rewriting the real first jet.
  have htwo : taylorPolynomial Φ 2 x h=Φ x+D := by
    simp [taylorPolynomial,Finset.sum_range_succ,iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,D]
  have hbound := ht x hx h hh 2 (by omega) le_rfl
  change ‖Φ (x+h)-taylorPolynomial Φ 2 x h‖≤_ at hbound
  rw [htwo,← hρ] at hbound
  -- Actual reference CG orthogonality and the genuine projector put the common component in the true orthogonal complement.
  have he : e∈Pᗮ := exploredFlag_error_orthogonal (base x) ((hpos x hx).self_of_nhds) (g x) (hcount x hx)
  have hi : ι∈Pᗮ := P.sub_starProjection_mem_orthogonal (canonicalFrozenResponse (base x) (g x) (fun t => A (x+t • h)) N)
  have hν : ν∈P := P.starProjection_apply_mem D
  have horth : inner ℝ (e+ι) ν=0 := by
    rw [real_inner_comm]
    exact (Pᗮ.add_mem he hi) ν hν
  refine ⟨hbound,Pᗮ.add_mem he hi,hν,?_⟩
  have hn := orthogonal_envelope_norm (e+ι) ν ρ horth
  have hfull : e+ι+ν+ρ=Φ (x+h) := by dsimp only [ρ];abel
  rwa [hfull] at hn
end
end krylov.Envelope
