import krylov.Envelope.CompactNormVariation
import krylov.Envelope.NormTrace
import krylov.Envelope.CanonicalDirectionalFiltration

set_option autoImplicit false
/-!
Article: Theorem B.11 [thm:E] of krylov.tex.
Use: identify the printed common Frobenius trace first variation of real
smooth source methods, with the genuine initial-error weighted quadratic
remainder and its explicit dependence on the possibly small final error.
Source: actual raw-method filtration, true canonical injection trace formula
and standard compact Taylor and Hilbert norm estimates; no expansion is assumed.
-/

namespace krylov.Envelope
noncomputable section
open Set Matrix Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.LinearAlgebra krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The actual canonical gradient norm of every genuine smooth CG-consistent source policy has the printed common norm-trace expansion, uniformly on compact varying-reference families, with the true initial-error weight and the explicit near-exhaustion factor.
Use: The actual canonical gradient norm of every genuine smooth CG-consistent source policy has the printed common norm-trace expansion, uniformly on compact varying-reference families, with the true initial-error weight and the explicit near-exhaustion factor.
Article: main_krylov, thm:E, actual compact-uniform norm-trace expansion.
Proof: Derive actual cycle smoothness from primitive coefficient charts and true positive reference curvatures. Apply the proved weighted compact norm Taylor estimate; genuine explored-flag orthogonality and actual directional filtration identify its real derivative with the printed Frobenius trace sum. -/
theorem actual_compact_norm_trace (memory : ℕ → ℕ) (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
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
      ∀ E : ℕ → Matrix (Fin n) (Fin n) ℝ,
        (∀ t : ℝ, A (x+t • h)=canonicalFCPath (base x) E t) →
        (∀ l<N-1, (E l).IsSymm) →
        let a := ‖cgCanonicalError (base x) (g x) N‖
        0<a →
        |‖Φ (x+h)‖-a-(∑ l∈Finset.range (N-1), inner ℝ (frobeniusVector (E l))
          (frobeniusVector (normTraceCoefficient (base x) (g x) N l)))/a|≤
          C*‖h‖^2*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖*
            (1+‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖/a) := by
  -- First derive the actual smooth cycle and positive error weight on the whole compact reference family.
  let Φ := fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹
    (probedGradient m (A p) (B p) (g p) N)
  let e0 := fun x => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖
  have hpre (x : X) (hx : x∈K) (i : ℕ) (hi : i<N) : CG.gradient (cgOperator (base x)) (g x) i≠0 :=
    cg_nonstagnation (base x) ((hpos x hx).self_of_nhds) (g x) i (hi.trans_le (hcount x hx))
  have hΦ (x : X) (hx : x∈K) : ContDiffAt ℝ 2 Φ x := by
    have hG := smoothProbed_gradient_regular m hm A B g x N (hA x hx) (hB x hx) (hg x hx)
      (cgOperator (base x)) (hAx x hx) (hBx x hx) (cgOperator_positive _ ((hpos x hx).self_of_nhds)).1
      (cgOperator_positive _ ((hpos x hx).self_of_nhds)).2 (hpre x hx) (hsmooth x hx)
    exact (matrixOperator_contDiffAt _ x (metricRoot_inverse_contDiffAt base x (hb x hx) (hpos x hx))).clm_apply hG
  have he0 : ContinuousOn e0 K := canonical_error_continuousOn base g K
    (fun x hx => (hb x hx).continuousAt.continuousWithinAt) (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hpos x hx).self_of_nhds)
  have hp0 (x : X) (hx : x∈K) : 0<e0 x := canonical_error_pos (base x) ((hpos x hx).self_of_nhds) (g x) (hpre x hx 0 hN)
  obtain ⟨δ,C,hδ,hC,ht⟩ := compact_weighted_norm_variation Φ e0 K hK hΦ he0 hp0
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx h hh hbl hgl E hline hE
  let e := cgCanonicalError (base x) (g x) N
  let P := exploredFlag (base x) (g x) N
  let D := fderiv ℝ Φ x h
  change 0<‖e‖ → _
  intro ha
  have href : Φ x=e := by
    dsimp only [Φ,e,cgCanonicalError]
    rw [hAx x hx,hBx x hx]
    exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹)
      (quadratic_gradient_eq_cg m hm _ (cgOperator_positive _ ((hpos x hx).self_of_nhds)).1
        (cgOperator_positive _ ((hpos x hx).self_of_nhds)).2 (g x) N)
  -- The actual derivative has the same unexplored component as the true frozen response; the reference error kills its explored projection.
  have hcommon := actual_fderiv_common_transverse memory m hm hspan base g A B x h N
    (hb x hx) (hpos x hx) (hA x hx) (hB x hx) (hg x hx) (hAx x hx) (hBx x hx) (hpre x hx) (hsmooth x hx) hbl hgl
  have hline' : (fun t => A (x+t • h))=canonicalFCPath (base x) E := funext hline
  rw [hline'] at hcommon
  have ho : inner ℝ e (P.starProjection D)=0 := by
    rw [real_inner_comm]
    exact exploredFlag_error_orthogonal (base x) ((hpos x hx).self_of_nhds) (g x) (hcount x hx) _ (P.starProjection_apply_mem D)
  have hi : inner ℝ e D=∑ l∈Finset.range (N-1), inner ℝ (frobeniusVector (E l))
      (frobeniusVector (normTraceCoefficient (base x) (g x) N l)) := by
    calc
      inner ℝ e D=inner ℝ e (D-P.starProjection D) := by rw [inner_sub_right,ho,sub_zero]
      _ = inner ℝ e (commonTransverseResponse (base x) (g x) (canonicalFCPath (base x) E) N) := congrArg (inner ℝ e) hcommon
      _ = _ := commonTransverseResponse_norm_trace (base x) ((hpos x hx).self_of_nhds) (g x) E N (hcount x hx) hE
  have hbound := ht x hx h hh (by rw [href];exact ha)
  change |‖Φ (x+h)‖-‖Φ x‖-inner ℝ (Φ x) D/‖Φ x‖|≤_ at hbound
  rw [href,hi] at hbound
  exact hbound
end
end krylov.Envelope
