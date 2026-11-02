import krylov.Envelope.CompactEnvelope
import krylov.Envelope.PerturbedComparison

set_option autoImplicit false
/-!
Article: main_krylov, cor:lm, actual compact-uniform comparison of smooth source methods.
Use: compare the true canonical output norms of any two actual smooth
globally CG-consistent information-class methods on a compact varying
reference family, before and near exhaustion, with genuine weighted remainders.
Source: actual primitive smooth-class membership, the proved compact
common-response envelopes and exact perturbed orthogonal comparison geometry.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- Any two actual smooth globally CG-consistent source methods have both printed norm-comparison bounds on a genuine compact reference family: the uniform maximum-component bound and the real quadratic bound when the common norm is positive, with a true initial-error weighted uniform quadratic remainder.
Use: Any two actual smooth globally CG-consistent source methods have both printed norm-comparison bounds on a genuine compact reference family: the uniform maximum-component bound and the real quadratic bound when the common norm is positive, with a true initial-error weighted uniform quadratic remainder.
Article: main_krylov, cor:lm, actual compact-uniform comparison of smooth source methods.
Proof: Derive both primitive smooth-cycle domains from actual source-class membership and reference activity. Combine the two genuine compact envelopes with common unexplored response, retain the sum of their actual Taylor constants, and apply the true orthogonal comparison estimates with both real vector remainders. -/
theorem actual_compact_method_comparison
    (M L : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A B D : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : ℕ) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hA : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 2 (fun p => A p i) x)
    (hB : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 2 (fun p => B p i) x)
    (hD : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 2 (fun p => D p i) x)
    (hg : ∀ x∈K, ContDiffAt ℝ 2 g x)
    (hAx : ∀ x∈K, A x=fun _ => cgOperator (base x))
    (hBx : ∀ x∈K, B x=fun _ => cgOperator (base x))
    (hDx : ∀ x∈K, D x=fun _ => cgOperator (base x))
    (hN : 0<N) (hcount : ∀ x (hx : x∈K), N≤referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x)) :
    let Φ := fun p => cgOperator (metricRoot (base p))⁻¹ (probedGradient M.policy (A p) (B p) (g p) N)
    let Ψ := fun p => cgOperator (metricRoot (base p))⁻¹ (probedGradient L.policy (A p) (D p) (g p) N)
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      (∀ t : ℝ, base (x+t • h)=base x) → (∀ t : ℝ, g (x+t • h)=g x) →
      let u := cgCanonicalError (base x) (g x) N+commonTransverseResponse (base x) (g x) (fun t => A (x+t • h)) N
      let ν := (exploredFlag (base x) (g x) N).starProjection (fderiv ℝ Φ x h)
      let μ := (exploredFlag (base x) (g x) N).starProjection (fderiv ℝ Ψ x h)
      let R := C*‖h‖^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖
      |‖Φ (x+h)‖-‖Ψ (x+h)‖|≤max ‖ν‖ ‖μ‖+R ∧
      (0<‖u‖ → |‖Φ (x+h)‖-‖Ψ (x+h)‖|≤(‖ν‖^2+‖μ‖^2)/(2*‖u‖)+R) := by
  -- Derive genuine primitive cycle domains for both actual source-class members before obtaining their true compact envelopes.
  let Φ := fun p => cgOperator (metricRoot (base p))⁻¹ (probedGradient M.policy (A p) (B p) (g p) N)
  let Ψ := fun p => cgOperator (metricRoot (base p))⁻¹ (probedGradient L.policy (A p) (D p) (g p) N)
  have hs (T : SmoothProbedClass (EuclideanSpace ℝ (Fin n))) (x : X) (hx : x∈K) :
      SmoothProbedCycleAt T.policy 2 (cgOperator (base x)) (g x) N :=
    T.smooth _ (cgOperator_positive _ ((hpos x hx).self_of_nhds)).1
      (cgOperator_positive _ ((hpos x hx).self_of_nhds)).2 _ _
      (fun i hi => cg_nonstagnation _ ((hpos x hx).self_of_nhds) _ i (hi.trans_le (hcount x hx)))
  -- Use the intersection of the two genuine neighborhoods and the sum of the actual weighted Taylor constants.
  obtain ⟨δ₁,C₁,hδ₁,hC₁,h₁⟩ := actual_compact_envelope M.memory M.policy M.consistent M.admissible base g A B N K hK hb hpos hA hB hg hAx hBx (hs M) hN hcount
  obtain ⟨δ₂,C₂,hδ₂,hC₂,h₂⟩ := actual_compact_envelope L.memory L.policy L.consistent L.admissible base g A D N K hK hb hpos hA hD hg hAx hDx (hs L) hN hcount
  refine ⟨min δ₁ δ₂,C₁+C₂,lt_min hδ₁ hδ₂,add_nonneg hC₁ hC₂,?_⟩
  intro x hx h hh hbl hgl
  have ha := h₁ x hx h (hh.trans (min_le_left _ _)) hbl hgl
  have hd := h₂ x hx h (hh.trans (min_le_right _ _)) hbl hgl
  let P := exploredFlag (base x) (g x) N
  let u := cgCanonicalError (base x) (g x) N+commonTransverseResponse (base x) (g x) (fun t => A (x+t • h)) N
  let ν := P.starProjection (fderiv ℝ Φ x h)
  let μ := P.starProjection (fderiv ℝ Ψ x h)
  let r := Φ (x+h)-(u+ν)
  let s := Ψ (x+h)-(u+μ)
  -- Both actual method components are orthogonal to the same genuine common response; retain both true trajectory remainders.
  have ho₁ : inner ℝ u ν=0 := by rw [real_inner_comm];exact ha.2.1 _ ha.2.2.1
  have ho₂ : inner ℝ u μ=0 := by rw [real_inner_comm];exact hd.2.1 _ hd.2.2.1
  have hf : u+ν+r=Φ (x+h) := by dsimp only [r];abel
  have hj : u+μ+s=Ψ (x+h) := by dsimp only [s];abel
  have hr : ‖r‖+‖s‖≤(C₁+C₂)*‖h‖^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ := by
    calc
      _ ≤ C₁*‖h‖^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖+C₂*‖h‖^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ := add_le_add ha.1 hd.1
      _ = _ := by ring
  have hc := perturbed_orthogonal_comparison u ν μ r s ho₁ ho₂
  rw [hf,hj] at hc
  exact ⟨by linarith [hc.1],fun hu => by linarith [hc.2 hu]⟩
end
end krylov.Envelope
