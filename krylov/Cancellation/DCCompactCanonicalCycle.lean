import krylov.Cancellation.DCCompactFrozenCycle
import krylov.Stability.ReferenceErrorRegularity
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), original compact-uniform canonical cycle.
Use: state the full native C-one cycle remainder with the literal calibrated
response and true initial-error weight for all original source parameters.
Source: proved actual compact C-one full physical reconstruction, exact
canonical fresh dictionary and genuine compact inverse-root/error bounds.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Set Filter krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped Topology Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The original consistent full-memory exact-search DC-slide full canonical
output has one genuine compact-uniform quadratic remainder about the literal
calibrated deferred response, under C-one primitive data and estimates.
Use: the radius and weighted constant precede the reference and every real
source parameter; the actual source operators are identified exactly with
the original cumulative canonical increment sequence.
Article: main_krylov, apH:dcs2(b), full compact-uniform native canonical cycle.
Proof: derive the real compact C-one vector reconstruction from actual
residuals and moving steps. The true fixed reference fresh coordinates are
exactly the proved calibrated canonical response. Actual inverse metric
roots are bounded on the compact reference set, and the genuine initial
error norm has a positive compact minimum, giving the printed common weight. -/
theorem dc_slide_consistent_compact_canonical_cycle
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A B : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hfull : k+1=n) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K,ContDiffAt ℝ 1 base x)
    (hpos : ∀ x∈K,∀ᶠ p in 𝓝 x,(base p).PosDef)
    (hcount : ∀ x (hx : x∈K),referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x)=n)
    (hA : ∀ x∈K,∀ j<n,ContDiffAt ℝ 1 (fun p => A p j) x)
    (hB : ∀ x∈K,∀ j<n,ContDiffAt ℝ 1 (fun p => B p j) x)
    (hg : ∀ x∈K,ContDiffAt ℝ 1 g x)
    (hAx : ∀ x∈K,A x=fun _ => cgOperator (base x))
    (hBx : ∀ x∈K,B x=fun _ => cgOperator (base x))
    (hAsym : ∀ p j,(A p j).toLinearMap.IsSymmetric)
    (ha : ∀ x∈K,∀ j<n,
      let Q := cgOperator (base x)
      let H := methodRun (dcSlideMethod fullMemory estimate) (fun _ => Q) (fun _ => Q) (g x) j
      ContDiffAt ℝ 1 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ x∈K,∀ j<n,0<estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) j))
    (hcal : ∀ x∈K,∀ j<n,estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) j)=CG.length (cgOperator (base x)) (g x) j) :
    let m := dcSlideMethod fullMemory estimate
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ y : X,‖y-x‖≤delta →
      ∀ E : ℕ → Matrix (Fin n) (Fin n) ℝ,A y=canonicalFCPath (base x) E 1 →
      let R := cgOperator (metricRoot (base x))⁻¹
      ‖R (probedGradient m (A y) (B y) (g y) n)-deferredResponse (base x) (g x) k 0 E‖≤
        C*‖y-x‖^2*‖R (g x)‖ := by
  let m := dcSlideMethod fullMemory estimate
  let R := fun x => cgOperator (metricRoot (base x))⁻¹
  let e := fun x => ‖R x (g x)‖
  have hp (x : X) (hx : x∈K) : (base x).PosDef := (hpos x hx).self_of_nhds
  obtain ⟨delta,C0,hd,hC0,hphysical⟩ := dc_slide_consistent_compact_frozen_cycle estimate base g A B k hfull K hK hp
    hcount hA hB hg hAx hBx hAsym ha ha0 hcal
  have hroot : ContinuousOn (fun x => (metricRoot (base x))⁻¹) K := fun x hx =>
    (metricRoot_inverse_contDiffAt base x (hb x hx) (hpos x hx)).continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hroot
  let MR := max M 0
  have hMR : 0≤MR := le_max_right _ _
  have hR (x : X) (hx : x∈K) : ‖R x‖≤MR := (hM x hx).trans (le_max_left _ _)
  have he : ContinuousOn e K := canonical_error_continuousOn base g K
    (fun x hx => (hb x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hp
  have hepos (x : X) (hx : x∈K) : 0<e x := canonical_error_pos (base x) (hp x hx) (g x)
    (cg_nonstagnation _ (hp x hx) _ 0 (by rw [hcount x hx];omega))
  by_cases hn : K.Nonempty
  · obtain ⟨x0,hx0,hmin⟩ := hK.exists_isMinOn hn he
    have he0 : 0<e x0 := hepos x0 hx0
    refine ⟨delta,(MR*C0)/e x0,hd,div_nonneg (mul_nonneg hMR hC0) he0.le,?_⟩
    intro x hx y hy E hsource
    let F := frozenFreshGradient (fun i : Fin n => probedStep m (A x) (B x) (g x) i.val)
      (probedStep m (A x) (B x) (g x) k) (A y) k
    have href (j : ℕ) : probedStep m (A x) (B x) (g x) j=referenceStep (cgOperator (base x)) (g x) j := by
      rw [hAx x hx,hBx x hx]
      exact quadratic_probedStep_eq_cg m (dc_slide_consistent fullMemory (fun _ hj => hj) estimate)
        _ (cgOperator_positive _ (hp x hx)).1 (cgOperator_positive _ (hp x hx)).2 (g x) j
    have hF : R x F=deferredResponse (base x) (g x) k 0 E := by
      have hs : (fun i : Fin n => probedStep m (A x) (B x) (g x) i.val)=
          fun i : Fin n => referenceStep (cgOperator (base x)) (g x) i.val := funext fun i => href i.val
      dsimp only [F]
      rw [hs,href k,hsource]
      exact frozen_fresh_gradient_canonical (base x) (hp x hx) (g x) k (hcount x hx) hfull E
    have hnative := hphysical x hx y hy
    change ‖probedGradient m (A y) (B y) (g y) n-F‖≤C0*‖y-x‖^2 at hnative
    have hcanon : ‖R x (probedGradient m (A y) (B y) (g y) n)-deferredResponse (base x) (g x) k 0 E‖≤
        (MR*C0)*‖y-x‖^2 := by
      rw [← hF,← map_sub]
      exact ((R x).le_opNorm _).trans ((mul_le_mul (hR x hx) hnative (norm_nonneg _) hMR).trans_eq (by ring))
    have hw : MR*C0≤((MR*C0)/e x0)*e x := by
      calc
        _=((MR*C0)/e x0)*e x0 := (div_mul_cancel₀ _ he0.ne').symm
        _≤((MR*C0)/e x0)*e x := mul_le_mul_of_nonneg_left (hmin hx) (div_nonneg (mul_nonneg hMR hC0) he0.le)
    exact hcanon.trans ((mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans_eq (by ring))
  · exact ⟨1,0,zero_lt_one,le_refl 0,fun x hx => (hn ⟨x,hx⟩).elim⟩

end
end krylov.Cancellation
