import krylov.Information.ScenarioCoordinates

/-!
Article: main_krylov, thm:C, compact-uniform physical source upper bound.
Use: the sharp RFC constant bounds every original admissible physical
scenario with a common cubic remainder over varying positive references.
Source: the genuine compact canonical tube, exact physical oracle bridge
and positive compact reference-error normalization.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Methods krylov.Stability krylov.Correction krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- The actual normalized RFC output has a sharp upper bound uniformly over a compatible compact reference family and every original physical admissible scenario.
Use: bound the genuine supremum in the source's physical scenario class, with no canonical-coordinate or finite-output premise.
Article: main_krylov, thm:C, compact-uniform physical admissible RFC upper bound.
Proof: the genuine full active references have a positive continuous last
CG error, so compactness bounds the actual initial-to-last error ratio.
The original physical budgets bound the exact finite canonical parameters.
The common compact RFC estimate applies there, and the proved exact oracle
bridge identifies its output with the original physical executor. Divide by
the genuine positive own-base normalization and retain a uniform cubic term.
-/
theorem compact_admissible_rfc_upper {N : ℕ}
    (base : X → Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : X → EuclideanSpace ℝ (Fin (N+1))) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, AnalyticAt ℝ base x) (hg : ∀ x∈K, AnalyticAt ℝ g x)
    (hpos : ∀ x∈K, ∀ᶠ y in 𝓝 x, (base y).PosDef)
    (hcount : ∀ x (hx : x∈K), N+1≤referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x))
    (hN : 0<N) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ x∈K, ∀ (S : Scenario (N+1)), S.base=base x →
      ∀ (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (r : ℝ) (ω : ℕ → ℝ) (w τ μ : ℝ),
      S.Admissible N A r ω w τ → 0≤μ → μ≤δ → (∀ i<N, ω i≤μ) → w≤μ → τ≤μ →
      S.outputRatio (rfcMethod fullMemory 1) (g x) N≤sharpConstant (∑ i∈range N, ω i) w+C*μ^3 := by
  -- Derive the actual compact normalization bound before every physical source scenario.
  have hbp (x : X) (hx : x∈K) : (base x).PosDef := (hpos x hx).self_of_nhds
  have hφ (x : X) (hx : x∈K) : 0<‖cgCanonicalError (base x) (g x) N‖ :=
    canonical_error_pos _ (hbp x hx) _ (cg_nonstagnation _ (hbp x hx) _ N (by have := hcount x hx; omega))
  have he0 := canonical_error_continuousOn base g K
    (fun x hx => (hb x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hbp
  have heφ : ContinuousOn (fun x => ‖cgCanonicalError (base x) (g x) N‖) K := by
    intro x hx
    exact ((referenceCanonicalError_analyticAt base g x N (hb x hx) (hpos x hx) (hg x hx)
      (fun i hi => cg_nonstagnation _ (hbp x hx) _ i (by have := hcount x hx; omega))).continuousAt.norm).continuousWithinAt
  obtain ⟨R₀,hR₀⟩ := hK.exists_bound_of_continuousOn (he0.div heφ (fun x hx => (hφ x hx).ne'))
  let R := max R₀ 0
  have hR : 0≤R := le_max_right _ _
  have hratio (x : X) (hx : x∈K) :
      ‖cgOperator (metricRoot (base x))⁻¹ (g x)‖≤R*‖cgCanonicalError (base x) (g x) N‖ := by
    apply (div_le_iff₀ (hφ x hx)).mp
    have hr : |‖cgOperator (metricRoot (base x))⁻¹ (g x)‖/‖cgCanonicalError (base x) (g x) N‖|≤R₀ := by
      simpa only [Real.norm_eq_abs,cgOperator,Pi.div_apply] using hR₀ x hx
    exact (le_abs_self _).trans (hr.trans (le_max_left _ _))
  obtain ⟨δ,C,hδ,hC,hT⟩ := compact_scenario_spectral_upper base g K hK hb hpos hg hcount hN
  refine ⟨δ,C*R+1,hδ,by positivity,?_⟩
  intro x hx S hbase A r ω w τ μ hS hμ hμδ hω hw hτ
  -- Use exactly the original physical scenario's actual own-base finite parameters.
  let Θ := S.symmetricParameters N (fun i hi => (hS.2.2.1 i hi).1) hS.2.2.2.1
    (fun i hi => (hS.2.2.2.2.2 i hi).1)
  have hΘμ : ‖Θ‖≤μ := S.symmetricParameters_norm_le N A r ω w τ hS hμ hω hw hτ
  have hΘδ : ‖Θ‖≤δ := hΘμ.trans hμδ
  have he (i : ℕ) (hi : i∈range N) : ‖matrixSequenceExtension N Θ.val.1 i‖≤ω i := by
    change ‖matrixSequenceExtension N (S.canonicalParameters N).1 i‖≤ω i
    rw [S.canonicalParameters_increment N (mem_range.mp hi)]
    exact (hS.2.2.1 i (mem_range.mp hi)).2
  have hf : ‖matrixSequenceExtension (N+1) Θ.val.2 N‖≤w := by
    change ‖matrixSequenceExtension (N+1) (S.canonicalParameters N).2 N‖≤w
    rw [S.canonicalParameters_correction N le_rfl,ite_eq_right (by omega : ¬ N<N)]
    exact hS.2.2.2.2.1
  have ht := hT x hx Θ hΘδ ω w he hf
  rw [← hbase] at ht
  have hcoord : Θ.val=S.canonicalParameters N := rfl
  rw [hcoord,S.canonicalParameters_output N hS.1] at ht
  have hφS : 0<‖cgCanonicalError S.base (g x) N‖ := by simpa only [hbase] using hφ x hx
  have hrS : ‖cgOperator (metricRoot S.base)⁻¹ (g x)‖≤R*‖cgCanonicalError S.base (g x) N‖ := by
    simpa only [hbase] using hratio x hx
  change _/‖cgCanonicalError S.base (g x) N‖≤_
  apply (div_le_iff₀ hφS).mpr
  have hpow : ‖Θ‖^3≤μ^3 := pow_le_pow_left₀ (norm_nonneg _) hΘμ 3
  calc
    _ ≤ ‖cgCanonicalError S.base (g x) N‖*sharpConstant (∑ i∈range N, ω i) w+
        C*‖Θ‖^3*‖cgOperator (metricRoot S.base)⁻¹ (g x)‖ := ht
    _ ≤ ‖cgCanonicalError S.base (g x) N‖*sharpConstant (∑ i∈range N, ω i) w+
        C*μ^3*(R*‖cgCanonicalError S.base (g x) N‖) :=
      add_le_add le_rfl (mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) hrS (norm_nonneg _) (by positivity))
    _ = (sharpConstant (∑ i∈range N, ω i) w+C*R*μ^3)*‖cgCanonicalError S.base (g x) N‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (by nlinarith [pow_nonneg hμ 3] : C*R*μ^3≤(C*R+1)*μ^3)) hφS.le

end
end krylov.Information
