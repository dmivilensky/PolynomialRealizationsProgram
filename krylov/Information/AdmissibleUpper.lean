import krylov.Information.ReferenceBall

/-!
Article: main_krylov, thm:C, full original physical admissible-class upper bound.
Use: choose one genuine base radius and a common sharp RFC cubic bound
before every original source scenario and perturbation budget profile.
Source: derived full-reference compact ball and the true compact-uniform
physical-source RFC bound with exact own-base normalization.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.LinearAlgebra krylov.Stability krylov.Correction krylov.Methods
open scoped BigOperators MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
/-- The actual RFC upper bound holds for every original physical scenario in one derived relative base ball, uniformly over every source budget profile.
Use: this is the full physical-admissible-supremum upper half of the unknown-base minimax theorem.
Article: main_krylov, thm:C, unconditional local physical source-class RFC bound.
Proof: construct the genuine compact full-reference ball first. Its affine
physical chart and constant initial gradient satisfy the proved compact
upper theorem. Every source base belongs to that compact through its exact
symmetric relative displacement; reconstruction preserves the actual source
execution and its own normalization. All constants precede every profile.
-/
theorem admissible_rfc_sharp_upper {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) :
    ∃ r₀ δ C : ℝ, 0<r₀ ∧ 0<δ ∧ 0<C ∧ ∀ (r : ℝ), r≤r₀ →
      ∀ (ω : ℕ → ℝ) (w τ μ : ℝ), 0≤μ → μ≤δ →
        (∀ i<N, ω i≤μ) → w≤μ → τ≤μ →
      ∀ S : Scenario (N+1), S.Admissible N A r ω w τ →
        S.outputRatio (rfcMethod fullMemory 1) g N≤sharpConstant (∑ i∈range N, ω i) w+C*μ^3 := by
  -- Derive one genuine compact before all physical scenarios and their primitive profiles.
  obtain ⟨r₀,hr₀,hr₁,hfull⟩ := referenceBaseChart_full_ball A hA g hcount
  let Z := selfAdjoint.submodule ℝ (Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
  let K : Set Z := Metric.closedBall 0 r₀
  have hnorm (z : Z) (hz : z∈K) : ‖z‖≤r₀ := by simpa only [K,Metric.mem_closedBall,dist_zero_right] using hz
  have hpos (z : Z) (hz : z∈K) : ∀ᶠ y in 𝓝 z, (referenceBaseChart A y).PosDef :=
    referenceBaseChart_eventually_posDef A hA z ((hnorm z hz).trans_lt hr₁)
  have hactive (z : Z) (hz : z∈K) :
      N+1≤referenceAtomCount (referenceBaseChart A z) (hpos z hz).self_of_nhds g := by
    obtain ⟨_,hc⟩ := hfull z (hnorm z hz)
    exact hc.ge
  obtain ⟨δ,C,hδ,hC,hupper⟩ := compact_admissible_rfc_upper (referenceBaseChart A) (fun _ => g) K
    (isCompact_closedBall 0 r₀) (fun z _ => referenceBaseChart_analyticAt A z)
    (fun _ _ => analyticAt_const) hpos hactive hN
  refine ⟨r₀,δ,C,hr₀,hδ,hC,?_⟩
  intro r hr ω w τ μ hμ hμδ hω hw hτ S hS
  -- The original source radius places its exact genuine relative displacement in that compact.
  let z : Z := ⟨relativeOperator A (S.base-A),
    Matrix.isHermitian_iff_isSymm.mpr (relativeOperator_isSymm _ _ (hS.1.1.isSymm.sub hA.1.isSymm))⟩
  have hz : z∈K := by
    change dist z 0≤r₀
    rw [dist_zero_right]
    exact hS.2.1.trans hr
  have hbase : S.base=referenceBaseChart A z := (referenceBaseChart_reconstruct A S.base hA hS.1.1.isSymm).symm
  exact hupper z hz S hbase A r ω w τ μ hS hμ hμδ hω hw hτ

end
end krylov.Information
