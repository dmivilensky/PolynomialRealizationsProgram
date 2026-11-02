import krylov.Information.ReferenceBall
import krylov.Stability.ReferenceErrorRegularity

/-!
Article: main_krylov, s4:cor-Q, genuine own-normalized instance comparison.
Use: Actual compact relative normalization of the true CG reference error.
Source: actual common-centre execution and robust radius, genuine compact
CG reference regularity and elementary real order and positive-ratio algebra.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Topology Finset krylov.Reference krylov.Secant krylov.LinearAlgebra krylov.Stability krylov.Correction
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true last CG error has one relative Lipschitz constant on every compact positive nonstagnating reference family.
Use: Compare genuine own-reference error normalizations uniformly.
Article: main_krylov, s4:cor-Q, original instance-optimality and inner attainment.
Proof: Actual reference-error analyticity supplies the absolute compact tube. A positive attained minimum of the true error converts its constant into a common relative bound; the empty compact case is included. -/
theorem compact_referenceError_relative_variation
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (N : ℕ) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, AnalyticAt ℝ base x)
    (hpos : ∀ x∈K, ∀ᶠ y in 𝓝 x, (base y).PosDef) (hg : ∀ x∈K, AnalyticAt ℝ g x)
    (hpre : ∀ x∈K, ∀ i<N, CG.gradient (cgOperator (base x)) (g x) i≠0)
    (hφ : ∀ x∈K, 0<‖cgCanonicalError (base x) (g x) N‖) :
    ∃ δ L : ℝ, 0<δ ∧ 0≤L ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ‖cgCanonicalError (base (x+h)) (g (x+h)) N‖≤
        ‖cgCanonicalError (base x) (g x) N‖*(1+L*‖h‖) := by
  -- Normalize only after deriving a genuine positive minimum on the actual compact.
  by_cases hn : K.Nonempty
  · let φ := fun x => ‖cgCanonicalError (base x) (g x) N‖
    have hc : ContinuousOn φ K := by
      intro x hx
      exact (referenceCanonicalError_analyticAt base g x N (hb x hx) (hpos x hx) (hg x hx) (hpre x hx)).continuousAt.norm.continuousWithinAt
    obtain ⟨x₀,hx₀,hmin⟩ := hK.exists_isMinOn hn hc
    obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_referenceError_norm_variation base g N K hK hb hpos hg hpre
    have hp : 0<φ x₀ := hφ x₀ hx₀
    refine ⟨δ,C/φ x₀,hδ,div_nonneg hC hp.le,?_⟩
    intro x hx h hh
    have hm : C≤φ x*(C/φ x₀) := by
      calc
        C = φ x₀*(C/φ x₀) := (mul_div_cancel₀ C hp.ne').symm.trans (by ring)
        _ ≤ _ := mul_le_mul_of_nonneg_right (hmin hx) (div_nonneg hC hp.le)
    have hr := (le_abs_self (φ (x+h)-φ x)).trans (hbound x hx h hh)
    have hh' := mul_le_mul_of_nonneg_right hm (norm_nonneg h)
    change φ (x+h)≤φ x*(1+(C/φ x₀)*‖h‖)
    nlinarith
  · exact ⟨1,0,zero_lt_one,le_refl 0,fun x hx => (hn ⟨x,hx⟩).elim⟩


/-- One genuine fixed-reference ball gives a common relative CG-error Lipschitz estimate for every actual symmetric nearby physical base displacement.
Use: Derive the normalization constant before every source scenario, twin and perturbation profile.
Article: main_krylov, s4:cor-Q, original instance factor and normalization.
Proof: The genuine compact full-active reference chart supplies positive errors throughout the ball. Apply the relative compact tube and reconstruct both actual physical bases from their true relative displacements, with no normalization regularity premise on the scenarios themselves. -/
theorem referenceBaseChart_relative_error_control {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount A hA g=N+1) :
    ∃ r₀ δ L : ℝ, 0<r₀ ∧ r₀<1 ∧ 0<δ ∧ 0≤L ∧
      ∀ (B C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ),
        B.PosDef → C.IsSymm → relativeBudget A (B-A)≤r₀ → relativeBudget A (C-B)≤δ →
        0<‖cgCanonicalError B g N‖ ∧
          ‖cgCanonicalError C g N‖≤‖cgCanonicalError B g N‖*(1+L*relativeBudget A (C-B)) := by
  -- Choose the true compact full-reference chart before every source and its base displacement.
  obtain ⟨r₀,hr₀,hr₁,hfull⟩ := referenceBaseChart_full_ball A hA g hcount
  let Z := selfAdjoint.submodule ℝ (Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
  let K : Set Z := Metric.closedBall 0 r₀
  have hnorm (z : Z) (hz : z∈K) : ‖z‖≤r₀ := by simpa only [K,Metric.mem_closedBall,dist_zero_right] using hz
  have hp (z : Z) (hz : z∈K) : ∀ᶠ y in 𝓝 z, (referenceBaseChart A y).PosDef :=
    referenceBaseChart_eventually_posDef A hA z ((hnorm z hz).trans_lt hr₁)
  have hpre (z : Z) (hz : z∈K) (i : ℕ) (hi : i≤N) : CG.gradient (cgOperator (referenceBaseChart A z)) g i≠0 := by
    obtain ⟨hB,hcountB⟩ := hfull z (hnorm z hz)
    exact cg_nonstagnation _ hB g i (by omega)
  have hφ (z : Z) (hz : z∈K) : 0<‖cgCanonicalError (referenceBaseChart A z) g N‖ :=
    canonical_error_pos _ (hp z hz).self_of_nhds _ (hpre z hz N le_rfl)
  obtain ⟨δ,L,hδ,hL,hcontrol⟩ := compact_referenceError_relative_variation (referenceBaseChart A) (fun _ => g)
    N K (isCompact_closedBall 0 r₀) (fun z _ => referenceBaseChart_analyticAt A z) hp
    (fun _ _ => analyticAt_const) (fun z hz i hi => hpre z hz i hi.le) hφ
  refine ⟨r₀,δ,L,hr₀,hr₁,hδ,hL,?_⟩
  intro B C hB hC hBr hCB
  let z : Z := ⟨relativeOperator A (B-A), Matrix.isHermitian_iff_isSymm.mpr (relativeOperator_isSymm _ _ (hB.1.isSymm.sub hA.1.isSymm))⟩
  let h : Z := ⟨relativeOperator A (C-B), Matrix.isHermitian_iff_isSymm.mpr (relativeOperator_isSymm _ _ (hC.sub hB.1.isSymm))⟩
  have hz : z∈K := by
    change dist z 0≤r₀
    rw [dist_zero_right]
    exact hBr
  have hh : ‖h‖≤δ := hCB
  have hzB : referenceBaseChart A z=B := referenceBaseChart_reconstruct A B hA hB.1.isSymm
  have hzC : referenceBaseChart A (z+h)=C := by
    have he : z+h=⟨relativeOperator A (C-A), Matrix.isHermitian_iff_isSymm.mpr (relativeOperator_isSymm _ _ (hC.sub hA.1.isSymm))⟩ := by
      apply Subtype.ext
      change relativeOperator A (B-A)+relativeOperator A (C-B)=relativeOperator A (C-A)
      simp only [relativeOperator,Matrix.mul_sub,Matrix.sub_mul]
      abel
    rw [he,referenceBaseChart_reconstruct A C hA hC]
  have hr := hcontrol z hz h hh
  rw [hzB,hzC] at hr
  exact ⟨by simpa only [hzB] using hφ z hz,hr⟩

end
end krylov.Information
