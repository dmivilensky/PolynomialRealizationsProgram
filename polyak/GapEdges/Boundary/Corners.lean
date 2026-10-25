import polyak.GapEdges.Boundary.OmegaOne
import polyak.GapEdges.Boundary.Crossing
import polyak.Levels.Chart.BoundaryFaces

/-! The diagonal projection theorem includes precisely the admissible
locked corners.  The exceptional lower corner of the second gap is absent. -/
noncomputable section
namespace polyak.GapEdges
open General Levels Set Filter
open scoped Topology

def rootPullback (V : Set Tuning) : Set Chart.ParameterSpace :=
  {p | Chart.gapPolynomial p.1 p.2.1 p.2.2 ∈
    Subtype.val '' {C : Chart.CoefficientPoint | Chart.inverseTuning C ∈ V}}

theorem rootPullback_isOpen {V : Set Tuning} (hV : IsOpen V) : IsOpen (rootPullback V) :=
  (Chart.isOpen_coeffDomain.isOpenMap_subtype_val _
    (hV.preimage Chart.continuous_inverseTuning)).preimage Chart.continuous_gapPolynomial

theorem rootPullback_actual {V : Set Tuning} {p : Chart.ParameterSpace}
    (hp : p ∈ rootPullback V) (q : Tuning)
    (he : Chart.coefficients q = Chart.gapPolynomial p.1 p.2.1 p.2.2) : q ∈ V := by
  obtain ⟨C, hC, heC⟩ := hp
  have hb : 0 < q.beta := (Chart.coefficient_quadratic_neg_iff q).mp (by
    rw [he, ← heC]
    exact C.property.1)
  have hq : Chart.inverseTuning C = q := Chart.coefficients_injective
    (Chart.inverseBeta_pos C) hb ((Chart.coefficients_inverseTuning C).trans (heC.trans he.symm))
  change Chart.inverseTuning C ∈ V at hC
  rwa [hq] at hC

theorem first_tongue_corner_tip {k : ℕ} (hk : 3 ≤ k) {a : ℝ}
    (ha : Chart.amplitudeFloor (Chart.boundaryCosine k) (Chart.boundaryCosine k) < a)
    (q : Tuning) (he : Chart.coefficients q =
      Chart.gapPolynomial a (Chart.boundaryCosine k) (Chart.boundaryCosine k)) : Tip q k := by
  have hω := Chart.boundaryAngle_strict_mem hk
  have hr : Chart.boundaryCosine k ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · have hh := Real.strictAntiOn_cos ⟨hω.1.le, hω.2.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hω.2
      simpa only [Real.cos_pi, Chart.boundaryCosine, Chart.boundaryAngle] using hh
    · have hh := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨hω.1.le, hω.2.le⟩ hω.1
      simpa only [Real.cos_zero, Chart.boundaryCosine, Chart.boundaryAngle] using hh
  refine ⟨hk, (Chart.double_root_boundary q
    ((Chart.amplitudeFloor_pos hr.2 hr.2).trans ha) hr he).2.2, ?_⟩
  exact Chart.root_at_boundary_phase q hk he (Or.inl rfl)

theorem corner_positive_neighborhood {K k : ℕ} (hk : 3 ≤ k) {a : ℝ}
    (ha : Chart.amplitudeFloor (Chart.boundaryCosine k) (Chart.boundaryCosine k) < a) :
    ∃ U : Set Chart.ParameterSpace, IsOpen U ∧
      (a, Chart.boundaryCosine k, Chart.boundaryCosine k) ∈ U ∧
      ∀ p ∈ U, ∀ q : Tuning,
        Chart.coefficients q = Chart.gapPolynomial p.1 p.2.1 p.2.2 →
        Geometry.Gap K q → 0 < Threshold.sigma q := by
  have hω := Chart.boundaryAngle_strict_mem hk
  have hr : Chart.boundaryCosine k ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · have hh := Real.strictAntiOn_cos ⟨hω.1.le, hω.2.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hω.2
      simpa only [Real.cos_pi, Chart.boundaryCosine, Chart.boundaryAngle] using hh
    · have hh := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨hω.1.le, hω.2.le⟩ hω.1
      simpa only [Real.cos_zero, Chart.boundaryCosine, Chart.boundaryAngle] using hh
  let C : Chart.CoefficientPoint := ⟨Chart.gapPolynomial a
    (Chart.boundaryCosine k) (Chart.boundaryCosine k),
    Chart.gapPolynomial_mem_domain hr.1 le_rfl hr.2 ha⟩
  have htip := first_tongue_corner_tip hk ha (Chart.inverseTuning C)
    (Chart.coefficients_inverseTuning C)
  have hev : ∀ᶠ q in 𝓝 (Chart.inverseTuning C), Geometry.Gap K q → 0 < Threshold.sigma q :=
    htip.closed_tongue_near.mono (fun _ h => h.2 K)
  obtain ⟨V, hsub, hV, hqV⟩ := mem_nhds_iff.mp hev
  refine ⟨rootPullback V, rootPullback_isOpen hV, ⟨C, hqV, rfl⟩, ?_⟩
  intro p hp q he hgap
  exact hsub (rootPullback_actual hp q he) hgap

theorem corner_projection_neighborhood {K k : ℕ} (hK : 2 ≤ K) (hk : 3 ≤ k)
    (_hcorner : k = K ∨ k = K + 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r₁ r₂ : ℝ,
      Chart.boundaryCosine K < r₁ → r₁ < r₂ → r₂ < Chart.boundaryCosine (K + 1) →
      |r₁ - Chart.boundaryCosine k| < δ → |r₂ - Chart.boundaryCosine k| < δ →
      ∃ b : ℝ, ∃ q : Tuning, q ∈ ModeLocking.BoundaryInGap K ∧
        Chart.coefficients q = Chart.gapPolynomial b r₁ r₂ := by
  let r := Chart.boundaryCosine k
  let a := Chart.amplitudeFloor r r + 1
  have ha : Chart.amplitudeFloor r r < a := by dsimp [a]; linarith
  obtain ⟨U, hU, hbase, hpos⟩ := corner_positive_neighborhood (K := K) hk ha
  let W := {x : ℝ × ℝ | (a, x.1, x.2) ∈ U ∧ Chart.amplitudeFloor x.1 x.2 < a}
  have hr : r < 1 := by
    have hh := Chart.boundaryCosine_succ_lt_one (K := k - 1) (by omega : 2 ≤ k - 1)
    have he : k - 1 + 1 = k := by omega
    simpa only [he] using hh
  have hfloor : ContinuousAt (fun x : ℝ × ℝ => Chart.amplitudeFloor x.1 x.2) (r, r) := by
    unfold Chart.amplitudeFloor
    fun_prop (disch := exact mul_ne_zero (by linarith) (by linarith))
  have hW : W ∈ 𝓝 (r, r) := by
    filter_upwards [((hU.preimage (continuous_const.prodMk continuous_id)).mem_nhds hbase),
      hfloor.eventually_lt_const ha] with x hx hxa
    exact ⟨hx, hxa⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨δ, hδ, ?_⟩
  intro r₁ r₂ h₁ hrr h₂ he₁ he₂
  have hx : (r₁, r₂) ∈ W := hball (show (r₁, r₂) ∈ Metric.ball (r, r) δ from by
    simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff] using And.intro he₁ he₂)
  have hgap := (rayTuning hK h₁ hrr h₂ ⟨a, hx.2⟩).property
  apply ray_meets_boundary_of_positive hK h₁ hrr h₂ hx.2
  exact hpos (a, r₁, r₂) hx.1 _ (Chart.coefficients_inverseTuning _) hgap

theorem boundary_projection_neighborhood {K : ℕ} (hK : 2 ≤ K) {r : ℝ}
    (hr : (Chart.boundaryCosine K < r ∧ r ≤ Chart.boundaryCosine (K + 1)) ∨
      (3 ≤ K ∧ r = Chart.boundaryCosine K)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r₁ r₂ : ℝ,
      Chart.boundaryCosine K < r₁ → r₁ < r₂ → r₂ < Chart.boundaryCosine (K + 1) →
      |r₁ - r| < δ → |r₂ - r| < δ →
      ∃ b : ℝ, ∃ q : Tuning, q ∈ ModeLocking.BoundaryInGap K ∧
        Chart.coefficients q = Chart.gapPolynomial b r₁ r₂ := by
  rcases hr with ⟨hl, hu⟩ | ⟨hk, rfl⟩
  · rcases hu.eq_or_lt with rfl | hu
    · exact corner_projection_neighborhood hK (by omega : 3 ≤ K + 1) (Or.inr rfl)
    · exact diagonal_projection_neighborhood hK hl hu
  · exact corner_projection_neighborhood hK hk (Or.inl rfl)

end polyak.GapEdges
