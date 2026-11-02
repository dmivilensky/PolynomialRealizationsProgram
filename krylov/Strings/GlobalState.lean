import krylov.Strings.StateRegularity

/-!
Article: main_krylov, apC:eq:state, half-line strings.
Use: Patch the unique finite-window states into an actual global state. This
is a proved compatibility construction, not a global-existence assumption.
Source: finite-window uniqueness, elementary localization of continuous
functions, and equality of integrals on intervals.
-/

/-!
Article: krylov, Definition D.6 [s3:def:string].

The unit left atom is part of the initial state. Genuine Volterra existence and uniqueness,
compact gluing, RN density, type clock and monotone exhaustion reward cover arbitrary Stieltjes
strings.
Mass is represented as a measure with a unit origin atom; finite excluded endpoints are handled
by local windows, not by assuming a finite total mass.
-/

namespace krylov.Strings
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal

namespace Mass

/-- Equal physical position histories give equal reconstructed slopes. -/
theorem slope_eq_of_eqOn (M : Mass) {φ ψ : ℝ → ℝ} {x : ℝ}
    (h : EqOn φ ψ (Icc 0 x)) : integralSlope M.measure φ x = integralSlope M.measure ψ x := by
  dsimp [integralSlope]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  exact h ⟨ht.1.le, ht.2⟩

/-- Transfer the position equation between equal histories on a finite window. -/
theorem position_equation_congr (M : Mass) {φ ψ : ℝ → ℝ} (L : ℝ≥0)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (h : EqOn φ ψ (Icc 0 (L : ℝ))) :
    ∀ x ∈ Icc 0 (L : ℝ), ψ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure ψ t := by
  intro x hx
  rw [← h hx, he x hx]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  apply M.slope_eq_of_eqOn
  intro y hy
  exact h ⟨hy.1, hy.2.trans (ht.2.trans hx.2)⟩

/-- All finite-window states can be chosen with the same constant extension
to negative positions; their physical equations remain unchanged. -/
theorem exists_state_on_left_constant (M : Mass) (L : ℝ≥0) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ φ 0 = 1 ∧ Monotone φ ∧
      (∀ x ≤ 0, φ x = 1) ∧
      ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t := by
  obtain ⟨φ, hc, hz, hm, he⟩ := M.exists_state_on L
  let ψ : ℝ → ℝ := fun x ↦ φ (max x 0)
  have hagree : EqOn φ ψ (Icc 0 (L : ℝ)) := by
    intro x hx
    dsimp [ψ]
    rw [max_eq_left hx.1]
  refine ⟨ψ, by fun_prop, ?_, ?_, ?_, ?_⟩
  · simpa only [ψ, max_self] using hz
  · exact hm.comp (fun _ _ hxy ↦ max_le_max hxy le_rfl)
  · intro x hx
    dsimp [ψ]
    rw [max_eq_right hx, hz]
  · exact M.position_equation_congr L (fun x hx ↦ (he x hx).1) hagree

/-- The compatible compact constructions produce a global half-line state,
with a harmless constant left extension. No boundedness of total mass or
absolute continuity of mass is required. -/
theorem exists_global_state (M : Mass) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ φ 0 = 1 ∧ Monotone φ ∧
      (∀ x ≤ 0, φ x = 1) ∧
      ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t := by
  choose F hc hz hm hleft he using M.exists_state_on_left_constant
  let windowAt (x : ℝ) : ℝ≥0 := ⟨max x 0 + 1, by positivity⟩
  let φ : ℝ → ℝ := fun x ↦ F (windowAt x) x
  have hbound (x : ℝ) : x ≤ (windowAt x : ℝ) := by
    change x ≤ max x 0 + 1
    linarith [le_max_left x 0]
  have hagree (L : ℝ≥0) {x : ℝ} (hx : x ≤ L) : φ x = F L x := by
    by_cases hx0 : 0 ≤ x
    · exact M.state_overlap (windowAt x) L (hc _) (hc _) (he _) (he _)
        ⟨hx0, by simpa using (le_min (hbound x) hx)⟩
    · dsimp [φ]
      rw [hleft _ x (le_of_not_ge hx0), hleft _ x (le_of_not_ge hx0)]
  have hcφ : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro x
    let L := windowAt x
    have hlt : x < (L : ℝ) := by
      change x < max x 0 + 1
      linarith [le_max_left x 0]
    apply (hc L).continuousAt.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hlt] with y hy
    exact hagree L hy.le
  have hzero : φ 0 = 1 := by
    rw [hagree (windowAt 0) (hbound 0), hz]
  have hmφ : Monotone φ := by
    intro x y hxy
    let L := windowAt y
    rw [hagree L (hxy.trans (hbound y)), hagree L (hbound y)]
    exact hm L hxy
  refine ⟨φ, hcφ, hzero, hmφ, ?_, ?_⟩
  · intro x hx
    exact hleft _ x hx
  · intro x hx
    let L := windowAt x
    have heq : EqOn (F L) φ (Icc 0 (L : ℝ)) := by
      intro y hy
      exact (hagree L hy.2).symm
    exact M.position_equation_congr L (he L) heq x ⟨hx, hbound x⟩

/-- The global physical state is unique, independently of the chosen finite
windows or their extensions outside the physical half-line. -/
theorem global_state_unique (M : Mass) {φ ψ : ℝ → ℝ} (hcφ : Continuous φ) (hcψ : Continuous ψ)
    (heφ : ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (heψ : ∀ x ≥ 0, ψ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure ψ t) :
    EqOn φ ψ (Ici 0) := by
  intro x hx
  let L : ℝ≥0 := ⟨x, hx⟩
  exact M.state_unique_on L hcφ hcψ (fun t ht ↦ heφ t ht.1)
    (fun t ht ↦ heψ t ht.1) ⟨hx, le_rfl⟩

end Mass
end
end krylov.Strings
