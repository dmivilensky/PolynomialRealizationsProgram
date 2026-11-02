import krylov.LotkaVolterra.EndpointFiniteClock

/-!
Article: `main_krylov`, `apC:prop:g1`, original-orbit exit classes.
The actual state coordinate stays above its initial value one. The signed
difference from the constructed separating graph has a positive integrating
factor along every finite positive original orbit. Actual lower exits and
escape-wedge entrances therefore lie on the prescribed initial sides.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set

/-- The physical state coordinate cannot cross downward through one. -/
theorem positive_solution_u_ge_one {γ T : ℝ} {α : ℝ → ℝ × ℝ}
    (hα : IsSolutionOn γ α (Icc 0 T)) (hU₀ : (α 0).2 = 1)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, α t ∈ positiveQuadrant) :
    ∀ t ∈ Icc (0 : ℝ) T, 1 ≤ (α t).2 := by
  intro t ht
  by_contra! hn
  let ε := (1 - (α t).2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hUder (u : ℝ) (hu : u ∈ Icc (0 : ℝ) t) :
      HasDerivAt (fun u ↦ (α u).2 - 1 + ε)
        ((α u).2 * ((α u).1 + 1 - (α u).2)) u := by
    have hdu : HasDerivAt (fun u ↦ (α u).2)
        ((α u).2 * ((α u).1 + 1 - (α u).2)) u := by
      convert! (hasFDerivAt_snd (𝕜 := ℝ) (p := α u)).comp_hasDerivAt u
        (hα u ⟨hu.1, hu.2.trans ht.2⟩) using 1
    exact (hdu.sub_const 1).add_const ε
  have hb := pair_positive_invariant ht.1 hUder
    (fun u _ ↦ hasDerivAt_const u (1 : ℝ))
    (show 0 < (α 0).2 - 1 + ε by rw [hU₀]; linarith)
    (show (0 : ℝ) < 1 by norm_num)
    (fun u hu heq _ ↦ ?_) (fun _ _ heq _ ↦ by norm_num at heq)
  · dsimp [ε] at hb
    linarith [hb.1]
  · have hh := hp u ⟨hu.1, hu.2.trans ht.2⟩
    apply mul_pos hh.2
    linarith [hh.1]

/-- Positive factor for the difference from an actual endpoint separating
graph, valid on every finite physical orbit segment. -/
theorem endpoint_orbit_difference_factor {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U)
    {T : ℝ} (hT : 0 ≤ T) {α : ℝ → ℝ × ℝ}
    (hα : IsSolutionOn 1 α (Icc 0 T))
    (hU : ∀ t ∈ Icc (0 : ℝ) T, 1 ≤ (α t).2) :
    ∃ k > 0, (α T).1 - ((α T).2 + e ((α T).2)) =
      ((α 0).1 - ((α 0).2 + e ((α 0).2))) * k := by
  have hαC := HasDerivAt.continuousOn hα
  have heC : ContinuousOn e (Ici 1) := HasDerivAt.continuousOn fun U hU ↦ (he U hU).2
  have heUC : ContinuousOn (fun t ↦ e ((α t).2)) (Icc (0 : ℝ) T) := heC.comp hαC.snd hU
  let R : ℝ → ℝ := fun t ↦ 1 + endpointGraphRate ((α t).2) (e ((α t).2))
  have hR : ContinuousOn R (Icc (0 : ℝ) T) := by
    unfold R endpointGraphRate
    apply continuousOn_const.add
    apply ContinuousOn.add
    · exact (heUC.sub continuousOn_const).div (heUC.add continuousOn_const)
        (fun t ht ↦ by
          change e ((α t).2) + 1 ≠ 0
          linarith [(he _ (hU t ht)).1.1])
    · exact (((heUC.const_mul 2).sub continuousOn_const).add
        (continuousOn_const.div (heUC.add continuousOn_const)
          (fun t ht ↦ by
          change e ((α t).2) + 1 ≠ 0
          linarith [(he _ (hU t ht)).1.1]))).div hαC.snd
        (fun t ht ↦ by linarith [hU t ht])
  let a : ℝ → ℝ := fun t ↦
    2 * ((α t).1 + ((α t).2 + e ((α t).2)) - 1 - (α t).2) - (α t).2 * R t
  have ha : ContinuousOn a (Icc (0 : ℝ) T) :=
    (((hαC.fst.add (hαC.snd.add heUC)).sub continuousOn_const).sub hαC.snd).const_mul 2
      |>.sub (hαC.snd.mul hR)
  apply scalar_linear_endpoint_factor hT ha
  intro t ht
  have hSder : HasDerivAt (fun t ↦ (α t).1)
      (2 * (α t).1 * ((α t).1 - 1 - (α t).2)) t := by
    convert! (hasFDerivAt_fst (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t (hα t ht) using 1
    simp [vectorField, sRate]
  have hUder : HasDerivAt (fun t ↦ (α t).2)
      ((α t).2 * ((α t).1 + 1 - (α t).2)) t := by
    convert! (hasFDerivAt_snd (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t (hα t ht) using 1
  have hgraph : R t * ((α t).2 * (e ((α t).2) + 1)) =
      2 * ((α t).2 + e ((α t).2)) * (e ((α t).2) - 1) := by
    dsimp [R]
    rw [endpointGraphRate_eq (by linarith [hU t ht])
      (by linarith [(he _ (hU t ht)).1.1])]
    field_simp [show (α t).2 ≠ 0 by linarith [hU t ht],
      show e ((α t).2) + 1 ≠ 0 by linarith [(he _ (hU t ht)).1.1]]
    ring
  have hcomp := hUder.add ((he _ (hU t ht)).2.comp t hUder)
  have hh := hSder.sub hcomp
  convert hh using 1
  · rfl
  · dsimp [a, R] at *
    nlinarith only [hgraph]

/-- Actual finite original-orbit exit from the endpoint wedge. -/
def endpointLowerOrbitSet : Set ℝ := {s | 2 < s ∧ ∃ α : ℝ → ℝ × ℝ,
  α 0 = (s, 1) ∧ ∃ T ≥ 0, IsSolutionOn 1 α (Icc 0 T) ∧
    (∀ t ∈ Icc 0 T, α t ∈ positiveQuadrant) ∧ (α T).1 ≤ (α T).2 + 1}

/-- Actual finite original-orbit entrance into the escape wedge. -/
def endpointUpperOrbitSet : Set ℝ := {s | 2 < s ∧ ∃ α : ℝ → ℝ × ℝ,
  α 0 = (s, 1) ∧ ∃ T ≥ 0, IsSolutionOn 1 α (Icc 0 T) ∧
    (∀ t ∈ Icc 0 T, α t ∈ positiveQuadrant) ∧ α T ∈ endpointEscapeRegion}

theorem endpointLowerOrbitSet_subset {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) :
    endpointLowerOrbitSet ⊆ Ioo (2 : ℝ) (1 + e 1) := by
  rintro s ⟨hs, α, hα₀, T, hT, hα, hp, hlast⟩
  have hU := positive_solution_u_ge_one hα (by rw [hα₀]) hp
  obtain ⟨k, hk, hdiff⟩ := endpoint_orbit_difference_factor he hT hα hU
  have hh := endpoint_graph_gap_strict he (hU T ⟨hT, le_rfl⟩)
  rw [hα₀] at hdiff
  refine ⟨hs, ?_⟩
  by_contra! hn
  have hnonneg := mul_nonneg (show 0 ≤ s - (1 + e 1) by linarith) hk.le
  linarith [hh.1]

theorem endpointUpperOrbitSet_subset {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) :
    endpointUpperOrbitSet ⊆ Ioi (1 + e 1) := by
  rintro s ⟨_, α, hα₀, T, hT, hα, hp, hlast⟩
  have hU := positive_solution_u_ge_one hα (by rw [hα₀]) hp
  obtain ⟨k, hk, hdiff⟩ := endpoint_orbit_difference_factor he hT hα hU
  have heU := (he _ (hU T ⟨hT, le_rfl⟩)).1.2
  change 4 < (α T).1 ∧ 0 < (α T).2 ∧ (α T).2 < (α T).1 / 4 at hlast
  rw [hα₀] at hdiff
  change 1 + e 1 < s
  by_contra! hn
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (show s - (1 + e 1) ≤ 0 by linarith) hk.le
  linarith [hU T ⟨hT, le_rfl⟩, hlast.2.2]

end
end krylov.LotkaVolterra
