import krylov.LotkaVolterra.GlobalSubcriticalGraph
import krylov.LotkaVolterra.GlobalSaddleLimit

/-!
The global separating graph in normalized chord coordinates. The wedge
bounds supply the bounded slope interval, and the exact graph equation
supplies the regular-singular derivative. This is the bridge matching the
globally constructed graph to the analytic local saddle chord.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set

namespace SubcriticalGraph
variable {γ : ℝ} (G : SubcriticalGraph γ)

def rawChord (u : ℝ) : ℝ :=
  (saddleS γ - G.σ (saddleU γ - (saddleU γ / 2) * u)) / ((saddleU γ / 2) * u)

theorem rawChord_bounds_of_lt_two {u : ℝ} (hγ₁ : γ < 1)
    (hu : u < 2) (hu₀ : u ≠ 0) : G.rawChord u ∈ Ioo 0 γ := by
  have hB := saddleU_pos hγ₁
  let c := saddleU γ / 2
  let U := saddleU γ - c * u
  have hc : 0 < c := half_pos hB
  have hU : 0 < U := by
    have hh := mul_lt_mul_of_pos_left hu hc
    dsimp [U, c] at *
    linarith
  have hA := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
  change 0 < (saddleS γ - G.σ U) / (c * u) ∧ (saddleS γ - G.σ U) / (c * u) < γ
  rcases lt_or_gt_of_ne hu₀ with hun | hup
  · have hcu : c * u < 0 := mul_neg_of_pos_of_neg hc hun
    have hUB : saddleU γ < U := by dsimp [U]; linarith
    have hh := G.upper U hUB
    refine ⟨div_pos_of_neg_of_neg (by linarith [hh.1]) hcu, ?_⟩
    apply (div_lt_iff_of_neg hcu).mpr
    rw [hA]
    dsimp [U] at hh
    nlinarith [hh.2.1]
  · have hcu : 0 < c * u := mul_pos hc hup
    have hUB : U < saddleU γ := by dsimp [U]; linarith
    have hh := G.lower U ⟨hU, hUB⟩
    refine ⟨div_pos (by linarith [hh.2.1]) hcu, ?_⟩
    apply (div_lt_iff₀ hcu).mpr
    rw [hA]
    dsimp [U] at hh
    nlinarith [hh.1]

theorem rawChord_hasDerivAt_of_lt_two {u : ℝ} (hγ₁ : γ < 1)
    (hu : u < 2) (hu₀ : u ≠ 0) :
    HasDerivAt G.rawChord (saddleSlopeRate γ ((saddleU γ / 2) * u) (G.rawChord u) / u) u := by
  let c := saddleU γ / 2
  let U := saddleU γ - c * u
  have hc : 0 < c := half_pos (saddleU_pos hγ₁)
  have hU : 0 < U := by
    have hh := mul_lt_mul_of_pos_left hu hc
    dsimp [U, c] at *
    linarith
  have hcu : c * u ≠ 0 := mul_ne_zero (ne_of_gt hc) hu₀
  have hZU : saddleU γ - U = c * u := by dsimp [U]; ring
  have hUne : U ≠ saddleU γ := by
    intro heq
    have hh : c * u = 0 := by rw [← hZU, heq]; ring
    exact hcu hh
  have hbound := G.rawChord_bounds_of_lt_two hγ₁ hu hu₀
  have hvden : 1 - G.rawChord u ≠ 0 := by linarith [hbound.2]
  have hσ : G.σ U = saddleS γ - G.rawChord u * (saddleU γ - U) := by
    unfold rawChord
    change G.σ U = saddleS γ - ((saddleS γ - G.σ U) / (c * u)) * (saddleU γ - U)
    rw [hZU, div_mul_cancel₀ _ hcu]
    ring
  have hrate := graphRate_from_chord (ne_of_lt hγ₁) (ne_of_gt hU)
    (sub_ne_zero.mpr (Ne.symm hUne)) hvden
  rw [← hσ, hZU] at hrate
  have hgd : HasDerivAt G.σ (G.rawChord u + saddleSlopeRate γ (c * u) (G.rawChord u)) U := by
    rw [hrate]
    exact G.derivative U hU hUne
  have hN := (hgd.comp u ((hasDerivAt_id u).const_mul c |>.const_sub (saddleU γ)))
    |>.const_sub (saddleS γ)
  have hD := (hasDerivAt_id u).const_mul c
  have hh := hN.div hD hcu
  convert hh using 1
  · rfl
  · dsimp only [id_eq, Function.comp_apply]
    have hnum : saddleS γ - G.σ U = G.rawChord u * (c * u) := by
      rw [hσ, hZU]
      ring
    rw [hnum]
    simp only [c, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    field_simp [ne_of_gt (saddleU_pos hγ₁), hu₀]
    ring

theorem rawChord_bounds {u : ℝ} (hγ₁ : γ < 1)
    (hu : u ∈ Icc (-1 : ℝ) 1) (hu₀ : u ≠ 0) : G.rawChord u ∈ Ioo 0 γ :=
  G.rawChord_bounds_of_lt_two hγ₁ (hu.2.trans_lt (by norm_num)) hu₀

theorem rawChord_hasDerivAt {u : ℝ} (hγ₁ : γ < 1)
    (hu : u ∈ Icc (-1 : ℝ) 1) (hu₀ : u ≠ 0) :
    HasDerivAt G.rawChord (saddleSlopeRate γ ((saddleU γ / 2) * u) (G.rawChord u) / u) u :=
  G.rawChord_hasDerivAt_of_lt_two hγ₁ (hu.2.trans_lt (by norm_num)) hu₀

end SubcriticalGraph
end
end krylov.LotkaVolterra
