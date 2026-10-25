import polyak.FareyPlateau.Plateau.SingletonResults

/-! Every source Farey fraction has a nonempty open plateau, and the
literal fraction 2/(2K+1) gives regular boundary points in every gap. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels ModeLocking Plateaus Set

theorem every_farey_plateau {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) :
    (singletonPlateau hK hf b hb0 hbk hb).Nonempty ∧
      IsOpen (singletonPlateau hK hf b hb0 hbk hb) ∧
      IsConnected (singletonPlateau hK hf b hb0 hbk hb) := by
  have hc := singletonPlateau_connected hK hf b hb0 hbk hb
  obtain ⟨q,hq⟩ := hc.nonempty
  have ho : IsOpen (singletonPlateau hK hf b hb0 hbk hb) := by
    rw [singletonPlateau_eq_component hK hf b hb0 hbk hb hq]
    exact plateau_open q
  exact ⟨hc.nonempty,ho,hc⟩

theorem middle_fraction_in_window {K : ℕ} (hK : 2≤K) :
    Chart.FractionInWindow K 2 (2*K+1) := by
  have hKR : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  refine ⟨by omega,?_,?_⟩
  · apply (div_lt_div_iff₀ (by positivity : (0:ℝ)<K+1)
      (by positivity : (0:ℝ)<(2*K+1:ℕ))).mpr
    push_cast
    linarith
  · apply (div_lt_div_iff₀ (by positivity : (0:ℝ)<(2*K+1:ℕ)) hKR).mpr
    push_cast
    linarith

theorem every_gap_regular_boundary {K : ℕ} (hK : 2≤K) :
    ∃q : Tuning,q∈BoundaryInGap K ∧ RegularPoint q 0 (2*K+1) := by
  have hf := middle_fraction_in_window hK
  let b : ℤ := K+1
  have hb0 : 0<b := by dsimp [b];omega
  have hbk : b<(2*K+1:ℕ) := by dsimp [b];omega
  have hb : b*(2:ℤ)≡1 [ZMOD ((2*K+1:ℕ):ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-1,?_⟩
    dsimp [b]
    ring
  obtain ⟨q,hq⟩ := (every_farey_plateau hK hf b hb0 hbk hb).1
  obtain ⟨C⟩ := singletonPlateau_certificate hK hf b hb0 hbk hb hq
  exact ⟨q.val,singletonPlateau_in_gap hK hf b hb0 hbk hb hq,C.regular⟩

end polyak.FareyPlateau
