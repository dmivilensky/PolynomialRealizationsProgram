import polyak.Farey.FanDivergence.Supported

/-! Source Theorem Fan tongues, with the exact grid, dimensions,
remaining classes, and closed phase endpoint. -/
noncomputable section
namespace polyak.Farey
open polyak.General polyak.Levels

abbrev FanHarmonicIndex (P : FanParameters) :=
  {j : Fin P.k.toNat // 0<j.val ∧ 2*j.val<P.k.toNat}

def fanHarmonicFrequency (P : FanParameters) (j : FanHarmonicIndex P) : Frequency :=
  gridFrequency P.k (j.val.val:ℤ) P.k_pos (by omega) (by
    have hcast : (P.k.toNat:ℤ)=P.k := Int.toNat_of_nonneg P.k_pos.le
    have hh : (2:ℤ)*j.val.val<(P.k.toNat:ℤ) := by exact_mod_cast j.property.2
    omega)

theorem fanHarmonicFrequency_grid (P : FanParameters) (j : FanHarmonicIndex P) :
    fanHarmonicFrequency P j∈periodicGrid P.k.toNat := by
  exact gridFrequency_mem_grid P.k j.val.val P.k_pos
    (by exact_mod_cast j.property.1) (by
      have hcast : (P.k.toNat:ℤ)=P.k := Int.toNat_of_nonneg P.k_pos.le
      have hh : (2:ℤ)*j.val.val<(P.k.toNat:ℤ) := by exact_mod_cast j.property.2
      omega)

theorem fan_div_a (P : FanParameters) (q : Tuning) (w : FanHarmonicIndex P→ℝ)
    (hw : ∀j,0≤w j) (hne : ∃j,w j≠0)
    (hmin : 0≤∑j,w j*(tuningCurve q).minimizer (fanHarmonicFrequency P j))
    (hlag : ∀n : ℕ,0<n→n<P.k.toNat→
      0≤∑j,w j*(tuningCurve q).lag (n:ℤ) (fanHarmonicFrequency P j)) :
    FanPeriodicOrbit q P.k.toNat (Fintype.card {j // w j≠0}) ∧ 1≤q.rate := by
  have hpos : ∃j,0<w j := by
    obtain ⟨j,hj⟩ := hne
    exact ⟨j,lt_of_le_of_ne (hw j) (Ne.symm hj)⟩
  have hpred : (fun j=>0<w j)=(fun j=>w j≠0) := by
    funext j
    exact propext ⟨ne_of_gt,fun hj=>lt_of_le_of_ne (hw j) (Ne.symm hj)⟩
  have hk : 0<P.k.toNat := by have := P.k_pos;omega
  have hh := fan_divergence_of_real_weights q hk w (fanHarmonicFrequency P)
    hw hpos (fanHarmonicFrequency_grid P) hmin hlag
  simpa only [hpred] using hh

theorem fan_phase_forces_p_bound (P : FanParameters) (Θ : Curve)
    (hcomp : P.halfCompanion<Θ P.companion ∧ Θ P.companion<P.companionAngle) :
    P.p≤P.K+1 := by
  have hh := hcomp.1.trans hcomp.2
  have hkR : (0:ℝ)<P.k := by exact_mod_cast P.k_pos
  dsimp [FanParameters.halfCompanion,FanParameters.companionAngle] at hh
  have hnum := (div_lt_div_iff_of_pos_right hkR).mp hh
  have hpR : (P.p:ℝ)<P.K+2 := by nlinarith [Real.pi_pos]
  have hpZ : P.p<P.K+2 := by exact_mod_cast hpR
  omega

theorem fan_div_b (P : FanParameters) (Θ : Curve)
    (hmain : P.firstAngle<Θ P.anchor ∧ Θ P.anchor<P.halfAnchor)
    (hcomp : P.halfCompanion<Θ P.companion ∧ Θ P.companion<P.companionAngle) :
    P.p≤P.K+1 ∧
      (0<Θ.lag 1 P.anchor ∧ Θ.lag (-P.K) P.anchor<0 ∧
        0<Θ.lag (-P.K) P.companion ∧ Θ.lag 1 P.companion<0) ∧
      (FanPairFeasible P Θ ↔ 0≤fanDeterminant P Θ) ∧
      (3≤P.p→Θ P.companion<Real.pi/2) :=
  ⟨fan_phase_forces_p_bound P Θ hcomp,P.four_strict_signs Θ hmain hcomp,
    fan_pair_determinant_iff P Θ hmain.1 hcomp,
    fun hp=>P.companion_phase_lt_half_of_three_le Θ hp hcomp.2⟩

theorem fan_div_c (P : FanParameters) (hp : P.p=2) (Θ : Curve)
    (hcomp : P.firstAngle<Θ P.companion ∧ Θ P.companion≤P.halfAnchor)
    (hmain : P.firstAngle<Θ P.anchor ∧ Θ P.anchor≤P.halfAnchor) :
    (∀u v : ℝ,0≤u→0≤v→∀n : ℤ,2≤n→n<P.k→n≠P.K+1→0≤fanLagSum P Θ u v n) ∧
      (FanSupportedFP P Θ ↔ 0≤fanP2Expression P Θ) :=
  ⟨fun _ _ hu hv _ hn hnk hne=>P.p2_remaining_weights hp Θ hcomp.2 hmain.2 hu hv hn hnk hne,
    p2_full_program_iff_displayed P hp Θ hcomp hmain⟩

end polyak.Farey
