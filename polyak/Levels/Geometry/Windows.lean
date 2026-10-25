import polyak.Levels.Geometry.Convexity
import Mathlib.Algebra.Order.Floor.Semiring

/-! The exact, unique rotation window between consecutive first-harmonic grids. -/
noncomputable section
namespace polyak.Levels.Geometry
open Set

def firstFrequency (K : ℕ) (hK : 2≤K) : Frequency :=
  ⟨2*Real.pi/K,by
    have hR : (2:ℝ)≤K:=by exact_mod_cast hK
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : (0:ℝ)<K)).mpr
      nlinarith [Real.pi_pos]⟩

def InWindow (K : ℕ) (ω : Frequency) : Prop :=
  2*Real.pi/(K+1)<(ω:ℝ) ∧ (ω:ℝ)<2*Real.pi/K

theorem exists_window {ω : Frequency} (hω : 0<(ω:ℝ)) (hπ : (ω:ℝ)<Real.pi)
    (hgrid : ∀K : ℕ,∀hK : 3≤K,ω≠firstFrequency K (by omega)) :
    ∃K : ℕ,2≤K ∧ InWindow K ω := by
  let R:=2*Real.pi/(ω:ℝ)
  let K:=Nat.floor R
  have hR : 2<R:=by dsimp [R]; exact (lt_div_iff₀ hω).mpr (by linarith)
  have hK : 2≤K:=by exact Nat.le_floor hR.le
  have hkR : (K:ℝ)≤R:=Nat.floor_le (by linarith)
  have hnext : R<(K:ℝ)+1:=Nat.lt_floor_add_one R
  have hstrict : (K:ℝ)<R := by
    apply lt_of_le_of_ne hkR
    intro he
    have hk3 : 3≤K := by
      have h2 : 2<K := by exact_mod_cast (show (2:ℝ)<K by linarith)
      omega
    apply hgrid K hk3
    apply Subtype.ext
    change (ω:ℝ)=2*Real.pi/K
    apply (eq_div_iff (by positivity : (K:ℝ)≠0)).mpr
    have heq : (K:ℝ)*(ω:ℝ)=2*Real.pi:=by
      rw [he]
      dsimp [R]
      field_simp
    linarith
  refine ⟨K,hK,?_,?_⟩
  · apply (div_lt_iff₀ (by positivity : (0:ℝ)<(K:ℝ)+1)).mpr
    nlinarith [(div_lt_iff₀ hω).mp hnext]
  · apply (lt_div_iff₀ (by positivity : (0:ℝ)<K)).mpr
    nlinarith [(lt_div_iff₀ hω).mp hstrict]

theorem window_disjoint {K L : ℕ} (hK : 2≤K) (hL : 2≤L) {ω : Frequency}
    (hω : InWindow K ω) (hη : InWindow L ω) : K=L := by
  have hωpos : 0<(ω:ℝ):=lt_trans (by positivity) hω.1
  have hKr : (0:ℝ)<K:=by positivity
  have hLr : (0:ℝ)<L:=by positivity
  have hklo : (K:ℝ)<2*Real.pi/(ω:ℝ):=
    (lt_div_iff₀ hωpos).mpr (by nlinarith [(lt_div_iff₀ hKr).mp hω.2])
  have hkhi : 2*Real.pi/(ω:ℝ)<(K:ℝ)+1:=
    (div_lt_iff₀ hωpos).mpr (by nlinarith [(div_lt_iff₀ (by positivity : (0:ℝ)<(K:ℝ)+1)).mp hω.1])
  have hllo : (L:ℝ)<2*Real.pi/(ω:ℝ):=
    (lt_div_iff₀ hωpos).mpr (by nlinarith [(lt_div_iff₀ hLr).mp hη.2])
  have hlhi : 2*Real.pi/(ω:ℝ)<(L:ℝ)+1:=
    (div_lt_iff₀ hωpos).mpr (by nlinarith [(div_lt_iff₀ (by positivity : (0:ℝ)<(L:ℝ)+1)).mp hη.1])
  have hkl : (K:ℝ)<L+1:=hklo.trans hlhi
  have hlk : (L:ℝ)<K+1:=hllo.trans hkhi
  have : K<L+1:=by exact_mod_cast hkl
  have : L<K+1:=by exact_mod_cast hlk
  omega

/-- An interval avoiding every grid point is contained in one unique window. -/
theorem interval_unique_window {C : Set Frequency} (hC : C.OrdConnected)
    (hne : C.Nonempty) (hint : ∀ω∈C,0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi)
    (hgrid : ∀K : ℕ,∀hK : 3≤K,firstFrequency K (by omega)∉C) :
    ∃!K : ℕ,2≤K ∧ ∀ω∈C,InWindow K ω := by
  obtain ⟨ω,hω⟩:=hne
  obtain ⟨K,hK,hw⟩:=exists_window (hint ω hω).1 (hint ω hω).2 (fun L hL he=>hgrid L hL (he ▸ hω))
  have hforall : ∀η∈C,InWindow K η := by
    intro η hη
    constructor
    · by_contra hn
      have hb : firstFrequency (K+1) (by omega)∈Icc η ω:=
        ⟨by change (η:ℝ)≤2*Real.pi/((K+1:ℕ):ℝ); simpa only [Nat.cast_add,Nat.cast_one] using le_of_not_gt hn,
          by change 2*Real.pi/((K+1:ℕ):ℝ)≤(ω:ℝ); simpa only [Nat.cast_add,Nat.cast_one] using hw.1.le⟩
      exact hgrid (K+1) (by omega) (hC.out hη hω hb)
    · by_contra hn
      by_cases hk2 : K=2
      · subst K
        have hp : (firstFrequency 2 (by omega):ℝ)=Real.pi:=by norm_num [firstFrequency]
        have hge : (firstFrequency 2 (by omega):ℝ)≤(η:ℝ):=le_of_not_gt hn
        rw [hp] at hge
        exact (not_le_of_gt (hint η hη).2) hge
      · have hb : firstFrequency K hK∈Icc ω η:=⟨hw.2.le,le_of_not_gt hn⟩
        exact hgrid K (by omega) (hC.out hω hη hb)
  refine ⟨K,⟨hK,hforall⟩,?_⟩
  intro L hL
  exact window_disjoint hL.1 hK (hL.2 ω hω) hw

end polyak.Levels.Geometry
