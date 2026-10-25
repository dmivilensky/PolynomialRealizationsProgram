import polyak.Boundary.P1.PhysicalContinuation

/-! Article: the exact finite active set of the open P1 regime. -/
noncomputable section
namespace polyak.Boundary.P1
open Spectral polyak.Certificates.P1Slacks

def ActivePair (n : ℕ) (σ : ℝ) : Prop := (n=1 ∧ σ= -1) ∨ (n=3 ∧ σ=1)

theorem continuation_atom_lower_strict {z : ℝ} (hz : z∈Set.Ioo (0 : ℝ) zW) :
    -z/2<branchAtom z (continuation z 1) := by
  have hb := continuation_physical ⟨hz.1,hz.2.le⟩
  have hz1 : z≤3/4 := by linarith [hz.2,zW_bounds.2]
  have hZ := continuation_source ⟨hz.1.le,(hz.2.trans zW_bounds.2).le⟩
  apply lt_of_le_of_ne hb.atom_lower
  intro he
  let c : Frequency := ⟨-z/2,⟨by linarith,by linarith [hz.1]⟩⟩
  have hactual : quartic z (branchU z (continuation z 0)) c=0 := by
    have hq := (regularSystem_contacts hZ).1
    rwa [← he] at hq
  have hspiral : quartic z (1-z/2) c=0 := quartic_spiral_zero z
  have hu := (quartic_strictMono_u hz.1.le hz1 c).injOn hb.u_nonneg
    (show 0≤1-z/2 by linarith) (hactual.trans hspiral.symm)
  exact hz.2.ne (regularRoot_spiral_eq_imp_switch hz.1 hz1 hZ hb hu)

theorem scaledSlack_inactive_prefix_pos {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2<a ∧ a≤0) (n : ℕ) (hn : 1≤n) (hN : n≤12)
    (σ : ℝ) (hs : σ= -1 ∨ σ=1) (hactive : ¬ActivePair n σ) :
    0<scaledSlack n σ z a := by
  have ha' : -z/2≤a ∧ a≤0 := ⟨ha.1.le,ha.2⟩
  rcases hs with rfl | rfl
  · interval_cases n
    · exact (hactive (Or.inl ⟨rfl,rfl⟩)).elim
    · exact positive02Lower hz hz1 ha'
    · exact positive03Lower hz hz1 ha'
    · exact positive04Lower hz hz1 ha'
    · exact positive05Lower hz hz1 ha'
    · exact positive06Lower hz hz1 ha'
    · exact positive07Lower hz hz1 ha'
    · exact positive08Lower hz hz1 ha'
    · exact positive09Lower hz hz1 ha'
    · exact positive10Lower hz hz1 ha'
    · exact positive11Lower hz hz1 ha'
    · exact positive12Lower hz hz1 ha'
  · interval_cases n
    · exact positive01Upper hz hz1 ha'
    · rw [scaledSlack_two_upper]
      apply mul_pos_of_neg_of_neg
      · have hp := mul_pos hz (show 0<2*a+z by linarith [ha.1])
        nlinarith
      · have hp := mul_nonpos_of_nonpos_of_nonneg ha.2 hz.le
        linarith
    · exact (hactive (Or.inr ⟨rfl,rfl⟩)).elim
    · exact positive04Upper hz hz1 ha'
    · exact positive05Upper hz hz1 ha'
    · exact positive06Upper hz hz1 ha'
    · exact positive07Upper hz hz1 ha'
    · exact positive08Upper hz hz1 ha'
    · exact positive09Upper hz hz1 ha'
    · exact positive10Upper hz hz1 ha'
    · exact positive11Upper hz hz1 ha'
    · exact positive12Upper hz hz1 ha'

theorem rawSlack_pos_of_scaled {z u a : ℝ} (hz : 0<z) (hD : 0<contactD z a)
    (hu : 0<u) (ha : a^2<1) (h0 : quartic z u a=0) (n : ℕ) (hn : 1≤n)
    (σ : ℝ) (hscaled : 0<scaledSlack n σ z a) :
    0<rawSlack u (1/z) (chargeNumerator z u a) n σ a := by
  have he := scaledSlack_source hz.ne' hD.ne' h0 n hn σ
  have hp : 0<2*u*(1-a^2)*scaledSlack n σ z a := by positivity
  rw [← he] at hp
  exact pos_of_mul_pos_right hp (mul_pos hD (pow_pos hz _)).le

end polyak.Boundary.P1
