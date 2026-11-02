import jacobi.Jacobi.EndpointGeometry
import jacobi.Jacobi.PotentialBound
import jacobi.Oscillation.ZeroGap

/-!
Article: jacobi, Proposition B.1.
The actual two-edge distance bounds control both singularities of the
original restoring equation. Comparison with one literal constant-frequency
sine wave then bounds every genuine consecutive angular gap, including
the central gap, by a common positive multiple of 1/N.
Use: supplies the full angular-separation assertion in Proposition B.1 (c), including the center, and the later node-gap and interpolation estimates.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Oscillation
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every original consecutive finite Jacobi angle has a uniform positive inverse-frequency gap, with all source-function and geometry hypotheses discharged.
Use: supplies the full angular-separation assertion in Proposition B.1 (c), including the center, and the later node-gap and interpolation estimates.
Article: jacobi, Proposition B.1.
Proof: the genuine uniform endpoint-distance theorem puts every original
zero away from both singular endpoints by d/N. The entire genuine nodal
interval inherits those distances. Bound its true restoring potential by
(L*N)^2 and apply the proved ordinary Sturm gap theorem. Original zero
simplicity, ordering and nodal exhaustion have already been established. -/
theorem angle_gap_bound {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧
      ∀ k : ℕ,∀ hk : k+1<n,
        c/frequency a b n≤angle a b ha hb (⟨k+1,hk⟩ : Fin n)-angle a b ha hb (⟨k,by omega⟩ : Fin n) := by
  -- Both actual endpoint singularities are controlled before invoking Sturm, so the middle interval needs no separate asymptotic argument.
  obtain ⟨d,_,hd,_,hends⟩ := angle_endpoint_bounds ha hb
  obtain ⟨L,hL,hpot⟩ := restoring_potential_bound a b hd
  refine ⟨Real.pi/L,by positivity,?_⟩
  filter_upwards [hends] with n hn
  let N := frequency a b n
  have hN : 0<N := hn.1
  have hext : ∀ i : Fin n,d≤N*angle a b ha hb i ∧ d≤N*(Real.pi-angle a b ha hb i) := by
    intro i
    have hcount : 1≤min (i.val+1) (n-i.val) := by omega
    have hcountR : (1:ℝ)≤(min (i.val+1) (n-i.val):ℕ) := by exact_mod_cast hcount
    have hl : d/N≤min (angle a b ha hb i) (Real.pi-angle a b ha hb i) := by
      calc
        _ ≤ d*(min (i.val+1) (n-i.val):ℕ)/N := div_le_div_of_nonneg_right (by nlinarith) hN.le
        _ ≤ _ := (hn.2 i).1
    constructor
    · nlinarith [(div_le_iff₀ hN).mp (hl.trans (min_le_left _ _))]
    · nlinarith [(div_le_iff₀ hN).mp (hl.trans (min_le_right _ _))]
  refine ⟨hN,?_⟩
  intro k hk
  let i : Fin n := ⟨k,by omega⟩
  let j : Fin n := ⟨k+1,hk⟩
  have hij : i<j := by exact Nat.lt_succ_self k
  have horder := angle_strictMono ha hb n hij
  have hi := (angle_properties ha hb i).1
  have hj := (angle_properties ha hb j).1
  have hI : Icc (angle a b ha hb i) (angle a b ha hb j)⊆Ioo 0 Real.pi :=
    fun t ht => ⟨hi.1.trans_le ht.1,ht.2.trans_lt hj.2⟩
  have hg := (restoringState a b ha hb n).zero_gap (mul_pos hL hN) horder hI
    (liouville_angle_zero ha hb i) (liouville_angle_zero ha hb j) (by
      intro t ht
      apply finiteAngleAt_no_zero_between ha hb hk
      simpa only [finiteAngleAt_eq ha hb (show k<n by omega),finiteAngleAt_eq ha hb hk] using ht) (by
      intro t ht
      have hphys := hI ⟨ht.1.le,ht.2.le⟩
      rw [restoringState_potential ha hb n hphys]
      exact hpot N hN t hphys
        (by nlinarith [(hext i).1,mul_le_mul_of_nonneg_left ht.1.le hN.le])
        (by nlinarith [(hext j).2,mul_le_mul_of_nonneg_left ht.2.le hN.le]))
  have hh : Real.pi/(L*N)<angle a b ha hb j-angle a b ha hb i :=
    (div_lt_iff₀ (mul_pos hL hN)).mpr (by nlinarith [hg])
  have he : (Real.pi/L)/N=Real.pi/(L*N) := by ring
  rw [he]
  exact hh.le

end
end jacobi.Jacobi
