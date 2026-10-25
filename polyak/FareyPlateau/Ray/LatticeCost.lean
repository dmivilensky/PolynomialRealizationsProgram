import polyak.FareyPlateau.Ray.ContactMoments
import polyak.FareyPlateau.Edge.LatticeCurvature

/-! Sharp discrete curvature minimization on both tight residue classes. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open scoped BigOperators Classical

def latticeCost (k : ℕ) (b n₁ n : ℤ) (t : ℝ) : ℝ :=
  if n%k=b%k then ((n:ℝ)-n₁)*((n:ℝ)-n₁-k)
  else (n:ℝ)*((n:ℝ)+(k:ℝ)*(1-2*t))

theorem class_lattice_decomposition {k : ℕ} {b n₁ n : ℤ}
    (h₁ : n₁%k=b%k) (hn : n%k=b%k) :
    ∃m : ℤ,n=n₁+m*k := by
  have h := Int.emod_add_ediv_mul n (k:ℤ)
  have h' := Int.emod_add_ediv_mul n₁ (k:ℤ)
  rw [hn] at h
  rw [h₁] at h'
  exact ⟨n/k-n₁/k,by nlinarith only [h,h']⟩

theorem latticeCost_nonneg {k : ℕ} {b n₁ n : ℤ} {t : ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1) (h₁ : n₁%k=b%k)
    (hn0 : n≠0) (hclass : n%k=b%k ∨ n%k=0) : 0≤latticeCost k b n₁ n t := by
  unfold latticeCost
  by_cases hn : n%k=b%k
  · rw [ite_eq_left hn]
    obtain ⟨m,hm⟩ := class_lattice_decomposition h₁ hn
    have he : (n:ℝ)=(n₁:ℝ)+(m:ℝ)*(k:ℝ) := by exact_mod_cast hm
    rw [he]
    simpa only [sub_add_eq_sub_sub] using Edge.adjacent_lattice_product (n₁:=(n₁:ℝ)) (k:=(k:ℝ)) m
  · rw [ite_eq_right hn]
    have hz := hclass.resolve_left hn
    have hem := Int.emod_add_ediv_mul n (k:ℤ)
    rw [hz,zero_add] at hem
    have hm : n/k≠0 := by intro hh;rw [hh,zero_mul] at hem;exact hn0 hem.symm
    have he : (n:ℝ)=(n/k:ℤ)*(k:ℝ) := by exact_mod_cast hem.symm
    rw [he]
    exact (Edge.zero_class_product (by exact_mod_cast hk) ht0 ht1 _ hm).le

theorem latticeCost_eq_zero_iff {k : ℕ} {b n₁ n : ℤ} {t : ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1) (h₁ : n₁%k=b%k)
    (hn0 : n≠0) (hclass : n%k=b%k ∨ n%k=0) :
    latticeCost k b n₁ n t=0 ↔ n=n₁ ∨ n=n₁+k := by
  constructor
  · intro hzero
    unfold latticeCost at hzero
    by_cases hn : n%k=b%k
    · rw [ite_eq_left hn,mul_eq_zero] at hzero
      rcases hzero with hl|hr
      · left;exact_mod_cast (sub_eq_zero.mp hl)
      · right
        have he : (n:ℝ)=(n₁:ℝ)+(k:ℝ) := by linarith
        exact_mod_cast he
    · rw [ite_eq_right hn] at hzero
      have hz := hclass.resolve_left hn
      have hem := Int.emod_add_ediv_mul n (k:ℤ)
      rw [hz,zero_add] at hem
      have hm : n/k≠0 := by intro hh;rw [hh,zero_mul] at hem;exact hn0 hem.symm
      have he : (n:ℝ)=(n/k:ℤ)*(k:ℝ) := by exact_mod_cast hem.symm
      rw [he] at hzero
      have hp := Edge.zero_class_product (by exact_mod_cast hk : (0:ℝ)<k) ht0 ht1 _ hm
      rw [hzero] at hp
      exact False.elim (lt_irrefl _ hp)
  · rintro (rfl|rfl)
    · simp [latticeCost,h₁]
    · have hn : (n₁+(k:ℤ))%k=b%k := by rw [Int.add_emod_right,h₁]
      simp only [latticeCost,ite_eq_left hn,Int.cast_add,Int.cast_natCast]
      ring

end polyak.FareyPlateau.Ray
