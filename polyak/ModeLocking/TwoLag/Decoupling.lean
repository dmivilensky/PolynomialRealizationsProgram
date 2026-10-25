import polyak.ModeLocking.TwoLag.DecouplingAtoms

/-! The independent supremum product criterion of Proposition decouple(a)
includes arbitrary measures and the empty positive-side domain. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open Levels Set

structure PlusMaximum (Θ : Curve) (K : ℕ) where
  value : ℝ
  nonneg : 0≤value
  bound : ∀ω∈plusSet Θ K,plusRatio Θ K ω≤value
  empty_zero : plusSet Θ K=∅→value=0
  attained : (plusSet Θ K).Nonempty→∃u∈plusSet Θ K,plusRatio Θ K u=value

theorem exists_plusMaximum {Θ : Curve} {K : ℕ} (hno : NoCommonNonnegative Θ K) :
    Nonempty (PlusMaximum Θ K) := by
  by_cases hne : (plusSet Θ K).Nonempty
  · obtain ⟨u,hu,hmax⟩ := plusRatio_attained hno hne
    exact ⟨{
      value:=plusRatio Θ K u
      nonneg:=(plusRatio_pos hu).le
      bound:=hmax
      empty_zero:=fun he=>False.elim (by rw [he] at hu;exact hu)
      attained:=fun _=>⟨u,hu,rfl⟩
    }⟩
  · have he : plusSet Θ K=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    exact ⟨{
      value:=0
      nonneg:=le_rfl
      bound:=fun ω hω=>False.elim (hne ⟨ω,hω⟩)
      empty_zero:=fun _=>rfl
      attained:=fun h=>False.elim (hne h)
    }⟩

/-- This is the two independent maxima criterion, without an assumption
that an arbitrary feasible measure is atomic. -/
theorem decoupling_feasible_iff {Θ : Curve} {K : ℕ} (hK : 2≤K)
    (hno : NoCommonNonnegative Θ K) (M : PlusMaximum Θ K)
    {v : Frequency} (hv : v∈minusSet Θ K) (hmin : 0<Θ.minimizer v)
    (hmax : ∀ω∈minusSet Θ K,minusRatio Θ K ω≤minusRatio Θ K v) :
    FPOn Θ (pairLags K) ↔ 1≤M.value*minusRatio Θ K v := by
  constructor
  · intro hfp
    by_contra hn
    have hp := lt_of_not_ge hn
    obtain ⟨r,hr,hstrict⟩ := strict_pair_of_product_lt_one hno M.nonneg (minusRatio_pos hv)
      M.bound hmax hp
    exact no_solution_of_pair_strict (by omega : 1≤K) hr.le hstrict hfp
  · intro hp
    have hne : (plusSet Θ K).Nonempty := by
      by_contra hn
      have hz := M.empty_zero (Set.not_nonempty_iff_eq_empty.mp hn)
      rw [hz,zero_mul] at hp
      norm_num at hp
    obtain ⟨u,hu,hMu⟩ := M.attained hne
    obtain ⟨r,hr,hsol,hslack⟩ := feasible_of_ratio_product hu hv hmin (by rwa [hMu])
    exact ⟨pairMeasure u v r,hsol⟩

end polyak.ModeLocking.TwoLag
