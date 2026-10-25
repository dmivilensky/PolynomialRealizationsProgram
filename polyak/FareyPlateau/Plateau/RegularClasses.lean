import polyak.FareyPlateau.Plateau.SingletonPeriod
import polyak.FareyPlateau.Edge.Classes

/-! Every singleton regular certificate has the two original tight Farey
classes and at least two genuine position-one lags, also at resonant slopes. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels ModeLocking Set
open scoped BigOperators

namespace RegularSingleton
variable {q : Tuning} {s : ℝ} {L j k : ℕ} (D : RegularData q s L)
  (hk : 3≤k) (hj : 1≤j) (hjk : 2*j<k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
  (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
  (hS : Set.range D.atoms={Edge.atom j k (lt_of_lt_of_le (by decide : 0<3) hk) hjk.le})

include hS in
theorem atoms_eq (i : Fin D.d) : D.atoms i=Edge.atom j k (lt_of_lt_of_le (by decide : 0<3) hk) hjk.le := by
  have hh : D.atoms i∈Set.range D.atoms := ⟨i,rfl⟩
  simpa only [hS,mem_singleton_iff] using hh

include hS in
theorem tight_at_atom (n : ℤ)
    (ht : ∑ i,(D.primal i:ℝ)*(Geometry.shiftedCurve q s).lag n (D.atoms i)=0) :
    (Geometry.shiftedCurve q s).lag n (Edge.atom j k (lt_of_lt_of_le (by decide : 0<3) hk) hjk.le)=0 := by
  have hs : ∑ i,(D.primal i:ℝ)=1 := by exact_mod_cast D.primal_sum
  simpa only [atoms_eq D hk hjk hS,←Finset.sum_mul,hs,one_mul] using ht

include hk hj hjk hb0 hbk hb hS

theorem lag_classes (n : ℤ) (hn : n∈D.lags) : n%(k:ℤ)=0 ∨ n%(k:ℤ)=b := by
  apply Edge.tight_classes_of_phase hk hjk.le (Geometry.shiftedCurve q s)
    (Edge.singleton_phase_eq D hk hj hjk b (by
      simpa only [Int.ModEq,Int.emod_eq_of_lt (by norm_num : (0:ℤ)≤1) (by omega : (1:ℤ)<k)] using hb) hS)
    b hb0 hbk hb n
  exact tight_at_atom D hk hjk hS n (D.lag_tight n hn)

theorem reps_eq (i : Fin D.d) : D.reps i=b := by
  have hper : L=k := singleton_regular_period D (lt_of_lt_of_le (by decide : 0<3) hk) hj hjk.le b hb hS
  have hr : 0<D.reps i ∧ D.reps i<k := ⟨D.reps_pos i,by simpa only [hper] using D.reps_lt i⟩
  have hclasses := Edge.tight_classes_of_phase hk hjk.le (Geometry.shiftedCurve q s)
    (Edge.singleton_phase_eq D hk hj hjk b (by
      simpa only [Int.ModEq,Int.emod_eq_of_lt (by norm_num : (0:ℤ)≤1) (by omega : (1:ℤ)<k)] using hb) hS)
    b hb0 hbk hb (D.reps i) (tight_at_atom D hk hjk hS _ (D.tight i))
  rw [Int.emod_eq_of_lt hr.1.le hr.2] at hclasses
  exact hclasses.resolve_left hr.1.ne'

theorem position_one_pair : ∃n₁∈D.lags,∃n₂∈D.lags,n₁≠n₂ ∧
    n₁%(k:ℤ)=b ∧ n₂%(k:ℤ)=b := by
  have hper : L=k := singleton_regular_period D (lt_of_lt_of_le (by decide : 0<3) hk) hj hjk.le b hb hS
  obtain ⟨n₁,h₁,n₂,h₂,hne,hr₁,hr₂⟩ := D.class_pair ⟨0,D.d_pos⟩
  rw [reps_eq D hk hj hjk b hb0 hbk hb hS,hper] at hr₁ hr₂
  exact ⟨n₁,h₁,n₂,h₂,hne,hr₁,hr₂⟩

end RegularSingleton
end polyak.FareyPlateau
