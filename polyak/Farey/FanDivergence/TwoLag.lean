import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Exact positive two-weight feasibility, including a zero good value.
The latter is essential at the closed p=2 phase endpoint. -/
noncomputable section
namespace polyak.Farey

def TwoLagFeasible (A B C D : ℝ) : Prop :=
  ∃u v : ℝ,0≤u ∧ 0≤v ∧ 0<u+v ∧ 0≤v*A-u*C ∧ 0≤u*D-v*B

theorem twoLag_weights_pos {A B C D u v : ℝ}
    (hB : 0<B) (hC : 0<C) (hu : 0≤u) (hv : 0≤v) (hne : 0<u+v)
    (h1 : 0≤v*A-u*C) (h2 : 0≤u*D-v*B) : 0<u ∧ 0<v := by
  constructor
  · apply lt_of_le_of_ne hu
    intro he
    have hu0 : u=0 := he.symm
    simp only [hu0,zero_mul,zero_sub] at h2
    have hvp : 0<v := by linarith
    nlinarith [mul_pos hvp hB]
  · apply lt_of_le_of_ne hv
    intro he
    have hv0 : v=0 := he.symm
    rw [hv0,zero_mul,zero_sub] at h1
    have hup : 0<u := by linarith
    nlinarith [mul_pos hup hC]

theorem twoLag_ratio_iff {A B C D r : ℝ} (hC : 0<C) (hD : 0<D) :
    (0≤A-r*C ∧ 0≤r*D-B) ↔ B/D≤r ∧ r≤A/C := by
  rw [div_le_iff₀ hD,le_div_iff₀ hC]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem twoLag_feasible_iff {A B C D : ℝ} (hB : 0<B) (hC : 0<C) (hD : 0<D) :
    TwoLagFeasible A B C D ↔ B*C≤A*D := by
  constructor
  · rintro ⟨u,v,hu,hv,hne,h1,h2⟩
    have hvp := (twoLag_weights_pos hB hC hu hv hne h1 h2).2
    have hh := add_nonneg (mul_nonneg hD.le h1) (mul_nonneg hC.le h2)
    have he : D*(v*A-u*C)+C*(u*D-v*B)=v*(A*D-B*C) := by ring
    rw [he] at hh
    have hd := (mul_nonneg_iff_of_pos_left hvp).mp hh
    linarith
  · intro hdet
    refine ⟨B,D,hB.le,hD.le,by linarith,?_,?_⟩
    · nlinarith
    · ring_nf
      exact le_rfl

theorem twoLag_feasible_positive_iff {A B C D : ℝ} (hB : 0<B) (hC : 0<C) :
    TwoLagFeasible A B C D ↔
      ∃u v : ℝ,0<u ∧ 0<v ∧ 0≤v*A-u*C ∧ 0≤u*D-v*B := by
  constructor
  · rintro ⟨u,v,hu,hv,hne,h1,h2⟩
    have hp := twoLag_weights_pos hB hC hu hv hne h1 h2
    exact ⟨u,v,hp.1,hp.2,h1,h2⟩
  · rintro ⟨u,v,hu,hv,h1,h2⟩
    exact ⟨u,v,hu.le,hv.le,add_pos hu hv,h1,h2⟩

end polyak.Farey
