import polyak.CertifiedExamples.Exact313.Tuning
import polyak.ModeLocking.TwoLag.TangencyEquivalence
import polyak.ModeLocking.TwoLag.Signs
import polyak.Levels.Geometry.Windows

/-! Exact fixed-frequency Hermite contacts at the certified tuning. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels ModeLocking.TwoLag

def atom (j : ℕ) (hj : 2*j≤13) : Frequency :=
  ⟨2*Real.pi*j/13,by
    constructor
    · positivity
    · have h : 2*(j:ℝ)≤13 := by exact_mod_cast hj
      have hm := mul_le_mul_of_nonneg_left h Real.pi_pos.le
      nlinarith⟩
def atoms : Fin 2→Frequency := ![atom 3 (by norm_num),atom 2 (by norm_num)]

theorem atoms_coe (i : Fin 2) : (atoms i:ℝ)=(if i=0 then u else v) := by
  fin_cases i <;> dsimp [atoms,atom,u,v] <;> ring

theorem atoms_interior (i : Fin 2) : 0<(atoms i:ℝ) ∧ (atoms i:ℝ)<Real.pi := by
  rw [atoms_coe]
  fin_cases i <;> norm_num [u,v] <;> constructor <;> linarith [Real.pi_pos]

theorem atoms_cos (i : Fin 2) : Real.cos (atoms i:ℝ)=(if i=0 then c₁ else c₂) := by
  rw [atoms_coe]
  fin_cases i <;> rfl

theorem contact_values (i : Fin 2) :
    qStar.Xi (Real.cos (atoms i:ℝ))=Psi 4 scalarRoot.value (Real.cos (atoms i:ℝ)) := by
  rw [qStar_Xi,atoms_cos]
  fin_cases i
  · exact (hermiteQuadratic_first 4 scalarRoot.value c₁ c₂).1
  · exact hermiteQuadratic_second_value 4 scalarRoot.value c₁_lt_c₂.ne

theorem contact_slopes_first :
    deriv (coefficients scalarRoot.value).eval c₁=deriv (Psi 4 scalarRoot.value) c₁ :=
  (hermiteQuadratic_first 4 scalarRoot.value c₁ c₂).2

theorem contact_slopes_second :
    deriv (coefficients scalarRoot.value).eval c₂=deriv (Psi 4 scalarRoot.value) c₂ :=
  hermiteQuadratic_second_slope 4 scalarRoot.value c₁_lt_c₂.ne scalarRoot_G

theorem atoms_grid (i : Fin 2) : atoms i∈periodicGrid 13 := by
  fin_cases i
  · refine ⟨(atoms_interior 0).1,3,?_⟩
    dsimp [atoms,atom]
    push_cast
    ring
  · refine ⟨(atoms_interior 1).1,2,?_⟩
    dsimp [atoms,atom]
    push_cast
    ring

theorem first_in_window : Geometry.InWindow 4 (atoms 0) := by
  constructor <;> dsimp [atoms,atom] <;> norm_num <;> linarith [Real.pi_pos]

theorem second_below_window : (atoms 1:ℝ)<2*Real.pi/((4:ℝ)+1) := by
  dsimp [atoms,atom]
  norm_num
  linarith [Real.pi_pos]

theorem lag_signs_first :
    0<(tuningCurve qStar).lag 1 (atoms 0) ∧ (tuningCurve qStar).lag (-4) (atoms 0)<0 := by
  have h := (contact_lag_signs qStar (K:=4) (by norm_num) (a:=1)
    (b:=scalarRoot.value) (by norm_num) scalarRoot_positive (atoms 0) (atoms_interior 0)
    (by simpa using contact_values 0)).1
  apply h.mpr
  exact signProduct_window (by norm_num : 2≤4) first_in_window.1 first_in_window.2

theorem lag_signs_second :
    0<(tuningCurve qStar).lag (-4) (atoms 1) ∧ (tuningCurve qStar).lag 1 (atoms 1)<0 := by
  have h := (contact_lag_signs qStar (K:=4) (by norm_num) (a:=1)
    (b:=scalarRoot.value) (by norm_num) scalarRoot_positive (atoms 1) (atoms_interior 1)
    (by simpa using contact_values 1)).2
  apply h.mpr
  exact signProduct_below (by norm_num : 1≤4) (atoms_interior 1).1 second_below_window

end polyak.CertifiedExamples.Exact313
