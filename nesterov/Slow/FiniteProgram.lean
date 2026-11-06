import nesterov.Slow.Splitting

/-! Finite spectral inequalities, including homogeneous reweighting. -/
namespace nesterov.Slow
noncomputable section
open Spectral
open scoped BigOperators NNReal
variable {J : Type*} [Fintype J]

/-- The source finite inequalities with twice the skew as second coordinate. -/
def FiniteProgram (w ω G S : J→ℝ) (t C : ℝ) : Prop :=
  |C|≤∑ j,w j*G j ∧ ∀ n : ℕ,1≤n →
    0≤(∑ j,w j*(G j*(Real.cosh (n*t)-Real.cos (n*ω j))-S j*Real.sin (n*ω j)))+C*Real.sinh (n*t) ∧
    0≤(∑ j,w j*(G j*(Real.cosh (n*t)-Real.cos (n*ω j))+S j*Real.sin (n*ω j)))-C*Real.sinh (n*t)

theorem feasible_iff_finiteProgram (w : J→ℝ≥0) (c : J→Frequency)
    (hw : ∑ j,w j=1) (a : SymbolPair) (t C : ℝ) :
    Feasible a t (finiteSpectrum w c hw) C ↔
      FiniteProgram (fun j=>(w j:ℝ)) (fun j=>Real.arccos (c j))
        (fun j=>g a (c j)) (fun j=>2*skew a (c j)) t C := by
  unfold Feasible FiniteProgram
  rw [meanG_finite]
  simp_rw [meanA_finite,meanB_finite]
  simp only [lagA,lagB,Finset.sum_sub_distrib,Finset.sum_add_distrib,mul_sub,mul_add]

/-- Multiplying all data and the common value charge by one positive number
preserves every minimizer and lag inequality. -/
theorem finiteProgram_scale {w ω G S : J→ℝ} {t C a : ℝ} (ha : 0<a) :
    FiniteProgram w ω (fun j=>a*G j) (fun j=>a*S j) t (a*C) ↔ FiniteProgram w ω G S t C := by
  have hg : (∑ j,w j*(a*G j))=a*∑ j,w j*G j := by
    rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro j _;ring
  have hl (n : ℕ) :
      (∑ j,w j*((a*G j)*(Real.cosh (n*t)-Real.cos (n*ω j))-(a*S j)*Real.sin (n*ω j)))+
        (a*C)*Real.sinh (n*t)=a*((∑ j,w j*(G j*(Real.cosh (n*t)-Real.cos (n*ω j))-S j*Real.sin (n*ω j)))+C*Real.sinh (n*t)) := by
    rw [mul_add,Finset.mul_sum,mul_assoc]
    congr 1
    apply Finset.sum_congr rfl;intro j _;ring
  have hu (n : ℕ) :
      (∑ j,w j*((a*G j)*(Real.cosh (n*t)-Real.cos (n*ω j))+(a*S j)*Real.sin (n*ω j)))-
        (a*C)*Real.sinh (n*t)=a*((∑ j,w j*(G j*(Real.cosh (n*t)-Real.cos (n*ω j))+S j*Real.sin (n*ω j)))-C*Real.sinh (n*t)) := by
    rw [mul_sub,Finset.mul_sum,mul_assoc]
    congr 1
    apply Finset.sum_congr rfl;intro j _;ring
  simp only [FiniteProgram,abs_mul,abs_of_pos ha,hg,hl,hu,mul_le_mul_iff_right₀ ha,
    mul_nonneg_iff_of_pos_left ha]

/-- Positive per-atom weight changes cancel the inverse changes in both
amplitudes.  The mass normalization rescales the single common charge. -/
theorem finiteProgram_reweight {w ω G S d : J→ℝ} {t C A : ℝ}
    (hd : ∀ j,d j≠0) (hA : 0<A) :
    FiniteProgram (fun j=>w j*d j/A) ω (fun j=>G j/d j) (fun j=>S j/d j) t (C/A) ↔
      FiniteProgram w ω G S t C := by
  have hG : (∑ j,(w j*d j/A)*(G j/d j))=(∑ j,w j*G j)/A := by
    rw [Finset.sum_div];apply Finset.sum_congr rfl;intro j _;field_simp [hd j]
  have hl (n : ℕ) :
      (∑ j,(w j*d j/A)*((G j/d j)*(Real.cosh (n*t)-Real.cos (n*ω j))-(S j/d j)*Real.sin (n*ω j)))=
      (∑ j,w j*(G j*(Real.cosh (n*t)-Real.cos (n*ω j))-S j*Real.sin (n*ω j)))/A := by
    rw [Finset.sum_div];apply Finset.sum_congr rfl;intro j _;field_simp [hd j]
  have hu (n : ℕ) :
      (∑ j,(w j*d j/A)*((G j/d j)*(Real.cosh (n*t)-Real.cos (n*ω j))+(S j/d j)*Real.sin (n*ω j)))=
      (∑ j,w j*(G j*(Real.cosh (n*t)-Real.cos (n*ω j))+S j*Real.sin (n*ω j)))/A := by
    rw [Finset.sum_div];apply Finset.sum_congr rfl;intro j _;field_simp [hd j]
  unfold FiniteProgram
  rw [hG]
  simp_rw [hl,hu]
  simp only [abs_div,abs_of_pos hA,div_mul_eq_mul_div,←add_div,←sub_div,
    div_le_div_iff_of_pos_right hA,le_div_iff₀ hA,zero_mul]

end
end nesterov.Slow
