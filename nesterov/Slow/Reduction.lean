import nesterov.Slow.FiniteProgram
import nesterov.Flow.Kernel

/-! Article: Lemma D.3, the exact sampled program, independently of any expansion. -/
namespace nesterov.Slow
noncomputable section
open scoped BigOperators
variable {J : Type*} [Fintype J]

def sampleCharge (w γ S : J→ℝ) (c : ℝ) : ℝ := -(∑ j,w j*γ j*S j)/c

theorem sampled_lower (w γ G S : J→ℝ) (c ε : ℝ) (n : ℕ) :
    (∑ j,w j*(G j*(Real.cosh (n*(-c*ε))-Real.cos (n*(ε*γ j)))-S j*Real.sin (n*(ε*γ j))))+
      sampleCharge w γ S c*Real.sinh (n*(-c*ε))=
    ∑ j,w j*(G j*Flow.kernelA c (γ j) (n*ε)+S j*Flow.kernelB c (γ j) (n*ε)) := by
  have hc : (n:ℝ)*(-c*ε)= -(c*(n*ε)) := by ring
  have hω (j : J) : (n:ℝ)*(ε*γ j)=γ j*(n*ε) := by ring
  rw [hc]
  simp only [hω,Real.cosh_neg,Real.sinh_neg,sampleCharge,neg_div,mul_neg,neg_mul,neg_neg]
  rw [Finset.sum_div,Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [Flow.kernelA,Flow.kernelB]
  ring

theorem sampled_upper (w γ G S : J→ℝ) (c ε : ℝ) (n : ℕ) :
    (∑ j,w j*(G j*(Real.cosh (n*(-c*ε))-Real.cos (n*(ε*γ j)))+S j*Real.sin (n*(ε*γ j))))-
      sampleCharge w γ S c*Real.sinh (n*(-c*ε))=
    ∑ j,w j*(G j*Flow.kernelA c (γ j) (n*ε)-S j*Flow.kernelB c (γ j) (n*ε)) := by
  have hc : (n:ℝ)*(-c*ε)= -(c*(n*ε)) := by ring
  have hω (j : J) : (n:ℝ)*(ε*γ j)=γ j*(n*ε) := by ring
  rw [hc]
  simp only [hω,Real.cosh_neg,Real.sinh_neg,sampleCharge,neg_div,mul_neg,neg_mul,neg_neg]
  rw [Finset.sum_div,Finset.sum_mul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [Flow.kernelA,Flow.kernelB]
  ring

theorem sampled_program_iff {w γ G S : J→ℝ} {c ε : ℝ} (hc : 0<c) :
    FiniteProgram w (fun j=>ε*γ j) G S (-c*ε) (sampleCharge w γ S c) ↔
      |∑ j,w j*γ j*S j|≤c*(∑ j,w j*G j) ∧
      ∀ n : ℕ,1≤n →
        0≤∑ j,w j*(G j*Flow.kernelA c (γ j) (n*ε)+S j*Flow.kernelB c (γ j) (n*ε)) ∧
        0≤∑ j,w j*(G j*Flow.kernelA c (γ j) (n*ε)-S j*Flow.kernelB c (γ j) (n*ε)) := by
  unfold FiniteProgram
  simp_rw [sampled_lower,sampled_upper]
  simp only [sampleCharge,abs_div,abs_neg,abs_of_pos hc,div_le_iff₀ hc,mul_comm]

theorem sampled_scaled_program_iff {w γ G S : J→ℝ} {c ε a : ℝ} (hc : 0<c) (ha : 0<a) :
    FiniteProgram w (fun j=>ε*γ j) (fun j=>a*G j) (fun j=>a*S j) (-c*ε)
      (a*sampleCharge w γ S c) ↔
      |∑ j,w j*γ j*S j|≤c*(∑ j,w j*G j) ∧
      ∀ n : ℕ,1≤n →
        0≤∑ j,w j*(G j*Flow.kernelA c (γ j) (n*ε)+S j*Flow.kernelB c (γ j) (n*ε)) ∧
        0≤∑ j,w j*(G j*Flow.kernelA c (γ j) (n*ε)-S j*Flow.kernelB c (γ j) (n*ε)) := by
  rw [finiteProgram_scale ha]
  exact sampled_program_iff hc

end
end nesterov.Slow
