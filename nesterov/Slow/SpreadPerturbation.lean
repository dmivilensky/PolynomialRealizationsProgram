import nesterov.Flow.Spread
import nesterov.Slow.Reduction

/-!
Article: Lemma D.5, uniform perturbation of the flow spectrum at every lag.
The finite spectrum and its margin are fixed before the perturbation size.
-/
namespace nesterov.Slow
noncomputable section
open Flow
open scoped BigOperators
variable {J : Type*} [Fintype J]

theorem kernel_average_perturb (ν : Flow.Spectrum J) {c q η σ : ℝ}
    (hc : 0<c) (hq : 0≤q) (hσ : |σ|≤1)
    (G₀ S₀ G S : J→ℝ) (hG : ∀ j,|G j-G₀ j|≤η) (hS : ∀ j,|S j-S₀ j|≤η) :
    (∑ j,ν.weight j*(G₀ j*kernelA c (ν.frequency j) q+σ*S₀ j*kernelB c (ν.frequency j) q))-
      η*ν.average (fun γ=>kernelA c γ q+kernelB c γ q)≤
    ∑ j,ν.weight j*(G j*kernelA c (ν.frequency j) q+σ*S j*kernelB c (ν.frequency j) q) := by
  have hp (j : J) : G₀ j*kernelA c (ν.frequency j) q+σ*S₀ j*kernelB c (ν.frequency j) q-
      η*(kernelA c (ν.frequency j) q+kernelB c (ν.frequency j) q)≤
      G j*kernelA c (ν.frequency j) q+σ*S j*kernelB c (ν.frequency j) q := by
    have hA := kernelA_nonneg c (ν.frequency j) q
    have hB := kernelB_nonneg hc (ν.frequency_nonneg j) hq
    have hga := mul_le_mul_of_nonneg_right (abs_le.mp (hG j)).1 hA
    have hsa : |σ*(S j-S₀ j)|≤η := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul hσ (hS j) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have hsb := mul_le_mul_of_nonneg_right (abs_le.mp hsa).1 hB
    nlinarith only [hga,hsb]
  have hh := Finset.sum_le_sum (fun j (_ : j∈Finset.univ)=>
    mul_le_mul_of_nonneg_left (hp j) (ν.weight_nonneg j))
  convert hh using 1
  unfold Flow.Spectrum.average
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem spread_perturb_lags {θ y c : ℝ} (W : SpreadWitness θ y c)
    (hc : 0<c) {η : ℝ} (hηW : η≤W.margin)
    (G S : Fin W.J→ℝ)
    (hG : ∀ j,|G j-(W.spectrum.frequency j^2-delta θ y c)|≤η)
    (hS : ∀ j,|S j-(θ-2*c)*W.spectrum.frequency j|≤η) :
    ∀ q : ℝ,0<q →
      0≤∑ j,W.spectrum.weight j*(G j*kernelA c (W.spectrum.frequency j) q+
        S j*kernelB c (W.spectrum.frequency j) q) ∧
      0≤∑ j,W.spectrum.weight j*(G j*kernelA c (W.spectrum.frequency j) q-
        S j*kernelB c (W.spectrum.frequency j) q) := by
  intro q hq
  have hab : 0≤W.spectrum.average (fun γ=>kernelA c γ q+kernelB c γ q) :=
    W.spectrum.le_average (fun j=>add_nonneg (kernelA_nonneg _ _ _) (kernelB_nonneg hc (W.spectrum.frequency_nonneg j) hq.le))
  have hplus := kernel_average_perturb W.spectrum hc hq.le (σ:=1) (by norm_num) _ _ G S hG hS
  have hminus := kernel_average_perturb W.spectrum hc hq.le (σ:= -1) (by norm_num) _ _ G S hG hS
  have hp := W.backward q hq
  have hm := W.forward q hq
  have hscale := mul_le_mul_of_nonneg_right hηW hab
  unfold Flow.Spectrum.average backwardKernel at hp
  unfold Flow.Spectrum.average forwardKernel at hm
  simp only [one_mul] at hplus
  norm_num only [neg_mul,one_mul,←sub_eq_add_neg] at hminus
  unfold Flow.Spectrum.average at hplus hminus hscale
  dsimp only at hp hm
  constructor <;> linarith


theorem minimizer_perturb (ν : Flow.Spectrum J) {θ y c η B : ℝ}
    (hc : 0<c) (hb : 0≤θ-2*c) (hη : 0≤η) (hB : ∀ j,ν.frequency j≤B)
    (G S : J→ℝ)
    (hG : ∀ j,|G j-(ν.frequency j^2-delta θ y c)|≤η)
    (hS : ∀ j,|S j-(θ-2*c)*ν.frequency j|≤η) :
    (3*c-θ)*ν.average (fun γ=>γ^2)-c*delta θ y c-(c+B)*η≤
      c*(∑ j,ν.weight j*G j)-|∑ j,ν.weight j*ν.frequency j*S j| := by
  have hgs := Finset.sum_le_sum (fun j (_ : j∈Finset.univ)=>
    mul_le_mul_of_nonneg_left (abs_le.mp (hG j)).1 (ν.weight_nonneg j))
  have hgval : (∑ j,ν.weight j*(-η))= -η := by
    rw [←Finset.sum_mul,ν.weight_sum,one_mul]
  have hGsum : ν.average (fun γ=>γ^2)-delta θ y c-η≤∑ j,ν.weight j*G j := by
    simp only [mul_sub,Finset.sum_sub_distrib] at hgs
    rw [hgval,←Finset.sum_mul,ν.weight_sum,one_mul] at hgs
    unfold Flow.Spectrum.average
    linarith
  have hSabs (j : J) : |S j|≤(θ-2*c)*ν.frequency j+η := by
    have hh := abs_le.mp (hS j)
    have hp := mul_nonneg hb (ν.frequency_nonneg j)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hsabs : |∑ j,ν.weight j*ν.frequency j*S j|≤
      (θ-2*c)*ν.average (fun γ=>γ^2)+η*ν.average (fun γ=>γ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have hh := Finset.sum_le_sum (fun j (_ : j∈Finset.univ)=>
      mul_le_mul_of_nonneg_left (hSabs j) (mul_nonneg (ν.weight_nonneg j) (ν.frequency_nonneg j)))
    simp only [abs_mul,abs_of_nonneg (ν.weight_nonneg _),abs_of_nonneg (ν.frequency_nonneg _)]
    convert hh using 1
    unfold Flow.Spectrum.average
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hfreq : ν.average (fun γ=>γ)≤B := ν.average_le hB
  have hSsum : |∑ j,ν.weight j*ν.frequency j*S j|≤(θ-2*c)*ν.average (fun γ=>γ^2)+η*B := by
    linarith [mul_le_mul_of_nonneg_left hfreq hη]
  have hGmult := mul_le_mul_of_nonneg_left hGsum hc.le
  nlinarith only [hGmult,hSsum]


theorem spread_robust {θ y c : ℝ} (W : SpreadWitness θ y c)
    (hc : 0<c) (hb : 0≤θ-2*c) :
    ∃ η : ℝ,0<η ∧ ∀ G S : Fin W.J→ℝ,
      (∀ j,|G j-(W.spectrum.frequency j^2-delta θ y c)|≤η) →
      (∀ j,|S j-(θ-2*c)*W.spectrum.frequency j|≤η) →
      (∀ q : ℝ,0<q →
        0≤∑ j,W.spectrum.weight j*(G j*kernelA c (W.spectrum.frequency j) q+S j*kernelB c (W.spectrum.frequency j) q) ∧
        0≤∑ j,W.spectrum.weight j*(G j*kernelA c (W.spectrum.frequency j) q-S j*kernelB c (W.spectrum.frequency j) q)) ∧
      |∑ j,W.spectrum.weight j*W.spectrum.frequency j*S j|<c*(∑ j,W.spectrum.weight j*G j) := by
  let B := ∑ j,W.spectrum.frequency j
  have hB : ∀ j,W.spectrum.frequency j≤B := fun j=>
    Finset.single_le_sum (fun i _=>W.spectrum.frequency_nonneg i) (Finset.mem_univ j)
  have hB0 : 0≤B := Finset.sum_nonneg (fun j _=>W.spectrum.frequency_nonneg j)
  have hden : 0<2*(c+B) := by linarith
  let η := min (W.margin/2) (1/(2*(c+B)))
  have hη : 0<η := lt_min (div_pos W.margin_pos (by norm_num)) (one_div_pos.mpr hden)
  have hηW : η≤W.margin := (min_le_left _ _).trans (by linarith [W.margin_pos])
  have hηB : (c+B)*η≤1/2 := by
    have hh := (le_div_iff₀ hden).mp (min_le_right (W.margin/2) (1/(2*(c+B))))
    change η*(2*(c+B))≤1 at hh
    nlinarith
  refine ⟨η,hη,fun G S hG hS=>⟨spread_perturb_lags W hc hηW G S hG hS,?_⟩⟩
  have hh := minimizer_perturb W.spectrum hc hb hη.le hB G S hG hS
  have hm := W.minimizer
  linarith

end
end nesterov.Slow
