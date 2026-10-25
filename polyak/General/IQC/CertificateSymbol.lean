import polyak.General.IQC.Certificate
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! Article: lem:iqc(b). The explicit 2×2 Hermitian trigonometric symbol
of the same two-channel finite quadratic form. -/
noncomputable section
namespace polyak.General.IQC
open polyak Energy Duality Spectral

def hermitianBlock (d : ℝ) (w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(d:ℂ),star w;w,-(d:ℂ)]
def matrixQuadratic (P : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) : ℝ :=
  (∑ i,∑ j,star (v i)*P i j*v j).re

theorem hermitianBlock_isHermitian (d : ℝ) (w : ℂ) :
    (hermitianBlock d w).IsHermitian := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hermitianBlock,Matrix.conjTranspose_apply]

theorem hermitianBlock_quadratic (d : ℝ) (w u v : ℂ) :
    matrixQuadratic (hermitianBlock d w) ![u,v]=
      d*(Complex.normSq u-Complex.normSq v)+2*(star v*w*u).re := by
  simp [matrixQuadratic,hermitianBlock,Fin.sum_univ_two,Complex.normSq_apply]
  ring

def pairSymbol (δ : ℝ) (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  hermitianBlock (Complex.normSq (u-1)/4) ((-(δ/4):ℝ)*star (1+u)*(u-1))
def starSymbol (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := hermitianBlock (1/4) (-(δ/4):ℝ)

theorem pairSymbol_trig (δ t ω : ℝ) (n : ℕ) :
    pairSymbol δ (Waves.z t ω^n)=hermitianBlock
      ((Real.exp (2*n*t)+1-2*Real.exp (n*t)*Real.cos (n*ω))/4)
      ((-(δ/4):ℝ)*(((Real.exp (2*n*t)-1:ℝ):ℂ)+
        2*Complex.I*((Real.exp (n*t)*Real.sin (n*ω):ℝ):ℂ))) := by
  have hnorm (u : ℂ) : Complex.normSq (u-1)=Complex.normSq u+1-2*u.re := by
    simp [Complex.normSq_apply]
    ring
  have hcross (u : ℂ) : star (1+u)*(u-1)=((Complex.normSq u-1:ℝ):ℂ)+2*Complex.I*(u.im:ℂ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  rw [pairSymbol,hnorm,mul_assoc,hcross,Waves.normSq_z_pow,Waves.z_pow_re,Waves.z_pow_im]
  congr 1; ring

theorem pairSymbol_quadratic (δ : ℝ) (u x σ : ℂ) :
    matrixQuadratic (pairSymbol δ u) ![x,σ]=pairQuadratic δ x (u*x) σ (u*σ) := by
  rw [pairSymbol,hermitianBlock_quadratic]
  simp only [pairQuadratic,← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring
theorem starSymbol_quadratic (δ : ℝ) (x σ : ℂ) :
    matrixQuadratic (starSymbol δ) ![x,σ]=starQuadratic δ x σ := by
  rw [starSymbol,hermitianBlock_quadratic]
  simp only [starQuadratic,← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

variable {m : C(Frequency,ℂ)} {t : ℝ}
def certificateSymbol (cert : StrictCertificate m t) (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (∑ n ∈ cert.lags,((2*Real.exp (-(n*t)):ℝ):ℂ) •
    ((cert.α n:ℂ) • pairSymbol 1 (Waves.z t ω^n)+
      (cert.β n:ℂ) • pairSymbol (-1) (Waves.z t ω^n)))+
    ((4*cert.γplus:ℝ):ℂ) • starSymbol 1+
    ((4*cert.γminus:ℝ):ℂ) • starSymbol (-1)

theorem matrixQuadratic_add (P Q : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    matrixQuadratic (P+Q) v=matrixQuadratic P v+matrixQuadratic Q v := by
  simp [matrixQuadratic,Fin.sum_univ_two,mul_add,add_mul]
  ring
theorem matrixQuadratic_real_smul (c : ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    matrixQuadratic ((c:ℂ) • P) v=c*matrixQuadratic P v := by
  simp [matrixQuadratic,Fin.sum_univ_two,Complex.mul_re,Complex.mul_im]
  ring
theorem matrixQuadratic_sum {I : Type*} (s : Finset I)
    (P : I → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    matrixQuadratic (∑ i ∈ s,P i) v=∑ i ∈ s,matrixQuadratic (P i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [matrixQuadratic]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,matrixQuadratic_add,ih]

theorem hermitian_real_smul (c : ℝ) {P : Matrix (Fin 2) (Fin 2) ℂ}
    (hP : P.IsHermitian) : ((c:ℂ) • P).IsHermitian :=
  hP.smul (by simp [isSelfAdjoint_iff])

theorem certificateSymbol_isHermitian (cert : StrictCertificate m t) (ω : ℝ) :
    (certificateSymbol cert ω).IsHermitian := by
  classical
  have hterm (n : ℕ) : (((2*Real.exp (-(n*t)):ℝ):ℂ) •
      ((cert.α n:ℂ) • pairSymbol 1 (Waves.z t ω^n)+
       (cert.β n:ℂ) • pairSymbol (-1) (Waves.z t ω^n))).IsHermitian := by
    apply hermitian_real_smul
    apply Matrix.IsHermitian.add
    · exact hermitian_real_smul _ (hermitianBlock_isHermitian _ _)
    · exact hermitian_real_smul _ (hermitianBlock_isHermitian _ _)
  have hsum (s : Finset ℕ) : (∑ n ∈ s,((2*Real.exp (-(n*t)):ℝ):ℂ) •
      ((cert.α n:ℂ) • pairSymbol 1 (Waves.z t ω^n)+
       (cert.β n:ℂ) • pairSymbol (-1) (Waves.z t ω^n))).IsHermitian := by
    induction s using Finset.induction_on with
    | empty => simp [Matrix.IsHermitian]
    | @insert n s hn ih => rw [Finset.sum_insert hn]; exact (hterm n).add ih
  exact ((hsum cert.lags).add (hermitian_real_smul _ (hermitianBlock_isHermitian _ _))).add
    (hermitian_real_smul _ (hermitianBlock_isHermitian _ _))

theorem certificateSymbol_continuous (cert : StrictCertificate m t) :
    Continuous (certificateSymbol cert) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [certificateSymbol,pairSymbol,starSymbol,hermitianBlock]
  all_goals unfold Waves.z; fun_prop

theorem certificateSymbol_unit_wave (cert : StrictCertificate m t) (ω : ℝ) (M : ℂ) :
    matrixQuadratic (certificateSymbol cert ω) ![1,M]=
      certificateQuadratic cert (fun n => Waves.z 0 ω^n) (fun n => M*Waves.z 0 ω^n) 0 := by
  unfold certificateSymbol
  simp only [matrixQuadratic_add,matrixQuadratic_sum,matrixQuadratic_real_smul,
    pairSymbol_quadratic,starSymbol_quadratic]
  unfold certificateQuadratic
  simp only [Nat.zero_add,pow_zero,mul_one,Complex.real_smul]
  congr 2
  apply Finset.sum_congr rfl
  intro n _
  have he := exp_mul_unit_wave t ω n
  have he' : (Real.exp (n*t):ℂ)*(M*Waves.z 0 ω^n)=Waves.z t ω^n*M := by rw [← mul_assoc,mul_comm _ M,mul_assoc,he,mul_comm]
  rw [he,he']

theorem certificateSymbol_source (cert : StrictCertificate m t) (c : Frequency) :
    matrixQuadratic (certificateSymbol cert (Real.arccos c)) ![1,m c]=
      symbol m t cert.lags cert.α cert.β cert.γplus cert.γminus c := by
  rw [certificateSymbol_unit_wave,certificateQuadratic_unit_wave]

end polyak.General.IQC
