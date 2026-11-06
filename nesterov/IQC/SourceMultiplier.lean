import nesterov.IQC.Certificate

/-! The literal A,iB form of the certificate's source Fourier multiplier. -/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators
open polyak.General.IQC
variable {a : Spectral.SymbolPair} {t : ℝ}

def sourceA (cert : Duality.StrictCertificate a t) (ω : ℝ) : ℝ:=
  (∑ n∈cert.lags,(cert.α n+cert.β n)*(Real.cosh (n*t)-Real.cos (n*ω)))+cert.γplus+cert.γminus
def sourceB (cert : Duality.StrictCertificate a t) (ω : ℝ) : ℝ:=
  ∑ n∈cert.lags,(cert.α n-cert.β n)*Real.sin (n*ω)

private theorem weighted_pair_trig (α β t ω : ℝ) (n : ℕ) :
    ((2*Real.exp (-(n*t)):ℝ):ℂ) •
      ((α:ℂ) • pairSymbol 1 (polyak.Waves.z t ω^n)+(β:ℂ) • pairSymbol (-1) (polyak.Waves.z t ω^n))=
      hermitianBlock ((α+β)*(Real.cosh (n*t)-Real.cos (n*ω)))
        (((-(α-β)*Real.sinh (n*t):ℝ):ℂ)-Complex.I*((α-β)*Real.sin (n*ω):ℝ)) := by
  have he : Real.exp (-(n*t))*Real.exp (n*t)=1:=by rw [←Real.exp_add];simp
  have he2 : Real.exp (-(n*t))*Real.exp (2*n*t)=Real.exp (n*t):=by
    rw [←Real.exp_add]
    congr 1
    ring
  have hA : 2*Real.exp (-(n*t))*((Real.exp (2*n*t)+1-2*Real.exp (n*t)*Real.cos (n*ω))/4)=
      Real.cosh (n*t)-Real.cos (n*ω) := by
    rw [Real.cosh_eq]
    linear_combination (1/2:ℝ)*he2-Real.cos (n*ω)*he
  have hS : 2*Real.exp (-(n*t))*((Real.exp (2*n*t)-1)/4)=Real.sinh (n*t) := by
    rw [Real.sinh_eq]
    linear_combination (1/2:ℝ)*he2
  have hI : 2*Real.exp (-(n*t))*(2*Real.exp (n*t)*Real.sin (n*ω)/4)=Real.sin (n*ω) := by
    linear_combination Real.sin (n*ω)*he
  rw [pairSymbol_trig,pairSymbol_trig]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [hermitianBlock,Matrix.smul_apply,Complex.mul_re,Complex.mul_im,
      -Complex.ofReal_exp,-Complex.ofReal_cos,-Complex.ofReal_sin,
      -Complex.ofReal_cosh,-Complex.ofReal_sinh]
  all_goals first
    | linear_combination (α+β)*hA
    | linear_combination -(α+β)*hA
    | linear_combination -(α-β)*hS
    | linear_combination (α-β)*hI
    | linear_combination -(α-β)*hI

/-- The cancellation constraint removes the real off-diagonal part, leaving
exactly the Hermitian matrix printed in Lemma IQC. -/
theorem certificateMatrix_source (cert : Duality.StrictCertificate a t) (ω : ℝ) :
    certificateMatrix cert ω=!![(sourceA cert ω:ℂ),Complex.I*(sourceB cert ω:ℂ);
      -Complex.I*(sourceB cert ω:ℂ),-(sourceA cert ω:ℂ)] := by
  unfold certificateMatrix certificateSymbol
  simp only [transported_lags,transported_α,transported_β,transported_γplus,transported_γminus]
  simp_rw [weighted_pair_trig]
  have hc:=cert.cancel
  have hs : (∑ n∈cert.lags,(cert.β n-cert.α n)*Real.sinh (n*t))=
      -(∑ n∈cert.lags,(cert.α n-cert.β n)*Real.sinh (n*t)) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hc' : (∑ n∈cert.lags,(cert.β n-cert.α n)*Real.sinh (n*t))-cert.γplus+cert.γminus=0 := by
    rw [hs]
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [hermitianBlock,starSymbol,sourceA,sourceB,Matrix.sum_apply,
      Complex.mul_re,Complex.mul_im,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      Finset.sum_neg_distrib,-Complex.ofReal_exp,-Complex.ofReal_cos,-Complex.ofReal_sin,
      -Complex.ofReal_cosh,-Complex.ofReal_sinh]
  all_goals linarith

/-- The exact source matrix acts on arbitrary complex amplitudes, including
zero query or gradient amplitudes. -/
theorem sourceMatrix_quadratic (cert : Duality.StrictCertificate a t) (ω : ℝ) (U P : ℂ) :
    matrixQuadratic (certificateMatrix cert ω) ![U,P]=
      sourceA cert ω*(Complex.normSq U-Complex.normSq P)-
        2*sourceB cert ω*(P*star U).im := by
  rw [certificateMatrix_source]
  simp [matrixQuadratic,Fin.sum_univ_two,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

end
end nesterov.IQC
