import nesterov.IQC.Certificate
import nesterov.IQC.LinearFilters

/-!
The finite polynomial IQC kernel. It acts directly on the latent whole-line
signal through both u and p. Thus query zeros, nonminimum-phase queries, and
shared latent modes need no inverse query filter.
-/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators
open Spectral polyak.General.IQC polyak.Energy
variable {a : SymbolPair} {t : ℝ}

/-- Certificate kernel through two arbitrary real polynomial filters. -/
def twoFilterKernel (X S : LinearFilter) (cert : Duality.StrictCertificate a t) : Kernel :=
  (cert.lags.toList.flatMap fun (n:ℕ)=>kernelScale (2*Real.exp (-(n*t)))
    (kernelScale (cert.α n) (pairKernel 1 X
      (filterScale (Real.exp (n*t)) (filterShift n X)) S
      (filterScale (Real.exp (n*t)) (filterShift n S)))++
     kernelScale (cert.β n) (pairKernel (-1) X
      (filterScale (Real.exp (n*t)) (filterShift n X)) S
      (filterScale (Real.exp (n*t)) (filterShift n S)))))++
    kernelScale (4*cert.γplus) (starKernel 1 X S)++
    kernelScale (4*cert.γminus) (starKernel (-1) X S)

theorem twoFilterKernel_eval {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X S : LinearFilter) (cert : Duality.StrictCertificate a t) (w : ℤ→E) (k : ℤ) :
    kernelEval (twoFilterKernel X S cert) w k=
      zCertificateQuadratic (transported cert) (filterEval X w) (filterEval S w) k := by
  simp only [twoFilterKernel,kernelEval_append,kernelEval_scale,kernelEval_star,
    kernelEval_flatMap,Finset.sum_map_toList,kernelEval_pair,filterEval_scale,
    filterEval_shift,zCertificateQuadratic,transported_lags,transported_α,
    transported_β,transported_γplus,transported_γminus]

theorem twoFilterKernel_form {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X S : LinearFilter) (cert : Duality.StrictCertificate a t) (w : ZSpace E) :
    certificateForm (transported cert) (filterCLM X w,filterCLM S w)
      (filterCLM X w,filterCLM S w)=kernelBilinear (twoFilterKernel X S cert) w w := by
  rw [certificateForm_eq_tsum,kernelBilinear_eq_tsum]
  apply tsum_congr
  intro k
  have hx : (fun j=>(filterCLM X w) j)=filterEval X (fun j=>w j) :=
    funext (fun j=>filterCLM_apply X w j)
  have hs : (fun j=>(filterCLM S w) j)=filterEval S (fun j=>w j) :=
    funext (fun j=>filterCLM_apply S w j)
  change zCertificateQuadratic (transported cert)
    (fun j=>(filterCLM X w) j) (fun j=>(filterCLM S w) j) k=_
  rw [hx,hs]
  exact (twoFilterKernel_eval X S cert w k).symm

theorem twoFilterKernel_symbol (X S : LinearFilter) (cert : Duality.StrictCertificate a t)
    (c : Frequency)
    (hX : filterEval X (fun k=>character k ((Real.arccos c:ℝ):FrequencyCircle)) 0=a.u c)
    (hS : filterEval S (fun k=>character k ((Real.arccos c:ℝ):FrequencyCircle)) 0=a.p c) :
    kernelSymbol (twoFilterKernel X S cert) ((Real.arccos c:ℝ):FrequencyCircle)=
      Duality.symbol a t cert.lags cert.α cert.β cert.γplus cert.γminus c := by
  let ω:=Real.arccos c
  have hchar (k : ℤ) : filterEval X (fun j=>character j (ω:FrequencyCircle)) k=
      a.u c*character k (ω:FrequencyCircle) := by
    rw [filterEval_character,hX,mul_comm]
  have hgrad (k : ℤ) : filterEval S (fun j=>character j (ω:FrequencyCircle)) k=
      a.p c*character k (ω:FrequencyCircle) := by
    rw [filterEval_character,hS,mul_comm]
  rw [kernelSymbol_eq_eval,twoFilterKernel_eval]
  have hxseq : filterEval X (fun j=>character j (ω:FrequencyCircle))=
      (fun k=>a.u c*character k (ω:FrequencyCircle)):=funext hchar
  have hsseq : filterEval S (fun j=>character j (ω:FrequencyCircle))=
      (fun k=>a.p c*character k (ω:FrequencyCircle)):=funext hgrad
  change zCertificateQuadratic (transported cert)
    (filterEval X (fun j=>character j (ω:FrequencyCircle)))
    (filterEval S (fun j=>character j (ω:FrequencyCircle))) 0=_
  rw [hxseq,hsseq]
  have hm:=certificateMatrix_wave cert ω (a.u c) (a.p c)
  unfold certificateQuadratic at hm
  simp only [Nat.zero_add,pow_zero,mul_one] at hm
  rw [←certificateMatrix_graph cert c]
  rw [hm]
  unfold zCertificateQuadratic
  simp only [transported_lags,transported_α,transported_β,transported_γplus,transported_γminus,
    zero_add,character,fourier_zero,mul_one]
  congr 2
  apply Finset.sum_congr rfl
  intro n _
  rw [show fourier (n:ℤ) (ω:FrequencyCircle)=polyak.Waves.z 0 ω^n from
    character_nat_eq_wave n ω]

/-- The strict frequency gap controls latent energy directly. -/
theorem twoFilterKernel_strict {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X S : LinearFilter) (cert : Duality.StrictCertificate a t)
    (hX : ∀ c : Frequency,filterEval X
      (fun k=>character k ((Real.arccos c:ℝ):FrequencyCircle)) 0=a.u c)
    (hS : ∀ c : Frequency,filterEval S
      (fun k=>character k ((Real.arccos c:ℝ):FrequencyCircle)) 0=a.p c)
    (w : ZSpace E) :
    certificateForm (transported cert) (filterCLM X w,filterCLM S w)
      (filterCLM X w,filterCLM S w)≤ -cert.ε*‖w‖^2 := by
  rw [twoFilterKernel_form]
  apply kernelBilinear_le
  apply kernelSymbol_le_of_halfCircle
  intro ω hω0 hωπ
  let c : Frequency:=⟨Real.cos ω,Real.neg_one_le_cos ω,Real.cos_le_one ω⟩
  have hc : Real.arccos c=ω:=Real.arccos_cos hω0 hωπ
  rw [←hc,twoFilterKernel_symbol X S cert c (hX c) (hS c)]
  exact cert.strict c

end
end nesterov.IQC
