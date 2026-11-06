import nesterov.IQC.PolynomialKernel
import nesterov.IQC.StationaryPlant

/-! The exact FIR symbols and zero-extension identities of the causal plant. -/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators
open polyak.General.IQC polyak.Energy

/-- Zero initial history removes every negative-index boundary impulse of a
forward polynomial filter. This includes the full denominator polynomial. -/
theorem zeroExtend_coefficientFilter {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {d : ℕ} (v : Fin d→ℝ) (w : ℕ→E)
    (hw : ∀ n : ℕ,n<d-1→w n=0) (k : ℤ) :
    filterEval (coefficientFilter v) (zeroExtend w) k=
      zeroExtend (fun n=>∑ j,v j • w (n+j.val)) k := by
  rw [filterEval_coefficientFilter]
  by_cases hk : 0≤k
  · lift k to ℕ using hk
    simp only [←Int.natCast_add,zeroExtend_nat]
  · rw [zeroExtend_neg _ (lt_of_not_ge hk)]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hkj : 0≤k+(j.val:ℤ)
    · rw [zeroExtend,ite_eq_left hkj,hw _ (by have :=j.isLt; omega),smul_zero]
    · rw [zeroExtend_neg _ (lt_of_not_ge hkj),smul_zero]

end
end nesterov.IQC

namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
open nesterov.IQC polyak.General.IQC polyak.Energy
variable (M : nesterov.StationaryMethod)

/-- Full forward query filter after discounting. -/
def queryFilter (t : ℝ) : LinearFilter:=coefficientFilter (M.discountedQueryCoeff t)

/-- Full forward normalized-gradient filter after discounting. -/
def normalizedFilter (μ L t : ℝ) : LinearFilter:=coefficientFilter (M.discountedCoeff μ L t)

/-- Its Fourier value is the literal u(exp(t+iω)). -/
theorem queryFilter_symbol (μ L t : ℝ) (c : nesterov.Spectral.Frequency) :
    filterEval (M.queryFilter t) (fun k=>character k ((Real.arccos c:ℝ):FrequencyCircle)) 0=
      (M.symbolPair μ L t).u c := by
  rw [queryFilter,filterEval_coefficientFilter,M.symbolPair_u,M.queryPolynomial_complex_eval]
  simp only [zero_add,Complex.real_smul,discountedQueryCoeff,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [character_nat_eq_wave,mul_assoc,exp_mul_unit_wave]

/-- Its Fourier value is p(exp(t+iω)), retaining its actual leading term. -/
theorem normalizedFilter_symbol (μ L t : ℝ) (c : nesterov.Spectral.Frequency) :
    filterEval (M.normalizedFilter μ L t)
      (fun k=>character k ((Real.arccos c:ℝ):FrequencyCircle)) 0=(M.symbolPair μ L t).p c := by
  rw [normalizedFilter,filterEval_coefficientFilter,M.symbolPair_p,M.normalizedPolynomial_eq_sum]
  simp only [Polynomial.eval_map,Polynomial.eval₂_finsetSum,Polynomial.eval₂_monomial,
    Complex.ofRealHom_eq_coe,zero_add,Complex.real_smul,discountedCoeff,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [character_nat_eq_wave,mul_assoc,exp_mul_unit_wave]

/-- Exact strict graph inequality for the complete latent signal, in every
real Hilbert space and without an inverse query polynomial. -/
theorem normalizedFilter_strict_graph {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ L t : ℝ}
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t) (w : ZSpace E) :
    certificateForm (transported cert)
      (filterCLM (M.queryFilter t) w,filterCLM (M.normalizedFilter μ L t) w)
      (filterCLM (M.queryFilter t) w,filterCLM (M.normalizedFilter μ L t) w)≤
        -cert.ε*‖w‖^2 :=
  twoFilterKernel_strict _ _ cert (M.queryFilter_symbol μ L t) (M.normalizedFilter_symbol μ L t) w

section Vector
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The whole-line query relation has no omitted startup boundary term. -/
theorem zeroLatent_whole_query (μ L t : ℝ) (input : ℕ→E) (k : ℤ) :
    filterEval (M.queryFilter t) (zeroExtend (M.zeroLatent μ L t input)) k=
      zeroExtend (convolution (M.queryImpulse μ L t) input) k := by
  rw [queryFilter,zeroExtend_coefficientFilter]
  · congr 1
    funext n
    exact M.zeroLatent_query μ L t input n
  · intro n hn
    exact M.zeroLatent_initial μ L t input ⟨n,by omega⟩

/-- The whole-line denominator relation retains the full normalized recurrence. -/
theorem zeroLatent_whole_normalized {μ L : ℝ} (hμL : μ<L) (t : ℝ)
    (input : ℕ→E) (k : ℤ) :
    filterEval (M.normalizedFilter μ L t) (zeroExtend (M.zeroLatent μ L t input)) k=
      zeroExtend input k := by
  rw [normalizedFilter,zeroExtend_coefficientFilter]
  · congr 1
    funext n
    exact M.zeroLatent_equation hμL t input n
  · intro n hn
    exact M.zeroLatent_initial μ L t input ⟨n,by omega⟩

end Vector
end
end nesterov.StationaryMethod
