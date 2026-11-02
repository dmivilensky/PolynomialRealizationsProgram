import jacobi.Analytic.ReferenceWave
import jacobi.Reference.Solutions

/-!
Article: jacobi, Lemma C.1.
Pairing the original two Gauss numerator factors gives a reference
series polynomial in the actual energy. It retains the original complex
order and eliminates any analyticity assumption about a square root.
Use: proves actual joint analytic dependence in order and energy, including the frequency branch point.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Polynomial Filter jacobi.Hankel
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The literal original reference coefficient polynomial in energy at complex order.
Use: proves actual joint analytic dependence in order and energy, including the frequency branch point.
Article: jacobi, Lemma C.1.
-/
def energyCoefficient (a : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  (n.factorial:ℂ)⁻¹*(∏ j∈Finset.range n,((gamma a+j)^2-(z-besselCoefficient a)/(Real.pi:ℂ)^2))*
    ((ascPochhammer ℂ n).eval (gamma a+1/2))⁻¹

/-- The original paired frequency rising factorials equal the genuine energy polynomial product at every prescribed frequency square.
Use: the square-root-free reference series has exactly the original Gauss coefficients.
Article: jacobi, Lemma C.1.
Proof: both finite products start at one. Their next paired numerator
factor is (gamma+n)^2-omega^2/pi^2, which is precisely the original
energy factor after substituting the genuine frequency square. -/
theorem paired_pochhammer (a : ℂ) {omega z : ℂ} (h : omega^2=z-besselCoefficient a) (n : ℕ) :
    (ascPochhammer ℂ n).eval (gamma a-omega/(Real.pi:ℂ))*
      (ascPochhammer ℂ n).eval (gamma a+omega/(Real.pi:ℂ))=
      ∏ j∈Finset.range n,((gamma a+j)^2-(z-besselCoefficient a)/(Real.pi:ℂ)^2) := by
  -- This identity is finite and precedes every convergence or analytic argument.
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval,ascPochhammer_succ_eval,Finset.prod_range_succ]
    calc
      _ = ((ascPochhammer ℂ n).eval (gamma a-omega/(Real.pi:ℂ))*
        (ascPochhammer ℂ n).eval (gamma a+omega/(Real.pi:ℂ)))*
        ((gamma a+n)^2-omega^2/(Real.pi:ℂ)^2) := by ring
      _ = _ := by rw [ih,h]

/-- The actual energy coefficient is the original Gauss coefficient for every frequency with the prescribed energy square.
Use: all reference series bounds apply to the same source function independently of a frequency branch choice.
Article: jacobi, Lemma C.1.
Proof: insert the proved finite paired-product identity into the literal coefficient formula. -/
theorem energyCoefficient_eq_frequency (a : ℂ) {omega z : ℂ}
    (h : omega^2=z-besselCoefficient a) (n : ℕ) :
    energyCoefficient a n z=ordinaryHypergeometricCoefficient (gamma a-omega/(Real.pi:ℂ))
      (gamma a+omega/(Real.pi:ℂ)) (gamma a+1/2) n := by
  unfold energyCoefficient ordinaryHypergeometricCoefficient
  rw [← paired_pochhammer a h n]
  ring

/-- The original energy coefficient is analytic along all analytic order and energy curves with admissible exponent.
Use: the actual reference energy series consists of genuine holomorphic terms.
Article: jacobi, Lemma C.1.
Proof: the numerator is a finite product of polynomials in order and
energy. The moving denominator is a rising-factorial polynomial with
positive-real-part argument and therefore does not vanish. -/
theorem energyCoefficient_comp_analytic {A Z : ℂ → ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ A p) (hZ : AnalyticAt ℂ Z p) (ha : 0<(gamma (A p)).re) (n : ℕ) :
    AnalyticAt ℂ (fun u => energyCoefficient (A u) n (Z u)) p := by
  -- The genuine varying denominator is inverted only after its nonvanishing is proved.
  have hg : AnalyticAt ℂ (fun u => gamma (A u)+1/2) p := by unfold gamma; fun_prop
  have hd := (AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ n) _ (mem_univ _)).comp
    (f := fun u => gamma (A u)+1/2) hg
  have hp : 0<(gamma (A p)+1/2).re := by norm_num; linarith
  have hn : AnalyticAt ℂ (fun u => (n.factorial:ℂ)⁻¹*
      (∏ j∈Finset.range n,((gamma (A u)+j)^2-(Z u-besselCoefficient (A u))/(Real.pi:ℂ)^2))) p := by
    unfold gamma besselCoefficient
    fun_prop
  exact hn.mul (hd.inv (jacobi.Reference.Hypergeometric.pochhammer_ne_zero hp n))

/-- Bounded complex order and shifted energy give one genuine positive-parameter majorant for the original energy coefficients.
Use: proves normal convergence in the actual order and energy variables, including zero frequency.
Article: jacobi, Lemma C.1.
Proof: choose any square root of the bounded shifted energy solely for
its norm estimate. Its norm is at most E+1. Both original frequency
numerator parameters are therefore bounded by a fixed positive number,
and the actual denominator is bounded below by its real-part margin.
Apply the proved moving-parameter Gauss coefficient bound. -/
theorem energyCoefficient_bound {G δ E : ℝ} (hG : 0<G) (hδ : 0<δ) (hE : 0≤E)
    {a z : ℂ} (ha : ‖gamma a‖≤G) (hc : δ≤(gamma a+1/2).re)
    (hz : ‖z-besselCoefficient a‖≤E) (n : ℕ) :
    ‖energyCoefficient a n z‖≤‖ordinaryHypergeometricCoefficient
      ((G+(E+1)/Real.pi+1:ℝ):ℂ) ((G+(E+1)/Real.pi+1:ℝ):ℂ) (δ:ℂ) n‖ := by
  -- No continuity or analyticity of this auxiliary square root is required.
  let omega := Complex.sqrt (z-besselCoefficient a)
  have hs : ‖omega‖^2=‖z-besselCoefficient a‖ := by
    rw [← norm_pow]
    exact congrArg norm (jacobi.Reference.frequency_square _)
  have homega : ‖omega‖≤E+1 := by nlinarith [norm_nonneg omega,sq_nonneg E]
  have hdiv : ‖omega/(Real.pi:ℂ)‖≤(E+1)/Real.pi := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    exact div_le_div_of_nonneg_right homega Real.pi_pos.le
  have hm := norm_sub_le (gamma a) (omega/(Real.pi:ℂ))
  have hp := norm_add_le (gamma a) (omega/(Real.pi:ℂ))
  rw [energyCoefficient_eq_frequency a (jacobi.Reference.frequency_square _) n]
  exact jacobi.Reference.Hypergeometric.coefficient_parameters_bound
    (by positivity) hδ (by linarith) (by linarith) hc n

/-- The original regular reference core as its actual square-root-free energy series at complex order.
Use: defines the jointly analytic reference energy function used in the continued GL summands.
Article: jacobi, Lemma C.1.
-/
def energyCore (a z x : ℂ) : ℂ := ∑' n,energyCoefficient a n z*x^n

/-- The actual original normalized reference solution at complex order and arbitrary energy.
Use: supplies f(t,sigma_k) and f(t,tau_k) in the analytic GL construction without a branch convention in their proofs.
Article: jacobi, Lemma C.1.
-/
def solution (a z : ℂ) (t : ℝ) : ℂ := weight a t*energyCore a z (jacobi.Reference.coordinate t:ℂ)

/-- Every actual frequency with the correct energy square gives exactly the square-root-free reference solution.
Use: transfers the proved full frequency-strip bounds to the actual energy reference function.
Article: jacobi, Lemma C.1.
Proof: the literal Gauss series and the energy series have equal
coefficients by the proved paired-factor identity; their original
normalizing sine prefactors are identical. -/
theorem solution_eq_wave (a : ℂ) {z omega : ℂ} (h : omega^2=z-besselCoefficient a) (t : ℝ) :
    solution a z t=wave a omega t := by
  unfold solution energyCore wave waveCore
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  congr 1
  apply tsum_congr
  intro n
  rw [energyCoefficient_eq_frequency a h n]

/-- The complex-order energy solution restricts to the exact original real-order reference solution at every physical point.
Use: identifies the analytic GL reference factors with all earlier real
kernel summands and transformed profiles, retaining their energy normalization.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: evaluate the genuine energy series at the original square-root
frequency using its proved square identity. The continued wave agrees
with the original real-order wave, and the actual fixed energy shifts
are the same polynomial under real inclusion. -/
theorem solution_real (a : ℝ) (z : ℂ) {t : ℝ} (ht : t∈Ico 0 1) :
    solution (a:ℂ) z t= jacobi.Reference.solution a z t := by
  have hc : besselCoefficient (a:ℂ)=(jacobi.Jacobi.endpointCorrection a:ℂ) := by
    unfold besselCoefficient jacobi.Jacobi.endpointCorrection
    push_cast
    ring
  rw [solution_eq_wave (a:ℂ) (jacobi.Reference.frequency_square _) t,
    wave_real a _ ht,hc]
  rfl

end
end jacobi.ComplexReference
