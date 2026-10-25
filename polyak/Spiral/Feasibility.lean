import polyak.Spiral.KernelPositive
import polyak.Spiral.Factor
import polyak.Waves.Finite

/-!
Article: Proposition spiral and its conversion to the actual Polyak parameter q.
Use: one explicitly specified atom is feasible at every spiral exponent, with
strict minimizer slack, including the limiting three-cycle.
Proof: all-lag kernel positivity, exact lag identities and the quartic relation.
-/

noncomputable section

namespace polyak.Spiral

open Spectral

/-- Article: the common value constant has exactly its printed tanh expression. -/
theorem valueConstant_eq_tanh (t : ℝ) : valueConstant t = gap t*Real.tanh t := by
  rw [Real.tanh_eq_sinh_div_cosh]
  unfold valueConstant G
  ring

/-- Article: the minimizer slack is strict on the entire spiral, even at t=0. -/
theorem abs_valueConstant_lt_gap (t : ℝ) : |valueConstant t| < gap t := by
  rw [valueConstant_eq_tanh,abs_mul,abs_of_pos (gap_pos t)]
  have h := mul_lt_mul_of_pos_left (Real.abs_tanh_lt_one t) (gap_pos t)
  simpa only [mul_one] using h

/-- Article: the minimizer slack of the Dirac spectrum is the explicit positive g. -/
theorem meanG_spectrum (t : ℝ) : meanG (spectrum t) (twist t) = gap t := by
  rw [meanG_eq_integral,avg_spectrum]
  exact g_spiral t

/-- Article: exact evaluation of a Dirac lower lag. -/
theorem mean_lower_eq (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    meanA (spectrum t) (twist t) t n-meanB (spectrum t) (twist t) n+
      valueConstant t*Real.sinh (n*t) = gap t/G t*kernel t (n+1) := by
  rw [meanA_eq_integral,meanB_eq_integral,avg_spectrum,avg_spectrum]
  exact lag_lower_eq t n hn

/-- Article: exact evaluation of a Dirac upper lag. -/
theorem mean_upper_eq (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    meanA (spectrum t) (twist t) t n+meanB (spectrum t) (twist t) n-
      valueConstant t*Real.sinh (n*t) = gap t/G t*kernel t (n-1) := by
  rw [meanA_eq_integral,meanB_eq_integral,avg_spectrum,avg_spectrum]
  exact lag_upper_eq t n hn

/-- Article: the full infinite system is feasible for the special spiral.
Use: no finite-lag truncation or asymptotic approximation enters this result. -/
theorem feasibleU (t : ℝ) : FeasibleU (twist t) t (spectrum t) (valueConstant t) := by
  refine ⟨?_,fun n hn => ?_⟩
  · rw [meanG_spectrum]
    exact (abs_valueConstant_lt_gap t).le
  · rw [mean_lower_eq t n hn,mean_upper_eq t n hn]
    exact ⟨mul_nonneg (div_pos (gap_pos t) (G_pos t)).le (kernel_nonneg t _),
      mul_nonneg (div_pos (gap_pos t) (G_pos t)).le (kernel_nonneg t _)⟩

/-- Article: the original (v,t) statement of Proposition spiral, now including t=0. -/
theorem feasible (t : ℝ) :
    Feasible (Real.arsinh (twist t)) t (spectrum t) (valueConstant t) := by
  simpa only [Feasible,Real.sinh_arsinh] using feasibleU t

/-- Article: the active lower lag is one. -/
theorem lower_one_zero (t : ℝ) :
    meanA (spectrum t) (twist t) t 1-meanB (spectrum t) (twist t) 1+
      valueConstant t*Real.sinh t = 0 := by
  have h := mean_lower_eq t 1 (by omega)
  simpa only [Nat.cast_one,one_mul,Nat.reduceAdd,kernel_two,mul_zero] using h

/-- Article: the active upper lag is two. -/
theorem upper_two_zero (t : ℝ) :
    meanA (spectrum t) (twist t) t 2+meanB (spectrum t) (twist t) 2-
      valueConstant t*Real.sinh (2*t) = 0 := by
  have h := mean_upper_eq t 2 (by omega)
  simpa only [Nat.cast_ofNat,Nat.reduceSub,kernel_one,mul_zero] using h

/-- Article: the active upper lag is three. -/
theorem upper_three_zero (t : ℝ) :
    meanA (spectrum t) (twist t) t 3+meanB (spectrum t) (twist t) 3-
      valueConstant t*Real.sinh (3*t) = 0 := by
  have h := mean_upper_eq t 3 (by omega)
  simpa only [Nat.cast_ofNat,Nat.reduceSub,kernel_two,mul_zero] using h

/-- Article: every lower lag except the active first one is strictly positive off t=0. -/
theorem mean_lower_pos {t : ℝ} (ht : t ≠ 0) (n : ℕ) (hn : 2 ≤ n) :
    0 < meanA (spectrum t) (twist t) t n-meanB (spectrum t) (twist t) n+
      valueConstant t*Real.sinh (n*t) := by
  rw [mean_lower_eq t n (by omega)]
  have hk := kernel_add_three_pos ht (n-2)
  rw [show n-2+3=n+1 by omega] at hk
  exact mul_pos (div_pos (gap_pos t) (G_pos t)) hk

/-- Article: the upper first lag is strictly positive, also at t=0. -/
theorem mean_upper_one_pos (t : ℝ) :
    0 < meanA (spectrum t) (twist t) t 1+meanB (spectrum t) (twist t) 1-
      valueConstant t*Real.sinh t := by
  have he := mean_upper_eq t 1 (by omega)
  simp only [Nat.cast_one,one_mul,Nat.sub_self,kernel_zero] at he
  rw [he]
  exact mul_pos (div_pos (gap_pos t) (G_pos t)) (by positivity)

/-- Article: every upper lag beyond the two active ones is strictly positive off t=0. -/
theorem mean_upper_pos {t : ℝ} (ht : t ≠ 0) (n : ℕ) (hn : 4 ≤ n) :
    0 < meanA (spectrum t) (twist t) t n+meanB (spectrum t) (twist t) n-
      valueConstant t*Real.sinh (n*t) := by
  rw [mean_upper_eq t n (by omega)]
  have hk := kernel_add_three_pos ht (n-4)
  rw [show n-4+3=n-1 by omega] at hk
  exact mul_pos (div_pos (gap_pos t) (G_pos t)) hk

/-- Article: the spiral twist written in terms of ρ=exp t. -/
theorem twist_eq_exp (t : ℝ) :
    twist t = 1-Real.exp t/(Real.exp t^2+1) := by
  have he := (Real.exp_pos t).ne'
  have hG := (G_pos t).ne'
  unfold twist G
  rw [Real.cosh_eq,Real.exp_neg]
  field_simp

/-- Article: exact actual twist in exponential coordinates. -/
theorem sinh_sub_log {q : ℝ} (hq : 0 < q) (t : ℝ) :
    Real.sinh (t-Real.log q) = (Real.exp t/q-q/Real.exp t)/2 := by
  rw [Real.sinh_eq,Real.exp_sub,Real.exp_log hq,Real.exp_neg,Real.exp_sub,Real.exp_log hq]
  have he := (Real.exp_pos t).ne'
  field_simp

/-- Article: the original quartic is the cleared exact actual-twist equation. -/
theorem spiralPolynomial_eq_twist_gap {ρ q : ℝ} (hρ : 0 < ρ) (hq : 0 < q) :
    spiralPolynomial ρ q = 2*q*ρ*(ρ^2+1)*
      ((ρ/q-q/ρ)/2-(1-ρ/(ρ^2+1))) := by
  unfold spiralPolynomial
  field_simp
  ring

/-- Article: F(exp t,q)=0 is precisely the original actual-parameter relation. -/
theorem actual_relation_iff {q : ℝ} (hq : 0 < q) (t : ℝ) :
    twist t = Real.sinh (t-Real.log q) ↔ spiralPolynomial (Real.exp t) q = 0 := by
  rw [twist_eq_exp,sinh_sub_log hq,spiralPolynomial_eq_twist_gap (Real.exp_pos t) hq]
  have hp : 0 < 2*q*Real.exp t*(Real.exp t^2+1) := by positivity
  constructor
  · intro h
    rw [← h,sub_self,mul_zero]
  · intro h
    have hh := (mul_eq_zero.mp h).resolve_left hp.ne'
    linarith

/-- Article: the positive quartic root supplies an actual feasible Polyak spectrum. -/
theorem actual_feasible {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Feasible (Real.log (factor q)-Real.log q) (Real.log (factor q))
      (spectrum (Real.log (factor q))) (valueConstant (Real.log (factor q))) := by
  have hρ := (factor_spec hq hq1).1
  have hr := (actual_relation_iff hq (Real.log (factor q))).mpr (by
    rw [Real.exp_log hρ]
    exact (factor_spec hq hq1).2)
  change FeasibleU (Real.sinh (Real.log (factor q)-Real.log q)) _ _ _
  rw [← hr]
  exact feasibleU _

/-- Article: a singleton finite mixture is exactly the spiral Dirac spectrum. -/
theorem finiteSpectrum_one_eq (t : ℝ) :
    Waves.finiteSpectrum (fun _ : Fin 1 => (1 : NNReal)) (fun _ => atom t)
      (by simp : (∑ _ : Fin 1, (1 : NNReal)) = 1) = spectrum t := by
  apply Subtype.ext
  simp [Waves.finiteSpectrum,spectrum]

/-- Article: feasibility for the multiplier of the actual normalized recurrence. -/
theorem actual_mixture_feasible {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Waves.MixtureFeasible (spectrum (Real.log (factor q)))
      (Waves.multiplierMap 0 (2*q) (q^2) (Real.log (factor q)))
      (valueConstant (Real.log (factor q))) (Real.log (factor q)) := by
  rw [Waves.multiplierMap_polyak q _ hq,Waves.mixtureFeasible_polyak_iff]
  exact actual_feasible hq hq1

/-- Article: the strict minimizer reserve in the actual multiplier notation. -/
theorem actual_mixture_gap {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Waves.spectrumG (spectrum (Real.log (factor q)))
      (Waves.multiplierMap 0 (2*q) (q^2) (Real.log (factor q))) =
        gap (Real.log (factor q)) := by
  rw [Waves.multiplierMap_polyak q _ hq,Waves.spectrumG_polyak]
  have hr := (actual_relation_iff hq (Real.log (factor q))).mpr (by
    rw [Real.exp_log (factor_spec hq hq1).1]
    exact (factor_spec hq hq1).2)
  rw [← hr,meanG_spectrum]

end polyak.Spiral
