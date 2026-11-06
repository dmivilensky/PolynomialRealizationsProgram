import nesterov.Faithful.CoefficientLimits
import nesterov.Faithful.PolynomialTail
import nesterov.Faithful.SourcePhase

/-! Faithful(a): strict positivity of the actual full-circle lag-one symbol. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial Filter Set
open scoped Topology
variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

theorem familyPolynomial_coeff_tendsto (hc : F.CoeffCk 1) (c : ℝ) (j : ℕ) :
    Tendsto (fun ε=>(familyPolynomial F c ε).coeff j) (𝓝[>] (0:ℝ))
      (𝓝 ((familyPolynomial F c 0).coeff j)) :=
  ((familyPolynomial_coeff_ck F hc c j).continuousWithinAt.tendsto).mono_left
    (nhdsWithin_mono _ Ioi_subset_Ici_self)

theorem familyPolynomial_constant (c ε : ℝ) :
    (familyPolynomial F c ε).coeff 0=familySymbol F c ε 0 := by
  simpa only [Real.cos_zero,sub_self,←coeff_zero_eq_eval_zero] using familyPolynomial_eval F c ε 0

theorem family_constant_ratio (c : ℝ) :
    Tendsto (fun ε : ℝ=>(familyPolynomial F c ε).coeff 0/ε^3) (𝓝[>] (0:ℝ))
      (𝓝 (c*Flow.delta θ y c/y)) := by
  simp_rw [familyPolynomial_constant]
  simpa only [mul_zero,zero_pow (by decide : 2≠0),mul_zero,add_zero] using scaled_symbol_tendsto F c 0

theorem family_linear_ratio (hc : F.CoeffCk 1) (c : ℝ) :
    Tendsto (fun ε : ℝ=>(familyPolynomial F c ε).coeff 1/ε) (𝓝[>] (0:ℝ))
      (𝓝 (2*(θ-3*c)/y)) := by
  have hd (ε : ℝ) : (familyPolynomial F c ε).natDegree<2*(F.memory+2)+2 :=
    (familyPolynomial_natDegree F c ε).trans_lt (by omega)
  have h1 : Tendsto (fun ε : ℝ=>(familyPolynomial F c ε).eval (1-Real.cos ε)/ε^3)
      (𝓝[>] (0:ℝ)) (𝓝 ((c*Flow.delta θ y c+(θ-3*c))/y)) := by
    simp_rw [familyPolynomial_eval]
    simpa only [mul_one,one_pow,mul_one] using scaled_symbol_tendsto F c 1
  have hh := linear_coeff_ratio_limit hd (familyPolynomial_coeff_tendsto F hc c)
    (family_constant_ratio F c) h1
  convert! hh using 1
  congr 1
  ring

theorem familySymbol_zero (c ω : ℝ) : familySymbol F c 0 ω=limitSymbol (F.u 0) F.q0 ω := by
  unfold familySymbol limitSymbol
  simp only [mul_zero,zero_pow (by decide : 2≠0)]
  have hz : polyak.Waves.z 0 ω=circle ω := by simp [circle,polyak.Waves.z]
  rw [hz,mul_assoc,←limitProduct_characteristic (F.method 0) F.q0 F.initial_factor]

theorem positive_limit_polynomial (c : ℝ)
    (hS : ∀ ω∈Ioc (0:ℝ) Real.pi,0<limitSymbol (F.u 0) F.q0 ω) :
    ∀ x : ℝ,0<x → x≤2 → 0<(familyPolynomial F c 0).eval x := by
  intro x hx hx2
  let ω := Real.arccos (1-x)
  have hω0 : 0<ω := by
    apply Real.arccos_pos.mpr
    linarith
  have hωpi : ω≤Real.pi := Real.arccos_le_pi _
  have hξ : 1-Real.cos ω=x := by
    rw [Real.cos_arccos (by linarith : -1≤1-x) (by linarith : 1-x≤1)]
    ring
  rw [←hξ,familyPolynomial_eval,familySymbol_zero]
  exact hS ω ⟨hω0,hωpi⟩

/-- Strict positivity of the limit symbol gives positivity on the whole
perturbed circle. C¹ suffices for this finite-polynomial proof. -/
theorem family_symbol_eventually_positive (hc : F.CoeffCk 1) {c : ℝ}
    (hc0 : 0<c) (hcF : c<Flow.cF θ y)
    (hS : ∀ ω∈Ioc (0:ℝ) Real.pi,0<limitSymbol (F.u 0) F.q0 ω) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ ω : ℝ,0<familySymbol F c ε ω := by
  have hQ : c<Flow.cQ θ y := hcF.trans_le (Flow.cF_le_cQ θ y)
  have hd : 0<Flow.delta θ y c := (Flow.lt_cQ_iff θ y c).mp hQ |>.2
  have hθ : 0<θ-3*c := by have hh := hcF.trans_le (Flow.cF_le_third θ y);linarith
  have hy := F.step_pos
  have hdeg (ε : ℝ) : (familyPolynomial F c ε).natDegree<2*(F.memory+2)+2 :=
    (familyPolynomial_natDegree F c ε).trans_lt (by omega)
  have hzero : (familyPolynomial F c 0).coeff 0=0 := coefficient_zero_of_ratio (k:=3) (by norm_num)
    (familyPolynomial_coeff_tendsto F hc c 0) (family_constant_ratio F c)
  have hone : (familyPolynomial F c 0).coeff 1=0 := coefficient_zero_of_ratio (k:=1) (by norm_num)
    (familyPolynomial_coeff_tendsto F hc c 1) (by simpa only [pow_one] using family_linear_ratio F hc c)
  have hh := eventually_positive_polynomial (2*(F.memory+2)) hdeg
    (familyPolynomial_coeff_ck F hc c) hzero hone (positive_limit_polynomial F c hS)
    (A:=c*Flow.delta θ y c/y) (B:=2*(θ-3*c)/y)
    (by positivity) (by positivity) (family_constant_ratio F c) (family_linear_ratio F hc c)
  filter_upwards [hh] with ε hε ω
  rw [←familyPolynomial_eval]
  exact hε (1-Real.cos ω) ⟨by linarith [Real.cos_le_one ω],by linarith [Real.neg_one_le_cos ω]⟩

end
end nesterov.Faithful
