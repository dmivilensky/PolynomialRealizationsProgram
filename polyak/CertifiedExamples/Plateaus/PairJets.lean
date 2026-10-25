import polyak.CertifiedExamples.Plateaus.PairConstruction
import polyak.CertifiedExamples.Plateaus.SymbolSemantics

/-! The exact root equation and the exact Cramer solve force value and slope
zero of the original polynomial dual on every prescribed support site. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels Polynomial LeanCert.Engine
open scoped BigOperators

def pairPolynomial {d : ℕ} (q : Tuning) (n₁ n₂ : Fin d → ℤ)
    (μ m : Fin d → ℝ) (c : ℝ) : ℝ :=
  ∑ p:Fin d×Fin 2,pairWeight μ m p*dividedLag q (pairLag n₁ n₂ p) c

private theorem coefficient_actual (q : Tuning) (c : ℝ) :
    coefficientValue (coefficientVector q) c=q.Xi c := by
  change (Chart.coefficients q).eval c=q.Xi c
  exact Chart.eval_coefficients q c

theorem coordinateLag_actual_vector (q : Tuning) (n : ℤ) (c : ℝ) :
    coordinateLag (coefficientVector q) n c=Farey.Certificates.signedLagPolynomial q n c := by
  unfold coordinateLag Farey.Certificates.signedLagPolynomial
  rw [coefficient_actual]

theorem coordinateLag_differentiable (X : Fin 3 → ℝ) (n : ℤ) (c : ℝ) :
    DifferentiableAt ℝ (coordinateLag X n) c := by
  have he : coordinateCodeValue X n 0=coordinateLag X n := funext (coordinateCodeValue_zero X n)
  rw [←he]
  unfold coordinateCodeValue
  exact DifferentiableAt.fun_sum fun i _ =>
    (((QPoly.derivative^[0]) (lagComponentCode n i)).toPoly.hasDerivAt_aeval c).differentiableAt.const_mul _

theorem pair_G_factor {d : ℕ} (q : Tuning) (n₁ n₂ : Fin d → ℤ)
    (μ m : Fin d → ℝ) (c : ℝ) :
    (∑ p:Fin d×Fin 2,pairWeight μ m p*
      coordinateLag (coefficientVector q) (pairLag n₁ n₂ p) c)=
      (1-c)*pairPolynomial q n₁ n₂ μ m c := by
  unfold pairPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [coordinateLag_actual_vector,signedLag_divided]
  ring

theorem pair_G_deriv {d : ℕ} (X : Fin 3 → ℝ) (n₁ n₂ : Fin d → ℤ)
    (μ m : Fin d → ℝ) (c : ℝ) :
    deriv (fun z=>∑ p:Fin d×Fin 2,pairWeight μ m p*coordinateLag X (pairLag n₁ n₂ p) z) c=
      ∑ p:Fin d×Fin 2,pairWeight μ m p*coordinateCodeValue X (pairLag n₁ n₂ p) 1 c := by
  rw [deriv_fun_sum (fun p _=>(coordinateLag_differentiable X _ c).const_mul _)]
  simp only [deriv_const_mul_field,←coordinateCodeValue_one]

theorem pairPolynomial_analytic {d : ℕ} (q : Tuning) (n₁ n₂ : Fin d → ℤ)
    (μ m : Fin d → ℝ) (c : ℝ) : AnalyticAt ℝ (pairPolynomial q n₁ n₂ μ m) c := by
  unfold pairPolynomial
  apply Finset.analyticAt_fun_sum
  intro p _
  apply analyticAt_const.mul
  have h := polynomialSymbol_analytic q {pairLag n₁ n₂ p} (fun _=>1) c
  have he : polynomialSymbol q {pairLag n₁ n₂ p} (fun _=>1)=
      dividedLag q (pairLag n₁ n₂ p) := by
    funext x
    simp only [polynomialSymbol,Finset.sum_singleton,one_mul]
  rwa [he] at h

theorem pair_polynomial_double_zero {d : ℕ} (q : Tuning) (n₁ n₂ : Fin d → ℤ)
    (c μ : Fin d → ℝ)
    (hμ : ∀ i,(∑ r,μ r*coordinateLag (coefficientVector q) (n₁ r) (c i))=0)
    (hp : ∀ i r,coordinateLag (coefficientVector q) (n₂ r) (c i)=
      coordinateLag (coefficientVector q) (n₁ r) (c i))
    (hV : (pairSlope (coefficientVector q) n₁ n₂ c).det≠0)
    (hc : ∀i,c i≠1) (i : Fin d) :
    let m:=pairMoments (coefficientVector q) n₁ n₂ c μ
    pairPolynomial q n₁ n₂ μ m (c i)=0 ∧
      deriv (pairPolynomial q n₁ n₂ μ m) (c i)=0 := by
  let m:=pairMoments (coefficientVector q) n₁ n₂ c μ
  let H:=pairPolynomial q n₁ n₂ μ m
  let F:=fun z=>∑ p:Fin d×Fin 2,pairWeight μ m p*
    coordinateLag (coefficientVector q) (pairLag n₁ n₂ p) z
  have hf : F=fun z=>(1-z)*H z := funext (pair_G_factor q n₁ n₂ μ m)
  have h0 : F (c i)=0 := pair_value_zero (coefficientVector q) n₁ n₂ c μ m hμ hp i
  have h1 : deriv F (c i)=0 := by
    change deriv (fun z=>∑ p:Fin d×Fin 2,pairWeight μ m p*
      coordinateLag (coefficientVector q) (pairLag n₁ n₂ p) z) (c i)=0
    rw [pair_G_deriv]
    exact pair_first_jet_zero (coefficientVector q) n₁ n₂ c μ hV i
  have hfac : 1-c i≠0 := sub_ne_zero.mpr (hc i).symm
  have hH0 : H (c i)=0 := by
    rw [hf] at h0
    exact (mul_eq_zero.mp h0).resolve_left hfac
  have hd := (((hasDerivAt_const (c i) (1:ℝ)).sub (hasDerivAt_id (c i))).mul
    (pairPolynomial_analytic q n₁ n₂ μ m (c i)).differentiableAt.hasDerivAt).deriv
  change deriv (fun z=>(1-z)*H z) (c i)=(0-1)*H (c i)+(1-c i)*deriv H (c i) at hd
  rw [←hf,h1,hH0,mul_zero,zero_add] at hd
  have hH1 : deriv H (c i)=0 := (mul_eq_zero.mp hd.symm).resolve_left hfac
  exact ⟨hH0,hH1⟩

end polyak.CertifiedExamples.Plateaus
