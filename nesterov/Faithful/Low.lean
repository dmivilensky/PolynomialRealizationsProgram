import nesterov.Faithful.Analytic
import nesterov.Attainment.LagPolynomial
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Asymptotics.Lemmas

/-! The exact analytic germs behind Lemma `lem:low`. -/
namespace nesterov.Faithful
noncomputable section
open Filter Asymptotics Polynomial
open scoped Topology

@[simp] theorem evalComplex_one (p : Polynomial ℝ) : evalComplex p 1=((p.eval 1:ℝ):ℂ) := by
  simp [evalComplex]

@[simp] theorem evalComplex_star (p : Polynomial ℝ) (z : ℂ) :
    evalComplex p (star z)=star (evalComplex p z) := Attainment.ceval_conj p z

theorem analyticAt_star {f : ℝ→ℂ} {x : ℝ} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun x=>star (f x)) x := by
  exact (Complex.conjCLE.toContinuousLinearMap.analyticAt (f x)).fun_comp hf

def limitProduct (u q : Polynomial ℝ) (ω : ℝ) : ℂ :=
  -((circle ω-1)^2*evalComplex q (circle ω))*
    star (evalComplex u (circle ω)-(circle ω-1)^2*evalComplex q (circle ω))

def limitSymbol (u q : Polynomial ℝ) (ω : ℝ) : ℝ :=
  ((1-circle ω)*limitProduct u q ω).re

theorem circle_neg (ω : ℝ) : circle (-ω)=star (circle ω) := by
  simp only [circle,Complex.star_def,←Complex.exp_conj,map_mul,Complex.conj_ofReal,
    Complex.conj_I,Complex.ofReal_neg]
  congr 1
  ring

theorem limitProduct_neg (u q : Polynomial ℝ) (ω : ℝ) :
    limitProduct u q (-ω)=star (limitProduct u q ω) := by
  simp only [limitProduct,circle_neg,evalComplex_star,star_mul,star_sub,star_neg,star_pow,star_one,star_star]
  ring

theorem limitSymbol_even (u q : Polynomial ℝ) : Function.Even (limitSymbol u q) := by
  intro ω
  rw [limitSymbol,limitProduct_neg,circle_neg]
  have hh : (1-star (circle ω))*star (limitProduct u q ω)=
      star ((1-circle ω)*limitProduct u q ω) := by simp only [star_mul,star_sub,star_one];ring
  rw [hh]
  exact Complex.conj_re _

/-- A first-order analytic expansion with a global analytic remainder germ. -/
theorem analytic_first_jet {f : ℝ→ℂ} {d : ℂ} (hf : AnalyticAt ℝ f 0)
    (hd : HasDerivAt f d 0) :
    ∃ R : ℝ→ℂ,AnalyticAt ℝ R 0 ∧ ∀ ω,f ω=f 0+(ω:ℂ)*d+(ω:ℂ)^2*R ω := by
  obtain ⟨R,hR,he⟩ := hf.exists_eq_sum_add_pow_mul 2
  refine ⟨R,hR,fun ω=>?_⟩
  have hh := he ω
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,iteratedDeriv_zero,
    iteratedDeriv_succ,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,pow_zero,pow_one,
    zero_add,div_one,hd.deriv,Complex.real_smul] at hh
  simpa using hh

/-- The factored endpoint product has its exact first analytic jet. -/
theorem exists_product_germ (u q : Polynomial ℝ) {y : ℝ} (hy : 0<y)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) :
    ∃ X : ℝ→ℂ,AnalyticAt ℝ X 0 ∧ X 0= -1/y ∧
      HasDerivAt X (Complex.I*(effectiveLead u q y/y)) 0 ∧
      ∀ ω,limitProduct u q ω=(ω:ℂ)^2*X ω := by
  obtain ⟨E,hE,hE0,hEd,hinc⟩ := exists_circle_increment
  let U : ℝ→ℂ := fun ω=>evalComplex u (circle ω)
  let V : ℝ→ℂ := fun ω=>E ω^2*evalComplex q (circle ω)
  let X : ℝ→ℂ := fun ω=> -(V ω*star (U ω))+(ω:ℂ)^2*(V ω*star (V ω))
  have hU : AnalyticAt ℝ U 0 := AnalyticAt.fun_comp (f:=circle) (analyticAt_evalComplex u (circle 0)) (analyticAt_circle 0)
  have hQ : AnalyticAt ℝ (fun ω=>evalComplex q (circle ω)) 0 :=
    AnalyticAt.fun_comp (f:=circle) (analyticAt_evalComplex q (circle 0)) (analyticAt_circle 0)
  have hV : AnalyticAt ℝ V 0 := (hE.fun_pow 2).fun_mul hQ
  have hreal : AnalyticAt ℝ (fun ω : ℝ=>(ω:ℂ)) 0 := Complex.ofRealCLM.analyticAt 0
  have hX : AnalyticAt ℝ X 0 := (hV.fun_mul (analyticAt_star hU)).fun_neg.fun_add
    ((hreal.fun_pow 2).fun_mul (hV.fun_mul (analyticAt_star hV)))
  have hU0 : U 0=1 := by simp [U,hu]
  have hV0 : V 0=(1/y:ℝ) := by simp [V,hE0,hq,Complex.I_sq];ring
  have hUd : HasDerivAt U ((u.derivative.eval 1:ℝ)*Complex.I) 0 := by
    simpa only [circle_zero,evalComplex_one,mul_one] using hasDerivAt_evalComplex_comp u (hasDerivAt_circle 0)
  have hQd : HasDerivAt (fun ω=>evalComplex q (circle ω)) ((q.derivative.eval 1:ℝ)*Complex.I) 0 := by
    simpa only [circle_zero,evalComplex_one,mul_one] using hasDerivAt_evalComplex_comp q (hasDerivAt_circle 0)
  have hVd : HasDerivAt V (Complex.I*((1/y:ℝ)-q.derivative.eval 1)) 0 := by
    convert! (hEd.pow 2).mul hQd using 1
    simp only [Pi.pow_apply,hE0,circle_zero,evalComplex_one,hq,Complex.I_sq]
    push_cast
    ring
  refine ⟨X,hX,?_,?_,fun ω=>?_⟩
  · simp [X,hU0,hV0,neg_div]
  · have hz : HasDerivAt (fun ω : ℝ=>(ω:ℂ)^2) 0 0 := by
      convert! (Complex.ofRealCLM.hasDerivAt (x:=(0:ℝ))).pow 2 using 1
      simp
    have hh := ((hVd.mul hUd.star).neg).add (hz.mul (hVd.mul hVd.star))
    convert! hh using 1
    norm_num only [hU0,hV0,star_one,Pi.pow_apply,Complex.ofReal_zero,zero_pow (by decide : 2≠0),mul_one,mul_zero,zero_mul,add_zero]
    simp only [effectiveLead,star_mul,Complex.star_def,Complex.conj_ofReal,Complex.conj_I]
    push_cast
    field_simp [hy.ne']
    ring
  · unfold limitProduct X V U
    rw [hinc ω]
    simp only [star_sub,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
    ring


theorem product_expansion (u q : Polynomial ℝ) {y : ℝ} (hy : 0<y)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) :
    ∃ R : ℝ→ℂ,AnalyticAt ℝ R 0 ∧ ∀ ω,
      limitProduct u q ω= -(ω:ℂ)^2/y+Complex.I*(effectiveLead u q y/y:ℝ)*(ω:ℂ)^3+(ω:ℂ)^4*R ω := by
  obtain ⟨X,hX,hX0,hd,hprod⟩ := exists_product_germ u q hy hu hq
  obtain ⟨R,hR,hjet⟩ := analytic_first_jet hX hd
  refine ⟨R,hR,fun ω=>?_⟩
  rw [hprod,hjet,hX0]
  push_cast
  ring

theorem symbol_expansion (u q : Polynomial ℝ) {y : ℝ} (hy : 0<y)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) :
    ∃ R : ℝ→ℝ,AnalyticAt ℝ R 0 ∧ ∀ ω,
      limitSymbol u q ω=((2*effectiveLead u q y-1)/(2*y))*ω^4+ω^6*R ω := by
  obtain ⟨E,hE,hE0,hEd,hinc⟩ := exists_circle_increment
  obtain ⟨X,hX,hX0,hXd,hprod⟩ := exists_product_germ u q hy hu hq
  let a := (2*effectiveLead u q y-1)/(2*y)
  let A : ℝ→ℝ := fun ω=>(-(E ω*X ω)).re
  have hA : AnalyticAt ℝ A 0 :=
    AnalyticAt.fun_comp (f:=fun ω=> -(E ω*X ω)) (Complex.reCLM.analyticAt _) (hE.fun_mul hX).fun_neg
  have hA0 : A 0=0 := by simp [A,hE0,hX0]
  have hAd : HasDerivAt A a 0 := by
    have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 ((hEd.mul hXd).neg)
    convert! hh using 1
    norm_num [hE0,hX0,a,Complex.mul_re,Complex.mul_im]
    field_simp [hy.ne']
    ring
  have hSA (ω : ℝ) : limitSymbol u q ω=ω^3*A ω := by
    unfold limitSymbol
    rw [hprod]
    have hi : 1-circle ω= -(ω:ℂ)*E ω := by rw [←neg_sub,hinc];ring
    rw [hi]
    have he : (-(ω:ℂ)*E ω)*((ω:ℂ)^2*X ω)=(ω^3:ℝ)*(-(E ω*X ω)) := by push_cast;ring
    rw [he]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,A]
  obtain ⟨R₁,hR₁,hjetA⟩ := hA.exists_eq_sum_add_pow_mul 2
  let B : ℝ→ℝ := fun ω=>a+ω*R₁ ω
  have hB : AnalyticAt ℝ B 0 := analyticAt_const.fun_add (analyticAt_id.fun_mul hR₁)
  have hB0 : B 0=a := by simp [B]
  have hSB (ω : ℝ) : limitSymbol u q ω=ω^4*B ω := by
    have hh := hjetA ω
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,iteratedDeriv_zero,
      iteratedDeriv_succ,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,pow_zero,pow_one,
      zero_add,div_one,one_smul,hAd.deriv,hA0,smul_eq_mul] at hh
    rw [hSA,hh]
    dsimp [B]
    ring
  have hBeven : Function.Even B := by
    intro ω
    by_cases hω : ω=0
    · subst ω;simp
    · have hh := limitSymbol_even u q ω
      rw [hSB,hSB] at hh
      rw [show (-ω)^4=ω^4 by ring] at hh
      exact (mul_left_cancel₀ (pow_ne_zero 4 hω)) hh
  have hBd := hB.differentiableAt.hasDerivAt
  have hBd' : HasDerivAt B (deriv B 0) (-0:ℝ) := by simpa using hBd
  have hBneg := hBd'.comp 0 (hasDerivAt_id' (0:ℝ)).neg
  change HasDerivAt (fun ω : ℝ=>B (-ω)) (deriv B 0*(-1)) 0 at hBneg
  have heq : (fun ω : ℝ=>B (-ω))=B := funext hBeven
  rw [heq] at hBneg
  have hBder : deriv B 0=0 := by
    have hh := hBd.unique hBneg
    linarith
  obtain ⟨R,hR,hjetB⟩ := hB.exists_eq_sum_add_pow_mul 2
  refine ⟨R,hR,fun ω=>?_⟩
  have hh := hjetB ω
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,iteratedDeriv_zero,
    iteratedDeriv_succ,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,pow_zero,pow_one,
    zero_add,div_one,one_smul,hBder,hB0,smul_eq_mul] at hh
  rw [hSB,hh]
  dsimp [a]
  ring

end
end nesterov.Faithful
