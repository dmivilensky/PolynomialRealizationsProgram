import polyak.General.Angle
import polyak.General.Regions.Topology

/-! The three literal coefficients of the source quadratic Ξ. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set

structure Coefficients where
  c0 : ℝ
  c1 : ℝ
  c2 : ℝ
  deriving DecidableEq

def Coefficients.eval (C : Coefficients) (c : ℝ) : ℝ := C.c0+C.c1*c+C.c2*c^2

instance : TopologicalSpace Coefficients := TopologicalSpace.induced
  (fun C : Coefficients=>(C.c0,C.c1,C.c2)) inferInstance

@[fun_prop] theorem Coefficients.continuous_c0 : Continuous Coefficients.c0 :=
  (show Continuous (fun C : Coefficients=>(C.c0,C.c1,C.c2)) from continuous_induced_dom).fst
@[fun_prop] theorem Coefficients.continuous_c1 : Continuous Coefficients.c1 :=
  (show Continuous (fun C : Coefficients=>(C.c0,C.c1,C.c2)) from continuous_induced_dom).snd.fst
@[fun_prop] theorem Coefficients.continuous_c2 : Continuous Coefficients.c2 :=
  (show Continuous (fun C : Coefficients=>(C.c0,C.c1,C.c2)) from continuous_induced_dom).snd.snd
@[fun_prop] theorem Coefficients.continuous_eval (c : ℝ) : Continuous (fun C : Coefficients=>C.eval c) := by
  unfold Coefficients.eval
  fun_prop

@[ext] theorem Coefficients.ext {C D : Coefficients} (h0 : C.c0=D.c0)
    (h1 : C.c1=D.c1) (h2 : C.c2=D.c2) : C=D := by
  cases C; cases D; simp_all

def coefficients (q : Tuning) : Coefficients where
  c0 := (q.B^2-(1-q.beta)^2-q.A^2)/(2*q.B*(1-q.beta))
  c1 := (2*q.A*(1+q.beta))/(2*q.B*(1-q.beta))
  c2 := -4*q.beta/(2*q.B*(1-q.beta))

theorem eval_coefficients (q : Tuning) (c : ℝ) : (coefficients q).eval c=q.Xi c := by
  dsimp [Coefficients.eval,coefficients,Tuning.Xi]
  field_simp
  ring

theorem coefficient_quadratic_neg_iff (q : Tuning) : (coefficients q).c2<0 ↔ 0<q.beta := by
  change -4*q.beta/(2*q.B*(1-q.beta))<0 ↔ _
  rw [div_lt_iff₀ (by positivity [q.B_pos,q.beta_lt_one])]
  constructor <;> intro h <;> linarith

theorem coefficient_quadratic_zero_iff (q : Tuning) : (coefficients q).c2=0 ↔ q.beta=0 := by
  dsimp [coefficients]
  rw [div_eq_zero_iff]
  have hden : 2*q.B*(1-q.beta)≠0 := by positivity [q.B_pos,q.beta_lt_one]
  simp only [hden,or_false,mul_eq_zero,neg_eq_zero,OfNat.ofNat_ne_zero,false_or]

def CoeffDomain : Set Coefficients :=
  {C | C.c2<0 ∧ C.eval 1<0 ∧ C.eval (-1)<0}

theorem coefficients_mem (q : Tuning) (hb : 0<q.beta) : coefficients q∈CoeffDomain := by
  exact ⟨(coefficient_quadratic_neg_iff q).mpr hb,
    (eval_coefficients q 1) ▸ q.Xi_one_neg,
    (eval_coefficients q (-1)) ▸ q.Xi_neg_one_neg⟩

theorem coefficient_domain_endpoint (C : Coefficients) (hC : C∈CoeffDomain) :
    C.c0 < -C.c2-|C.c1| := by
  have hp := hC.2.1
  have hm := hC.2.2
  simp only [Coefficients.eval,one_pow,mul_one,neg_one_sq,mul_neg_one] at hp hm
  rcases le_total 0 C.c1 with h|h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_nonpos h]; linarith

@[fun_prop] theorem continuous_coefficients : Continuous coefficients := by
  apply continuous_induced_rng.mpr
  change Continuous (fun q : Tuning=>
    ((q.B^2-(1-q.beta)^2-q.A^2)/(2*q.B*(1-q.beta)),
      (2*q.A*(1+q.beta))/(2*q.B*(1-q.beta)),
      -4*q.beta/(2*q.B*(1-q.beta))))
  unfold Tuning.A Tuning.B
  fun_prop (disch := intro q; positivity [q.x_lt_y,q.beta_lt_one])

theorem isOpen_coeffDomain : IsOpen CoeffDomain := by
  exact (isOpen_lt Coefficients.continuous_c2 continuous_const).inter
    ((isOpen_lt (Coefficients.continuous_eval 1) continuous_const).inter
      (isOpen_lt (Coefficients.continuous_eval (-1)) continuous_const))

end polyak.Levels.Chart
