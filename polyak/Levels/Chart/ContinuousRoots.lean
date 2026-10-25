import polyak.Levels.Chart.Homeomorphism

/-! Globally continuous root labels for real quadratics, including a
repeated root. They give actual stable and reversed stable root labels for
every coefficient point of the chart. -/
noncomputable section
namespace polyak.Levels.Chart
open General

def splitSqrt (d : ℝ) : ℂ := (Real.sqrt d:ℂ)+(Real.sqrt (-d):ℂ)*Complex.I

theorem splitSqrt_sq (d : ℝ) : splitSqrt d^2=(d:ℂ) := by
  by_cases hd : 0≤d
  · unfold splitSqrt
    rw [Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr hd)]
    simp only [Complex.ofReal_zero,zero_mul,add_zero,←Complex.ofReal_pow]
    exact congrArg Complex.ofReal (Real.sq_sqrt hd)
  · unfold splitSqrt
    rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hd)]
    simp only [Complex.ofReal_zero,zero_add,mul_pow,Complex.I_sq]
    rw [←Complex.ofReal_pow,Real.sq_sqrt (by linarith : 0≤ -d)]
    push_cast
    ring

@[fun_prop] theorem continuous_splitSqrt : Continuous splitSqrt := by
  unfold splitSqrt
  fun_prop

def rootPlus (p β : ℝ) : ℂ := ((p:ℂ)+splitSqrt (p^2-4*β))/2
def rootMinus (p β : ℝ) : ℂ := ((p:ℂ)-splitSqrt (p^2-4*β))/2

theorem root_factor (p β : ℝ) (z : ℂ) :
    (z-rootPlus p β)*(z-rootMinus p β)=z^2-(p:ℂ)*z+β := by
  calc
    _=z^2-(p:ℂ)*z+((p:ℂ)^2-splitSqrt (p^2-4*β)^2)/4 := by
      unfold rootPlus rootMinus
      ring
    _=_ := by rw [splitSqrt_sq]; push_cast; ring

theorem rootPlus_zero (p β : ℝ) : (rootPlus p β)^2-(p:ℂ)*rootPlus p β+β=0 := by
  rw [←root_factor]
  simp

theorem rootMinus_zero (p β : ℝ) : (rootMinus p β)^2-(p:ℂ)*rootMinus p β+β=0 := by
  rw [←root_factor]
  simp

theorem quadratic_zero_iff (p β : ℝ) (z : ℂ) :
    z^2-(p:ℂ)*z+β=0 ↔ z=rootPlus p β ∨ z=rootMinus p β := by
  rw [←root_factor,mul_eq_zero,sub_eq_zero,sub_eq_zero]

@[fun_prop] theorem continuous_rootPlus : Continuous (fun p : ℝ×ℝ=>rootPlus p.1 p.2) := by
  unfold rootPlus
  fun_prop
@[fun_prop] theorem continuous_rootMinus : Continuous (fun p : ℝ×ℝ=>rootMinus p.1 p.2) := by
  unfold rootMinus
  fun_prop

def aRootPlus (C : CoefficientPoint) : ℂ :=
  rootPlus (1+(inverseTuning C).beta-(inverseTuning C).x) (inverseTuning C).beta
def aRootMinus (C : CoefficientPoint) : ℂ :=
  rootMinus (1+(inverseTuning C).beta-(inverseTuning C).x) (inverseTuning C).beta
def bRootPlus (C : CoefficientPoint) : ℂ :=
  rootPlus (1+(inverseTuning C).beta-(inverseTuning C).y) (inverseTuning C).beta
def bRootMinus (C : CoefficientPoint) : ℂ :=
  rootMinus (1+(inverseTuning C).beta-(inverseTuning C).y) (inverseTuning C).beta

theorem aRootPlus_zero (C : CoefficientPoint) : (inverseTuning C).a (aRootPlus C)=0 :=
  rootPlus_zero _ _
theorem aRootMinus_zero (C : CoefficientPoint) : (inverseTuning C).a (aRootMinus C)=0 :=
  rootMinus_zero _ _
theorem bRootPlus_zero (C : CoefficientPoint) : (inverseTuning C).b (bRootPlus C)=0 :=
  rootPlus_zero _ _
theorem bRootMinus_zero (C : CoefficientPoint) : (inverseTuning C).b (bRootMinus C)=0 :=
  rootMinus_zero _ _

theorem a_roots_iff (C : CoefficientPoint) (z : ℂ) :
    (inverseTuning C).a z=0 ↔ z=aRootPlus C ∨ z=aRootMinus C :=
  quadratic_zero_iff _ _ _
theorem b_roots_iff (C : CoefficientPoint) (z : ℂ) :
    (inverseTuning C).b z=0 ↔ z=bRootPlus C ∨ z=bRootMinus C :=
  quadratic_zero_iff _ _ _

@[fun_prop] theorem continuous_aRootPlus : Continuous aRootPlus := by
  unfold aRootPlus
  exact continuous_rootPlus.comp
    (((continuous_const.add (Tuning.continuous_beta.comp continuous_inverseTuning)).sub
      (Tuning.continuous_x.comp continuous_inverseTuning)).prodMk
        (Tuning.continuous_beta.comp continuous_inverseTuning))
@[fun_prop] theorem continuous_aRootMinus : Continuous aRootMinus := by
  unfold aRootMinus
  exact continuous_rootMinus.comp
    (((continuous_const.add (Tuning.continuous_beta.comp continuous_inverseTuning)).sub
      (Tuning.continuous_x.comp continuous_inverseTuning)).prodMk
        (Tuning.continuous_beta.comp continuous_inverseTuning))
@[fun_prop] theorem continuous_bRootPlus : Continuous bRootPlus := by
  unfold bRootPlus
  exact continuous_rootPlus.comp
    (((continuous_const.add (Tuning.continuous_beta.comp continuous_inverseTuning)).sub
      (Tuning.continuous_y.comp continuous_inverseTuning)).prodMk
        (Tuning.continuous_beta.comp continuous_inverseTuning))
@[fun_prop] theorem continuous_bRootMinus : Continuous bRootMinus := by
  unfold bRootMinus
  exact continuous_rootMinus.comp
    (((continuous_const.add (Tuning.continuous_beta.comp continuous_inverseTuning)).sub
      (Tuning.continuous_y.comp continuous_inverseTuning)).prodMk
        (Tuning.continuous_beta.comp continuous_inverseTuning))

theorem bRootPlus_ne_zero (C : CoefficientPoint) : bRootPlus C≠0 := by
  intro hz
  have hh := bRootPlus_zero C
  rw [hz] at hh
  have hb : (inverseTuning C).beta=0 := by exact_mod_cast (by simpa [Tuning.b] using hh : ((inverseTuning C).beta:ℂ)=0)
  exact (inverseBeta_pos C).ne' hb

theorem bRootMinus_ne_zero (C : CoefficientPoint) : bRootMinus C≠0 := by
  intro hz
  have hh := bRootMinus_zero C
  rw [hz] at hh
  have hb : (inverseTuning C).beta=0 := by exact_mod_cast (by simpa [Tuning.b] using hh : ((inverseTuning C).beta:ℂ)=0)
  exact (inverseBeta_pos C).ne' hb

@[fun_prop] theorem continuous_reversedRootPlus : Continuous (fun C : CoefficientPoint=>(bRootPlus C)⁻¹) :=
  continuous_bRootPlus.inv₀ bRootPlus_ne_zero
@[fun_prop] theorem continuous_reversedRootMinus : Continuous (fun C : CoefficientPoint=>(bRootMinus C)⁻¹) :=
  continuous_bRootMinus.inv₀ bRootMinus_ne_zero

theorem root_locations (C : CoefficientPoint) :
    ‖aRootPlus C‖<1 ∧ ‖aRootMinus C‖<1 ∧
      1<‖(bRootPlus C)⁻¹‖ ∧ 1<‖(bRootMinus C)⁻¹‖ := by
  refine ⟨(inverseTuning C).a_root_stable (aRootPlus_zero C),
    (inverseTuning C).a_root_stable (aRootMinus_zero C),?_,?_⟩
  · apply inverse_reversed_b_roots_outside C (inv_ne_zero (bRootPlus_ne_zero C))
    simpa only [inv_inv] using bRootPlus_zero C
  · apply inverse_reversed_b_roots_outside C (inv_ne_zero (bRootMinus_ne_zero C))
    simpa only [inv_inv] using bRootMinus_zero C

end polyak.Levels.Chart
