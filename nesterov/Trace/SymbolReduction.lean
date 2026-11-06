import nesterov.Trace.Reduction
import nesterov.Trace.Circle
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Module.Cardinality

/-! Cancellation preserves the sign of the lag-one symbol, including at
zeros of the canceled common factor by continuity. -/
namespace nesterov.Trace
noncomputable section
open Complex Polynomial Metric Set Real
open scoped Topology
namespace DoubleRootData
variable (A : DoubleRootData)

def unitSymbol (z : ℂ) : ℝ := ((1-z)*eval (A.phi 0) z*star (eval (A.phi 1) z)).re

theorem unitSymbol_continuous : Continuous A.unitSymbol := by unfold unitSymbol eval;fun_prop

theorem unitSymbol_conj (z : ℂ) : A.unitSymbol (star z)=A.unitSymbol z := by
  unfold unitSymbol
  rw [eval_conj,eval_conj,star_star]
  have he : (1-star z)*star (eval (A.phi 0) z)*eval (A.phi 1) z=
      star ((1-z)*eval (A.phi 0) z*star (eval (A.phi 1) z)) := by simp only [star_mul,star_sub,star_one,star_star];ring
  rw [he]
  simp only [Complex.star_def,Complex.conj_re]

theorem unitSymbol_nonneg (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤A.symbol ω) :
    ∀ z : ℂ,Complex.normSq z=1 → 0≤A.unitSymbol z :=
  nonneg_unit_of_upper A.unitSymbol_continuous.continuousOn
    (fun z _=>A.unitSymbol_conj z) hS

theorem symbol_continuous : Continuous A.symbol := by
  change Continuous (fun ω : ℝ=>A.unitSymbol (Complex.exp ((ω:ℂ)*Complex.I)))
  exact A.unitSymbol_continuous.comp (by fun_prop)
end DoubleRootData

namespace CommonReduction
variable {A : DoubleRootData} (R : CommonReduction A)

theorem phi_factor (lam : ℝ) : A.phi lam=R.common*R.reduced.phi lam := by
  unfold DoubleRootData.phi
  rw [R.u_factor,R.v_factor]
  ring

theorem symbol_factor (ω : ℝ) :
    A.symbol ω=Complex.normSq (eval R.common (Complex.exp ((ω:ℂ)*Complex.I)))*R.reduced.symbol ω := by
  dsimp only [DoubleRootData.symbol]
  rw [R.phi_factor 0,R.phi_factor 1,eval_mul,eval_mul]
  have he (z a b r : ℂ) : (1-z)*(r*a)*star (r*b)=
      (r*star r)*((1-z)*a*star b) := by simp only [star_mul];ring
  rw [he]
  rw [Complex.star_def,Complex.mul_conj]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem common_ne_zero : R.common≠0 := by
  intro he
  have hh := R.common_one
  rw [he,Polynomial.eval_zero] at hh
  norm_num at hh

private theorem circle_injOn : Set.InjOn (fun ω : ℝ=>Complex.exp ((ω:ℂ)*Complex.I)) (Icc (0:ℝ) Real.pi) := by
  intro ω hω θ hθ he
  apply Real.strictAntiOn_cos.injOn hω hθ
  have hh := congrArg Complex.re he
  dsimp only at hh
  rw [Complex.exp_mul_I,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin,
    ←Complex.ofReal_cos,←Complex.ofReal_sin] at hh
  simpa only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] using hh

theorem symbol_nonneg (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤A.symbol ω) :
    ∀ ω∈Ioo (0:ℝ) Real.pi,0≤R.reduced.symbol ω := by
  let bad : Set ℝ := {ω|ω∈Icc (0:ℝ) Real.pi ∧ eval R.common (Complex.exp ((ω:ℂ)*Complex.I))=0}
  have hp : R.common.map Complex.ofRealHom≠0 := by
    intro he
    have hh : eval R.common 1=1 := by rw [eval_one,R.common_one];rfl
    simp only [eval,he,Polynomial.eval_zero] at hh
    norm_num at hh
  have hbad : bad.Finite := by
    apply Set.Finite.of_finite_image (f:=fun ω : ℝ=>Complex.exp ((ω:ℂ)*Complex.I))
    · apply (Polynomial.finite_setOfPred_isRoot hp).subset
      rintro z ⟨ω,hω,rfl⟩
      exact hω.2
    · exact fun ω hω θ hθ he=>circle_injOn hω.1 hθ.1 he
  intro ω hω
  by_contra hh
  have hneg : R.reduced.symbol ω<0 := lt_of_not_ge hh
  let s : Set ℝ := Ioo (0:ℝ) Real.pi ∩ {θ|R.reduced.symbol θ<0}
  have hopen : IsOpen s := isOpen_Ioo.inter (isOpen_lt R.reduced.symbol_continuous continuous_const)
  have hcount : bad.Countable := hbad.countable
  obtain ⟨θ,hθ,hnot⟩ := hcount.dense_compl ℝ |>.inter_open_nonempty s hopen ⟨ω,hω,hneg⟩
  have hr : eval R.common (Complex.exp ((θ:ℂ)*Complex.I))≠0 := by
    intro he
    exact hnot ⟨⟨hθ.1.1.le,hθ.1.2.le⟩,he⟩
  have hpos := Complex.normSq_pos.mpr hr
  have hval := hS θ hθ.1
  rw [R.symbol_factor] at hval
  exact (not_lt_of_ge hval) (mul_neg_of_pos_of_neg hpos hθ.2)

end CommonReduction
end
end nesterov.Trace
