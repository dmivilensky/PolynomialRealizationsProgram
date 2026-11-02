import jacobi.Complex.FiniteJensen
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Article: jacobi, Proposition 2.2.
Sixteen equal blocks retain enough of the complete logarithmic zero
mass to contradict exponential type one half. All constants below are
exact mathematical inequalities. There is no numerical root count,
asymptotic zero-count premise or finite verification certificate.
Source: Levin, Distribution of Zeros of Entire Functions, Jensen's formula.
Use: a fixed positive excess over the source exponential type gives the entire-function uniqueness contradiction.
-/
namespace jacobi.Complex
noncomputable section
open Real Set Metric
open scoped Topology

/-- The exact logarithmic mass of sixteen consecutive equal zero blocks.
Use: a fixed positive excess over the source exponential type gives the entire-function uniqueness contradiction.
Article: jacobi, Proposition 2.2.
-/
def blockLogMass : ℝ := ∑ j:Fin 16,Real.log (16/(j.val+1:ℝ))

/-- The genuine sixteen-block logarithmic mass is strictly larger than thirteen.
Use: its doubled value exceeds eight pi, the actual radius growth of a function of exponential type one half.
Article: jacobi, Proposition 2.2.
Source: elementary logarithm identities and the community bound exp(1)<11/4.
Proof: the sum is the logarithm of the exact rational product
16^16/16!. The actual exponential of thirteen is smaller, by the
proved community exponential bound and exact rational arithmetic. -/
theorem blockLogMass_gt : 13<blockLogMass := by
  -- This finite calculation bounds a universal constant, never the article's spectral data.
  have hprod : (∏ j:Fin 16,(16/(j.val+1:ℝ)))=(16:ℝ)^16/(Nat.factorial 16:ℝ) := by
    norm_num [Fin.prod_univ_succ,Nat.factorial]
  have hlog : blockLogMass=Real.log ((16:ℝ)^16/(Nat.factorial 16:ℝ)) := by
    unfold blockLogMass
    rw [← Real.log_prod (fun j _ => by positivity),hprod]
  rw [hlog,← Real.exp_lt_exp,Real.exp_log (by positivity)]
  calc
    Real.exp 13 = (Real.exp 1)^13 := by
      simp [← Real.exp_nat_mul]
    _ < (11/4:ℝ)^13 := pow_lt_pow_left₀
      (by linarith [Real.exp_one_lt_d9]) (Real.exp_pos 1).le (by norm_num)
    _ < _ := by norm_num [Nat.factorial]

/-- A strictly increasing positive real root sequence gives distinct actual roots after including both signs.
Use: the Jensen logarithmic sum counts each original positive and negative Bessel frequency exactly once.
Article: jacobi, Proposition 2.2.
Source: positivity and strict enumeration of real zeros.
Proof: equal signs reduce to injectivity of the original root sequence. Opposite signs contradict strict positivity. -/
theorem signed_roots_injective {x : ℕ → ℝ} (hx : StrictMono x) (hp : ∀ k,0<x k) :
    Function.Injective (fun p:Bool×ℕ => if p.1 then (x p.2:ℂ) else -(x p.2:ℂ)) := by
  -- Strict positivity excludes the two opposite-sign cases before using the original zero enumeration.
  rintro ⟨b,k⟩ ⟨d,l⟩ h
  cases b <;> cases d
  · change -(x k:ℂ)=-(x l:ℂ) at h
    have he := hx.injective (Complex.ofReal_injective (neg_injective h))
    subst l
    rfl
  · change -(x k:ℂ)=(x l:ℂ) at h
    have he := congrArg Complex.re h
    simp only [Complex.neg_re,Complex.ofReal_re] at he
    linarith [hp k,hp l]
  · change (x k:ℂ)=-(x l:ℂ) at h
    have he := congrArg Complex.re h
    simp only [Complex.neg_re,Complex.ofReal_re] at he
    linarith [hp k,hp l]
  · change (x k:ℂ)=(x l:ℂ) at h
    have he := hx.injective (Complex.ofReal_injective h)
    subst l
    rfl

end
end jacobi.Complex
