import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Article: Lemma `lem:spread`, midpoint approximation of the spread spectrum.
Use: a uniform Lipschitz estimate gives an explicit quadrature error, with
one grid working simultaneously for every lag in a compact band.
-/
namespace nesterov.Flow
noncomputable section
open Finset Set intervalIntegral

def midpoint (J : ℕ) (j : ℕ) : ℝ := 1+((j:ℝ)+1/2)/(J:ℝ)
def grid (J : ℕ) (j : ℕ) : ℝ := 1+(j:ℝ)/(J:ℝ)
def midpointAverage (J : ℕ) (f : ℝ→ℝ) : ℝ :=
  (1/(J:ℝ))*∑ j∈range J,f (midpoint J j)

theorem midpoint_error {J : ℕ} (hJ : 0<J) {f : ℝ→ℝ} (hf : Continuous f)
    {K : ℝ} (hK : 0≤K)
    (hlip : ∀ x∈Icc (1:ℝ) 2,∀ y∈Icc (1:ℝ) 2,|f x-f y|≤K*|x-y|) :
    |(∫ x in (1:ℝ)..2,f x)-midpointAverage J f|≤K/(2*J) := by
  have hJp : (0:ℝ)<J := Nat.cast_pos.mpr hJ
  have hJn : (J:ℝ)≠0 := ne_of_gt hJp
  have hcell (j : ℕ) (hj : j<J) :
      |(∫ x in grid J j..grid J (j+1),f x)-(1/(J:ℝ))*f (midpoint J j)|≤K/(2*J^2) := by
    have hj' : (j:ℝ)+1≤J := by exact_mod_cast hj
    have hends : grid J j≤grid J (j+1) := by
      dsimp [grid]
      push_cast
      rw [add_div]
      linarith [div_pos zero_lt_one hJp]
    have hmid : midpoint J j∈Icc (1:ℝ) 2 := by
      dsimp [midpoint]
      constructor
      · exact le_add_of_nonneg_right (div_nonneg (by positivity) hJp.le)
      · have hh : ((j:ℝ)+1/2)/(J:ℝ)≤1 := (div_le_one hJp).mpr (by linarith)
        linarith
    have hi (x : ℝ) (hx : x∈uIoc (grid J j) (grid J (j+1))) :
        ‖f x-f (midpoint J j)‖≤K/(2*J) := by
      rw [uIoc_of_le hends] at hx
      have hx' : x∈Icc (1:ℝ) 2 := by
        constructor
        · exact (show 1≤grid J j from le_add_of_nonneg_right
            (div_nonneg (Nat.cast_nonneg j) hJp.le)).trans hx.1.le
        · apply hx.2.trans
          dsimp [grid]
          have hh : ((j+1:ℕ):ℝ)/(J:ℝ)≤1 := (div_le_one hJp).mpr (by exact_mod_cast hj)
          linarith
      have hdist : |x-midpoint J j|≤1/(2*J) := by
        apply abs_le.mpr
        have hlo := hx.1
        have hhi := hx.2
        dsimp [grid] at hlo hhi
        push_cast at hhi
        rw [add_div] at hhi
        dsimp [midpoint]
        rw [add_div]
        have hhalf : (1/2:ℝ)/(J:ℝ)=1/(2*J) := by ring
        have hfull : (1:ℝ)/(J:ℝ)=2*(1/(2*J)) := by ring
        rw [hhalf]
        rw [hfull] at hhi
        constructor <;> linarith
      rw [Real.norm_eq_abs]
      calc
        _ ≤ K*|x-midpoint J j| := hlip x hx' _ hmid
        _ ≤ K*(1/(2*J)) := mul_le_mul_of_nonneg_left hdist hK
        _ = _ := by ring
    have hh := norm_integral_le_of_norm_le_const hi
    rw [integral_sub (hf.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
      integral_const,Real.norm_eq_abs] at hh
    have hd : grid J (j+1)-grid J j=1/(J:ℝ) := by dsimp [grid]; push_cast; ring
    rw [hd,smul_eq_mul,abs_of_pos (div_pos zero_lt_one hJp)] at hh
    convert hh using 1
    field_simp
  have hsum := sum_integral_adjacent_intervals (μ:=MeasureTheory.volume) (a:=grid J) (n:=J)
    (fun j _ => hf.intervalIntegrable (grid J j) (grid J (j+1)))
  have hg0 : grid J 0=1 := by simp [grid]
  have hgJ : grid J J=2 := by simp [grid,hJn]; norm_num
  rw [hg0,hgJ] at hsum
  rw [←hsum,midpointAverage,mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _j∈range J,K/(2*(J:ℝ)^2) := sum_le_sum (fun j hj => hcell j (mem_range.mp hj))
    _ = _ := by simp; field_simp

end
end nesterov.Flow
