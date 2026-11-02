import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Article: main_krylov, prop:cond, exact scalar conditional radii.
Use: retain the printed constants and all zero-defect endpoints. The
source equality clause needs its additional zero-defect branch, proved
here explicitly. Source: scalar Schur completion algebra; Davis--Kahan--
Weinberger (1982), with the existing full completion theorem reused later.
-/
namespace krylov.XR
noncomputable section

/-- The literal known-base two-pair conditional radius.
Article: main_krylov, prop:cond(a). -/
def knownConditionalRadius (ω δ k fresh : ℝ) : ℝ := ω-δ^2/(ω+|k|)+fresh

/-- The literal data-only two-pair conditional radius.
Article: main_krylov, prop:cond(b). -/
def unknownConditionalRadius (ω δ fresh : ℝ) : ℝ :=
  (δ^2+Real.sqrt (4*ω^2-4*δ^2+δ^4))/2+fresh

/-- The scalar Schur feasibility condition gives exactly the bounds on
the revealed hidden diagonal used by the conditional radius.
Article: main_krylov, prop:cond(a). -/
theorem conditional_feasible_diagonal {ω δ k : ℝ} (hω : 0≤ω)
    (hfeasible : δ^2+k^2≤ω^2) :
    0≤ω^2-δ^2 ∧ |k|≤Real.sqrt (ω^2-δ^2) ∧ Real.sqrt (ω^2-δ^2)≤ω := by
  have hr : 0≤ω^2-δ^2 := by nlinarith [sq_nonneg k]
  have hs := Real.sq_sqrt hr
  refine ⟨hr,?_,?_⟩
  · nlinarith [sq_abs k,abs_nonneg k,Real.sqrt_nonneg (ω^2-δ^2)]
  · nlinarith [Real.sqrt_nonneg (ω^2-δ^2),sq_nonneg δ]

/-- The exact gap between both printed known-base bounds factors into
the two nonnegative Schur margins. Article: main_krylov, prop:cond(a). -/
theorem conditional_radius_gap {ω δ k : ℝ} (hω : 0<ω)
    (hfeasible : δ^2+k^2≤ω^2) :
    Real.sqrt (ω^2-δ^2)-(ω-δ^2/(ω+|k|))=
      (ω-Real.sqrt (ω^2-δ^2))*(Real.sqrt (ω^2-δ^2)-|k|)/(ω+|k|) := by
  have hr := (conditional_feasible_diagonal hω.le hfeasible).1
  have hs := Real.sq_sqrt hr
  have hd : ω+|k|≠0 := ne_of_gt (by positivity)
  apply (eq_div_iff hd).mpr
  field_simp
  nlinarith only [hs]

/-- The original square-root upper bound, with its exact zero-inclusive
equality criterion. The source omits the delta=0 branch in its iff.
Article: main_krylov, prop:cond(a), corrected boundary clause. -/
theorem knownConditionalRadius_bound {ω δ k fresh : ℝ} (hω : 0<ω)
    (hfeasible : δ^2+k^2≤ω^2) :
    knownConditionalRadius ω δ k fresh≤Real.sqrt (ω^2-δ^2)+fresh ∧
    (knownConditionalRadius ω δ k fresh=Real.sqrt (ω^2-δ^2)+fresh ↔
      δ=0 ∨ |k|=Real.sqrt (ω^2-δ^2)) := by
  obtain ⟨hr,hkr,hrω⟩ := conditional_feasible_diagonal hω.le hfeasible
  have hd : 0<ω+|k| := by positivity
  have hg := conditional_radius_gap hω hfeasible
  have hgap : 0≤(ω-Real.sqrt (ω^2-δ^2))*(Real.sqrt (ω^2-δ^2)-|k|)/(ω+|k|) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hrω) (sub_nonneg.mpr hkr)) hd.le
  have hfirst : ω-Real.sqrt (ω^2-δ^2)=0 ↔ δ=0 := by
    constructor
    · intro hh
      have hs := Real.sq_sqrt hr
      nlinarith
    · intro hh
      rw [hh]
      norm_num
      rw [Real.sqrt_sq hω.le,sub_self]
  constructor
  · dsimp only [knownConditionalRadius]
    linarith
  · constructor
    · intro hh
      have hz : (ω-Real.sqrt (ω^2-δ^2))*(Real.sqrt (ω^2-δ^2)-|k|)=0 := by
        have hz' : (ω-Real.sqrt (ω^2-δ^2))*(Real.sqrt (ω^2-δ^2)-|k|)/(ω+|k|)=0 := by
          dsimp only [knownConditionalRadius] at hh
          linarith
        exact (div_eq_zero_iff.mp hz').resolve_right hd.ne'
      rcases mul_eq_zero.mp hz with hf|hs
      · exact Or.inl (hfirst.mp hf)
      · exact Or.inr (by linarith)
    · intro hh
      have hz : (ω-Real.sqrt (ω^2-δ^2))*(Real.sqrt (ω^2-δ^2)-|k|)=0 := by
        rcases hh with hf|hs
        · rw [hfirst.mpr hf,zero_mul]
        · rw [hs,sub_self,mul_zero]
      rw [hz,zero_div] at hg
      dsimp only [knownConditionalRadius]
      linarith

/-- For a fixed revealed diagonal the true known-base radius decreases
strictly with the modulus of the defect. Article: prop:cond. -/
theorem knownConditionalRadius_strictAnti {ω k fresh a b : ℝ} (hω : 0<ω)
    (ha : 0≤a) (hab : a<b) :
    knownConditionalRadius ω b k fresh<knownConditionalRadius ω a k fresh := by
  have hd : 0<ω+|k| := by positivity
  have hs : a^2<b^2 := by nlinarith
  have hh := (div_lt_div_iff_of_pos_right hd).mpr hs
  dsimp only [knownConditionalRadius]
  linarith

/-- Zero observed defect gives exactly the unconditioned total budget,
independently of the revealed hidden diagonal. Article: prop:cond. -/
theorem knownConditionalRadius_zero (ω k fresh : ℝ) : knownConditionalRadius ω 0 k fresh=ω+fresh := by
  simp [knownConditionalRadius]

/-- The data-only radius has the same exact zero-defect endpoint.
Article: main_krylov, prop:cond(b). -/
theorem unknownConditionalRadius_zero {ω : ℝ} (hω : 0≤ω) (fresh : ℝ) :
    unknownConditionalRadius ω 0 fresh=ω+fresh := by
  have he : 4*ω^2=(2*ω)^2 := by ring
  have hs : Real.sqrt (4*ω^2)=2*ω := by rw [he,Real.sqrt_sq (by positivity : 0≤2*ω)]
  simp [unknownConditionalRadius,hs]

/-- A vanishing old budget forces both revealed defect and diagonal
increment to vanish, with no division by a zero budget. Article: prop:cond. -/
theorem conditional_zero_budget {δ k : ℝ} (hfeasible : δ^2+k^2≤(0 : ℝ)^2) : δ=0 ∧ k=0 := by
  constructor <;> nlinarith [sq_nonneg δ,sq_nonneg k]

end
end krylov.XR
