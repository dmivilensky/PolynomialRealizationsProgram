import nesterov.Attainment.BoundaryDual

/-! Strict minimizer reserve removes both infinity labels; a finite active-lag
bound therefore concentrates the actual dual probability measure on a finite
set of signed finite lags. -/
noncomputable section
open MeasureTheory Set
open scoped Topology OnePoint
namespace nesterov.Attainment
open Spectral

namespace ExponentFrame
variable {t : ℝ} (F : ExponentFrame t)

theorem meanA_center (ν : Spectrum) (a : SymbolPair) (n : ℕ) :
    meanA ν a F.center n=meanA ν a t n := by
  conv_rhs => rw [← F.physical]
  rcases F.sign_cases with hs | hs <;>
    simp only [meanA,lagA,center,hs,one_mul,neg_one_mul,mul_neg,Real.cosh_neg]

theorem sinh_physical (n : ℕ) : Real.sinh (n*t)=F.sign*Real.sinh (n*(F.center : ℝ)) := by
  conv_lhs => rw [← F.physical]
  rcases F.sign_cases with hs | hs <;>
    simp only [center,hs,one_mul,neg_one_mul,mul_neg,Real.sinh_neg]

end ExponentFrame

namespace BoundaryDual
variable {M : StationaryMethod} {μ L : ℝ} (B : BoundaryDual M μ L)

set_option backward.isDefEq.respectTransparency false in
theorem normalizedSlack_infty (ν : Spectrum) (C : ℝ) (b : Bool) :
    B.normalizedSlack ν C (b,∞) =
      meanG ν (M.symbolPair μ L (Closure.T M μ L))+(if b then -1 else 1)*(B.frame.sign*C) := by
  change dualMomentCLM _ _ _ _ _ _
    (dualFamily B.frame.lo B.frame.hi (half_pos B.frame.radius_pos)
      (gapEntireMap M.queryPolynomial (M.normalizedPolynomial μ L) B.frame.lo B.frame.hi B.frame.sign)
      (skewEntireMap M.queryPolynomial (M.normalizedPolynomial μ L) B.frame.lo B.frame.hi B.frame.sign)
      (if b then -1 else 1) ∞) = _
  erw [dualMomentCLM_apply,dualFamily_charge]
  simp_rw [dualFamily_physical_infty,Complex.ofReal_re,B.pair_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem normalizedSlack_coe (ν : Spectrum) (C : ℝ) (b : Bool) (n : ℕ) :
    B.normalizedSlack ν C (b,(n : OnePoint ℕ)) =
      (if b then
        (meanA ν (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) (n+1)+
          meanB ν (M.symbolPair μ L (Closure.T M μ L)) (n+1)-C*Real.sinh ((n+1 : ℕ)*Closure.T M μ L)) /
            Real.sinh ((n+1 : ℕ)*(B.frame.center : ℝ))
       else
        (meanA ν (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) (n+1)-
          meanB ν (M.symbolPair μ L (Closure.T M μ L)) (n+1)+C*Real.sinh ((n+1 : ℕ)*Closure.T M μ L)) /
            Real.sinh ((n+1 : ℕ)*(B.frame.center : ℝ))) := by
  change dualMomentCLM _ _ _ _ _ _
    (dualFamily B.frame.lo B.frame.hi (half_pos B.frame.radius_pos)
      (gapEntireMap M.queryPolynomial (M.normalizedPolynomial μ L) B.frame.lo B.frame.hi B.frame.sign)
      (skewEntireMap M.queryPolynomial (M.normalizedPolynomial μ L) B.frame.lo B.frame.hi B.frame.sign)
      (if b then -1 else 1) (n : OnePoint ℕ)) = _
  erw [dualMomentCLM_apply,dualFamily_charge]
  simp_rw [dualFamily_physical_coe,Complex.ofReal_re,B.pair_eq]
  rw [integral_div, integral_sub
    (polyak.Spectral.integrable_continuous ν (continuous_lagA _ _ _))
    ((polyak.Spectral.integrable_continuous ν (continuous_lagB _ _)).const_mul _),integral_const_mul]
  change (meanA ν (M.symbolPair μ L (Closure.T M μ L)) B.frame.center (n+1)-
    (if b then -1 else 1)*meanB ν (M.symbolPair μ L (Closure.T M μ L)) (n+1)) /
      Real.sinh ((n+1 : ℕ)*(B.frame.center : ℝ))+(if b then -1 else 1)*(B.frame.sign*C) = _
  rw [B.frame.meanA_center,B.frame.sinh_physical]
  have hd : Real.sinh ((n+1 : ℕ)*(B.frame.center : ℝ)) ≠ 0 := ne_of_gt
    (Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) B.frame.radius_pos))
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul,sub_neg_eq_add]
  all_goals field_simp [hd]
  all_goals ring

end BoundaryDual

def lowerSlack (M : StationaryMethod) (μ L t : ℝ) (ν : Spectrum) (C : ℝ) (n : ℕ) : ℝ :=
  meanA ν (M.symbolPair μ L t) t n-meanB ν (M.symbolPair μ L t) n+C*Real.sinh (n*t)

def upperSlack (M : StationaryMethod) (μ L t : ℝ) (ν : Spectrum) (C : ℝ) (n : ℕ) : ℝ :=
  meanA ν (M.symbolPair μ L t) t n+meanB ν (M.symbolPair μ L t) n-C*Real.sinh (n*t)

def activeLags (M : StationaryMethod) (μ L t : ℝ) (ν : Spectrum) (C : ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧ (lowerSlack M μ L t ν C n=0 ∨ upperSlack M μ L t ν C n=0)}

def finiteLagLabels (N : ℕ) : Set DualLabel :=
  Set.range (fun i : Bool × Fin N => (i.1,((i.2.val : ℕ) : OnePoint ℕ)))

theorem finiteLagLabels_finite (N : ℕ) : (finiteLagLabels N).Finite := Set.finite_range _

/-- Any bound on the active lags of one optimal pair bounds the support of
one common dual measure, which consequently works for all optimal pairs. -/
theorem BoundaryDual.measure_finite_lags {M : StationaryMethod} {μ L : ℝ}
    (B : BoundaryDual M μ L) {ν : Spectrum} {C : ℝ}
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C)
    (hstar : |C| < meanG ν (M.symbolPair μ L (Closure.T M μ L)))
    {N : ℕ} (hN : ∀ n ∈ activeLags M μ L (Closure.T M μ L) ν C, n ≤ N) :
    (B.Λ : Measure DualLabel) (finiteLagLabels N)ᶜ=0 := by
  have hsub : {l | B.normalizedSlack ν C l=0} ⊆ finiteLagLabels N := by
    rintro ⟨b,l⟩ hl
    change B.normalizedSlack ν C (b,l)=0 at hl
    induction l using OnePoint.rec with
    | infty =>
      rw [B.normalizedSlack_infty] at hl
      have hsign : |B.frame.sign*C|=|C| := by
        rcases B.frame.sign_cases with hs | hs <;> simp only [hs,one_mul,neg_one_mul,abs_neg]
      have hC := abs_lt.mp (by rw [hsign]; exact hstar)
      cases b <;> simp only [Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul] at hl <;> linarith [hC.1,hC.2]
    | coe n =>
      rw [B.normalizedSlack_coe] at hl
      have hzero : lowerSlack M μ L (Closure.T M μ L) ν C (n+1)=0 ∨
          upperSlack M μ L (Closure.T M μ L) ν C (n+1)=0 := by
        cases b
        · exact Or.inl ((div_eq_zero_iff).mp hl |>.resolve_right (ne_of_gt
            (Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) B.frame.radius_pos))))
        · exact Or.inr ((div_eq_zero_iff).mp hl |>.resolve_right (ne_of_gt
            (Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) B.frame.radius_pos))))
      have hn := hN (n+1) ⟨Nat.succ_pos _,hzero⟩
      exact ⟨(b,⟨n,by omega⟩),rfl⟩
  exact measure_mono_null (Set.compl_subset_compl.mpr hsub) (B.measure_active h)

end nesterov.Attainment
