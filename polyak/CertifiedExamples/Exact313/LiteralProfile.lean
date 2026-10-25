import polyak.CertifiedExamples.Exact313.SystemSemantics
import polyak.CertifiedExamples.Exact313.SourceLag
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The original left-kernel lag symbol is an explicitly nonzero radial
factor times the denominator-cleared polynomial contact profile. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels ModeLocking.TwoLag Set Filter
open scoped Topology

def rawNumerator (z : CoefficientVector) (n : ℤ) (x : ℝ) : ℝ :=
  vectorXi z (Real.cos x)*(1-Real.cos ((n:ℝ)*x))-Real.sin x*Real.sin ((n:ℝ)*x)
def sourceRadius (z : CoefficientVector) (x : ℝ) : ℝ :=
  Real.sqrt (vectorXi z (Real.cos x)^2+Real.sin x^2)

theorem radius_argument_positive (z : CoefficientVector) {x : ℝ} (hx : x∈Ioo 0 Real.pi) :
    0<vectorXi z (Real.cos x)^2+Real.sin x^2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2))

theorem sourceRadius_positive (z : CoefficientVector) {x : ℝ} (hx : x∈Ioo 0 Real.pi) :
    0<sourceRadius z x := Real.sqrt_pos.mpr (radius_argument_positive z hx)

theorem u_interior : u∈Ioo 0 Real.pi := by constructor <;> dsimp [u] <;> linarith [Real.pi_pos]
theorem v_interior : v∈Ioo 0 Real.pi := by constructor <;> dsimp [v] <;> linarith [Real.pi_pos]

theorem raw_one (z : CoefficientVector) (x : ℝ) :
    rawNumerator z 1 x=(1-Real.cos x)*(vectorXi z (Real.cos x)-(1+Real.cos x)) := by
  dsimp [rawNumerator]
  norm_num
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem raw_minus_four (z : CoefficientVector) (x : ℝ) :
    rawNumerator z (-4) x=(1-Real.cos x)*
      (vectorXi z (Real.cos x)*(8*Real.cos x^2*(1+Real.cos x))+
        (1+Real.cos x)*(8*Real.cos x^3-4*Real.cos x)) := by
  have hT := W_identity 4 (Real.cos x)
  rw [W_four,Spectral.chebT_cos] at hT
  norm_num only [Nat.cast_ofNat] at hT
  have hU := Spectral.chebU_sin 3 x
  rw [U_three] at hU
  norm_num at hU
  have hs : Real.sin x*Real.sin (4*x)=
      (1-Real.cos x^2)*(8*Real.cos x^3-4*Real.cos x) := by
    rw [←hU]
    have hsq : Real.sin x^2=1-Real.cos x^2 := by linarith [Real.sin_sq_add_cos_sq x]
    rw [←hsq]
    ring
  dsimp [rawNumerator]
  norm_num only [Int.cast_neg,Int.cast_ofNat,neg_mul,Real.cos_neg,Real.sin_neg,mul_neg,sub_neg_eq_add]
  rw [←hT,hs]
  ring

def radialFactor (z : CoefficientVector) (x : ℝ) : ℝ :=
  (-(1-c₁)/sourceRadius z u)*((1-Real.cos x)/sourceRadius z x)

def literalSymbol (z : CoefficientVector) (x : ℝ) : ℝ :=
  (-rawNumerator z (-4) u/sourceRadius z u)*(rawNumerator z 1 x/sourceRadius z x)+
    (rawNumerator z 1 u/sourceRadius z u)*(rawNumerator z (-4) x/sourceRadius z x)

theorem literalSymbol_factor (z : CoefficientVector) (x : ℝ) :
    literalSymbol z x=radialFactor z x*contactProfile z (Real.cos x) := by
  rw [literalSymbol,raw_one,raw_one,raw_minus_four,raw_minus_four]
  dsimp [radialFactor,contactProfile,ratioNumerator,ratioDenominator,c₁]
  simp only [div_eq_mul_inv]
  ring

theorem contactProfile_first_zero (z : CoefficientVector) : contactProfile z c₁=0 := by
  dsimp [contactProfile,ratioNumerator,ratioDenominator]
  ring

def radiusSlope (z : CoefficientVector) (x : ℝ) : ℝ :=
  (vectorXi z (Real.cos x)*vectorXiD z (Real.cos x)*(-Real.sin x)+
    Real.sin x*Real.cos x)/sourceRadius z x

def radialFactorSlope (z : CoefficientVector) (x : ℝ) : ℝ :=
  (-(1-c₁)/sourceRadius z u)*
    ((Real.sin x*sourceRadius z x-(1-Real.cos x)*radiusSlope z x)/(sourceRadius z x)^2)

theorem sourceRadius_hasDerivAt (z : CoefficientVector) {x : ℝ} (hx : x∈Ioo 0 Real.pi) :
    HasDerivAt (sourceRadius z) (radiusSlope z x) x := by
  have hXi := (vectorXi_hasDerivAt z (Real.cos x)).comp x (Real.hasDerivAt_cos x)
  have hs := ((hXi.pow 2).add (Real.hasDerivAt_sin x |>.pow 2)).sqrt
    (radius_argument_positive z hx).ne'
  convert hs using 1
  · rfl
  · dsimp [radiusSlope,sourceRadius]
    field_simp [(sourceRadius_positive z hx).ne']

theorem radialFactor_hasDerivAt (z : CoefficientVector) {x : ℝ} (hx : x∈Ioo 0 Real.pi) :
    HasDerivAt (radialFactor z) (radialFactorSlope z x) x := by
  have hn : HasDerivAt (fun x:ℝ=>1-Real.cos x) (Real.sin x) x := by
    convert (hasDerivAt_const x 1).sub (Real.hasDerivAt_cos x) using 1
    simp
  exact ((hn.div (sourceRadius_hasDerivAt z hx) (sourceRadius_positive z hx).ne').const_mul
    (-(1-c₁)/sourceRadius z u))

theorem literalSymbol_hasDerivAt (z : CoefficientVector) {x : ℝ} (hx : x∈Ioo 0 Real.pi) :
    HasDerivAt (literalSymbol z)
      (radialFactorSlope z x*contactProfile z (Real.cos x)+
        radialFactor z x*(profileSlope z (Real.cos x)*(-Real.sin x))) x := by
  have h := (radialFactor_hasDerivAt z hx).mul
    ((profile_hasDerivAt z (Real.cos x)).comp x (Real.hasDerivAt_cos x))
  have he : literalSymbol z=(fun x=>radialFactor z x*contactProfile z (Real.cos x)) :=
    funext (literalSymbol_factor z)
  change HasDerivAt (fun x=>radialFactor z x*contactProfile z (Real.cos x)) _ x at h
  rwa [←he] at h

def literalMatrix (z : CoefficientVector) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![radialFactor z v,0,0;
    0,radialFactor z u*(-Real.sin u),0;
    radialFactorSlope z v,0,radialFactor z v*(-Real.sin v)]

def literalContactSystem (z : CoefficientVector) : CoefficientVector :=
  ![literalSymbol z v,deriv (literalSymbol z) u,deriv (literalSymbol z) v]

theorem literalContactSystem_eq (z : CoefficientVector) :
    literalContactSystem z=(literalMatrix z).mulVec (contactSystem z) := by
  ext i
  fin_cases i
  all_goals
    norm_num [literalContactSystem,literalMatrix,contactSystem,Matrix.mulVec,Fin.sum_univ_succ]
  · rw [literalSymbol_factor]
    rfl
  · rw [(literalSymbol_hasDerivAt z u_interior).deriv]
    change radialFactorSlope z u*contactProfile z c₁+
      radialFactor z u*(profileSlope z c₁*(-Real.sin u))=_
    rw [contactProfile_first_zero,mul_zero,zero_add]
    ring
  · rw [(literalSymbol_hasDerivAt z v_interior).deriv]
    dsimp [c₂]
    ring

end polyak.CertifiedExamples.Exact313
