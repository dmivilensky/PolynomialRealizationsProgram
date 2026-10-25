import polyak.Farey.Examples.ThirteenContracts
import chebyshev2.Numerics.IntervalExpr

/-! Independent source arithmetic for the period-thirteen example. The data
checker sees only a rational polynomial in the actual root-of-unity coordinates.
The equality with the original probability-weighted source slacks is proved here. -/
noncomputable section
namespace polyak.CertifiedExamples.Rational
open polyak.Farey.Examples polyak.Levels chebyshev2.Numerics

def gridCos (j:ℕ) : ℝ := Real.cos (2*Real.pi*j/13)
def gridSin (j:ℕ) : ℝ := Real.sin (2*Real.pi*j/13)

theorem gridCos_mod (j:ℕ) : gridCos j=gridCos (j%13) := by
  unfold gridCos
  have hj : (j:ℝ)=(j%13:ℕ)+(j/13:ℕ)*13 := by
    exact_mod_cast (show j=j%13+j/13*13 by have h:=(Nat.mod_add_div j 13); omega)
  have he : 2*Real.pi*j/13=2*Real.pi*(j%13:ℕ)/13+(j/13:ℕ)*(2*Real.pi) := by
    rw [hj]; ring
  rw [he,Real.cos_add_nat_mul_two_pi]

theorem gridSin_mod (j:ℕ) : gridSin j=gridSin (j%13) := by
  unfold gridSin
  have hj : (j:ℝ)=(j%13:ℕ)+(j/13:ℕ)*13 := by
    exact_mod_cast (show j=j%13+j/13*13 by have h:=(Nat.mod_add_div j 13); omega)
  have he : 2*Real.pi*j/13=2*Real.pi*(j%13:ℕ)/13+(j/13:ℕ)*(2*Real.pi) := by
    rw [hj]; ring
  rw [he,Real.sin_add_nat_mul_two_pi]

def thirteenCoordinates (i:Fin 26) : ℝ :=
  if i.val<13 then gridCos i.val else gridSin (i.val-13)

def cosExpression (j:Fin 13) : IntervalExpr 26 := .variable ⟨j.val,by omega⟩
def sinExpression (j:Fin 13) : IntervalExpr 26 := .variable ⟨j.val+13,by omega⟩

theorem cosExpression_value (j:Fin 13) :
    (cosExpression j).value thirteenCoordinates=gridCos j.val := by
  simp [cosExpression,IntervalExpr.value,thirteenCoordinates,j.isLt]

theorem sinExpression_value (j:Fin 13) :
    (sinExpression j).value thirteenCoordinates=gridSin j.val := by
  simp [sinExpression,IntervalExpr.value,thirteenCoordinates,show ¬j.val+13<13 by omega]

def xiExpression (j:Fin 13) : IntervalExpr 26 :=
  .add (.literal (88897198775653/91052250190902))
    (.add (.mul (.literal (242832333719/122711927481)) (cosExpression j))
      (.neg (.mul (.literal (26156560000/8676600933)) (.power (cosExpression j) 2))))

theorem xiExpression_value (j:Fin 13) :
    (xiExpression j).value thirteenCoordinates=thirteenTuning.Xi (gridCos j.val) := by
  simp only [xiExpression,IntervalExpr.value,cosExpression_value]
  rw [←thirteen_Xi_source_exact]
  norm_num [thirteenXiSource]
  ring

def normalizedMinExpression : IntervalExpr 26 :=
  .add (.mul (.literal (149/797)) (xiExpression ⟨2,by decide⟩))
    (.mul (.literal (648/797)) (xiExpression ⟨3,by decide⟩))

def singleLagExpression (j:Fin 13) (n:ℕ) : IntervalExpr 26 :=
  .add (.mul (xiExpression j)
    (.add (.literal 1) (.neg (cosExpression ⟨(n*j.val)%13,Nat.mod_lt _ (by decide)⟩))))
    (.neg (.mul (sinExpression j) (sinExpression ⟨(n*j.val)%13,Nat.mod_lt _ (by decide)⟩)))

def normalizedLagExpression (n:ℕ) : IntervalExpr 26 :=
  .add (.mul (.literal (149/797)) (singleLagExpression ⟨2,by decide⟩ n))
    (.mul (.literal (648/797)) (singleLagExpression ⟨3,by decide⟩ n))

def normalizationFactor : ℝ := 2*(1-thirteenTuning.beta)/thirteenTuning.B

theorem normalizationFactor_pos : 0<normalizationFactor := by
  unfold normalizationFactor
  positivity [thirteenTuning.beta_lt_one,thirteenTuning.B_pos]

private theorem raw_g (b:Bool) : sourceG thirteenTuning (thirteenFrequency b)=
    normalizationFactor*thirteenTuning.Xi (Real.cos (thirteenFrequency b)) := by
  change 1-Complex.normSq (angleMultiplier _ _)=_
  rw [angleMultiplier_eq,General.Tuning.g_threshold]
  rfl

private theorem raw_im (b:Bool) : 2*(angleMultiplier thirteenTuning (thirteenFrequency b)).im=
    normalizationFactor*Real.sin (thirteenFrequency b) := by
  rw [angleMultiplier_eq,General.Tuning.m_threshold_im]
  unfold normalizationFactor
  ring

theorem thirteen_min_source : thirteenRawMin=
    normalizationFactor*normalizedMinExpression.value thirteenCoordinates := by
  unfold thirteenRawMin
  simp only [Fintype.sum_bool,raw_g,normalizedMinExpression,IntervalExpr.value,xiExpression_value]
  norm_num [thirteenNuWeight,thirteenFrequency,gridCos]
  ring

private theorem singleLagExpression_value (j:Fin 13) (n:ℕ) :
    (singleLagExpression j n).value thirteenCoordinates=
      thirteenTuning.Xi (gridCos j.val)*(1-gridCos (n*j.val))-
        gridSin j.val*gridSin (n*j.val) := by
  simp only [singleLagExpression,IntervalExpr.value,xiExpression_value,
    cosExpression_value,sinExpression_value]
  rw [gridCos_mod (n*j.val),gridSin_mod (n*j.val)]
  ring

private theorem lag_angle_cos (n j:ℕ) :
    Real.cos ((n:ℝ)*(2*Real.pi*j/13))=gridCos (n*j) := by
  unfold gridCos
  push_cast
  congr 1
  ring

private theorem lag_angle_sin (n j:ℕ) :
    Real.sin ((n:ℝ)*(2*Real.pi*j/13))=gridSin (n*j) := by
  unfold gridSin
  push_cast
  congr 1
  ring

theorem thirteen_lag_source (n:ℕ) : thirteenRawLag n=
    normalizationFactor*(normalizedLagExpression n).value thirteenCoordinates := by
  unfold thirteenRawLag normalizedLagExpression
  simp only [Fintype.sum_bool,IntervalExpr.value,singleLagExpression_value]
  have hLag (b:Bool) : sourceLag thirteenTuning (n:ℤ) (thirteenFrequency b)=
      normalizationFactor*(thirteenTuning.Xi (Real.cos (thirteenFrequency b))*
        (1-Real.cos ((n:ℝ)*(thirteenFrequency b)))-
          Real.sin (thirteenFrequency b)*Real.sin ((n:ℝ)*(thirteenFrequency b))) := by
    change sourceG _ _*(1-Real.cos _)-2*(angleMultiplier _ _).im*Real.sin _=_
    rw [raw_g,raw_im]
    norm_num only [Int.cast_natCast]
    ring
  simp only [hLag]
  norm_num only [thirteenFrequency,thirteenNuWeight,Bool.false_eq_true,
    ite_false,ite_true,NNReal.coe_div,NNReal.coe_ofNat]
  have hc2 : Real.cos ((n:ℝ)*(2*Real.pi*2/13))=gridCos (n*2) := by
    simpa only [Nat.cast_ofNat] using lag_angle_cos n 2
  have hc3 : Real.cos ((n:ℝ)*(2*Real.pi*3/13))=gridCos (n*3) := by
    simpa only [Nat.cast_ofNat] using lag_angle_cos n 3
  have hs2 : Real.sin ((n:ℝ)*(2*Real.pi*2/13))=gridSin (n*2) := by
    simpa only [Nat.cast_ofNat] using lag_angle_sin n 2
  have hs3 : Real.sin ((n:ℝ)*(2*Real.pi*3/13))=gridSin (n*3) := by
    simpa only [Nat.cast_ofNat] using lag_angle_sin n 3
  rw [hc2,hc3,hs2,hs3]
  unfold gridCos gridSin
  ring

end polyak.CertifiedExamples.Rational
