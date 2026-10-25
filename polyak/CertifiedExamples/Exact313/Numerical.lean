import polyak.CertifiedExamples.Exact313.Contacts
import polyak.CertifiedExamples.Exact313.SourceLag

/-! The finite reserves imply exactly E3 and E4 for the actual lag functions. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels ModeLocking.TwoLag LeanCert.Core LeanCert.Engine Numerics.Parametric

theorem eval_lagNumerator (n j : ℤ) :
    Expr.eval (Code.environment scalarRoot.value) (Code.lagNumerator (n:ℚ) (j:ℚ))=
      rawLag qStar n (2*Real.pi*(j:ℝ)/13) := by
  simp only [Code.lagNumerator,Expr.eval_sub,Expr.eval_mul,Expr.eval_const,
    Code.eval_xi scalarRoot_positive.le,Code.eval_cosineAt,Code.eval_sine]
  rw [rawLag,qStar_Xi]
  push_cast
  congr 1 <;> congr 1 <;> congr 1 <;> ring

theorem eval_inactive (n : ℤ) :
    Expr.eval (Code.environment scalarRoot.value) (Code.inactive (n:ℚ))=
      -rawLag qStar 1 v*rawLag qStar n u+
        rawLag qStar 1 u*rawLag qStar n v := by
  simp only [Code.inactive,Expr.eval_add,Expr.eval_mul,Expr.eval_neg]
  have h12 := eval_lagNumerator 1 2
  have hn3 := eval_lagNumerator n 3
  have h13 := eval_lagNumerator 1 3
  have hn2 := eval_lagNumerator n 2
  norm_num only [Int.cast_one,Int.cast_ofNat] at h12 hn3 h13 hn2
  rw [h12,hn3,h13,hn2]
  dsimp [u,v]
  norm_num
  ring

theorem eval_sineNumerator (n j : ℤ) :
    Expr.eval (Code.environment scalarRoot.value) (Code.sineNumerator (n:ℚ) (j:ℚ))=
      rawSine qStar n (2*Real.pi*(j:ℝ)/13) := by
  simp only [Code.sineNumerator,Expr.eval_sub,Expr.eval_mul,
    Code.eval_xi scalarRoot_positive.le,Code.eval_cosineAt,Code.eval_sine]
  rw [rawSine,qStar_Xi]
  push_cast
  congr 1 <;> congr 1 <;> congr 1 <;> ring

theorem eval_minimizer :
    Expr.eval (Code.environment scalarRoot.value) Code.minimizer=
      -rawLag qStar 1 v*qStar.Xi c₁+rawLag qStar 1 u*qStar.Xi c₂ := by
  simp only [Code.minimizer,Expr.eval_add,Expr.eval_mul,Expr.eval_neg,
    Code.eval_xi scalarRoot_positive.le,Code.eval_cosineAt]
  have h12 := eval_lagNumerator 1 2
  have h13 := eval_lagNumerator 1 3
  norm_num only [Int.cast_one,Int.cast_ofNat] at h12 h13
  rw [h12,h13]
  rw [qStar_Xi,qStar_Xi]
  norm_num [coefficients,c₁,c₂,u,v]
  ring

theorem eval_determinant :
    Expr.eval (Code.environment scalarRoot.value) Code.determinant=
      rawSine qStar 1 u*rawSine qStar (-4) v-
        rawSine qStar (-4) u*rawSine qStar 1 v := by
  simp only [Code.determinant,Expr.eval_sub,Expr.eval_mul]
  have h13 := eval_sineNumerator 1 3
  have h42 := eval_sineNumerator (-4) 2
  have h43 := eval_sineNumerator (-4) 3
  have h12 := eval_sineNumerator 1 2
  norm_num only [Int.cast_one,Int.cast_ofNat,Int.cast_neg] at h13 h42 h43 h12
  rw [h13,h42,h43,h12]
  norm_num [u,v]
  ring

theorem inactive_numerator_positive (n : ℤ) (hn0 : 0<n) (hn13 : n<13)
    (hn1 : n≠1) (hn9 : n≠9) :
    0< -rawLag qStar 1 v*rawLag qStar n u+rawLag qStar 1 u*rawLag qStar n v := by
  rw [←eval_inactive]
  interval_cases n
  all_goals first | contradiction | skip
  · exact reserve_positive 5 scalarRoot.mem
  · exact reserve_positive 6 scalarRoot.mem
  · exact reserve_positive 7 scalarRoot.mem
  · exact reserve_positive 8 scalarRoot.mem
  · exact reserve_positive 9 scalarRoot.mem
  · exact reserve_positive 10 scalarRoot.mem
  · exact reserve_positive 11 scalarRoot.mem
  · exact reserve_positive 12 scalarRoot.mem
  · exact reserve_positive 13 scalarRoot.mem
  · exact reserve_positive 14 scalarRoot.mem

theorem minimizer_numerator_positive :
    0< -rawLag qStar 1 v*qStar.Xi c₁+rawLag qStar 1 u*qStar.Xi c₂ := by
  rw [←eval_minimizer]
  exact reserve_positive 15 scalarRoot.mem

theorem determinant_numerator_positive :
    0<rawSine qStar 1 u*rawSine qStar (-4) v-
      rawSine qStar (-4) u*rawSine qStar 1 v := by
  rw [←eval_determinant]
  exact reserve_positive 16 scalarRoot.mem

theorem inactive_strict (n : ℤ) (hn0 : 0<n) (hn13 : n<13) (hn1 : n≠1) (hn9 : n≠9) :
    -(tuningCurve qStar).lag 1 (atoms 1)*(tuningCurve qStar).lag n (atoms 0)+
      (tuningCurve qStar).lag 1 (atoms 0)*(tuningCurve qStar).lag n (atoms 1)>0 := by
  have h := inactive_numerator_positive n hn0 hn13 hn1 hn9
  have he : -(tuningCurve qStar).lag 1 (atoms 1)*(tuningCurve qStar).lag n (atoms 0)+
      (tuningCurve qStar).lag 1 (atoms 0)*(tuningCurve qStar).lag n (atoms 1)=
      (-rawLag qStar 1 v*rawLag qStar n u+rawLag qStar 1 u*rawLag qStar n v)/
        (qStar.angleRadius (atoms 0)*qStar.angleRadius (atoms 1)) := by
    rw [lag_eq_raw,lag_eq_raw,lag_eq_raw,lag_eq_raw]
    have h0 : (atoms 0:ℝ)=u := by rw [atoms_coe];rfl
    have h1 : (atoms 1:ℝ)=v := by rw [atoms_coe];rfl
    rw [h0,h1]
    ring
  rw [he]
  exact div_pos h (mul_pos (radius_positive qStar (atoms 0)) (radius_positive qStar (atoms 1)))

theorem minimizer_strict :
    -(tuningCurve qStar).lag 1 (atoms 1)*(tuningCurve qStar).minimizer (atoms 0)+
      (tuningCurve qStar).lag 1 (atoms 0)*(tuningCurve qStar).minimizer (atoms 1)>0 := by
  have he : -(tuningCurve qStar).lag 1 (atoms 1)*(tuningCurve qStar).minimizer (atoms 0)+
      (tuningCurve qStar).lag 1 (atoms 0)*(tuningCurve qStar).minimizer (atoms 1)=
      (-rawLag qStar 1 v*qStar.Xi c₁+rawLag qStar 1 u*qStar.Xi c₂)/
        (qStar.angleRadius (atoms 0)*qStar.angleRadius (atoms 1)) := by
    rw [lag_eq_raw,lag_eq_raw,minimizer_eq_raw,minimizer_eq_raw]
    have h0 : (atoms 0:ℝ)=u := by rw [atoms_coe];rfl
    have h1 : (atoms 1:ℝ)=v := by rw [atoms_coe];rfl
    rw [h0,h1]
    dsimp [c₁,c₂]
    ring
  rw [he]
  exact div_pos minimizer_numerator_positive
    (mul_pos (radius_positive qStar (atoms 0)) (radius_positive qStar (atoms 1)))

theorem sine_determinant_nonzero :
    Matrix.det (fun i j : Fin 2=>Real.sin
      (((![1,(-4:ℤ)] : Fin 2→ℤ) j:ℝ)*(atoms i:ℝ)-Geometry.shiftedCurve qStar 0 (atoms i)))≠0 := by
  rw [Geometry.shiftedCurve_zero]
  have he : Matrix.det (fun i j : Fin 2=>Real.sin
      (((![1,(-4:ℤ)] : Fin 2→ℤ) j:ℝ)*(atoms i:ℝ)-tuningCurve qStar (atoms i)))=
      (rawSine qStar 1 u*rawSine qStar (-4) v-rawSine qStar (-4) u*rawSine qStar 1 v)/
        (qStar.angleRadius (atoms 0)*qStar.angleRadius (atoms 1)) := by
    apply (Matrix.det_fin_two _).trans
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,tuningCurve_apply]
    change Real.sin (((1:ℤ):ℝ)*(atoms 0:ℝ)-qStar.angle (atoms 0))*
      Real.sin (((-4:ℤ):ℝ)*(atoms 1:ℝ)-qStar.angle (atoms 1))-
      Real.sin (((-4:ℤ):ℝ)*(atoms 0:ℝ)-qStar.angle (atoms 0))*
      Real.sin (((1:ℤ):ℝ)*(atoms 1:ℝ)-qStar.angle (atoms 1))=_
    rw [sine_eq_raw,sine_eq_raw,sine_eq_raw,sine_eq_raw]
    have h0 : (atoms 0:ℝ)=u := by rw [atoms_coe];rfl
    have h1 : (atoms 1:ℝ)=v := by rw [atoms_coe];rfl
    rw [h0,h1]
    ring
  rw [he]
  exact (div_pos determinant_numerator_positive
    (mul_pos (radius_positive qStar (atoms 0)) (radius_positive qStar (atoms 1)))).ne'

end polyak.CertifiedExamples.Exact313
