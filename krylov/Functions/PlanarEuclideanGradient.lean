import krylov.Functions.PlanarCorrectionRemainder

/-!
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii), genuine Hilbert-plane
interpretation of the actual cubic data fibre. Use: keep the exact Euclidean
Riesz-gradient norm and the sharp sqrt(1+4r²) coefficient while transporting
the proved unrestricted-output localization and fourth-order remainder.
Source: coordinate differentials, the true Riesz map and finite-dimensional
norm comparison; comparison factors affect only remainder constants.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor.BinaryCubic
open scoped InnerProductSpace

/-- The genuine Euclidean vector with two given real coordinates.
Article: main_krylov, thm:Fplanar. -/
def planeOfPair (z : ℝ × ℝ) : Plane := WithLp.toLp 2 ![z.1,z.2]

/-- The two real coordinates of a genuine Euclidean-plane point.
Article: main_krylov, thm:Fplanar. -/
def pairOfPlane (x : Plane) : ℝ × ℝ := (x 0,x 1)

/-- The coordinate maps are exact inverses. Article: main_krylov, thm:Fplanar. -/
theorem pairOfPlane_planeOfPair (z : ℝ × ℝ) : pairOfPlane (planeOfPair z)=z := by
  rcases z with ⟨x,y⟩
  rfl

/-- The genuine Euclidean embedding is additive. Article: main_krylov, thm:Fplanar. -/
theorem planeOfPair_add (z w : ℝ × ℝ) : planeOfPair (z+w)=planeOfPair z+planeOfPair w := by
  ext i
  fin_cases i <;> rfl

/-- The genuine Euclidean embedding preserves differences. Article: main_krylov, thm:Fplanar. -/
theorem planeOfPair_sub (z w : ℝ × ℝ) : planeOfPair (z-w)=planeOfPair z-planeOfPair w := by
  ext i
  fin_cases i <;> rfl

/-- The genuine Euclidean embedding preserves real scalar multiplication.
Article: main_krylov, thm:Fplanar. -/
theorem planeOfPair_smul (q : ℝ) (z : ℝ × ℝ) : planeOfPair (q • z)=q • planeOfPair z := by
  ext i
  fin_cases i <;> rfl

/-- Each actual differential coordinate is bounded by the genuine Euclidean
norm. Article: main_krylov, prop:Fcycle(iii). -/
theorem pair_norm_le_planeOfPair (z : ℝ × ℝ) : ‖z‖≤‖planeOfPair z‖ := by
  have hs := plane_norm_sq (planeOfPair z)
  change ‖planeOfPair z‖^2=z.1^2+z.2^2 at hs
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  apply max_le
  · nlinarith only [hs,sq_nonneg z.2,sq_abs z.1,norm_nonneg (planeOfPair z),abs_nonneg z.1]
  · nlinarith only [hs,sq_nonneg z.1,sq_abs z.2,norm_nonneg (planeOfPair z),abs_nonneg z.2]

/-- A coarse reverse comparison changes only genuine remainder constants.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planeOfPair_norm_le (z : ℝ × ℝ) : ‖planeOfPair z‖≤2*‖z‖ := by
  have hs := plane_norm_sq (planeOfPair z)
  change ‖planeOfPair z‖^2=z.1^2+z.2^2 at hs
  have hx := norm_fst_le z
  have hy := norm_snd_le z
  rw [Real.norm_eq_abs] at hx hy
  have hx' := (sq_le_sq₀ (abs_nonneg z.1) (norm_nonneg z)).mpr hx
  have hy' := (sq_le_sq₀ (abs_nonneg z.2) (norm_nonneg z)).mpr hy
  rw [sq_abs] at hx' hy'
  nlinarith only [hs,hx',hy',norm_nonneg (planeOfPair z),norm_nonneg z]

/-- Every true coordinate differential is determined by its actual two
coordinate observations. Article: main_krylov, prop:Fcycle(iii). -/
theorem planarDifferentialCoordinates_reconstruct (D : (ℝ × ℝ) →L[ℝ] ℝ) (z : ℝ × ℝ) :
    D z=(planarDifferentialCoordinates D).1*z.1+(planarDifferentialCoordinates D).2*z.2 := by
  have he : z=z.1 • (1,0)+z.2 • (0,1) := by ext <;> simp
  conv_lhs => rw [he]
  simp only [map_add,map_smul,smul_eq_mul,planarDifferentialCoordinates]
  ring

/-- The actual scalar cubic objective on the true real Hilbert plane.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
def planeCubicObjective (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : Plane) : ℝ :=
  planarCubicObjective p r t (pairOfPlane x)

/-- The actual true Euclidean gradient in its coordinate representation.
Article: main_krylov, thm:Fplanar. -/
def planeCubicGradient (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : Plane) : Plane :=
  planeOfPair (planarCubicGradient p r t (pairOfPlane x))

/-- The displayed Hilbert-plane vector is the actual mathematical gradient of
the genuine scalar objective. Article: main_krylov, prop:Fcycle(iii). -/
theorem planeCubicGradient_actual (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : Plane) :
    gradient (planeCubicObjective p r t) x=planeCubicGradient p r t x := by
  let C : Plane →L[ℝ] ℝ × ℝ := (EuclideanSpace.proj 0).prod (EuclideanSpace.proj 1)
  let D := fderiv ℝ (planarCubicObjective p r t) (pairOfPlane x)
  have hD : HasFDerivAt (planarCubicObjective p r t) D (pairOfPlane x) := by
    exact ((planarReferenceQuadratic_hasFDerivAt p r _).add
      (planarValueFamily_hasFDerivAt (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p r t _)).differentiableAt.hasFDerivAt
  have hd := hD.comp x C.hasFDerivAt
  have hcov : D.comp C=innerSL ℝ (planeCubicGradient p r t x) := by
    apply ContinuousLinearMap.ext
    intro v
    have hg := planarCubicGradient_actual p r t (pairOfPlane x)
    change planarCubicGradient p r t (pairOfPlane x)=planarDifferentialCoordinates D at hg
    change D (pairOfPlane v)=inner ℝ (planeCubicGradient p r t x) v
    rw [planarDifferentialCoordinates_reconstruct,←hg]
    simp only [planeCubicGradient,planeOfPair,pairOfPlane,PiLp.inner_apply,Fin.sum_univ_two,
      Real.inner_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hf : HasFDerivAt (planeCubicObjective p r t) (innerSL ℝ (planeCubicGradient p r t x)) x := by
    rw [←hcov]
    exact hd
  exact (hasGradientAt_iff_hasFDerivAt.mpr hf).gradient

/-- All true Hilbert-plane common cubic-small outputs have a genuine
fourth-order terminal affine gradient remainder, with the exact Euclidean
leading vector untouched. Article: main_krylov, prop:Fcycle(iii). -/
theorem planeCubic_common_output_affine_error (r : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) (hd : u.t2-t.t2≠0) (hr : r≠0)
    (A : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 → ∀ x : Plane,
      ‖gradient (planeCubicObjective p r t) x‖≤A*p^3 →
      ‖gradient (planeCubicObjective p r u) x‖≤A*p^3 →
      ‖gradient (planeCubicObjective p r t) x-planeOfPair (planarCubicTerminalModel p r t (pairOfPlane x-(p,r*p)))‖≤C*p^4 ∧
      ‖gradient (planeCubicObjective p r u) x-planeOfPair (planarCubicTerminalModel p r u (pairOfPlane x-(p,r*p)))‖≤C*p^4 := by
  obtain ⟨C,hC,hbound⟩ := planarCubic_common_output_coordinate_affine_error r t u hobs hd hr A hA
  refine ⟨2*C,by positivity,?_⟩
  intro p hp hp₁ x ht hu
  simp only [planeCubicGradient_actual] at ht hu ⊢
  have htc : ‖planarCubicGradient p r t (pairOfPlane x)‖≤A*p^3 := (pair_norm_le_planeOfPair _).trans ht
  have huc : ‖planarCubicGradient p r u (pairOfPlane x)‖≤A*p^3 := (pair_norm_le_planeOfPair _).trans hu
  have hh := hbound p hp hp₁ (pairOfPlane x) htc huc
  have hterm (w : krylov.Tensor.BinaryCubic)
      (hw : ‖planarCubicGradient p r w (pairOfPlane x)-planarCubicTerminalModel p r w (pairOfPlane x-(p,r*p))‖≤C*p^4) :
      ‖planeCubicGradient p r w x-planeOfPair (planarCubicTerminalModel p r w (pairOfPlane x-(p,r*p)))‖≤2*C*p^4 := by
    rw [planeCubicGradient,←planeOfPair_sub]
    exact (planeOfPair_norm_le _).trans ((mul_le_mul_of_nonneg_left hw (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))
  exact ⟨hterm t hh.1,hterm u hh.2⟩

end
end krylov.Functions
