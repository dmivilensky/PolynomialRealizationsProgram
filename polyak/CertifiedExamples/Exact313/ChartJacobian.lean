import polyak.CertifiedExamples.Exact313.Tuning
import polyak.Numerics.Parametric.Invertible
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Analytic.Constructions

/-! Nonsingularity of the original (κ,y,β) coefficient chart.
The proof factors through normalized stable-factor coordinates. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313.ChartJacobian
open General Levels Numerics.Parametric Filter
open scoped Topology
abbrev E := Fin 3→ℝ

def normalizedCoefficients (z : E) : E :=
  ![(z 1^2-1-z 0^2)/(2*z 1),z 0*z 2/z 1,-(z 2^2-1)/(2*z 1)]

def normalizedJacobian (z : E) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-z 0/z 1,(z 0^2+z 1^2+1)/(2*z 1^2),0;
    z 2/z 1,-z 0*z 2/z 1^2,z 0/z 1;
    0,(z 2^2-1)/(2*z 1^2),-z 2/z 1]

theorem normalizedCoefficients_differentiableAt {z : E} (hb : z 1≠0) :
    DifferentiableAt ℝ normalizedCoefficients z := by
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [normalizedCoefficients] <;> fun_prop (disch := norm_num [hb])

theorem normalizedCoefficients_matrix {z : E} (hb : z 1≠0) :
    LinearMap.toMatrix' (fderiv ℝ normalizedCoefficients z).toLinearMap=normalizedJacobian z := by
  let a : E→L[ℝ]ℝ := ContinuousLinearMap.proj 0
  let b : E→L[ℝ]ℝ := ContinuousLinearMap.proj 1
  let u : E→L[ℝ]ℝ := ContinuousLinearMap.proj 2
  let f0 : E→ℝ := fun x=>(1/2:ℝ)*((x 1^2-1-x 0^2)*(x 1)⁻¹)
  let f1 : E→ℝ := fun x=>(x 0*x 2)*(x 1)⁻¹
  let f2 : E→ℝ := fun x=>(-1/2:ℝ)*((x 2^2-1)*(x 1)⁻¹)
  have ha : HasFDerivAt (fun x:E=>x 0) a z := a.hasFDerivAt
  have hd : HasFDerivAt (fun x:E=>x 1) b z := b.hasFDerivAt
  have hu : HasFDerivAt (fun x:E=>x 2) u z := u.hasFDerivAt
  have hi := (hasDerivAt_inv hb).comp_hasFDerivAt z hd
  have h0 := ((((hd.pow 2).sub_const 1).sub (ha.pow 2)).mul hi).const_mul (1/2:ℝ)
  have h1 := (ha.mul hu).mul hi
  have h2 := (((hu.pow 2).sub_const 1).mul hi).const_mul (-1/2:ℝ)
  change HasFDerivAt f0 _ z at h0
  change HasFDerivAt f1 _ z at h1
  change HasFDerivAt f2 _ z at h2
  have he : normalizedCoefficients=(fun x:E=>![f0 x,f1 x,f2 x]) := by
    funext x i
    fin_cases i <;> dsimp [normalizedCoefficients,f0,f1,f2] <;> ring
  rw [he]
  have hmap : HasFDerivAt (fun x:E=>![f0 x,f1 x,f2 x])
      (ContinuousLinearMap.pi ![fderiv ℝ f0 z,fderiv ℝ f1 z,fderiv ℝ f2 z]) z := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact h0.differentiableAt.hasFDerivAt
    · exact h1.differentiableAt.hasFDerivAt
    · exact h2.differentiableAt.hasFDerivAt
  rw [hmap.fderiv]
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change (ContinuousLinearMap.pi ![fderiv ℝ f0 z,fderiv ℝ f1 z,fderiv ℝ f2 z])
    (Pi.single j 1) i=normalizedJacobian z i j
  rw [ContinuousLinearMap.pi_apply]
  fin_cases i <;> fin_cases j
  all_goals
    dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    try rw [h0.fderiv]
    try rw [h1.fderiv]
    try rw [h2.fderiv]
    norm_num [a,b,u,normalizedJacobian,Pi.single_apply]
  all_goals try field_simp [hb]
  all_goals ring

theorem normalizedJacobian_det {z : E} (hb : z 1≠0) :
    (normalizedJacobian z).det=(-z 0^2+z 1^2*z 2^2+z 2^2)/(2*z 1^4) := by
  unfold normalizedJacobian
  rw [Matrix.det_fin_three]
  norm_num
  field_simp
  ring

private theorem invertible_of_injective (D : E→L[ℝ]E) (hinj : Function.Injective D) : D.IsInvertible := by
  have hsurj : Function.Surjective D :=
    (LinearMap.injective_iff_surjective (f:=D.toLinearMap)).mp hinj
  refine ⟨(LinearEquiv.ofBijective D.toLinearMap ⟨hinj,hsurj⟩).toContinuousLinearEquiv,?_⟩
  ext x i
  rfl

private theorem invertible_of_matrix_det (D : E→L[ℝ]E)
    (hdet : (LinearMap.toMatrix' D.toLinearMap).det≠0) : D.IsInvertible := by
  have hu : IsUnit (LinearMap.toMatrix' D.toLinearMap) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hi := Matrix.mulVec_injective_of_isUnit hu
  apply invertible_of_injective D
  intro x y hxy
  apply hi
  rw [LinearMap.toMatrix'_mulVec,LinearMap.toMatrix'_mulVec]
  change D x=D y
  exact hxy

theorem normalizedCoefficients_jacobian_invertible {z : E}
    (hb : 0<z 1) (hstable : |z 0|+z 1<z 2) :
    (fderiv ℝ normalizedCoefficients z).IsInvertible := by
  apply invertible_of_matrix_det
  rw [normalizedCoefficients_matrix hb.ne',normalizedJacobian_det hb.ne']
  have hu : 0<z 2 := by linarith [abs_nonneg (z 0)]
  have ha : |z 0|<z 2 := by linarith
  have hs : z 0^2<z 2^2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (z 0)) hu.le).mpr ha
  have hn : 0< -z 0^2+z 1^2*z 2^2+z 2^2 := by
    nlinarith [mul_nonneg (sq_nonneg (z 1)) (sq_nonneg (z 2))]
  exact (div_pos hn (by positivity)).ne'

def originalPoint (q : Tuning) : E := ![q.kappa,q.y,q.beta]
def normalization (p : E) : E :=
  ![(1+p 2-(p 1/p 0+p 1)/2)/(1-p 2),
    ((p 1-p 1/p 0)/2)/(1-p 2),(1+p 2)/(1-p 2)]
def betaFromNormalized (z : E) : ℝ := (z 2-1)/(z 2+1)
def xFromNormalized (z : E) : ℝ :=
  1+betaFromNormalized z-(1-betaFromNormalized z)*(z 0+z 1)
def yFromNormalized (z : E) : ℝ :=
  1+betaFromNormalized z-(1-betaFromNormalized z)*(z 0-z 1)
def denormalization (z : E) : E :=
  ![yFromNormalized z/xFromNormalized z,yFromNormalized z,betaFromNormalized z]

theorem beta_normalization (p : E) (hβ : 1-p 2≠0) : betaFromNormalized (normalization p)=p 2 := by
  have hU : (1+p 2)/(1-p 2)+1≠0 := by
    have he : (1+p 2)/(1-p 2)+1=2/(1-p 2) := by field_simp;ring
    rw [he]
    exact div_ne_zero (by norm_num) hβ
  dsimp [betaFromNormalized,normalization]
  field_simp [hβ,hU]
  ring

theorem x_normalization (p : E) (hk : p 0≠0) (hβ : 1-p 2≠0) :
    xFromNormalized (normalization p)=p 1/p 0 := by
  rw [xFromNormalized,beta_normalization p hβ]
  dsimp [normalization]
  field_simp [hk,hβ]
  ring

theorem y_normalization (p : E) (hk : p 0≠0) (hβ : 1-p 2≠0) :
    yFromNormalized (normalization p)=p 1 := by
  rw [yFromNormalized,beta_normalization p hβ]
  dsimp [normalization]
  field_simp [hk,hβ]
  ring

theorem denormalization_normalization (p : E) (hk : p 0≠0) (hy : p 1≠0) (hβ : 1-p 2≠0) :
    denormalization (normalization p)=p := by
  ext i
  fin_cases i
  · change yFromNormalized (normalization p)/xFromNormalized (normalization p)=p 0
    rw [x_normalization p hk hβ,y_normalization p hk hβ]
    field_simp [hk,hy]
  · exact y_normalization p hk hβ
  · exact beta_normalization p hβ

theorem analyticAt_normalization (p : E) (hk : p 0≠0) (hβ : 1-p 2≠0) :
    AnalyticAt ℝ normalization p := by
  have h0 : AnalyticAt ℝ (fun x:E=>x 0) p := (ContinuousLinearMap.proj (R:=ℝ) 0).analyticAt p
  have h1 : AnalyticAt ℝ (fun x:E=>x 1) p := (ContinuousLinearMap.proj (R:=ℝ) 1).analyticAt p
  have h2 : AnalyticAt ℝ (fun x:E=>x 2) p := (ContinuousLinearMap.proj (R:=ℝ) 2).analyticAt p
  have hQ : AnalyticAt ℝ (fun x:E=>x 1/x 0) p := h1.div h0 hk
  have hA : AnalyticAt ℝ (fun x:E=>1+x 2-(x 1/x 0+x 1)/2) p :=
    (analyticAt_const.add h2).sub ((hQ.add h1).div_const)
  have hB : AnalyticAt ℝ (fun x:E=>(x 1-x 1/x 0)/2) p := (h1.sub hQ).div_const
  have hD : AnalyticAt ℝ (fun x:E=>1-x 2) p := analyticAt_const.sub h2
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact hA.div hD hβ
  · exact hB.div hD hβ
  · exact (analyticAt_const.add h2).div hD hβ

theorem analyticAt_denormalization (z : E) (hu : z 2+1≠0) (hx : xFromNormalized z≠0) :
    AnalyticAt ℝ denormalization z := by
  have h0 : AnalyticAt ℝ (fun x:E=>x 0) z := (ContinuousLinearMap.proj (R:=ℝ) 0).analyticAt z
  have h1 : AnalyticAt ℝ (fun x:E=>x 1) z := (ContinuousLinearMap.proj (R:=ℝ) 1).analyticAt z
  have h2 : AnalyticAt ℝ (fun x:E=>x 2) z := (ContinuousLinearMap.proj (R:=ℝ) 2).analyticAt z
  have hb : AnalyticAt ℝ betaFromNormalized z :=
    (h2.sub analyticAt_const).div (h2.add analyticAt_const) hu
  have hX : AnalyticAt ℝ xFromNormalized z :=
    (analyticAt_const.add hb).sub ((analyticAt_const.sub hb).mul (h0.add h1))
  have hY : AnalyticAt ℝ yFromNormalized z :=
    (analyticAt_const.add hb).sub ((analyticAt_const.sub hb).mul (h0.sub h1))
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact hY.div hX hx
  · exact hY
  · exact hb

theorem normalization_actual (q : Tuning) :
    normalization (originalPoint q)=![q.A/(1-q.beta),q.B/(1-q.beta),(1+q.beta)/(1-q.beta)] := rfl

theorem normalization_jacobian_invertible (q : Tuning) :
    (fderiv ℝ normalization (originalPoint q)).IsInvertible := by
  let p := originalPoint q
  have hk : p 0≠0 := q.kappa_pos.ne'
  have hy : p 1≠0 := q.y_pos.ne'
  have hβ : 1-p 2≠0 := (sub_pos.mpr q.beta_lt_one).ne'
  have hU : (normalization p) 2+1≠0 := by
    change (1+q.beta)/(1-q.beta)+1≠0
    have he : (1+q.beta)/(1-q.beta)+1=2/(1-q.beta) := by
      field_simp [(sub_pos.mpr q.beta_lt_one).ne'];ring
    rw [he]
    exact div_ne_zero (by norm_num) hβ
  have hX : xFromNormalized (normalization p)≠0 := by
    rw [x_normalization p hk hβ]
    exact div_ne_zero hy hk
  have hf := (analyticAt_normalization p hk hβ).differentiableAt
  have hg := (analyticAt_denormalization (normalization p) hU hX).differentiableAt
  have hnear : (fun y=>denormalization (normalization y)) =ᶠ[𝓝 p] id := by
    have hkn := (continuous_apply (0:Fin 3)).continuousAt.eventually_ne hk
    have hyn := (continuous_apply (1:Fin 3)).continuousAt.eventually_ne hy
    have hβn : ∀ᶠy in 𝓝 p,1-y 2≠0 := by
      exact ((continuous_const.sub (continuous_apply (2:Fin 3))).continuousAt).eventually_ne hβ
    filter_upwards [hkn,hyn,hβn] with y hky hyy hβy
    exact denormalization_normalization y hky hyy hβy
  have hcomp := hg.hasFDerivAt.comp p hf.hasFDerivAt
  have hid : HasFDerivAt (fun y:E=>denormalization (normalization y))
      (ContinuousLinearMap.id ℝ E) p :=
    (hasFDerivAt_id (𝕜:=ℝ) p).congr_of_eventuallyEq hnear
  have he := hcomp.unique hid
  apply invertible_of_injective
  intro v w hvw
  have hh := congrArg (fderiv ℝ denormalization (normalization p)) hvw
  change ((fderiv ℝ denormalization (normalization p)).comp (fderiv ℝ normalization p)) v=
    ((fderiv ℝ denormalization (normalization p)).comp (fderiv ℝ normalization p)) w at hh
  rw [he] at hh
  exact hh

def coefficientMap (p : E) : E := normalizedCoefficients (normalization p)

theorem coefficientMap_actual (q : Tuning) :
    coefficientMap (originalPoint q)=![(Chart.coefficients q).c0,(Chart.coefficients q).c1,(Chart.coefficients q).c2] := by
  unfold coefficientMap
  rw [normalization_actual]
  ext i
  fin_cases i <;> dsimp [normalizedCoefficients,Chart.coefficients]
  all_goals field_simp [q.B_ne_zero,(sub_pos.mpr q.beta_lt_one).ne']
  all_goals ring

theorem coefficientMap_jacobian_invertible (q : Tuning) :
    (fderiv ℝ coefficientMap (originalPoint q)).IsInvertible := by
  have hβ : 0<1-q.beta := sub_pos.mpr q.beta_lt_one
  have hb : 0<(normalization (originalPoint q)) 1 := div_pos q.B_pos hβ
  have hs : |(normalization (originalPoint q)) 0|+(normalization (originalPoint q)) 1<
      (normalization (originalPoint q)) 2 := by
    change |q.A/(1-q.beta)|+q.B/(1-q.beta)<(1+q.beta)/(1-q.beta)
    rw [abs_div,abs_of_pos hβ,←add_div]
    exact (div_lt_div_iff_of_pos_right hβ).mpr q.abs_A_add_B_lt
  have hn := normalization_jacobian_invertible q
  have hc := normalizedCoefficients_jacobian_invertible hb hs
  have hfd := (analyticAt_normalization (originalPoint q) q.kappa_pos.ne' hβ.ne').differentiableAt
  have hcd := normalizedCoefficients_differentiableAt hb.ne'
  have he : fderiv ℝ coefficientMap (originalPoint q)=
      (fderiv ℝ normalizedCoefficients (normalization (originalPoint q))).comp
        (fderiv ℝ normalization (originalPoint q)) :=
    fderiv_comp (originalPoint q) hcd hfd
  rw [he]
  exact hc.comp hn

end polyak.CertifiedExamples.Exact313.ChartJacobian
