import polyak.FareyPlateau.Ray.Interior

/-! Exact curvature of every admissible finite symbol at the actual
Farey contact, with the strictly positive source prefactor retained. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels ModeLocking Set Filter
open scoped BigOperators Topology

theorem analyticAt_tuningAngle (q : Tuning) {x : ℝ} (hx : x∈Ioo (0:ℝ) Real.pi) :
    AnalyticAt ℝ q.angle x := by
  have hp : AnalyticAt ℝ (fun y : ℝ=>![q.kappa,q.y,q.beta,0,y]) x := by
    apply AnalyticAt.pi
    intro i; fin_cases i <;> first | exact analyticAt_const | exact analyticAt_id
  have hθ := (Geometry.analyticAt_jointAngle_actual q 0 ⟨hx.1.le,hx.2.le⟩).comp (f:=fun y : ℝ=>![q.kappa,q.y,q.beta,0,y]) hp
  apply hθ.congr
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  change Geometry.jointAngle ![q.kappa,q.y,q.beta,0,y]=q.angle y
  rw [Geometry.jointAngle_actual q 0 ⟨hy.1.le,hy.2.le⟩]
  simp only [Geometry.shiftedAngle,Geometry.shiftRadius,Geometry.shiftNumerator,
    zero_mul,add_zero,Tuning.angle,Tuning.angleRadius]

theorem second_power_factor (R : ℝ→ℝ) (c : ℝ) (hR : AnalyticAt ℝ R c) :
    deriv^[2] (fun x=>(x-c)^2*R x) c=2*R c := by
  have hp (j : ℕ) : iteratedDeriv j (fun x : ℝ=>(x-c)^2) c =
      if j=2 then 2 else 0 := by
    have he := congrFun (iteratedDeriv_comp_sub_const j (fun z : ℝ=>z^2) c) c
    rw [he,sub_self,iteratedDeriv_fun_pow_zero]
    split_ifs <;> norm_num
  have he := iteratedDeriv_fun_mul (n:=2) (x:=c)
    (by fun_prop : ContDiffAt ℝ 2 (fun x : ℝ=>(x-c)^2) c) (hR.contDiffAt (n:=2))
  norm_num [Finset.sum_range_succ,hp,iteratedDeriv_zero,iteratedDeriv_eq_iterate] at he
  exact he

theorem SourceCertificate.second_contact {j k : ℕ} {b : ℤ} {D a : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1)
    (q : Tuning) (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    deriv^[2] (LargeCurvature.indexedSymbol q 0 C.lag C.weight) (Regions.rationalAngle j k)=
      4*(Real.sin (Real.pi/k))^3*Real.sin (Regions.rationalAngle j k)*
        oneMass k b C.lag C.weight*(C.R (Chart.rationalCosine j k)-a) := by
  let ω := Regions.rationalAngle j k
  let c := Chart.rationalCosine j k
  let g := fun z : ℝ=>(edgeCoefficients c (Chart.rationalHeight j k) a D).eval z-
    Symbols.psi C.lag C.weight z
  let A := fun x : ℝ=>Real.sin (q.angle x)*Symbols.denominator C.lag C.weight x/Real.sin x
  have hω : ω∈Ioo (0:ℝ) Real.pi := Regions.rationalAngle_mem hj hjk
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hψ := C.admissible.phaseFloor_analytic c ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  obtain ⟨hv,hd⟩ := phaseFloor_edge_contact hj hjk hb C.admissible
  have hf : AnalyticAt ℝ (Symbols.contactDifference C.lag C.weight c (Chart.rationalHeight j k) D) c := by
    have hl : AnalyticAt ℝ (fun z : ℝ=>Chart.rationalHeight j k+(1+D)*(z-c)) c := by fun_prop
    exact hl.sub hψ
  have hR : AnalyticAt ℝ C.R c := Symbols.quadraticQuotient_analytic hf
  have hgrepr : g=(fun z=>(z-c)^2*(C.R z-a)) :=
    funext (fun z=>C.parabola_difference hj hjk hb z)
  have hg : AnalyticAt ℝ g c := by rw [hgrepr]; fun_prop
  have hg0 : g c=0 := by rw [hgrepr]; simp
  have hg1 : deriv g c=0 := by
    rw [hgrepr]
    have hprod := (((hasDerivAt_id c).sub_const c).pow 2).mul
      (hR.differentiableAt.hasDerivAt.sub_const a)
    convert hprod.deriv using 1
    · congr 1
    · simp
  have hg2 : deriv^[2] g c=2*(C.R c-a) := by
    rw [hgrepr]
    exact second_power_factor _ _ (hR.sub analyticAt_const)
  have hA : AnalyticAt ℝ A ω := by
    have hθ := analyticAt_tuningAngle q hω
    have hP : AnalyticAt ℝ (Symbols.denominator C.lag C.weight) ω := by
      unfold Symbols.denominator
      exact Finset.analyticAt_fun_sum _ (fun i _=>analyticAt_const.mul
        (analyticAt_const.sub (Real.analyticAt_cos.comp (analyticAt_const.mul analyticAt_id))))
    exact ((Real.analyticAt_sin.comp hθ).mul hP).div Real.analyticAt_sin hs.ne'
  have hfun : LargeCurvature.indexedSymbol q 0 C.lag C.weight =ᶠ[𝓝 ω]
      (fun x=>A x*g (Real.cos x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hω] with x hx
    rw [indexedSymbol_phaseFloor q C.lag C.weight C.admissible.nonzero
      (fun i=>(C.admissible.positive i).le) C.admissible.normalization C.admissible.bezout hx,
      ←Chart.eval_coefficients,he]
  have hcomp : ContDiffAt ℝ 2 (fun x=>g (Real.cos x)) ω :=
    hg.contDiffAt.comp ω Real.contDiff_cos.contDiffAt
  have hfirst : deriv (fun x=>g (Real.cos x)) ω=0 := by
    rw [show (fun x=>g (Real.cos x))=g ∘ Real.cos by rfl,
      deriv_comp ω hg.differentiableAt Real.differentiableAt_cos]
    change deriv g c*deriv Real.cos ω=0
    rw [hg1,zero_mul]
  change deriv (deriv (LargeCurvature.indexedSymbol q 0 C.lag C.weight)) ω=_
  rw [hfun.deriv.deriv_eq]
  change deriv^[2] (fun x=>A x*g (Real.cos x)) ω=_
  rw [TwoLag.second_mul_at_double_zero hA.contDiffAt hcomp hg0 hfirst,
    TwoLag.second_cos_comp_at_stationary hg.contDiffAt hg1]
  change A ω*(deriv^[2] g c*(Real.sin ω)^2)=_
  rw [hg2]
  dsimp [A]
  rw [source_edge_phase q hj hjk he,denominator_contact (by omega) hjk.le hb C.admissible]
  rw [show 2*Real.pi/(k:ℝ)=2*(Real.pi/k) by ring,Real.cos_two_mul]
  have hγ : (Real.cos (Real.pi/k))^2=1-(Real.sin (Real.pi/k))^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi/k)]
  rw [hγ]
  field_simp [hs.ne']
  ring

end polyak.FareyPlateau.Ray
