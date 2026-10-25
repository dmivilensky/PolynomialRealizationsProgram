import polyak.ModeLocking.Gradient.Weights
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Differentiating the continued primal equations gives the exact weighted
source gradient. No derivative of an optimal measure is assumed. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels Continuation _root_.polyak.ModeLocking.Gradient Filter
open scoped BigOperators Topology
variable {q:Tuning} {s:ℝ} {L:ℕ} (D:RegularData q s L)

theorem weighted_gradient_direction
    (ψ:Parameters→ℝ×(Fin D.d→ℝ)) (hψ:AnalyticAt ℝ ψ (parameters q))
    (hbase:ψ (parameters q)=(s,fun i=>(D.primal i:ℝ)))
    (hsol:∀ᶠ p in 𝓝 (parameters q),
      (tightMatrix D.reps D.atoms (continuedPoint (fun p=>(ψ p).1) p)).mulVec (ψ p).2=0)
    (v:Parameters) :
    fderiv ℝ (fun p=>(ψ p).1) (parameters q) v =
      -∑i,D.gradientWeight i*fderiv ℝ (sourceCotangent (D.atoms i)) (parameters q) v := by
  let p0:=parameters q
  let σ:Parameters→ℝ:=fun p=>(ψ p).1
  let dσ:=fderiv ℝ σ p0
  let dh:Fin D.d→ℝ:=fun i=>fderiv ℝ (sourceCotangent (D.atoms i)) p0 v
  let line:ℝ→Parameters:=fun t=>p0+t•v
  have hline:HasDerivAt line v 0:=by
    apply hasDerivAt_pi.mpr
    intro j
    change HasDerivAt (fun t:ℝ=>p0 j+t*v j) (v j) 0
    simpa only [id_eq,one_mul] using (((hasDerivAt_id (0:ℝ)).mul_const (v j)).const_add (p0 j))
  have hσ:HasFDerivAt σ dσ p0:=hψ.differentiableAt.fst.hasFDerivAt
  have hbase0:ψ p0=(s,fun i=>(D.primal i:ℝ)):=hbase
  have hσbase:σ p0=s:=congrArg Prod.fst hbase
  let F:Fin D.d→Parameters→ℝ:=fun i p=>∑r,D.classWeight r*ambientLag (D.reps r) (D.atoms i) (continuedPoint σ p)
  have hFzero (i:Fin D.d):F i p0=0:=by
    have hpoint:continuedPoint σ p0=sourcePoint q s:=by
      change ![q.kappa,q.y,q.beta,σ p0]=![q.kappa,q.y,q.beta,s]
      rw [hσbase]
    dsimp only [F]
    rw [hpoint]
    simp only [ambientLag_actual]
    exact (D.class_sum_symbol (D.atoms i) (D.atoms_grid i)).trans (D.symbol_zero_support i)
  have hFd (i:Fin D.d):HasDerivAt (fun t=>F i (line t))
      (D.symbolShiftCoefficient i*(dh i+dσ v)) 0:=by
    have hterms (r:Fin D.d):HasDerivAt
        (fun t=>D.classWeight r*ambientLag (D.reps r) (D.atoms i) (continuedPoint σ (line t)))
        (D.classWeight r*(deriv (fun t=>(Geometry.shiftedCurve q t).lag (D.reps r) (D.atoms i)) s*
          (dh i+dσ v))) 0:=by
      have hd:=hasFDerivAt_continuedLag q s (D.atoms i)
        ⟨(D.atoms_grid i).1,D.atoms_lt_pi i⟩ (D.reps r) hσ hσbase
      have hd':HasFDerivAt (fun p=>ambientLag (D.reps r) (D.atoms i) (continuedPoint σ p))
          (deriv (fun t=>(Geometry.shiftedCurve q t).lag (D.reps r) (D.atoms i)) s •
            (fderiv ℝ (sourceCotangent (D.atoms i)) p0+dσ)) (line 0):=by
        simpa only [line,zero_smul,add_zero] using hd
      have hc:=(hd'.comp_hasDerivAt 0 hline).const_mul (D.classWeight r)
      simpa only [Function.comp_apply,smul_apply,add_apply,smul_eq_mul,dh] using hc
    have hd:=HasDerivAt.fun_sum (u:=Finset.univ) (fun r _=>hterms r)
    have he:(∑r,D.classWeight r*(deriv
        (fun t=>(Geometry.shiftedCurve q t).lag (D.reps r) (D.atoms i)) s*(dh i+dσ v)))=
        D.symbolShiftCoefficient i*(dh i+dσ v):=by
      rw [←D.class_derivative_sum i,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    rw [he] at hd
    exact hd
  have hw (i:Fin D.d):HasDerivAt (fun t=>(ψ (line t)).2 i)
      (fderiv ℝ (fun p=>(ψ p).2 i) p0 v) 0:=by
    have hwi:DifferentiableAt ℝ (fun p=>(ψ p).2 i) p0:=
      (differentiableAt_pi.mp hψ.differentiableAt.snd) i
    have hwi':HasFDerivAt (fun p=>(ψ p).2 i)
        (fderiv ℝ (fun p=>(ψ p).2 i) p0) (line 0):=by
      simpa only [line,zero_smul,add_zero] using hwi.hasFDerivAt
    exact hwi'.comp_hasDerivAt 0 hline
  let G:ℝ→ℝ:=fun t=>∑i,(ψ (line t)).2 i*F i (line t)
  have hGd:HasDerivAt G (∑i,D.gradientMass i*(dh i+dσ v)) 0:=by
    have hd:=HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=>(hw i).mul (hFd i))
    have he (i:Fin D.d):
        fderiv ℝ (fun p=>(ψ p).2 i) p0 v*F i (line 0)+
          (ψ (line 0)).2 i*(D.symbolShiftCoefficient i*(dh i+dσ v))=
            D.gradientMass i*(dh i+dσ v):=by
      simp only [line,zero_smul,add_zero,hFzero,hbase0,mul_zero,zero_add,gradientMass]
      ring
    change HasDerivAt G (∑i, (fderiv ℝ (fun p=>(ψ p).2 i) p0 v*F i (line 0)+
      (ψ (line 0)).2 i*(D.symbolShiftCoefficient i*(dh i+dσ v)))) 0 at hd
    simpa only [he] using hd
  have hGzero:G=ᶠ[𝓝 0](fun _=>0):=by
    have ht:(fun t=>line t) ⁻¹' {p| (tightMatrix D.reps D.atoms (continuedPoint σ p)).mulVec (ψ p).2=0}∈𝓝 0:=by
      have hc:Tendsto line (𝓝 0) (𝓝 (line 0)):=hline.continuousAt
      have hlim:Tendsto line (𝓝 0) (𝓝 p0):=by simpa only [line,zero_smul,add_zero] using hc
      exact hlim.eventually hsol
    filter_upwards [ht] with t ht
    dsimp only [G,F]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro r _
    have hrow:=congrFun ht r
    change (∑i,ambientLag (D.reps r) (D.atoms i) (continuedPoint σ (line t))*(ψ (line t)).2 i)=0 at hrow
    calc
      _=D.classWeight r*(∑i,ambientLag (D.reps r) (D.atoms i)
        (continuedPoint σ (line t))*(ψ (line t)).2 i):=by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _=0:=by rw [hrow,mul_zero]
  have hzero:(∑i,D.gradientMass i*(dh i+dσ v))=0:=
    hGd.unique ((hasDerivAt_const 0 (0:ℝ)).congr_of_eventuallyEq hGzero)
  have hsplit:(∑i,D.gradientMass i*(dh i+dσ v))=
      (∑i,D.gradientMass i*dh i)+D.gradientTotal*dσ v:=by
    simp only [gradientTotal,mul_add,Finset.sum_add_distrib,Finset.sum_mul]
  rw [hsplit] at hzero
  have hnorm:(∑i,D.gradientWeight i*dh i)=(∑i,D.gradientMass i*dh i)/D.gradientTotal:=by
    simp only [gradientWeight,div_mul_eq_mul_div,Finset.sum_div]
  change dσ v= -∑i,D.gradientWeight i*dh i
  rw [hnorm]
  rw [←neg_div]
  apply (eq_div_iff D.gradientTotal_pos.ne').mpr
  nlinarith

end polyak.ModeLocking.RegularData
