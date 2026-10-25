import polyak.ModeLocking.Gradient.Identity

/-! The kappa component of the exact weighted gradient is strictly negative. -/
noncomputable section
namespace polyak.ModeLocking.Gradient
open General Levels Continuation

def kappaDirection : Parameters := Pi.single 0 1

theorem hasDerivAt_kappaLine (q:Tuning) :
    HasDerivAt (fun κ:ℝ=>![κ,q.y,q.beta]) kappaDirection q.kappa := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simp only [kappaDirection,Pi.single_apply]
    convert hasDerivAt_id q.kappa using 1 <;> rfl
  · simpa [kappaDirection,Pi.single_apply] using hasDerivAt_const q.kappa q.y
  · simpa [kappaDirection,Pi.single_apply] using hasDerivAt_const q.kappa q.beta

theorem sourceCotangent_kappa_direction_pos (q:Tuning) (ω:Frequency)
    (hω:ω∈Threshold.interiorCarrier) :
    0<fderiv ℝ (sourceCotangent ω) (parameters q) kappaDirection := by
  have hd:=((analyticAt_sourceCotangent q ω).differentiableAt.hasFDerivAt).comp_hasDerivAt
    q.kappa (hasDerivAt_kappaLine q)
  have he:=hd.unique (hasDerivAt_sourceCotangent_kappa q ω)
  rw [he]
  apply div_pos (kappaNumerator_pos q ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
  exact mul_pos (mul_pos (mul_pos q.y_pos (sub_pos.mpr q.beta_lt_one))
    (sq_pos_of_pos (sub_pos.mpr q.kappa_gt_one)))
    (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2)

end polyak.ModeLocking.Gradient

namespace polyak.ModeLocking.RegularData
open General Levels Continuation _root_.polyak.ModeLocking.Gradient Filter
open scoped BigOperators Topology
variable {q:Tuning} {s:ℝ} {L:ℕ} (D:RegularData q s L)

theorem primal_kappa_derivative_neg
    (ψ:Parameters→ℝ×(Fin D.d→ℝ)) (hψ:AnalyticAt ℝ ψ (parameters q))
    (hbase:ψ (parameters q)=(s,fun i=>(D.primal i:ℝ)))
    (hsol:∀ᶠ p in 𝓝 (parameters q),
      (tightMatrix D.reps D.atoms (continuedPoint (fun p=>(ψ p).1) p)).mulVec (ψ p).2=0) :
    fderiv ℝ (fun p=>(ψ p).1) (parameters q) kappaDirection<0 := by
  rw [D.weighted_gradient_direction ψ hψ hbase hsol]
  apply neg_neg_of_pos
  have hp (i:Fin D.d):0<D.gradientWeight i*
      fderiv ℝ (sourceCotangent (D.atoms i)) (parameters q) kappaDirection:=
    mul_pos (D.gradientWeight_pos i) (sourceCotangent_kappa_direction_pos q (D.atoms i)
      ⟨(D.atoms_grid i).1,D.atoms_lt_pi i⟩)
  exact Finset.sum_pos' (fun i _=>(hp i).le) ⟨⟨0,D.d_pos⟩,Finset.mem_univ _,hp _⟩

end polyak.ModeLocking.RegularData
