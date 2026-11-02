import jacobi.Fredholm.OptimizerEquation
import jacobi.Fredholm.Trajectory

/-!
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
The actual radial optimizer has a genuine central upper turn and a strictly
descending Green diagonal. The free diagonal state is excluded by the strict
Neumann bound; the scalar phase signs and actual autonomous uniqueness exclude
all subsequent turns. Radial evenness of the actual density fixes its center.
Source: the proved actual Euler equation, phase turning theorem and trajectory calculus.
Use: applies genuine autonomous uniqueness through the switching level without a singular denominator.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual Green optimizer satisfies the clipped polynomial acceleration equation everywhere.
Use: applies genuine autonomous uniqueness through the switching level without a singular denominator.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: add the actual Gel'fand--Dikii identity and the proved zero first
integral. Their exact polynomial cancellation gives 2*g*(g''-force)=0;
the actual positive Green diagonal permits cancellation. -/
theorem Optimizer.force_hasDerivAt {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) (x : ℝ) :
    HasDerivAt (deriv (P.g hs.le)) (force P.A P.edge (P.g hs.le x)) x := by
  -- Both input equations belong to this same genuine minimizing inverse diagonal.
  have hc : ContDiff ℝ 2 (P.g hs.le) := P.density.greenDiagonal_contDiff P.continuous hs.le P.pole
  have hgd := P.gd hs x
  have hfirst := P.first_integral hs x
  unfold phase at hfirst
  have hz : 2*P.g hs.le x*(deriv (deriv (P.g hs.le)) x-force P.A P.edge (P.g hs.le x))=0 := by
    unfold force
    linear_combination hgd+hfirst
  have hpos : 0<2*P.g hs.le x := by
    have hh := (P.density.fredholmGreen_diagonal hs.le P.pole x).1
    change (1/2:ℝ)≤P.g hs.le x at hh
    linarith
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hpos.ne')
  convert (hc.differentiable_deriv_two x).hasDerivAt using 1
  exact heq.symm

/-- The actual optimizing Green diagonal attains an upper turning point with the complete true phase sign pattern.
Use: strict trajectory descent and exact centering are derived from actual minimizing data.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: the genuine two-ended free limit and strict Neumann diagonal
excess give an attained global maximum. Its actual derivative vanishes.
The proved scalar phase signs identify this maximum with the unique upper
turning zero, whose acceleration is strictly negative. -/
theorem Optimizer.turning_point {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    ∃ b : ℝ,P.edge<P.g hs.le b ∧ deriv (P.g hs.le) b=0 ∧
      (∀ x : ℝ,P.g hs.le x≤P.g hs.le b) ∧
      (∀ g : ℝ,(1/2:ℝ)<g → g<P.g hs.le b → 0<phase P.A P.edge g) ∧
      (∀ g : ℝ,P.g hs.le b<g → phase P.A P.edge g<0) ∧ force P.A P.edge (P.g hs.le b)<0 := by
  -- The turning point is an actual global maximum of the actual inverse diagonal.
  let f := P.g hs.le
  have hc : Continuous f := (P.density.greenDiagonal_contDiff P.continuous hs.le P.pole).continuous
  have hlim := green_diagonal_limits P.density hs.le P.pole
  have hboth : Tendsto f (cocompact ℝ) (𝓝 (1/2:ℝ)) := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_sup.mpr ⟨hlim.2,hlim.1⟩
  have hstrict (x : ℝ) : (1/2:ℝ)<f x := green_diagonal_strict P.density P.mass_pos hs P.pole x
  obtain ⟨b,hmax⟩ := hc.exists_forall_ge' 0 ((hboth.eventually (Iio_mem_nhds (hstrict 0))).mono fun _ h => h.le)
  have hdiff : Differentiable ℝ f := (P.density.greenDiagonal_contDiff P.continuous hs.le P.pole).differentiable (by norm_num)
  have hz : deriv f b=0 := ((show IsMaxOn f univ b from fun x _ => hmax x).isLocalMax univ_mem).hasDerivAt_eq_zero (hdiff b).hasDerivAt
  have hF : phase P.A P.edge (f b)=0 := by have hh := P.first_integral hs b; rw [hz] at hh; simpa only [zero_pow (by decide : 2≠0)] using hh.symm
  obtain ⟨g0,hg0,hzero,hbelow,habove,hforce⟩ := phase_turning (P.parameter_signs hs).2 (P.parameter_signs hs).1
  have heq : f b=g0 := by
    rcases lt_trichotomy (f b) g0 with hlt | heq | hgt
    · exact False.elim ((hbelow _ (hstrict b) hlt).ne' hF)
    · exact heq
    · exact False.elim ((habove _ hgt).ne hF)
  have heq' : P.g hs.le b=g0 := heq
  refine ⟨b,?_,hz,hmax,?_,?_,?_⟩
  · rwa [heq']
  · rwa [heq']
  · rwa [heq']
  · rwa [heq']

/-- The genuine Fredholm optimizer has its exact central turning point, global evenness and strictly negative slope at every positive radius.
Use: fixes the printed centered profile and its unique negative spatial Jacobian before normalized quadratures.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: the attained actual turning state determines the full trajectory by
autonomous uniqueness. No second turn is possible; its negative acceleration
gives strict descent. Reflection makes its peak unique. The actual density
is even and has the same unique positive peak, so the turning center is zero. -/
theorem Optimizer.shape {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    P.edge<P.g hs.le 0 ∧ deriv (P.g hs.le) 0=0 ∧
      (∀ x : ℝ,P.g hs.le (-x)=P.g hs.le x) ∧
      (∀ x : ℝ,0<x → deriv (P.g hs.le) x<0) := by
  -- The center is proved from the actual even density, not imposed by a coordinate convention.
  let f := P.g hs.le
  let k := deriv f
  have hc : ContDiff ℝ 2 f := P.density.greenDiagonal_contDiff P.continuous hs.le P.pole
  have hf (x : ℝ) : HasDerivAt f (k x) x := (hc.differentiable (by norm_num) x).hasDerivAt
  have hk := P.force_hasDerivAt hs
  have hfirst := P.first_integral hs
  have hlower (x : ℝ) : (1/2:ℝ)<f x := green_diagonal_strict P.density P.mass_pos hs P.pole x
  have hlim := (green_diagonal_limits P.density hs.le P.pole).1
  obtain ⟨b,hbe,hb,hmax,hbelow,habove,hforce⟩ := P.turning_point hs
  have hneg (x : ℝ) (hx : b<x) : k x<0 := descending_slope hf hk hfirst hb hlower hlim hbelow habove hforce hx
  have hreflect := profile_reflect P.A P.edge b hf hk hb
  have hanti : StrictAntiOn f (Ici b) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici b) hc.continuous.continuousOn
    intro x hx
    exact hneg x (by simpa only [interior_Ici,mem_Ioi] using hx)
  have hunique (x : ℝ) (he : f x=f b) : x=b := by
    rcases lt_trichotomy x b with hlt | heq | hgt
    · have hh := hanti (show b∈Ici b from mem_Ici.mpr le_rfl) (show 2*b-x∈Ici b from mem_Ici.mpr (by linarith)) (show b<2*b-x by linarith)
      rw [hreflect.1 x,he] at hh
      exact False.elim (lt_irrefl _ hh)
    · exact heq
    · have hh := hanti (show b∈Ici b from mem_Ici.mpr le_rfl) hgt.le hgt
      rw [he] at hh
      exact False.elim (lt_irrefl _ hh)
  have hvalues : f (-b)=f b := by
    have heq := congrArg (fun r : ℝ => 2*s*r) (P.radial.even b)
    rw [P.density_formula hs (-b),P.density_formula hs b] at heq
    have hA := (P.parameter_signs hs).2
    have he2 : (max (f (-b)-P.edge) 0)^2=(max (f b-P.edge) 0)^2 := by nlinarith [sq_pos_of_pos hA]
    have he1 := (sq_eq_sq₀ (le_max_right _ _) (le_max_right _ _)).mp he2
    rw [max_eq_left (sub_pos.mpr hbe).le] at he1
    have hleft : 0<f (-b)-P.edge := by
      by_contra! hle
      rw [max_eq_right hle] at he1
      linarith
    rw [max_eq_left hleft.le] at he1
    linarith
  have hb0 : b=0 := by have hh := hunique (-b) hvalues; linarith
  subst b
  exact ⟨hbe,hb,by simpa only [mul_zero,zero_sub] using hreflect.1,hneg⟩

end
end jacobi.Fredholm
