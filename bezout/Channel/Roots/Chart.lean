import bezout.Comparisons.RootAsymptotics.Profiles

/-!
Article: bezout, Proposition D.1, interval-independent normalized LF curves.
Use: normalized root and Prefix insertion profiles depend only on the Chebyshev
coordinate, even when that coordinate is exactly one of the roots.
Proof: the off-root quotient cancels epsilon/Delta; continuity supplies every
root value. The Prefix identity follows from its exact response-query product.
-/

namespace bezout.Channel.Roots
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- The physical eigenvalue corresponding to a prescribed Chebyshev chart point. -/
def inverseChart (I : chebyshev1.SpectralInterval) (x : ℝ) : ℝ :=
  (I.L+I.mu)/2-I.delta/2*x

/-- The physical inverse chart recovers its exact prescribed coordinate. -/
theorem z_inverseChart (I : chebyshev1.SpectralInterval) (x : ℝ) :
    I.z (inverseChart I x)=x := by
  unfold inverseChart chebyshev1.SpectralInterval.z
  field_simp [ne_of_gt I.delta_pos]
  ring

/-- The inverse chart is affine and continuous. -/
theorem continuous_inverseChart (I : chebyshev1.SpectralInterval) :
    Continuous (inverseChart I) := by unfold inverseChart; fun_prop

/-- The off-root actual physical kernel has an interval-independent normalized quotient. -/
theorem normalized_chart_quotient (I : chebyshev1.SpectralInterval) (N : ℕ)
    (e : Equiv.Perm (Fin N)) (s : Fin N) (x : ℝ)
    (hx : x≠Real.cos (angle N (e s))) :
    Lower.physicalKernel (history (steps I N e)) s (inverseChart I x) (inverseChart I x)*
      I.delta/I.epsilon N = -2*(T ℝ N).eval x/(x-Real.cos (angle N (e s))) := by
  have hd := I.delta_pos
  have hn : node I N (e s)≠inverseChart I x := by
    intro h
    apply hx
    have hz := congrArg I.z h
    rw [z_node,z_inverseChart] at hz
    exact hz.symm
  rw [history_root_quotient I N e s _ hn,I.residual_eval,z_inverseChart]
  have hdifference : node I N (e s)-inverseChart I x=
      I.delta/2*(x-Real.cos (angle N (e s))) := by unfold node inverseChart; ring
  rw [hdifference]
  unfold chebyshev1.SpectralInterval.epsilon
  field_simp [I.den_ne N,ne_of_gt hd,sub_ne_zero.mpr hx]

/-- Actual normalized root profiles agree across intervals, including their root extensions. -/
theorem normalized_chart_kernel (I J : chebyshev1.SpectralInterval) (N : ℕ)
    (e : Equiv.Perm (Fin N)) (s : Fin N) (x : ℝ) :
    Lower.physicalKernel (history (steps I N e)) s (inverseChart I x) (inverseChart I x)*
      I.delta/I.epsilon N =
    Lower.physicalKernel (history (steps J N e)) s (inverseChart J x) (inverseChart J x)*
      J.delta/J.epsilon N := by
  have hi : Continuous (fun x => Lower.physicalKernel (history (steps I N e)) s
      (inverseChart I x) (inverseChart I x)*I.delta/I.epsilon N) := by
    simp only [history_diagonalKernel]
    exact ((continuous_diagonalProfile _ _).comp (continuous_inverseChart I)).mul_const _ |>.div_const _
  have hj : Continuous (fun x => Lower.physicalKernel (history (steps J N e)) s
      (inverseChart J x) (inverseChart J x)*J.delta/J.epsilon N) := by
    simp only [history_diagonalKernel]
    exact ((continuous_diagonalProfile _ _).comp (continuous_inverseChart J)).mul_const _ |>.div_const _
  have hh := Continuous.ext_on (dense_compl_singleton (Real.cos (angle N (e s)))) hi hj
    (fun x hx => by
      have hx' : x≠Real.cos (angle N (e s)) := by simpa using hx
      rw [normalized_chart_quotient I N e s x hx',normalized_chart_quotient J N e s x hx'])
  exact congrFun hh x

/-- Prefix's actual normalized profile has no dependence on the physical interval. -/
theorem prefix_normalized_chart_formula (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0<N)
    (s : Fin N) (x : ℝ) :
    Lower.physicalKernel (Classical.history I N) s (inverseChart I x) (inverseChart I x)*
      I.delta/I.epsilon N = -4*Classical.initialWeight s*
        (U ℝ ((N-1-s.val:ℕ):ℤ)).eval x*(T ℝ s.val).eval x := by
  rw [Comparisons.RootAsymptotics.prefix_kernel I N hN,z_inverseChart]
  have he : I.epsilon N≠0 := one_div_ne_zero (I.den_ne N)
  field_simp [he,ne_of_gt I.delta_pos]

/-- Normalized Prefix profiles agree across physical intervals at identical chart points. -/
theorem prefix_normalized_chart_kernel (I J : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0<N)
    (s : Fin N) (x : ℝ) :
    Lower.physicalKernel (Classical.history I N) s (inverseChart I x) (inverseChart I x)*
      I.delta/I.epsilon N =
    Lower.physicalKernel (Classical.history J N) s (inverseChart J x) (inverseChart J x)*
      J.delta/J.epsilon N := by
  rw [prefix_normalized_chart_formula I N hN,prefix_normalized_chart_formula J N hN]

end
end bezout.Channel.Roots
