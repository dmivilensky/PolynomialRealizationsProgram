import jacobi.Fredholm.Support

/-!
Article: jacobi, Theorem D.7.
The genuine optimizing Green slope tends to zero. Beyond the true finite
switching radius its exact free exponential tail follows from its actual
first integral and strict branch sign. The formula is pointwise and holds
on both exterior components by genuine centered evenness.
Source: the actual Green shape, first integral and the mean value theorem.
Use: completes the slope asymptotic in the source's actual Green shape lemma.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual optimizing Green slope tends to zero at the positive infinite end.
Use: completes the slope asymptotic in the source's actual Green shape lemma.
Article: jacobi, Theorem D.7.
Proof: the genuine free-state limit gives F(g)->F(1/2)=0. The proved
negative spatial Jacobian is -sqrt(F(g)) at every positive radius,
so continuity of the actual square root determines the slope limit. -/
theorem Optimizer.green_slope_limit {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    Tendsto (deriv (P.g hs.le)) atTop (𝓝 0) := by
  -- No derivative limit is inferred solely from convergence of g; the actual zero first integral is used.
  have hc : Continuous (phase P.A P.edge) := by unfold phase; fun_prop
  have hz : phase P.A P.edge (1/2:ℝ)=0 := by
    have he : (1/2:ℝ)-P.edge≤0 := by linarith [(P.parameter_signs hs).1]
    norm_num [phase,max_eq_right he]
  have hlim := ((hc.tendsto (1/2:ℝ)).comp (green_diagonal_limits P.density hs.le P.pole).1).sqrt.neg
  simp only [hz,sqrt_zero,neg_zero] at hlim
  have heq : (fun x => -sqrt (phase P.A P.edge (P.g hs.le x)))=ᶠ[atTop] deriv (P.g hs.le) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact (P.green_jacobian hs hx).deriv.symm
  exact hlim.congr' heq

/-- At or beyond a true finite switching radius, the actual slope satisfies the free linear equation.
Use: derives the source's exact exterior matching formula from the original operator diagonal.
Article: jacobi, Theorem D.7.
Proof: radial decrease places g at or below the actual switching level.
The clipped phase is therefore (2*g-1)^2; strict diagonal positivity
selects its positive square root in the actual negative Jacobian. -/
theorem Optimizer.exterior_slope {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s)
    {a x : ℝ} (ha : 0<a) (hboundary : P.g hs.le a=P.edge) (hx : a≤x) :
    deriv (P.g hs.le) x=-(2*P.g hs.le x-1) := by
  -- The actual core boundary and actual Green order determine the clipping branch.
  have hbelow := (P.green_strictAnti hs).antitoneOn (mem_Ici.mpr ha.le) (mem_Ici.mpr (ha.le.trans hx)) hx
  rw [hboundary] at hbelow
  have hpos := green_diagonal_strict P.density P.mass_pos hs P.pole x
  change (1/2:ℝ)<P.g hs.le x at hpos
  have hphase : phase P.A P.edge (P.g hs.le x)=(2*P.g hs.le x-1)^2 := by
    unfold phase
    rw [max_eq_right (sub_nonpos.mpr hbelow),zero_pow (by decide : 3≠0),mul_zero,sub_zero]
  rw [(P.green_jacobian hs (ha.trans_le hx)).deriv,hphase,sqrt_sq (by linarith : 0≤2*P.g hs.le x-1)]

/-- The actual compact-core optimizer has the exact printed two-sided exponential Green exterior.
Use: supplies the genuine support-matching tail needed in the profile identification and envelope-family argument.
Article: jacobi, Theorem D.7.
Proof: on the actual right exterior the integrating factor
(g-1/2)*exp(2*x) has zero derivative. The convex mean value theorem
makes it constant from the genuine switching point onwards. Cancel
the positive exponential and use actual evenness for the left exterior. -/
theorem Optimizer.exterior_formula {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s)
    {a : ℝ} (ha : 0<a) (hboundary : P.g hs.le a=P.edge) {x : ℝ} (hx : a≤ |x|) :
    P.g hs.le x-(1/2:ℝ)=(P.edge-(1/2:ℝ))*exp (-2*(|x|-a)) := by
  -- The integrating factor is differentiated only on the genuine free exterior.
  let W := fun y : ℝ => (P.g hs.le y-(1/2:ℝ))*exp (2*y)
  have hW (y : ℝ) (hy : y∈Ici a) : HasDerivWithinAt W 0 (Ici a) y := by
    have hg : HasDerivAt (P.g hs.le) (deriv (P.g hs.le) y) y :=
      ((P.density.greenDiagonal_contDiff P.continuous hs.le P.pole).differentiable (by norm_num) y).hasDerivAt
    have hh := (hg.sub_const (1/2:ℝ)).mul (((hasDerivAt_id y).const_mul 2).exp)
    convert hh.hasDerivWithinAt using 1
    · rfl
    · rw [P.exterior_slope hs ha hboundary hy]
      dsimp only [id_eq]
      ring
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hW
    (fun y _ => by simp : ∀ y∈Ici a,‖(0:ℝ)‖≤0) (convex_Ici a) (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx)
  simp only [zero_mul] at hh
  have hconst : W |x|=W a := sub_eq_zero.mp (norm_eq_zero.mp (by
    exact le_antisymm hh (norm_nonneg _)))
  have habs : P.g hs.le |x|=P.g hs.le x := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h]
      exact (P.shape hs).2.2.1 x
  dsimp only [W] at hconst
  rw [habs,hboundary] at hconst
  apply (mul_right_cancel₀ (exp_ne_zero (2*|x|)))
  rw [mul_assoc,← exp_add,show -2*(|x|-a)+2*|x|=2*a by ring]
  exact hconst

/-- Every actual compact-branch optimizer has a genuine finite matching radius and the printed exterior, with no boundary hypothesis left to supply.
Use: applies the complete tail statement directly to the original attained optimizer.
Article: jacobi, Theorem D.7.
Proof: the actual compact-core theorem constructs the positive radius
and its true Green boundary value; apply the proved pointwise exterior
formula at that same radius on both complementary half-lines. -/
theorem Optimizer.compact_exterior {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s)
    (ht : P.tau hs<1) :
    ∃ a : ℝ,0<a ∧ P.g hs.le a=P.edge ∧
      (∀ x : ℝ,0<P.density.value x ↔ |x|<a) ∧
      (∀ x : ℝ,a≤ |x| → P.g hs.le x-(1/2:ℝ)=(P.edge-(1/2:ℝ))*exp (-2*(|x|-a))) := by
  obtain ⟨a,ha,hboundary,hpositive,_⟩ := P.compact_core hs ht
  exact ⟨a,ha,hboundary,hpositive,fun _ hx => P.exterior_formula hs ha hboundary hx⟩

end
end jacobi.Fredholm
