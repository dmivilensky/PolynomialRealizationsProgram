import jacobi.Continuum.PositiveFundamentalPair

/-!
Article: jacobi, Theorem D.7.
The actual positive Green factors belong to L2 at their respective ends.
They span the full global homogeneous solution space, and every solution
that is L2 near one end is a multiple of the corresponding factor.
All claims use the actual inverse kernel and its proved unit Wronskian.
Source: reduction of order, Sobolev representative integrability and infinite-measure tail limits.
Use: identifies their endpoint L2 spans as spaces of classical solutions of the source's second-order equation.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set jacobi.Continuum
open chebyshev2.Sobolev
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Both actual positive homogeneous Green solutions have the full classical C2 regularity.
Use: identifies their endpoint L2 spans as spaces of classical solutions of the source's second-order equation.
Article: jacobi, Theorem D.7.
Proof: their already proved actual derivative equations have the same
continuous potential. Apply the classical equation regularity theorem to each factor. -/
theorem L1Source.greenSolutions_contDiff (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) :
    ContDiff ℝ 2 (m.greenRightSolution s hs hp) ∧ ContDiff ℝ 2 (m.greenLeftSolution s hs hp) := by
  have hV : Continuous (fun x => 1-2*s*m.value x) := continuous_const.sub (hc.const_mul (2*s))
  exact ⟨classical_ode_contDiff hV (fun x => (m.greenRightSolution_equation hc hs hp x).1)
    (fun x => (m.greenRightSolution_equation hc hs hp x).2),
    classical_ode_contDiff hV (fun x => (m.greenLeftSolution_equation hc hs hp x).1)
    (fun x => (m.greenLeftSolution_equation hc hs hp x).2)⟩

/-- The complete actual Green kernel is the ordered product of the two positive factors, with their unit Wronskian normalization.
Use: gives the printed min/max representation for both orders of the kernel variables.
Article: jacobi, Theorem D.7.
Proof: the ordered factorization handles x<=y; symmetry gives the other order. -/
theorem L1Source.greenSolutions_kernel (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x y : ℝ) :
    m.fredholmGreen s hs hp x y=
      m.greenLeftSolution s hs hp (min x y)*m.greenRightSolution s hs hp (max x y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h,max_eq_right h]
    exact m.greenSolutions_product hs hp h
  · rw [min_eq_right h,max_eq_left h,m.fredholmGreen_symm hs hp x y]
    exact m.greenSolutions_product hs hp h

/-- The actual positive right and left Green solutions are square integrable at their respective ends.
Use: supplies existence in each of the two one-dimensional L2 solution spaces.
Article: jacobi, Theorem D.7.
Proof: on their decay half-lines both factors are fixed multiples of the
actual zero-source H1 Green representative, whose L2 membership is already proved. -/
theorem L1Source.greenSolutions_memLp (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) :
    MemLp (m.greenRightSolution s hs hp) 2 (volume.restrict (Ioi (0:ℝ))) ∧
      MemLp (m.greenLeftSolution s hs hp) 2 (volume.restrict (Iio (0:ℝ))) := by
  -- The inverse column is an actual H1 vector, giving genuine L2 membership rather than only decay.
  let G := m.fredholmGreen s hs hp
  have hi : MemLp (G 0) 2 volume := by
    have he : H1.rep (m.fredholmGreenVector s hs hp 0)=G 0 :=
      funext fun x => m.fredholmGreenVector_rep hs hp 0 x
    rw [← he]
    exact (H1.regular (m.fredholmGreenVector s hs hp 0)).value_memLp
  constructor
  · have hir : MemLp (G 0) 2 (volume.restrict (Ioi (0:ℝ))) := hi.restrict _
    have he : (fun x => (G 0 0)⁻¹*G 0 x)=ᵐ[volume.restrict (Ioi (0:ℝ))]
        m.greenRightSolution s hs hp := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [show m.greenRightSolution s hs hp x=G 0 x/G 0 0 from
        greenRightFactor_column (m.fredholmGreen_pos hs hp)
          (fun hxa haz => m.fredholmGreen_markov hs hp hxa haz) le_rfl hx.le]
      ring
    exact (memLp_congr_ae he).mp (hir.const_mul _)
  · have hil : MemLp (G 0) 2 (volume.restrict (Iio (0:ℝ))) := hi.restrict _
    apply (memLp_congr_ae (show G 0=ᵐ[volume.restrict (Iio (0:ℝ))]
        m.greenLeftSolution s hs hp from ?_)).mp hil
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    change G 0 x=greenLeftFactor G x
    rw [greenLeftFactor,ite_eq_left hx.le]
    exact m.fredholmGreen_symm hs hp 0 x

/-- The actual growing Green partner is at least one sufficiently far toward each opposite end.
Use: bounds the square-integrable solution quotient without assuming a Jost asymptotic expansion.
Article: jacobi, Theorem D.7.
Proof: the decaying factor is eventually below one half, while their
product is the actual diagonal and is always at least one half. -/
theorem L1Source.greenSolutions_large (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) :
    (∀ᶠ x in atTop,1≤m.greenLeftSolution s hs hp x) ∧
      (∀ᶠ x in atBot,1≤m.greenRightSolution s hs hp x) := by
  -- The uniform inverse-diagonal lower bound controls the growing branch at both ends.
  constructor
  · filter_upwards [(tendsto_order.1 (m.greenRightSolution_limit hs hp)).2 (1/2) (by norm_num)] with x hx
    obtain ⟨hR,hL⟩ := m.greenSolutions_pos hs hp x
    have hg := (m.fredholmGreen_diagonal hs hp x).1
    rw [m.greenSolutions_product hs hp le_rfl] at hg
    nlinarith
  · filter_upwards [(tendsto_order.1 (m.greenLeftSolution_limit hs hp)).2 (1/2) (by norm_num)] with x hx
    obtain ⟨hR,hL⟩ := m.greenSolutions_pos hs hp x
    have hg := (m.fredholmGreen_diagonal hs hp x).1
    rw [m.greenSolutions_product hs hp le_rfl] at hg
    nlinarith

/-- Every actual classical homogeneous solution is a linear combination of the two constructed positive Green factors.
Use: identifies the complete homogeneous solution space before imposing either endpoint condition.
Article: jacobi, Theorem D.7.
Proof: apply the positive fundamental-pair theorem to the actual equations
and actual unit Wronskian, all already proved for this inverse kernel. -/
theorem L1Source.greenSolutions_span (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) {f d : ℝ → ℝ}
    (hf : ∀ x,HasDerivAt f (d x) x)
    (hd : ∀ x,HasDerivAt d ((1-2*s*m.value x)*f x) x) :
    ∃ A B : ℝ,∀ x,f x=A*m.greenLeftSolution s hs hp x+B*m.greenRightSolution s hs hp x :=
  positive_fundamental_pair (fun x => (m.greenSolutions_pos hs hp x).1)
    (m.greenRightSolution_equation hc hs hp) (m.greenLeftSolution_equation hc hs hp)
    (m.greenSolutions_wronskian hc hs hp) hf hd

/-- Every classical homogeneous solution square integrable near positive infinity is a multiple of the actual positive right Green factor.
Use: proves the printed one-dimensional right L2 solution-space assertion with no extra uniqueness premise.
Article: jacobi, Theorem D.7.
Proof: expand in the actual fundamental pair. The quotient by the growing
left factor tends to its coefficient, yet its square is integrable on a tail.
The infinite-measure zero-limit theorem forces that coefficient to vanish. -/
theorem L1Source.greenRightSolution_unique (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) {f d : ℝ → ℝ}
    (hf : ∀ x,HasDerivAt f (d x) x)
    (hd : ∀ x,HasDerivAt d ((1-2*s*m.value x)*f x) x)
    {a : ℝ} (hi : MemLp f 2 (volume.restrict (Ioi a))) :
    ∃ B : ℝ,∀ x,f x=B*m.greenRightSolution s hs hp x := by
  -- Expansion and the actual endpoint ratio reduce uniqueness to an integrable constant limit.
  obtain ⟨A,B,he⟩ := m.greenSolutions_span hc hs hp hf hd
  have hL : Continuous (m.greenLeftSolution s hs hp) :=
    continuous_iff_continuousAt.mpr fun x => (m.greenLeftSolution_equation hc hs hp x).1.continuousAt
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hA : A=0 := l2_coefficient_vanishes (fun x => (m.greenSolutions_pos hs hp x).2)
    hL.measurable ((hfc.measurable.div hL.measurable).pow_const 2)
    (m.greenSolutions_large hs hp).1 (m.greenSolution_ratio_limits hs hp).2 he
    (Ioi_mem_atTop a) measurableSet_Ioi hi (fun S hS => by
      obtain ⟨b,hb⟩ := mem_atTop_sets.mp hS
      exact top_unique (by rw [← Real.volume_Ici (a := b)]; exact measure_mono hb))
  refine ⟨B,fun x => ?_⟩
  simpa only [hA,zero_mul,zero_add] using he x

/-- Every classical homogeneous solution square integrable near negative infinity is a multiple of the actual positive left Green factor.
Use: completes the two endpoint solution-space assertions of the printed Green representation.
Article: jacobi, Theorem D.7.
Proof: interchange the two actual factors and use their left-end ratio limit.
The same infinite-measure quotient argument forces the right-factor coefficient to vanish. -/
theorem L1Source.greenLeftSolution_unique (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) {f d : ℝ → ℝ}
    (hf : ∀ x,HasDerivAt f (d x) x)
    (hd : ∀ x,HasDerivAt d ((1-2*s*m.value x)*f x) x)
    {a : ℝ} (hi : MemLp f 2 (volume.restrict (Iio a))) :
    ∃ A : ℝ,∀ x,f x=A*m.greenLeftSolution s hs hp x := by
  -- Both ends share the same quotient argument; only the actual factor order changes.
  obtain ⟨A,B,he⟩ := m.greenSolutions_span hc hs hp hf hd
  have hR : Continuous (m.greenRightSolution s hs hp) :=
    continuous_iff_continuousAt.mpr fun x => (m.greenRightSolution_equation hc hs hp x).1.continuousAt
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hB : B=0 := l2_coefficient_vanishes (fun x => (m.greenSolutions_pos hs hp x).1)
    hR.measurable ((hfc.measurable.div hR.measurable).pow_const 2)
    (m.greenSolutions_large hs hp).2 (m.greenSolution_ratio_limits hs hp).1
    (fun x => (he x).trans (add_comm _ _)) (Iio_mem_atBot a) measurableSet_Iio hi (fun S hS => by
      obtain ⟨b,hb⟩ := mem_atBot_sets.mp hS
      exact top_unique (by rw [← Real.volume_Iic (a := b)]; exact measure_mono hb))
  refine ⟨A,fun x => ?_⟩
  simpa only [hB,zero_mul,add_zero] using he x

end
end jacobi.Variational
