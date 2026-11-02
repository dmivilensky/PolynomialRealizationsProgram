import jacobi.Variational.GreenReciprocal

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The actual positive Green factors and their unit Wronskian evaluate both
half-line reciprocal-square integrals exactly. Their sum gives the genuine
identity integral (G(x,y)/g(x))² dx=2g(y). This is the spatial integral
calculation needed to match the determinant variation to the Green diagonal.
Source: the actual Green product and the nonnegative improper FTC.
Use: evaluates the left reciprocal-square homogeneous Green integral without assuming its convergence.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The left-half-line nonnegative FTC gives integrability and the exact derivative integral from a finite left limit.
Use: evaluates the left reciprocal-square homogeneous Green integral without assuming its convergence.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Source: mathlib's nonnegative improper FTC, reflected through the origin.
Proof: reflect and negate the primitive, preserving a nonnegative derivative.
The right-half-line FTC proves convergence and the value; Lebesgue reflection
transfers both integrability and its exact integral back to the left. -/
theorem integral_Iic_nonnegative_derivative {f d : ℝ → ℝ} {l : ℝ}
    (hd : ∀ x,HasDerivAt f (d x) x) (hn : ∀ x,0≤d x)
    (hf : Tendsto f atBot (𝓝 l)) (a : ℝ) :
    IntegrableOn d (Iic a) ∧ (∫ x in Iic a,d x)=f a-l := by
  -- Reflection turns the left endpoint problem into the already proved right endpoint theorem.
  have hr (x : ℝ) : HasDerivAt (fun y => -f (-y)) (d (-x)) x := by
    have hh := ((hd (-x)).comp x (hasDerivAt_neg x)).neg
    change HasDerivAt (fun y => -f (-y)) (-(d (-x)*(-1))) x at hh
    simpa only [mul_neg_one,neg_neg] using hh
  have hl : Tendsto (fun x => -f (-x)) atTop (𝓝 (-l)) := (hf.comp tendsto_neg_atTop_atBot).neg
  have hi := integrableOn_Ioi_deriv_of_nonneg' (fun x (_hx : x∈Ici (-a)) => hr x)
    (fun x _ => hn (-x)) hl
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' (fun x (_hx : x∈Ici (-a)) => hr x)
    (fun x _ => hn (-x)) hl
  have hi' : IntegrableOn (fun x => d (-x)) (Ici (-a)) := by
    rwa [integrableOn_Ici_iff_integrableOn_Ioi]
  have hiLeft : IntegrableOn d (Iic a) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let A : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [A.integrableOn_map_iff]
    simpa only [Function.comp_def,neg_preimage,neg_Iic] using hi'
  refine ⟨hiLeft,?_⟩
  rw [integral_comp_neg_Ioi,neg_neg] at he
  simpa only [neg_neg,sub_neg_eq_add,neg_add_eq_sub] using he

/-- The actual Green kernel divided by its own diagonal has the exact integrable square mass 2g(y).
Use: identifies the derivative of the spatial Green-diagonal determinant integral with the actual spectral trace.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: on either side of y the Green product cancels one factor. The
remaining squared reciprocal is the derivative of a homogeneous-solution
ratio, with a proved zero endpoint limit. The two nonnegative FTC values
are each g(y), and their genuine integrable half-lines sum to the whole line. -/
theorem L1Source.green_ratio_square_integral (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) (y : ℝ) :
    Integrable (fun x => (m.fredholmGreen s hs hp x y/m.greenDiagonal s hs hp x)^2) ∧
      (∫ x,(m.fredholmGreen s hs hp x y/m.greenDiagonal s hs hp x)^2)=2*m.greenDiagonal s hs hp y := by
  -- Both reciprocal-square tail integrals are proved convergent before splitting the actual kernel integral.
  let L := m.greenLeftSolution s hs hp
  let R := m.greenRightSolution s hs hp
  let G := m.fredholmGreen s hs hp
  let g := m.greenDiagonal s hs hp
  let F (x : ℝ) := (G x y/g x)^2
  have hLder (x : ℝ) : HasDerivAt (fun z => L z/R z) (1/R x^2) x :=
    (m.greenSolution_ratio_derivatives hc hs hp x).1
  have hRder (x : ℝ) : HasDerivAt (fun z => -R z/L z) (1/L x^2) x :=
    (m.greenSolution_ratio_derivatives hc hs hp x).2
  obtain ⟨hiL,hvalL⟩ := integral_Iic_nonnegative_derivative hLder (fun x => by positivity)
    (m.greenSolution_ratio_limits hs hp).1 y
  have hRlim : Tendsto (fun z => -R z/L z) atTop (𝓝 0) := by
    simpa only [neg_div,neg_zero] using (m.greenSolution_ratio_limits hs hp).2.neg
  have hiR := integrableOn_Ioi_deriv_of_nonneg' (fun x (_hx : x∈Ici y) => hRder x)
    (fun x _ => by positivity : ∀ x∈Ioi y,0≤1/L x^2) hRlim
  have hvalR := integral_Ioi_of_hasDerivAt_of_nonneg' (fun x (_hx : x∈Ici y) => hRder x)
    (fun x _ => by positivity : ∀ x∈Ioi y,0≤1/L x^2) hRlim
  simp only [sub_zero] at hvalL
  simp only [zero_sub,neg_div,neg_neg] at hvalR
  have hleft (x : ℝ) (hx : x≤y) : F x=R y^2*(1/R x^2) := by
    dsimp only [F,G,g,L1Source.greenDiagonal,R,L]
    rw [m.greenSolutions_product hs hp hx,m.greenSolutions_product hs hp le_rfl]
    field_simp [(m.greenSolutions_pos hs hp x).1.ne',(m.greenSolutions_pos hs hp x).2.ne']
  have hright (x : ℝ) (hx : y≤x) : F x=L y^2*(1/L x^2) := by
    dsimp only [F,G,g,L1Source.greenDiagonal,R,L]
    rw [m.fredholmGreen_symm hs hp x y,m.greenSolutions_product hs hp hx,
      m.greenSolutions_product hs hp le_rfl]
    field_simp [(m.greenSolutions_pos hs hp x).1.ne',(m.greenSolutions_pos hs hp x).2.ne']
  have hFiL : IntegrableOn F (Iic y) := (hiL.const_mul (R y^2)).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    exact (hleft x hx).symm)
  have hFiR : IntegrableOn F (Ioi y) := (hiR.const_mul (L y^2)).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hright x hx.le).symm)
  have hFi : Integrable F := by
    have hh := hFiL.union hFiR
    rwa [Iic_union_Ioi,integrableOn_univ] at hh
  refine ⟨hFi,?_⟩
  rw [← intervalIntegral.integral_Iic_add_Ioi hFiL hFiR]
  have hl : (∫ x in Iic y,F x)=R y^2*(L y/R y) := by
    rw [← hvalL,← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Iic fun x hx => hleft x hx
  have hr : (∫ x in Ioi y,F x)=L y^2*(R y/L y) := by
    rw [← hvalR,← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun x hx => hright x hx.le
  change (∫ x in Iic y,F x)+(∫ x in Ioi y,F x)=2*g y
  rw [hl,hr]
  dsimp only [g,L1Source.greenDiagonal]
  rw [m.greenSolutions_product hs hp le_rfl]
  dsimp only [L,R]
  field_simp [(m.greenSolutions_pos hs hp y).1.ne',(m.greenSolutions_pos hs hp y).2.ne']
  ring

end
end jacobi.Variational
