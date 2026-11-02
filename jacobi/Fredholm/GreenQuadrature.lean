import jacobi.Fredholm.Jacobian

/-!
Article: jacobi, Theorem D.7.
The genuine optimizing Green diagonal itself parameterizes the entire
positive half-line, from its central turn down to the free value one half.
This second substitution retains the free exterior when the density has a
compact core. Convergence transfers by the same actual Jacobian theorem.
Source: the actual Green shape, free limit and zero first integral.
Use: gives the injective whole-tail coordinate needed by the determinant quadrature.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual Green diagonal is strictly decreasing from its central turn along the entire positive half-line.
Use: gives the injective whole-tail coordinate needed by the determinant quadrature.
Article: jacobi, Theorem D.7.
Proof: apply the mean value monotonicity theorem to the true C2 diagonal
and its already proved strictly negative derivative at every positive radius. -/
theorem Optimizer.green_strictAnti {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    StrictAntiOn (P.g hs.le) (Ici (0:ℝ)) := by
  have hc := P.density.greenDiagonal_contDiff P.continuous hs.le P.pole
  exact strictAntiOn_of_deriv_neg (convex_Ici 0) hc.continuous.continuousOn
    (fun x hx => (P.shape hs).2.2.2 x (by simpa only [interior_Ici,mem_Ioi] using hx))

/-- The actual optimizing Green branch covers the whole open interval between its free and turning values.
Use: the determinant substitution includes the genuine exterior, even when the density vanishes there.
Article: jacobi, Theorem D.7.
Proof: strict diagonal positivity and radial descent give the forward
inclusion; the true free-state limit and intermediate values give every
interior level at a finite strictly positive radius. -/
theorem Optimizer.green_image {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    P.g hs.le '' Ioi (0:ℝ)=Ioo (1/2:ℝ) (P.g hs.le 0) := by
  -- No exterior asymptotic expansion or assumed inverse is needed for surjectivity.
  apply subset_antisymm
  · rintro v ⟨x,hx,rfl⟩
    exact ⟨green_diagonal_strict P.density P.mass_pos hs P.pole x,
      P.green_strictAnti hs (show (0:ℝ)∈Ici 0 by simp) (mem_Ici.mpr hx.le) hx⟩
  · intro v hv
    obtain ⟨R,hR,hbelow⟩ := ((eventually_gt_atTop (0:ℝ)).and
      ((green_diagonal_limits P.density hs.le P.pole).1.eventually (Iio_mem_nhds hv.1))).exists
    obtain ⟨x,hx,hvalue⟩ := intermediate_value_Icc' hR.le
      (P.density.greenDiagonal_contDiff P.continuous hs.le P.pole).continuous.continuousOn
      ⟨hbelow.le,hv.2.le⟩
    exact ⟨x,lt_of_le_of_ne hx.1 (by intro heq; rw [← heq] at hvalue; exact hv.2.ne' hvalue),hvalue⟩

/-- The genuine Green radial derivative selects the negative square root of its actual phase on the whole positive half-line.
Use: fixes the true whole-tail Green Jacobian and excludes an arbitrary sign choice.
Article: jacobi, Theorem D.7.
Proof: the actual zero first integral gives equality of the squares;
the proved strict negative slope fixes the sign of the real square root. -/
theorem Optimizer.green_jacobian {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s)
    {x : ℝ} (hx : 0<x) :
    HasDerivAt (P.g hs.le) (-sqrt (phase P.A P.edge (P.g hs.le x))) x := by
  have hf := P.first_integral hs x
  have hd := (P.shape hs).2.2.2 x hx
  have he : -sqrt (phase P.A P.edge (P.g hs.le x))=deriv (P.g hs.le) x := by
    rw [← hf,Real.sqrt_sq_eq_abs,abs_of_neg hd,neg_neg]
  rw [he]
  exact ((P.density.greenDiagonal_contDiff P.continuous hs.le P.pole).differentiable (by norm_num) x).hasDerivAt

/-- Every genuine Green observable has its entire-line phase quadrature, and convergence transfers to that quadrature.
Use: evaluates the determinant core and free exterior in a single actual change of variables.
Article: jacobi, Theorem D.7.
Proof: the actual diagonal maps the positive half-line injectively onto
(1/2,g_0); its strict slope has absolute value sqrt(F). Apply the genuine
Jacobian equality and its integrability equivalence, then use evenness.
Every convergence statement concerns the original observable, not a formal integral. -/
theorem Optimizer.green_quadrature {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s)
    (F : ℝ → ℝ) (hF : Integrable (fun x => F (P.g hs.le x))) :
    IntegrableOn (fun v => F v/sqrt (phase P.A P.edge v)) (Ioo (1/2:ℝ) (P.g hs.le 0)) ∧
      (∫ x,F (P.g hs.le x))=2*
        (∫ v in (1/2:ℝ)..P.g hs.le 0,F v/sqrt (phase P.A P.edge v)) := by
  -- The reciprocal phase weight cancels only where the actual strict slope is nonzero.
  let f := P.g hs.le
  let W := fun v : ℝ => sqrt (phase P.A P.edge v)
  have hder (x : ℝ) (hx : x∈Ioi (0:ℝ)) :
      HasDerivWithinAt f (-W (f x)) (Ioi (0:ℝ)) x := (P.green_jacobian hs hx).hasDerivWithinAt
  have hinj := ((P.green_strictAnti hs).mono (show Ioi (0:ℝ)⊆Ici 0 from Ioi_subset_Ici_self)).injOn
  have hjac (x : ℝ) (hx : x∈Ioi (0:ℝ)) : |-W (f x)| • (F (f x)/W (f x))=F (f x) := by
    have hpos : 0<W (f x) := sqrt_pos.mpr (by
      rw [← P.first_integral hs x]
      exact sq_pos_of_neg ((P.shape hs).2.2.2 x hx))
    rw [smul_eq_mul,abs_of_neg (neg_neg_of_pos hpos),neg_neg]
    field_simp
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj (fun v => F v/W v)
  rw [P.green_image hs] at hchange
  have hright : (∫ x in Ioi (0:ℝ),|-W (f x)| • (F (f x)/W (f x)))=
      ∫ x in Ioi (0:ℝ),F (f x) := setIntegral_congr_fun measurableSet_Ioi hjac
  rw [hright] at hchange
  have hI := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hder hinj (fun v => F v/W v)
  rw [P.green_image hs] at hI
  have hi : IntegrableOn (fun x => |-W (f x)| • (F (f x)/W (f x))) (Ioi (0:ℝ)) :=
    hF.integrableOn.congr_fun (fun x hx => (hjac x hx).symm) measurableSet_Ioi
  refine ⟨hI.mpr hi,?_⟩
  have habs (x : ℝ) : f |x|=f x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx]
      exact (P.shape hs).2.2.1 x
  have hfull : (∫ x,F (f x))=2*(∫ x in Ioi (0:ℝ),F (f x)) := by
    simpa only [habs] using (integral_comp_abs (f := fun x => F (f x)))
  rw [hfull,← hchange,intervalIntegral.integral_of_le (by
    have he := (P.parameter_signs hs).1
    have hg := (P.shape hs).1
    linarith : (1/2:ℝ)≤P.g hs.le 0),integral_Ioc_eq_integral_Ioo]

end
end jacobi.Fredholm
