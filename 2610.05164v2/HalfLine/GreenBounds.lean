import «2610.05164v2».HalfLine.GreenSolution

/-!
Article: 2610.05164v2, Theorem 3.3, Appendix C.2.
`«2610.05164v2».HalfLine.greenSlope_bounded_left` and the left-limit bounds control the actual
half-line Green solution and its derivative.
Use: these are the boundary estimates for `«2610.05164v2».HalfLine.jostProfile_left_limit` in
`HalfLine/Profiles`, which fixes the causal normalization in the common-measure/filter
representation.
Source: 2610.05164v2, Appendix C.2 — half-line Green boundary estimates.
-/
namespace «2610.05164v2».HalfLine
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Continuum «2610.05164v2».Sobolev «2610.05164v2».GroundState
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `|leftGreen j x| ≤ leftGreen (fun t => |j t|) x`.

Use: `«2610.05164v2».HalfLine.convolutionSlope_abs_le_signed` uses this identity to establish
the stated quantitative bound `|convolutionSlope j t| ≤ H1.rep (convolution (fun t => |j t|))
t`.

Article: 2610.05164v2, Theorem 3.3, Appendix C.2.

Source: 2610.05164v2, Appendix C.2 — half-line Green boundary estimates.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem leftGreen_abs_le {j : ℝ → ℝ} (x : ℝ) :
    |leftGreen j x| ≤ leftGreen (fun t => |j t|) x := by
  rw [leftGreen,leftGreen,abs_mul,abs_of_pos (exp_pos _)]
  apply mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _)] using
    (norm_integral_le_integral_norm (f := fun t => exp t*j t) (μ := volume.restrict (Iic x)))

/--
The stated quantitative bound `|rightGreen j x| ≤ rightGreen (fun t => |j t|) x`.

Use: `«2610.05164v2».HalfLine.convolutionSlope_abs_le_signed` uses this identity to establish
the stated quantitative bound `|convolutionSlope j t| ≤ H1.rep (convolution (fun t => |j t|))
t`.

Article: 2610.05164v2, Theorem 3.3, Appendix C.2.

Source: 2610.05164v2, Appendix C.2 — half-line Green boundary estimates.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem rightGreen_abs_le {j : ℝ → ℝ} (x : ℝ) :
    |rightGreen j x| ≤ rightGreen (fun t => |j t|) x := by
  rw [rightGreen,rightGreen,abs_mul,abs_of_pos (exp_pos _)]
  apply mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _)] using
    (norm_integral_le_integral_norm (f := fun t => exp (-t)*j t) (μ := volume.restrict (Ioi x)))

/--
The stated quantitative bound `|convolutionSlope j t| ≤ H1.rep (convolution (fun t => |j t|))
t`.

Use: `«2610.05164v2».HalfLine.convolutionSlope_left_limit` uses this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto
(convolutionSlope j) atBot (𝓝 0)`.

Article: 2610.05164v2, Theorem 3.3, Appendix C.2.

Source: 2610.05164v2, Appendix C.2 — half-line Green boundary estimates.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.convolution_halves`,
`«2610.05164v2».HalfLine.rightGreen_abs_le`, `«2610.05164v2».HalfLine.leftGreen_abs_le` with
the arguments shown in the proof.
-/
theorem convolutionSlope_abs_le_signed {j : ℝ → ℝ} (hj : Integrable j) (t : ℝ) :
    |convolutionSlope j t| ≤ H1.rep (convolution (fun t => |j t|)) t := by
  rw [convolution_halves hj.abs]
  exact (abs_sub _ _).trans ((add_le_add (rightGreen_abs_le t) (leftGreen_abs_le t)).trans_eq (by ring))

/--
Convergence along the specified source filter to the specified limit: `Tendsto
(convolutionSlope j) atBot (𝓝 0)`.

Use: `«2610.05164v2».HalfLine.greenSlope_left_limit` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (greenSlope x j) atBot (𝓝
0)`.

Article: 2610.05164v2, Theorem 3.3, Appendix C.2.

Source: 2610.05164v2, Appendix C.2 — half-line Green boundary estimates.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem convolutionSlope_left_limit {j : ℝ → ℝ} (hj : Integrable j) :
    Tendsto (convolutionSlope j) atBot (𝓝 0) := by
  apply squeeze_zero_norm
    (fun t => by simpa only [Real.norm_eq_abs] using convolutionSlope_abs_le_signed hj t)
    (H1.rep_tendsto_zero (convolution (fun t => |j t|))).2

/--
Convergence along the specified source filter to the specified limit: `Tendsto (greenSolution x
j) atBot (𝓝 0)`.

Use: a standalone supporting limit for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.3, Appendix C.2.

Source: 2610.05164v2, Appendix C.2 — half-line Green boundary estimates.

Proof: Use the identities/estimates `«2610.05164v2».Sobolev.H1.rep_tendsto_zero` with the
arguments shown in the proof.
-/
theorem greenSolution_left_limit {j : ℝ → ℝ} (x : ℝ) :
    Tendsto (greenSolution x j) atBot (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => exp (t-x)) atBot (𝓝 0) := by
    simpa only [exp_sub,zero_div] using tendsto_exp_atBot.div_const (exp x)
  change Tendsto (fun t => (H1.rep (convolution (leftDensity j x)) t-
    exp (t-x)*H1.rep (convolution (leftDensity j x)) x)/2) atBot (𝓝 0)
  simpa only [zero_mul,sub_zero,zero_div] using
    ((H1.rep_tendsto_zero (convolution (leftDensity j x))).2.sub (he.mul_const _)).div_const 2

/--
Convergence along the specified source filter to the specified limit: `Tendsto (greenSlope x j)
atBot (𝓝 0)`.

Use: `«2610.05164v2».HalfLine.greenSlope_left_limit_of_integrableOn` uses this limit to
establish the precise assertion is `Filter.Tendsto (greenSlope x j) Filter.atBot (𝓝 0)`.

Article: 2610.05164v2, Theorem 3.3, Appendix C.2.

Source: 2610.05164v2, Appendix C.2 — half-line Green boundary estimates.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.convolutionSlope_left_limit`,
`«2610.05164v2».HalfLine.leftDensity_integrable` with the arguments shown in the proof.
-/
theorem greenSlope_left_limit {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    Tendsto (greenSlope x j) atBot (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => exp (t-x)) atBot (𝓝 0) := by
    simpa only [exp_sub,zero_div] using tendsto_exp_atBot.div_const (exp x)
  change Tendsto (fun t => (convolutionSlope (leftDensity j x) t-
    exp (t-x)*H1.rep (convolution (leftDensity j x)) x)/2) atBot (𝓝 0)
  simpa only [zero_mul,sub_zero,zero_div] using
    ((convolutionSlope_left_limit (leftDensity_integrable hj x)).sub (he.mul_const _)).div_const 2

/--
Establishes the uniform, quantified assertion `∀ t ≤ x, |greenSolution x j t| ≤ ‖convolution
(leftDensity j x)‖/sqrt 2`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.3, Appendix C.2.

Source: 2610.05164v2, Appendix C.2 — half-line Green boundary estimates.

Proof: Use the identities/estimates `«2610.05164v2».Sobolev.H1.evaluation_bound` with the
arguments shown in the proof.
-/
theorem greenSolution_bounded_left (j : ℝ → ℝ) (x : ℝ) :
    ∀ t ≤ x, |greenSolution x j t| ≤ ‖convolution (leftDensity j x)‖/sqrt 2 := by
  -- Use the identities/estimates `«2610.05164v2».Sobolev.H1.evaluation_bound` with the
  -- arguments shown in the proof.
  intro t ht
  have he : exp (t-x) ≤ 1 := exp_le_one_iff.mpr (sub_nonpos.mpr ht)
  have h1 := H1.evaluation_bound (convolution (leftDensity j x)) t
  have h2 := H1.evaluation_bound (convolution (leftDensity j x)) x
  rw [greenSolution,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  have h := abs_sub (H1.rep (convolution (leftDensity j x)) t)
    (exp (t-x)*H1.rep (convolution (leftDensity j x)) x)
  rw [abs_mul,abs_of_pos (exp_pos _)] at h
  nlinarith [mul_le_of_le_one_left (abs_nonneg (H1.rep (convolution (leftDensity j x)) x)) he]

/--
Establishes the uniform, quantified assertion `∀ t ≤ x, |greenSlope x j t| ≤ (‖convolution (fun
z => |leftDensity j x z|)‖+‖convolution (leftDensity j x)‖)/(2*sqrt 2)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.3, Appendix C.2.

Source: 2610.05164v2, Appendix C.2 — half-line Green boundary estimates.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.convolutionSlope_abs_le_signed`,
`«2610.05164v2».HalfLine.leftDensity_integrable`, `«2610.05164v2».Sobolev.H1.evaluation_bound`
with the arguments shown in the proof.
-/
theorem greenSlope_bounded_left {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    ∀ t ≤ x, |greenSlope x j t| ≤
      (‖convolution (fun z => |leftDensity j x z|)‖+‖convolution (leftDensity j x)‖)/(2*sqrt 2) := by
  -- Use the identities/estimates `«2610.05164v2».HalfLine.convolutionSlope_abs_le_signed`,
  -- `«2610.05164v2».HalfLine.leftDensity_integrable`,
  -- `«2610.05164v2».Sobolev.H1.evaluation_bound` with the arguments shown in the proof.
  intro t ht
  have he : exp (t-x) ≤ 1 := exp_le_one_iff.mpr (sub_nonpos.mpr ht)
  have h1 := (convolutionSlope_abs_le_signed (leftDensity_integrable hj x) t).trans
    ((le_abs_self _).trans (H1.evaluation_bound (convolution (fun z => |leftDensity j x z|)) t))
  have h2 := H1.evaluation_bound (convolution (leftDensity j x)) x
  rw [greenSlope,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h := abs_sub (convolutionSlope (leftDensity j x) t)
    (exp (t-x)*H1.rep (convolution (leftDensity j x)) x)
  rw [abs_mul,abs_of_pos (exp_pos _)] at h
  have hb := mul_le_of_le_one_left (abs_nonneg (H1.rep (convolution (leftDensity j x)) x)) he
  calc
    _ ≤ ((‖convolution (fun z => |leftDensity j x z|)‖/sqrt 2)+
        ‖convolution (leftDensity j x)‖/sqrt 2)/2 := by linarith
    _ = _ := by ring

end
end «2610.05164v2».HalfLine
