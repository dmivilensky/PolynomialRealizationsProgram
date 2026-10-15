import «2610.05164v2».Sobolev.Energy

/-!
Article: 2610.05164v2, Theorem 5.1.
Exact energy of the continuous representative, with its actual AE derivative.
Use: `«2610.05164v2».Sobolev.SobolevRegular.causal_representation` feeds
`«2610.05164v2».Sobolev.H1.range_iff` (range iff).
Proof chain: `«2610.05164v2».PrescribedSpeed.SpeedData.groundParameter_density` — 2610.05164v2,
Theorem 5.1; General measurable speed gives a density with the prescribed ground parameter.
Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel. The needed form is proved here.
-/
namespace «2610.05164v2».Sobolev
noncomputable section
open «2610.05164v2».Continuum Set MeasureTheory Real Filter
open scoped InnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false

/--
Convergence along the specified source filter to the specified limit: `Tendsto f atTop (𝓝 0) ∧
Tendsto f atBot (𝓝 0)`.

Use: `«2610.05164v2».Sobolev.SobolevRegular.eq_zero_of_derivative_add` uses this limit to
establish exact identity `f=0`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.groundProfile_left_limit`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `«2610.05164v2».Sobolev.SobolevRegular.square_tendsto_zero`
with the arguments shown in the proof.
-/
theorem SobolevRegular.tendsto_zero {f d : ℝ → ℝ} (h : SobolevRegular f d) :
    Tendsto f atTop (𝓝 0) ∧ Tendsto f atBot (𝓝 0) := by
  have aux {l : Filter ℝ} (ht : Tendsto (fun x => f x^2) l (𝓝 0)) :
      Tendsto f l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Function.comp_def, sqrt_sq_eq_abs, Real.norm_eq_abs, sqrt_zero] using
      (continuous_sqrt.tendsto 0).comp ht
  exact ⟨aux h.square_tendsto_zero.1, aux h.square_tendsto_zero.2⟩

/--
The stated quantitative bound `SobolevRegular (fun x => f x-g x) (fun x => d x-e x) where
value_memLp`.

Use: `«2610.05164v2».Sobolev.SobolevRegular.causal_representation` uses this identity to
establish constructs witnesses with the exact properties `∃ g : FeatureSpace, f=causalValue g ∧
g =ᵐ[volume] (fun x => d x+f x)`.

Article: 2610.05164v2, Theorem 5.1 via
`«2610.05164v2».PrescribedSpeed.SpeedData.groundParameter_density`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem SobolevRegular.sub {f d g e : ℝ → ℝ}
    (hf : SobolevRegular f d) (hg : SobolevRegular g e) :
    SobolevRegular (fun x => f x-g x) (fun x => d x-e x) where
  value_memLp := hf.value_memLp.sub hg.value_memLp
  derivative_memLp := hf.derivative_memLp.sub hg.derivative_memLp
  locally_ac a b := by
    -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
    -- at an arbitrary point in that intersection.
    apply ((hf.locally_ac a b).sub (hg.locally_ac a b)).congr
    intro x _
    rfl
  derivative_ae := by
    filter_upwards [hf.derivative_ae, hg.derivative_ae] with x hx hy
    exact hx.sub hy

/--
The homogeneous first-order equation has no nonzero H1 solution.

Exact identity `f=0`.

Use: `«2610.05164v2».Sobolev.SobolevRegular.causal_representation` uses this identity to
establish constructs witnesses with the exact properties `∃ g : FeatureSpace, f=causalValue g ∧
g =ᵐ[volume] (fun x => d x+f x)`.

Article: 2610.05164v2, Theorem 5.1 via
`«2610.05164v2».PrescribedSpeed.SpeedData.groundParameter_density`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem SobolevRegular.eq_zero_of_derivative_add {f d : ℝ → ℝ}
    (h : SobolevRegular f d) (hz : ∀ᵐ x, d x+f x=0) : f=0 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hac (a b : ℝ) : AbsolutelyContinuousOnInterval (fun x => exp x*f x) a b := by
    have he : AbsolutelyContinuousOnInterval exp a b :=
      (contDiff_exp.contDiffOn : ContDiffOn ℝ 1 exp (uIcc a b)).absolutelyContinuousOnInterval
    apply (he.mul (h.locally_ac a b)).congr
    intro x _
    rfl
  have hder : ∀ᵐ x, HasDerivAt (fun x => exp x*f x) 0 x := by
    filter_upwards [h.derivative_ae, hz] with x hx hxz
    convert (hasDerivAt_exp x).mul hx using 1
    linear_combination -(exp x)*hxz
  have he (x : ℝ) : exp x*f x=f 0 := by
    obtain ⟨c,hc⟩ := (hac 0 x).const_of_ae_hasDerivAt_zero
      (hder.mono (fun _ hx _ => hx))
    have h0 := hc 0 left_mem_uIcc
    have hx := hc x right_mem_uIcc
    simpa only [exp_zero, one_mul] using hx.trans h0.symm
  -- Record the convergence ht with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have ht : Tendsto (fun x => exp x*f x) atBot (𝓝 0) := by
    simpa only [mul_zero] using tendsto_exp_atBot.mul h.tendsto_zero.2
  have hf0 : f 0=0 := tendsto_nhds_unique
    (by simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => f 0) atBot (𝓝 (f 0)))) ht
  funext x
  have hx : exp x*f x=0 := (he x).trans hf0
  exact (mul_eq_zero.mp hx).resolve_left (exp_ne_zero x)

/--
Every literal H1 representative is the causal representative of f'+f. This is an onto
statement, not an assumed Sobolev identification.

Constructs witnesses with the exact properties `∃ g : FeatureSpace, f=causalValue g ∧ g
=ᵐ[volume] (fun x => d x+f x)`.

Use: `«2610.05164v2».Sobolev.H1.range_iff` uses this identity to establish equivalence of the
displayed criteria: `(∃ u : H1, rep u=f) ↔ ∃ d, SobolevRegular f d`.

Article: 2610.05164v2, Theorem 5.1 via
`«2610.05164v2».PrescribedSpeed.SpeedData.groundParameter_density`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem SobolevRegular.causal_representation {f d : ℝ → ℝ}
    (h : SobolevRegular f d) :
    ∃ g : FeatureSpace, f=causalValue g ∧
      g =ᵐ[volume] (fun x => d x+f x) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hm : MemLp (fun x => d x+f x) 2 volume := h.derivative_memLp.add h.value_memLp
  let g : FeatureSpace := hm.toLp (fun x => d x+f x)
  have hg : g =ᵐ[volume] (fun x => d x+f x) := hm.coeFn_toLp
  refine ⟨g, ?_, hg⟩
  have hr := h.sub (causalValue_sobolev g)
  have hz : ∀ᵐ x, (d x-(g x-causalValue g x))+(f x-causalValue g x)=0 := by
    filter_upwards [hg] with x hx
    rw [hx]
    ring
  have he := hr.eq_zero_of_derivative_add hz
  funext x
  have hx := congr_fun he x
  change f x-causalValue g x=0 at hx
  exact sub_eq_zero.mp hx

/--
Exact energy of the continuous representative, with its actual AE derivative.

Exact identity `‖causalValueLp g‖^2+‖causalDerivativeLp g‖^2=‖g‖^2`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 5.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem causalValue_energy_Lp (g : FeatureSpace) :
    ‖causalValueLp g‖^2+‖causalDerivativeLp g‖^2=‖g‖^2 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [l2_norm_sq, l2_norm_sq]
  have hu : (fun x => causalValueLp g x^2) =ᵐ[volume] (fun x => causalValue g x^2) :=
    (causalValueLp_coe g).fun_comp (fun x => x^2)
  have hd : (fun x => causalDerivativeLp g x^2) =ᵐ[volume]
      (fun x => (g x-causalValue g x)^2) :=
    (causalDerivativeLp_coe g).fun_comp (fun x => x^2)
  rw [integral_congr_ae hu, integral_congr_ae hd]
  exact causalValue_energy g

end
end «2610.05164v2».Sobolev
