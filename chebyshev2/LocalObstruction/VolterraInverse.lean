import chebyshev2.LocalObstruction.VolterraBanach
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Ring.GeomSum

/-!
Article: chebyshev2, Lemma 26.
The actual positive Volterra pencil is invertible on bounded continuous functions at every
nonnegative scale.
Use: `chebyshev2.LocalObstruction.volterraPencil_unit` feeds
`chebyshev2.LocalObstruction.volterraSolution_actual` (volterra Solution actual).
Proof chain: `chebyshev2.LocalObstruction.observationH_finite_joint_analytic` — chebyshev2,
Theorem 6.1; No locally sharp C1 bound from finitely many spectral observations.
Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation. The needed form is proved here.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Filters
open scoped Topology BoundedContinuousFunction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
Exact identity `(s • volterraMap hm) f x=volterra s m f x`.

Use: `chebyshev2.LocalObstruction.volterra_power_pointwise` rewrites with this identity to
establish the stated quantitative bound `‖((s • volterraMap hm)^n) f x‖≤‖f‖*factorialBound s
(cumulative m x) n`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem volterraScaled_apply {m : ℝ → ℝ} (hm : Integrable m) (s : ℝ)
    (f : VolterraSpace) (x : ℝ) : (s • volterraMap hm) f x=volterra s m f x := by
  change s*volterra 1 m f x=volterra s m f x
  unfold volterra
  ring

 /--
The stated quantitative bound `‖((s • volterraMap hm)^n) f x‖≤‖f‖*factorialBound s (cumulative
m x) n`.

Use: `chebyshev2.LocalObstruction.volterra_power_norm` uses this bound to establish the
stated quantitative bound `‖(s • volterraMap hm)^n‖≤factorialBound s (∫ x,m x) n`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Induct on `n` while keeping `x` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem volterra_power_pointwise {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    {s : ℝ} (hs : 0≤s) (n : ℕ) (f : VolterraSpace) (x : ℝ) :
    ‖((s • volterraMap hm)^n) f x‖≤‖f‖*factorialBound s (cumulative m x) n := by
  -- Induct on `n` while keeping `x` arbitrary; the recursive step uses the previous-stage
  -- assertion.
  induction n generalizing x with
  | zero => simpa only [pow_zero,one_apply_eq_self,factorialBound,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,div_one] using f.norm_coe_le_norm x
  | succ n ih =>
    let g := ((s • volterraMap hm)^n) f
    have hF := bounded_forcing_integrable hm g.continuous.aestronglyMeasurable g.norm_coe_le_norm
    rw [pow_succ',mul_apply_eq_comp,volterraScaled_apply]
    apply (volterra_norm_le hn hs hF x).trans
    have hdom : (∫ t in Iic x,m t*‖g t‖)≤
        ‖f‖*((s/2)^n/(n.factorial))*(cumulative m x)^(n+1)/(n+1) := by
      calc
        _ ≤ ∫ t in Iic x,‖f‖*((s/2)^n/(n.factorial))*(m t*(cumulative m t)^n) := by
          apply integral_mono_ae
            (hF.norm.integrableOn.congr (Eventually.of_forall (fun t => by
              change ‖m t*g t‖=m t*‖g t‖
              rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hn t)])))
            ((cumulative_power_integrable hm hn n).const_mul _).integrableOn
          exact Eventually.of_forall (fun t => by
            have h := mul_le_mul_of_nonneg_left (ih t) (hn t)
            dsimp only [factorialBound] at h
            convert! h using 1; ring)
        _ = _ := by rw [integral_const_mul,cumulative_power_integral hm hn];ring
    calc
      _ ≤ s/2*(‖f‖*((s/2)^n/(n.factorial))*(cumulative m x)^(n+1)/(n+1)) :=
        mul_le_mul_of_nonneg_left hdom (by positivity)
      _ = _ := by rw [← factorialBound_step s (cumulative m x) n];ring

 /--
The stated quantitative bound `‖(s • volterraMap hm)^n‖≤factorialBound s (∫ x,m x) n`.

Use: `chebyshev2.LocalObstruction.volterraPencil_unit` uses this bound to establish the
precise assertion is `IsUnit (ContinuousLinearMap.id ℝ VolterraSpace-s • volterraMap hm)`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates `chebyshev2.Filters.factorialBound_nonneg`,
`chebyshev2.LocalObstruction.volterra_power_pointwise`,
`chebyshev2.Filters.factorialBound_mono` with the arguments shown in the proof.
-/
theorem volterra_power_norm {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    {s : ℝ} (hs : 0≤s) (n : ℕ) :
    ‖(s • volterraMap hm)^n‖≤factorialBound s (∫ x,m x) n := by
  -- Use the identities/estimates `chebyshev2.Filters.factorialBound_nonneg`,
  -- `chebyshev2.LocalObstruction.volterra_power_pointwise`,
  -- `chebyshev2.Filters.factorialBound_mono` with the arguments shown in the proof.
  have hM : 0≤∫ x,m x := integral_nonneg hn
  apply ContinuousLinearMap.opNorm_le_bound _ (factorialBound_nonneg hs hM n)
  intro f
  rw [mul_comm (factorialBound s (∫ x,m x) n)]
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (factorialBound_nonneg hs hM n))).mpr
  intro x
  calc
    _ ≤ ‖f‖*factorialBound s (cumulative m x) n := volterra_power_pointwise hm hn hs n f x
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left
        (factorialBound_mono hs (cumulative_bounds hm hn x).1 (cumulative_bounds hm hn x).2 n) (norm_nonneg _)

 /--
The precise assertion is `IsUnit (ContinuousLinearMap.id ℝ VolterraSpace-s • volterraMap hm)`.

Use: `chebyshev2.LocalObstruction.volterraSolution_actual` uses this assertion to establish
exact identity `volterraSolution hm hv p=jostBCF (perturb_integrable hm hv p.1) hn hs`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates `chebyshev2.Filters.factorialBound_hasSum`,
`chebyshev2.LocalObstruction.volterra_power_norm` with the arguments shown in the proof.
-/
theorem volterraPencil_unit {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    {s : ℝ} (hs : 0≤s) :
    IsUnit (ContinuousLinearMap.id ℝ VolterraSpace-s • volterraMap hm) := by
  -- Use the identities/estimates `chebyshev2.Filters.factorialBound_hasSum`,
  -- `chebyshev2.LocalObstruction.volterra_power_norm` with the arguments shown in the
  -- proof.
  let A := s • volterraMap hm
  have ht := (factorialBound_hasSum s (∫ x,m x)).summable.tendsto_atTop_zero
  obtain ⟨n,hnorm⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).exists
  have hsmall : ‖A^n‖<1 := (volterra_power_norm hm hn hs n).trans_lt hnorm
  have hu : IsUnit (1-A^n) := isUnit_one_sub_of_norm_lt_one (x := A^n) hsmall
  let S := ∑ i∈Finset.range n,A^i
  have hc : Commute S (1-A) := by
    change S*(1-A)=(1-A)*S
    exact (geom_sum_mul_neg A n).trans (mul_neg_geom_sum A n).symm
  have hprod : IsUnit (S*(1-A)) := by rwa [geom_sum_mul_neg A n]
  exact ((hc.isUnit_mul_iff).mp hprod).2

end
end chebyshev2.LocalObstruction
