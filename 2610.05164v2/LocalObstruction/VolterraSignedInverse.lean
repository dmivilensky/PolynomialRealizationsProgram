import «2610.05164v2».LocalObstruction.VolterraInverse

/-!
Article: 2610.05164v2, Lemma 26.
The Volterra inverse exists for arbitrary signed L1 densities and real scales.
Use: `«2610.05164v2».LocalObstruction.volterra_signedPencil_unit` feeds
`«2610.05164v2».LocalObstruction.signedJost_scale_derivative` (signed Jost scale derivative).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation. The needed form is proved here.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Filters
open scoped Topology BoundedContinuousFunction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
The stated quantitative bound `‖volterra s m f x‖ ≤ |s|/2*∫ t in Iic x, |m t| *‖f t‖`.

Use: `«2610.05164v2».LocalObstruction.volterra_signed_power_pointwise` uses this bound to
establish the stated quantitative bound `‖((s • volterraMap hm)^n) f x‖≤‖f‖*factorialBound |s|
(cumulative (fun x => |m x|) x) n`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem volterra_norm_abs_le {m f : ℝ → ℝ}
    (hf : Integrable (fun t => m t*f t)) (s x : ℝ) :
    ‖volterra s m f x‖ ≤ |s|/2*∫ t in Iic x, |m t| *‖f t‖ := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [volterra_integral hf,norm_mul,Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans ?_) (by positivity)
  apply integral_mono_of_nonneg (Eventually.of_forall (fun t => norm_nonneg _))
    (hf.norm.integrableOn.congr (Eventually.of_forall (fun t => by
      change ‖m t*f t‖=|m t| *‖f t‖
      rw [norm_mul,Real.norm_eq_abs])))
  filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
  have he : exp (-2*(x-t)) ≤ 1 := exp_le_one_iff.mpr (by change t≤x at ht;linarith)
  rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr he),Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (abs_nonneg (m t)) (sub_le_self _ (exp_pos _).le)) (norm_nonneg _)

 /--
The stated quantitative bound `‖((s • volterraMap hm)^n) f x‖≤‖f‖*factorialBound |s|
(cumulative (fun x => |m x|) x) n`.

Use: `«2610.05164v2».LocalObstruction.volterra_signed_power_norm` uses this identity to
establish the stated quantitative bound `‖(s • volterraMap hm)^n‖≤factorialBound |s| (∫ x,|m
x|) n`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Induct on `n` while keeping `x` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem volterra_signed_power_pointwise {m : ℝ → ℝ} (hm : Integrable m)
    (s : ℝ) (n : ℕ) (f : VolterraSpace) (x : ℝ) :
    ‖((s • volterraMap hm)^n) f x‖≤‖f‖*factorialBound |s| (cumulative (fun x => |m x|) x) n := by
  -- Induct on `n` while keeping `x` arbitrary; the recursive step uses the previous-stage
  -- assertion.
  induction n generalizing x with
  | zero => simpa only [pow_zero,one_apply_eq_self,factorialBound,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,div_one] using f.norm_coe_le_norm x
  | succ n ih =>
    let g := ((s • volterraMap hm)^n) f
    have hF := bounded_forcing_integrable hm g.continuous.aestronglyMeasurable g.norm_coe_le_norm
    rw [pow_succ',mul_apply_eq_comp,volterraScaled_apply]
    apply (volterra_norm_abs_le hF s x).trans
    have hdom : (∫ t in Iic x,|m t| *‖g t‖)≤
        ‖f‖*((|s|/2)^n/(n.factorial))*(cumulative (fun x => |m x|) x)^(n+1)/(n+1) := by
      calc
        _ ≤ ∫ t in Iic x,‖f‖*((|s|/2)^n/(n.factorial))*(|m t| *(cumulative (fun x => |m x|) t)^n) := by
          apply integral_mono_ae
            (hF.norm.integrableOn.congr (Eventually.of_forall (fun t => by
              change ‖m t*g t‖=|m t| *‖g t‖
              rw [norm_mul,Real.norm_eq_abs])))
            ((cumulative_power_integrable hm.abs (fun x => abs_nonneg (m x)) n).const_mul _).integrableOn
          exact Eventually.of_forall (fun t => by
            have h := mul_le_mul_of_nonneg_left (ih t) (abs_nonneg (m t))
            dsimp only [factorialBound] at h
            convert! h using 1; ring)
        _ = _ := by rw [integral_const_mul,cumulative_power_integral hm.abs (fun x => abs_nonneg (m x))];ring
    calc
      _ ≤ |s|/2*(‖f‖*((|s|/2)^n/(n.factorial))*(cumulative (fun x => |m x|) x)^(n+1)/(n+1)) :=
        mul_le_mul_of_nonneg_left hdom (by positivity)
      _ = _ := by rw [← factorialBound_step |s| (cumulative (fun x => |m x|) x) n];ring

 /--
The stated quantitative bound `‖(s • volterraMap hm)^n‖≤factorialBound |s| (∫ x,|m x|) n`.

Use: `«2610.05164v2».LocalObstruction.volterra_signedPencil_unit` uses this bound to establish
the precise assertion is `IsUnit (ContinuousLinearMap.id ℝ VolterraSpace-s • volterraMap hm)`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates `«2610.05164v2».Filters.factorialBound_nonneg`,
`«2610.05164v2».LocalObstruction.volterra_signed_power_pointwise`,
`«2610.05164v2».Filters.factorialBound_mono` with the arguments shown in the proof.
-/
theorem volterra_signed_power_norm {m : ℝ → ℝ} (hm : Integrable m)
    (s : ℝ) (n : ℕ) :
    ‖(s • volterraMap hm)^n‖≤factorialBound |s| (∫ x,|m x|) n := by
  -- Use the identities/estimates `«2610.05164v2».Filters.factorialBound_nonneg`,
  -- `«2610.05164v2».LocalObstruction.volterra_signed_power_pointwise`,
  -- `«2610.05164v2».Filters.factorialBound_mono` with the arguments shown in the proof.
  have hM : 0≤∫ x,|m x| := integral_nonneg (fun x => abs_nonneg (m x))
  apply ContinuousLinearMap.opNorm_le_bound _ (factorialBound_nonneg (abs_nonneg s) hM n)
  intro f
  rw [mul_comm (factorialBound |s| (∫ x,|m x|) n)]
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (factorialBound_nonneg (abs_nonneg s) hM n))).mpr
  intro x
  calc
    _ ≤ ‖f‖*factorialBound |s| (cumulative (fun x => |m x|) x) n := volterra_signed_power_pointwise hm s n f x
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left
        (factorialBound_mono (abs_nonneg s) (cumulative_bounds hm.abs (fun x => abs_nonneg (m x)) x).1 (cumulative_bounds hm.abs (fun x => abs_nonneg (m x)) x).2 n) (norm_nonneg _)

 /--
The precise assertion is `IsUnit (ContinuousLinearMap.id ℝ VolterraSpace-s • volterraMap hm)`.

Use: `«2610.05164v2».LocalObstruction.groundLeft_eq_signedJost` uses this assertion to
establish exact identity `groundLeft G hM=groundLeftAmplitude G • signedJost hm
(-groundParameter hm hn)`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates `«2610.05164v2».Filters.factorialBound_hasSum`,
`«2610.05164v2».LocalObstruction.volterra_signed_power_norm` with the arguments shown in the
proof.
-/
theorem volterra_signedPencil_unit {m : ℝ → ℝ} (hm : Integrable m)
    (s : ℝ) :
    IsUnit (ContinuousLinearMap.id ℝ VolterraSpace-s • volterraMap hm) := by
  -- Use the identities/estimates `«2610.05164v2».Filters.factorialBound_hasSum`,
  -- `«2610.05164v2».LocalObstruction.volterra_signed_power_norm` with the arguments shown in
  -- the proof.
  let A := s • volterraMap hm
  have ht := (factorialBound_hasSum |s| (∫ x,|m x|)).summable.tendsto_atTop_zero
  obtain ⟨n,hnorm⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).exists
  have hsmall : ‖A^n‖<1 := (volterra_signed_power_norm hm s n).trans_lt hnorm
  have hu : IsUnit (1-A^n) := isUnit_one_sub_of_norm_lt_one (x := A^n) hsmall
  let S := ∑ i∈Finset.range n,A^i
  have hc : Commute S (1-A) := by
    change S*(1-A)=(1-A)*S
    exact (geom_sum_mul_neg A n).trans (mul_neg_geom_sum A n).symm
  have hprod : IsUnit (S*(1-A)) := by rwa [geom_sum_mul_neg A n]
  exact ((hc.isUnit_mul_iff).mp hprod).2

end
end «2610.05164v2».LocalObstruction
