import krylov.Secant.ModelStep

/-!
Article: main_krylov, apG:mss, convergence of actual corrected models and model steps.
Use: uniform genuine column conditioning and vanishing actual normalized data
errors imply actual inverse-model convergence and superlinear error reduction.
Source: actual inverse-congruence norm bounds, openness/continuity of inversion
at the identity and the proved genuine model-step identity.
-/

namespace krylov.Secant
noncomputable section
open Matrix Filter Asymptotics Topology krylov.LinearAlgebra
open scoped Matrix Matrix.Norms.L2Operator
variable {α : Type*} {n : ℕ} {f : Filter α}

/-- Uniformly bounded actual inverse coordinates preserve every actual normalized data order.
Use: model-data convergence is transferred through actual varying bases, not a fixed surrogate.
Article: main_krylov, apG:mss, uniformly conditioned X_D→0.
Proof: the actual congruence norm is bounded by the squared actual inverse norm. -/
theorem varying_congruence_bigO (V X : α → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    {C : ℝ} (hC : 0≤C) (hV : ∀ᶠ x in f, ‖(V x)⁻¹‖≤C) :
    (fun x => inverseCongruence (V x) (X x)) =O[f] X := by
  apply IsBigO.of_bound (C^2)
  filter_upwards [hV] with x hx
  exact (inverseCongruence_norm (V x) (X x)).trans
    (mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hC).mpr hx) (norm_nonneg _))

/-- Uniform positive actual smallest gains give an actual uniform inverse-norm bound.
Use: discharges the inverse-coordinate bound from the source's stated σ≥σ₀>0 hypothesis.
Article: main_krylov, apG:mss, uniform conditioning.
Proof: take positive reciprocals of the actual least-gain lower bound. -/
theorem inverse_bound_of_leastGain (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hV : IsUnit V.det) {σ : ℝ} (hσ : 0<σ) (hgain : σ≤leastGain V) : ‖V⁻¹‖≤σ⁻¹ := by
  have hg : 0<leastGain V := inv_pos.mpr (inverse_norm_pos V hV)
  have he := (inv_le_inv₀ hg hσ).mpr hgain
  simpa only [leastGain, inv_inv] using he

/-- Actual matrix actions transfer little-o orders to actual Euclidean vector errors.
Use: zero current errors are included without division by their norm.
Article: main_krylov, apG:mss, e_(k+1)=o(e_k).
Proof: the actual operator action is bounded by its actual spectral norm times
the actual input norm; multiply the given little-o by the input's tautological order. -/
theorem matrix_vector_littleO (T : α → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (v : α → EuclideanSpace ℝ (Fin (n+1))) (s : α → ℝ) (hT : T =o[f] s) :
    (fun x => WithLp.toLp 2 (T x*ᵥ WithLp.ofLp (v x))) =o[f] (fun x => s x*‖v x‖) := by
  have hb : (fun x => WithLp.toLp 2 (T x*ᵥ WithLp.ofLp (v x))) =O[f]
      (fun x => ‖T x‖*‖v x‖) := by
    apply isBigO_of_le
    intro x
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact Matrix.l2_opNorm_mulVec (T x) (v x)
  exact hb.trans_isLittleO (hT.norm_left.mul_isBigO (isBigO_refl (fun x => ‖v x‖) f))

/-- Actual uniformly conditioned data errors tending to zero yield the full actual model convergence.
Use: applies to X_D computed by the actual physical corrected-data bridge.
Article: main_krylov, apG:mss, Ĵ_D→I, ‖Ĵ_D⁻¹‖=1+o(1), e_(k+1)=o(e_k).
Proof: the proved true congruence bound makes the actual model error vanish;
openness gives actual inverse domains, continuity gives inverse convergence,
and the exact true model-step action has an operator coefficient tending to zero. -/
theorem conditioned_model_convergence (V X A : α → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (v : α → EuclideanSpace ℝ (Fin (n+1))) {C : ℝ} (hC : 0≤C)
    (hV : ∀ᶠ x in f, ‖(V x)⁻¹‖≤C) (hX : Tendsto X f (𝓝 0)) (hA : Tendsto A f (𝓝 1)) :
    let J := fun x => 1+inverseCongruence (V x) (X x)
    Tendsto J f (𝓝 1) ∧ Tendsto (fun x => (J x)⁻¹) f (𝓝 1) ∧
    (∀ᶠ x in f, IsUnit (J x).det) ∧
    ((fun x => ‖(J x)⁻¹‖-1) =o[f] (fun _ => (1 : ℝ))) ∧
    ((fun x => WithLp.toLp 2 (WithLp.ofLp (v x)-(J x)⁻¹*ᵥ (A x*ᵥ WithLp.ofLp (v x)))) =o[f]
      (fun x => ‖v x‖)) := by
  let J := fun x => 1+inverseCongruence (V x) (X x)
  have he := (varying_congruence_bigO V X hC hV).trans_isLittleO ((isLittleO_one_iff ℝ).mpr hX)
  have ht : Tendsto J f (𝓝 1) := by
    simpa only [add_zero] using ((isLittleO_one_iff ℝ).mp he).const_add (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
  have hi : Tendsto (fun x => (J x)⁻¹) f (𝓝 1) := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse, Units.val_one, Ring.inverse_one, Function.comp_def] using
      (NormedRing.inverse_continuousAt (1 : (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)ˣ)).tendsto.comp ht
  have hu : ∀ᶠ x in f, IsUnit (J x).det :=
    (ht.eventually (Units.isOpen.mem_nhds isUnit_one)).mono fun x hx => (Matrix.isUnit_iff_isUnit_det _).mp hx
  have hn : (fun x => ‖(J x)⁻¹‖-1) =o[f] (fun _ => (1 : ℝ)) := by
    apply (isLittleO_one_iff ℝ).mpr
    simpa only [norm_one, sub_self] using hi.norm.sub_const 1
  have hjA : (fun x => J x-A x) =o[f] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (by simpa only [sub_self] using ht.sub hA)
  have hT : (fun x => (J x)⁻¹*(J x-A x)) =o[f] (fun _ => (1 : ℝ)) := by
    simpa only [one_mul] using (hi.isBigO_one ℝ).mul_isLittleO hjA
  have hv := matrix_vector_littleO _ v (fun _ => 1) hT
  simp only [one_mul] at hv
  refine ⟨ht, hi, hu, hn, hv.congr' ?_ (Filter.EventuallyEq.refl _ _)⟩
  -- Identify the constructed vector coefficient with the actual model step on its proved inverse domain.
  filter_upwards [hu] with x hx
  rw [model_step_identity (J x) (A x) hx, mulVec_mulVec]

end
end krylov.Secant
