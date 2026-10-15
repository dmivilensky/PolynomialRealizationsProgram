import «2610.05164v2».Numerics.StateBoxBounds

/-!
Article: 2610.05164v2, Lemma 24.
The remaining analytic rules of Lemma 24: arbitrary segment Taylor, time-centre Taylor with
nonnegative curvature clipping, and the first-order state bound.
Result: `«2610.05164v2».Numerics.StateJetOn.state_gradient_upper` supplies the stated article
conclusion.
-/
namespace «2610.05164v2».Numerics
noncomputable section
open Set Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/--
The derivative within the stated domain: `HasDerivWithinAt (fun t => F.value (c+t • v)) (∑
i,F.gradient (c+t • v) i*v i) (Icc (0:ℝ) 1) t`.

Use: `«2610.05164v2».Numerics.StateJetOn.segment_first_order_upper` uses this derivative
formula to prove the bound `F.value (c+v)≤β+L`.

Article: 2610.05164v2, Lemma 24 via
`«2610.05164v2».Numerics.StateJetOn.segment_first_order_upper`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.gradientMap_apply` with the
arguments shown in the proof.
-/
theorem StateJetOn.segment_hasDerivWithinAt {d : ℕ} {s : Set (Fin d → ℝ)}
    (F : StateJetOn s) (c v : Fin d → ℝ)
    (hseg : ∀ t∈Icc (0:ℝ) 1,c+t • v∈s) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t => F.value (c+t • v))
      (∑ i,F.gradient (c+t • v) i*v i) (Icc (0:ℝ) 1) t := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.gradientMap_apply` with the
  -- arguments shown in the proof.
  have hp : HasDerivWithinAt (fun t : ℝ => c+t • v) v (Icc (0:ℝ) 1) t := by
    convert ((hasDerivAt_const t c).add ((hasDerivAt_id t).smul_const v)).hasDerivWithinAt using 1
    · rfl
    · simp
  convert! (F.value_derivative (c+t • v) (hseg t ht)).comp_hasDerivWithinAt t hp hseg using 1
  exact (gradientMap_apply (F.gradient (c+t • v)) v).symm

/--
The stated quantitative bound `F.value (c+v)≤β+(∑ i,F.gradient c i*v i)+H/2`.

Use: `«2610.05164v2».Numerics.StateJetOn.time_taylor_upper` uses this bound to establish the
stated quantitative bound `F.value (c+v)≤β+F.gradient c 2*v 2+max 0 H*(v 2)^2/2`.

Article: 2610.05164v2, Lemma 24.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.StateJetOn.segment_derivatives`,
`«2610.05164v2».Numerics.second_order_segment_upper` with the arguments shown in the proof.
-/
theorem StateJetOn.segment_taylor_upper {d : ℕ} {s : Set (Fin d → ℝ)}
    (F : StateJetOn s) (c v : Fin d → ℝ)
    (hseg : ∀ t∈Icc (0:ℝ) 1,c+t • v∈s)
    (hf : ContDiffOn ℝ 2 (fun t => F.value (c+t • v)) (Icc (0:ℝ) 1))
    {β H : ℝ} (h0 : F.value c≤β)
    (hH : ∀ t∈Icc (0:ℝ) 1,∑ i,∑ j,F.hessian (c+t • v) i j*v i*v j≤H) :
    F.value (c+v)≤β+(∑ i,F.gradient c i*v i)+H/2 := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.StateJetOn.segment_derivatives`,
  -- `«2610.05164v2».Numerics.second_order_segment_upper` with the arguments shown in the
  -- proof.
  have hd := F.segment_derivatives c v hseg
  have hg := (hd 0 (by norm_num)).1
  simp only [zero_smul,add_zero] at hg
  have hc : ∀ t∈Icc (0:ℝ) 1,
      2*normalizedWithin (fun t => F.value (c+t • v)) (Icc (0:ℝ) 1) 2 t≤H :=
    fun t ht => ((hd t ht).2.le).trans (hH t ht)
  simpa only [zero_smul,add_zero,one_smul] using second_order_segment_upper hf
    (by simpa only [zero_smul,add_zero] using h0) hg hc

/--
The stated quantitative bound `F.value (c+v)≤β+F.gradient c 2*v 2+max 0 H*(v 2)^2/2`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Lemma 24.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.StateJetOn.segment_taylor_upper`
with the arguments shown in the proof.
-/
theorem StateJetOn.time_taylor_upper {s : Set (Fin 3 → ℝ)} (F : StateJetOn s)
    (c v : Fin 3 → ℝ) (hseg : ∀ t∈Icc (0:ℝ) 1,c+t • v∈s)
    (hvU : v 0=0) (hvT : v 1=0)
    (hf : ContDiffOn ℝ 2 (fun t => F.value (c+t • v)) (Icc (0:ℝ) 1))
    {β H : ℝ} (h0 : F.value c≤β)
    (hTT : ∀ t∈Icc (0:ℝ) 1,F.hessian (c+t • v) 2 2≤H) :
    F.value (c+v)≤β+F.gradient c 2*v 2+max 0 H*(v 2)^2/2 := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.StateJetOn.segment_taylor_upper`
  -- with the arguments shown in the proof.
  have hc : ∀ t∈Icc (0:ℝ) 1,
      ∑ i,∑ j,F.hessian (c+t • v) i j*v i*v j≤max 0 H*(v 2)^2 := by
    intro t ht
    simpa [Fin.sum_univ_succ,hvU,hvT,pow_two,mul_assoc] using
      mul_le_mul_of_nonneg_right ((hTT t ht).trans (le_max_right 0 H)) (sq_nonneg (v 2))
  have ht := F.segment_taylor_upper c v hseg hf h0 hc
  simpa [Fin.sum_univ_succ,hvU,hvT] using ht

/--
Mean-value bound in any direction, with no second derivative premise.

The stated quantitative bound `F.value (c+v)≤β+L`.

Use: `«2610.05164v2».Numerics.StateJetOn.state_gradient_upper` uses this bound to establish the
stated quantitative bound `F.value (c+v)≤β+L`.

Article: 2610.05164v2, Lemma 24.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.StateJetOn.segment_hasDerivWithinAt` with the arguments shown in the
proof.
-/
theorem StateJetOn.segment_first_order_upper {d : ℕ} {s : Set (Fin d → ℝ)}
    (F : StateJetOn s) (c v : Fin d → ℝ)
    (hseg : ∀ t∈Icc (0:ℝ) 1,c+t • v∈s) {β L : ℝ} (h0 : F.value c≤β)
    (hgrad : ∀ t∈Icc (0:ℝ) 1,∑ i,F.gradient (c+t • v) i*v i≤L) :
    F.value (c+v)≤β+L := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.StateJetOn.segment_hasDerivWithinAt`
  -- with the arguments shown in the proof.
  let f : ℝ → ℝ := fun t => F.value (c+t • v)-L*t
  have hd : ∀ t∈Icc (0:ℝ) 1,HasDerivWithinAt f
      ((∑ i,F.gradient (c+t • v) i*v i)-L) (Icc (0:ℝ) 1) t := by
    intro t ht
    convert! (F.segment_hasDerivWithinAt c v hseg ht).sub
      ((hasDerivWithinAt_id t _).const_mul L) using 1
    simp
  have hm : AntitoneOn f (Icc (0:ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) (HasDerivWithinAt.continuousOn hd)
    · intro t ht
      have ht' : t∈Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using ht
      exact (hd t ⟨ht'.1.le,ht'.2.le⟩).mono interior_subset
    · intro t ht
      have ht' : t∈Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using ht
      exact sub_nonpos.mpr (hgrad t ⟨ht'.1.le,ht'.2.le⟩)
  have hb := hm (show (0:ℝ)∈Icc 0 1 by norm_num) (show (1:ℝ)∈Icc 0 1 by norm_num) (by norm_num)
  simp only [f,one_smul,mul_one,zero_smul,add_zero,mul_zero,sub_zero] at hb
  linarith

/--
The stated quantitative bound `F.value (c+v)≤β+L`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Lemma 24.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.StateJetOn.segment_first_order_upper` with the arguments shown in the
proof.
-/
theorem StateJetOn.state_gradient_upper {s : Set (Fin 3 → ℝ)} (F : StateJetOn s)
    (c v : Fin 3 → ℝ) (hseg : ∀ t∈Icc (0:ℝ) 1,c+t • v∈s) (hv : v 2=0)
    {β L : ℝ} (h0 : F.value c≤β)
    (hgrad : ∀ t∈Icc (0:ℝ) 1,
      F.gradient (c+t • v) 0*v 0+F.gradient (c+t • v) 1*v 1≤L) :
    F.value (c+v)≤β+L := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.StateJetOn.segment_first_order_upper` with the arguments shown in
  -- the proof.
  apply F.segment_first_order_upper c v hseg h0
  intro t ht
  simpa [Fin.sum_univ_succ,hv] using hgrad t ht

end
end «2610.05164v2».Numerics
