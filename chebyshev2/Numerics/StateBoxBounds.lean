import chebyshev2.Numerics.StateSegment

/-!
Article: chebyshev2, Lemma 24.
Lemma 24's state Taylor and concavity rules, linked to actual multivariable derivatives rather than
supplied surrogate scalar derivatives.
Result: `chebyshev2.Numerics.StateJetOn.state_concavity_upper` supplies the stated article
conclusion.
-/
namespace chebyshev2.Numerics
noncomputable section
open Set Real
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
The stated quantitative bound `F.value (c+v)≤β+F.gradient c 0*v 0+F.gradient c 1*v 1+H/2`.

Use: `chebyshev2.Numerics.StateJetOn.state_concavity_upper` uses this bound to establish
the stated quantitative bound `F.value (c+v)≤β+(αT*gU^2+αU*gT^2+2*γ*gU*gT)/(2*(αU*αT-γ^2))`.

Article: chebyshev2, Lemma 24.

Proof: Use the identities/estimates `chebyshev2.Numerics.StateJetOn.segment_derivatives`,
`chebyshev2.Numerics.second_order_segment_upper` with the arguments shown in the proof.
-/
theorem StateJetOn.state_taylor_upper {s : Set (Fin 3 → ℝ)} (F : StateJetOn s)
    (c v : Fin 3 → ℝ) (hseg : ∀ t∈Icc (0:ℝ) 1,c+t • v∈s) (hv : v 2=0)
    (hf : ContDiffOn ℝ 2 (fun t => F.value (c+t • v)) (Icc (0:ℝ) 1))
    {β H : ℝ} (h0 : F.value c≤β)
    (hH : ∀ t∈Icc (0:ℝ) 1,
      F.hessian (c+t • v) 0 0*(v 0)^2+
      (F.hessian (c+t • v) 0 1+F.hessian (c+t • v) 1 0)*v 0*v 1+
      F.hessian (c+t • v) 1 1*(v 1)^2≤H) :
    F.value (c+v)≤β+F.gradient c 0*v 0+F.gradient c 1*v 1+H/2 := by
  -- Use the identities/estimates `chebyshev2.Numerics.StateJetOn.segment_derivatives`,
  -- `chebyshev2.Numerics.second_order_segment_upper` with the arguments shown in the
  -- proof.
  have hder := F.segment_derivatives c v hseg
  have hg : normalizedWithin (fun t => F.value (c+t • v)) (Icc (0:ℝ) 1) 1 0=
      F.gradient c 0*v 0+F.gradient c 1*v 1 := by
    rw [(hder 0 (by norm_num)).1]
    simp [Fin.sum_univ_succ,hv]
  have hcurv : ∀ t∈Icc (0:ℝ) 1,
      2*normalizedWithin (fun t => F.value (c+t • v)) (Icc (0:ℝ) 1) 2 t≤H := by
    intro t ht
    rw [(hder t ht).2]
    convert hH t ht using 1
    simp [Fin.sum_univ_succ,hv]
    ring
  have ht := second_order_segment_upper hf (by simpa using h0) hg hcurv
  simpa only [one_smul,add_assoc] using ht

/--
The stated quantitative bound `F.value (c+v)≤β+(αT*gU^2+αU*gT^2+2*γ*gU*gT)/(2*(αU*αT-γ^2))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 24.

Proof: Use the identities/estimates `chebyshev2.Numerics.StateJetOn.state_taylor_upper`,
`chebyshev2.Numerics.concave_quadratic_upper` with the arguments shown in the proof.
-/
theorem StateJetOn.state_concavity_upper {s : Set (Fin 3 → ℝ)} (F : StateJetOn s)
    (c v : Fin 3 → ℝ) (hseg : ∀ t∈Icc (0:ℝ) 1,c+t • v∈s) (hv : v 2=0)
    (hf : ContDiffOn ℝ 2 (fun t => F.value (c+t • v)) (Icc (0:ℝ) 1))
    {β αU αT γ gU gT : ℝ} (h0 : F.value c≤β)
    (hgU : |F.gradient c 0|≤gU) (hgT : |F.gradient c 1|≤gT)
    (hUU : ∀ x∈s,F.hessian x 0 0≤-αU) (hTT : ∀ x∈s,F.hessian x 1 1≤-αT)
    (hUT : ∀ x∈s,|F.hessian x 0 1|≤γ) (hTU : ∀ x∈s,|F.hessian x 1 0|≤γ)
    (ha : 0<αU) (hD : 0<αU*αT-γ^2) :
    F.value (c+v)≤β+(αT*gU^2+αU*gT^2+2*γ*gU*gT)/(2*(αU*αT-γ^2)) := by
  -- Use the identities/estimates `chebyshev2.Numerics.StateJetOn.state_taylor_upper`,
  -- `chebyshev2.Numerics.concave_quadratic_upper` with the arguments shown in the proof.
  have hcross (x : Fin 3 → ℝ) (hx : x∈s) (i j : Fin 3) (hh : |F.hessian x i j|≤γ) :
      F.hessian x i j*v 0*v 1≤γ * |v 0| * |v 1| := by
    calc
      _≤|F.hessian x i j*v 0*v 1| := le_abs_self _
      _=|F.hessian x i j| * |v 0| * |v 1| := by rw [abs_mul,abs_mul]
      _≤γ * |v 0| * |v 1| := by gcongr
  have hcurv : ∀ t∈Icc (0:ℝ) 1,
      F.hessian (c+t • v) 0 0*(v 0)^2+
      (F.hessian (c+t • v) 0 1+F.hessian (c+t • v) 1 0)*v 0*v 1+
      F.hessian (c+t • v) 1 1*(v 1)^2≤
      -(αU * |v 0|^2-2*γ * |v 0| * |v 1|+αT * |v 1|^2) := by
    intro t ht
    have hu := mul_le_mul_of_nonneg_right (hUU _ (hseg t ht)) (sq_nonneg (v 0))
    have ht' := mul_le_mul_of_nonneg_right (hTT _ (hseg t ht)) (sq_nonneg (v 1))
    have hc := hcross _ (hseg t ht) 0 1 (hUT _ (hseg t ht))
    have hc' := hcross _ (hseg t ht) 1 0 (hTU _ (hseg t ht))
    rw [sq_abs,sq_abs]
    nlinarith
  have ht := F.state_taylor_upper c v hseg hv hf h0 hcurv
  have hg0 : F.gradient c 0*v 0≤gU * |v 0| := by
    exact (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_right hgU (abs_nonneg _))
  have hg1 : F.gradient c 1*v 1≤gT * |v 1| := by
    exact (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_right hgT (abs_nonneg _))
  have hm := concave_quadratic_upper (u := |v 0|) (v := |v 1|) (gU := gU) (gT := gT) ha hD
  linarith

/--
A point interval in one state coordinate needs curvature only in the other coordinate; no
artificial negative bound is required on the fixed axis.

The stated quantitative bound `F.value (c+v)≤β+g^2/(2*α)`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 24.

Proof: Use the identities/estimates `chebyshev2.Numerics.StateJetOn.state_taylor_upper`,
`chebyshev2.Numerics.concave_quadratic_upper_one` with the arguments shown in the proof.
-/
theorem StateJetOn.state_concavity_upper_fixed_U {s : Set (Fin 3 → ℝ)} (F : StateJetOn s)
    (c v : Fin 3 → ℝ) (hseg : ∀ t∈Icc (0:ℝ) 1,c+t • v∈s) (hv : v 2=0) (hvU : v 0=0)
    (hf : ContDiffOn ℝ 2 (fun t => F.value (c+t • v)) (Icc (0:ℝ) 1))
    {β α g : ℝ} (h0 : F.value c≤β) (hg : |F.gradient c 1|≤g)
    (hTT : ∀ x∈s,F.hessian x 1 1≤-α) (ha : 0<α) :
    F.value (c+v)≤β+g^2/(2*α) := by
  -- Use the identities/estimates `chebyshev2.Numerics.StateJetOn.state_taylor_upper`,
  -- `chebyshev2.Numerics.concave_quadratic_upper_one` with the arguments shown in the
  -- proof.
  have hcurv : ∀ t∈Icc (0:ℝ) 1,
      F.hessian (c+t • v) 0 0*(v 0)^2+
      (F.hessian (c+t • v) 0 1+F.hessian (c+t • v) 1 0)*v 0*v 1+
      F.hessian (c+t • v) 1 1*(v 1)^2≤-α*(v 1)^2 := by
    intro t ht
    simpa only [hvU,zero_pow (by decide : 2≠0),mul_zero,zero_mul,zero_add] using
      mul_le_mul_of_nonneg_right (hTT _ (hseg t ht)) (sq_nonneg (v 1))
  have ht := F.state_taylor_upper c v hseg hv hf h0 hcurv
  simp only [hvU,mul_zero,add_zero] at ht
  have hgrad : F.gradient c 1*v 1≤g * |v 1| :=
    (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_right hg (abs_nonneg _))
  have hm := concave_quadratic_upper_one (v := |v 1|) (g := g) ha
  rw [sq_abs] at hm
  nlinarith

/--
The stated quantitative bound `F.value (c+v)≤β+g^2/(2*α)`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 24.

Proof: Use the identities/estimates `chebyshev2.Numerics.StateJetOn.state_taylor_upper`,
`chebyshev2.Numerics.concave_quadratic_upper_one` with the arguments shown in the proof.
-/
theorem StateJetOn.state_concavity_upper_fixed_T {s : Set (Fin 3 → ℝ)} (F : StateJetOn s)
    (c v : Fin 3 → ℝ) (hseg : ∀ t∈Icc (0:ℝ) 1,c+t • v∈s) (hv : v 2=0) (hvT : v 1=0)
    (hf : ContDiffOn ℝ 2 (fun t => F.value (c+t • v)) (Icc (0:ℝ) 1))
    {β α g : ℝ} (h0 : F.value c≤β) (hg : |F.gradient c 0|≤g)
    (hUU : ∀ x∈s,F.hessian x 0 0≤-α) (ha : 0<α) :
    F.value (c+v)≤β+g^2/(2*α) := by
  -- Use the identities/estimates `chebyshev2.Numerics.StateJetOn.state_taylor_upper`,
  -- `chebyshev2.Numerics.concave_quadratic_upper_one` with the arguments shown in the
  -- proof.
  have hcurv : ∀ t∈Icc (0:ℝ) 1,
      F.hessian (c+t • v) 0 0*(v 0)^2+
      (F.hessian (c+t • v) 0 1+F.hessian (c+t • v) 1 0)*v 0*v 1+
      F.hessian (c+t • v) 1 1*(v 1)^2≤-α*(v 0)^2 := by
    intro t ht
    simpa only [hvT,zero_pow (by decide : 2≠0),mul_zero,add_zero] using
      mul_le_mul_of_nonneg_right (hUU _ (hseg t ht)) (sq_nonneg (v 0))
  have ht := F.state_taylor_upper c v hseg hv hf h0 hcurv
  simp only [hvT,mul_zero,add_zero] at ht
  have hgrad : F.gradient c 0*v 0≤g * |v 0| :=
    (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_right hg (abs_nonneg _))
  have hm := concave_quadratic_upper_one (v := |v 0|) (g := g) ha
  rw [sq_abs] at hm
  nlinarith

/--
The stated quantitative bound `F.value (c+v)≤β`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 24.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem StateJetOn.state_point_upper {s : Set (Fin 3 → ℝ)} (F : StateJetOn s)
    (c v : Fin 3 → ℝ) (hv : ∀ i,v i=0) {β : ℝ} (h0 : F.value c≤β) :
    F.value (c+v)≤β := by
  have he : v=0 := funext hv
  simpa only [he,add_zero] using h0

end
end chebyshev2.Numerics
