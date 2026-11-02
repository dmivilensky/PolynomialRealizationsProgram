import krylov.Functions.TrapezoidModulusKernel
import krylov.Functions.TrapezoidSpectral

/-!
Article: main_krylov, thm:ss1F, continuous-third-variation branch.
Use: derive the anchored corrected diagonal under a genuine oscillation
modulus, preserving stability for arbitrarily short observed segments and
arbitrarily large split parameter. Source: exact Peano kernels, the scalar
FTC and continuity of the actual third derivative.
-/
namespace krylov.Functions
noncomputable section
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Cache the canonical operator-space instances for the curried tensor.
-- This uses the ordinary operator norm at every level.
local instance trapezoidContinuousCLM2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance trapezoidContinuousCLM2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance trapezoidContinuousCLM3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance trapezoidContinuousCLM3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Actual mixed third-variation oscillation on a local set. Unlike a
Lipschitz budget it contains no distance factor. Article: thm:ss1F. -/
def ThirdVariationOscillationOn
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (eta : ℝ) (S : Set E) : Prop :=
  ∀ p ∈ S,∀ q ∈ S,∀ u v w,
    |T p u v w-T q u v w|≤eta*‖u‖*‖v‖*‖w‖

/-- A genuine Hessian diagonal has a first-order Taylor remainder
controlled by the actual local third-derivative oscillation.
Article: main_krylov, thm:ss1F, continuous D3 branch. -/
theorem hessian_diagonal_taylor_modulus
    (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (S : Set E) (hS : Convex ℝ S)
    (hT : ∀ z ∈ S,HasFDerivAt H (T z) z) (hc : ContinuousOn T S)
    (eta : ℝ) (hmod : ThirdVariationOscillationOn T eta S)
    (b x s : E) (hb : b ∈ S) (hx : x ∈ S) :
    |H x s s-H b s s-T b (x-b) s s|≤eta*‖x-b‖*‖s‖^2 := by
  let u := x-b
  have hp t (ht : t ∈ Icc (0 : ℝ) 1) : b+t • u ∈ S := by
    apply hS.add_smul_mem hb _ ht
    simpa only [u,add_sub_cancel] using hx
  let g := fun t : ℝ=>H (b+t • u) s s
  let g₁ := fun t : ℝ=>T (b+t • u) u s s
  have hd t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (g₁ t) t := by
    simpa only [map_zero,add_zero] using
      ((segment_hasDerivAt H T b u t (hT _ (hp t ht))).clm_apply
        (hasDerivAt_const t s)).clm_apply (hasDerivAt_const t s)
  have hline : ContinuousOn (fun t : ℝ=>T (b+t • u)) (Icc 0 1) :=
    hc.comp (by fun_prop : Continuous (fun t : ℝ=>b+t • u)).continuousOn hp
  have hcline : ContinuousOn g₁ (Icc 0 1) :=
    ((hline.clm_apply continuousOn_const).clm_apply continuousOn_const).clm_apply continuousOn_const
  have hdev t (ht : t ∈ Icc (0 : ℝ) 1) :
      |g₁ t-g₁ 0|≤eta*‖u‖*‖s‖^2 := by
    have hh := hmod _ (hp t ht) b hb u s s
    simpa only [g₁,zero_smul,add_zero,pow_two,mul_assoc] using hh
  have hh := scalar_unit_taylor_modulus g g₁ hd hcline _ hdev
  simpa only [g,g₁,u,one_smul,zero_smul,add_zero,add_sub_cancel] using hh

/-- Both actual multidimensional endpoint remainders follow from a
continuous third derivative and its genuine local oscillation budget.
Article: main_krylov, thm:ss1F. -/
theorem segment_trapezoid_endpoint_modulus (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (S : Set E) (hS : Convex ℝ S)
    (hD : ∀ z ∈ S,HasFDerivAt f (D z) z)
    (hH : ∀ z ∈ S,HasFDerivAt D (H z) z)
    (hT : ∀ z ∈ S,HasFDerivAt H (T z) z) (hc : ContinuousOn T S)
    (eta : ℝ) (heta : 0≤eta) (hmod : ThirdVariationOscillationOn T eta S)
    (a s : E) (ha : a ∈ S) (hb : a+s ∈ S) :
    let delta := f (a+s)-f a-(D a s+D (a+s) s)/2
    |(D (a+s)-D a) s-6*delta-H (a+s) s s|≤eta*‖s‖^3 ∧
      |delta+T (a+s) s s s/12|≤eta*‖s‖^3/12 := by
  have hp t (ht : t ∈ Icc (0 : ℝ) 1) : a+t • s ∈ S := hS.add_smul_mem ha hb ht
  let f₀ := fun t : ℝ=>f (a+t • s)
  let f₁ := fun t : ℝ=>D (a+t • s) s
  let f₂ := fun t : ℝ=>H (a+t • s) s s
  let f₃ := fun t : ℝ=>T (a+t • s) s s s
  have hd₁ t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f₀ (f₁ t) t :=
    segment_hasDerivAt f D a s t (hD _ (hp t ht))
  have hd₂ t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f₁ (f₂ t) t := by
    simpa only [map_zero,add_zero] using
      (segment_hasDerivAt D H a s t (hH _ (hp t ht))).clm_apply (hasDerivAt_const t s)
  have hd₃ t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f₂ (f₃ t) t := by
    simpa only [map_zero,add_zero] using
      ((segment_hasDerivAt H T a s t (hT _ (hp t ht))).clm_apply
        (hasDerivAt_const t s)).clm_apply (hasDerivAt_const t s)
  have hline : ContinuousOn (fun t : ℝ=>T (a+t • s)) (Icc 0 1) :=
    hc.comp (by fun_prop : Continuous (fun t : ℝ=>a+t • s)).continuousOn hp
  have hc₃ : ContinuousOn f₃ (Icc 0 1) :=
    ((hline.clm_apply continuousOn_const).clm_apply continuousOn_const).clm_apply continuousOn_const
  have hb₃ t (ht : t ∈ Icc (0 : ℝ) 1) : |f₃ t-f₃ 1|≤eta*‖s‖^3 := by
    have hh := hmod _ (hp t ht) (a+s) hb s s s
    simpa only [f₃,one_smul,pow_succ,pow_zero,one_mul,pow_two,mul_assoc] using hh
  have hh := trapezoid_endpoint_modulus f₀ f₁ f₂ f₃ hd₁ hd₂ hd₃ hc₃
    (eta*‖s‖^3) (by positivity) hb₃
  simpa only [trapezoidDefect,f₀,f₁,f₂,f₃,one_smul,zero_smul,add_zero,sub_apply] using hh

/-- The full anchored corrected diagonal is uniformly controlled by the
true third-derivative oscillation. Its split-dependent term is only
|lambda-1/2| times the actual segment length, so it remains useful when
that length tends to zero faster than the current error.
Article: main_krylov, thm:ss1F, continuous D3 remainder. -/
theorem anchored_trapezoid_remainder_continuous (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (S : Set E) (hS : Convex ℝ S)
    (hD : ∀ z ∈ S,HasFDerivAt f (D z) z)
    (hH : ∀ z ∈ S,HasFDerivAt D (H z) z)
    (hT : ∀ z ∈ S,HasFDerivAt H (T z) z) (hc : ContinuousOn T S)
    (eta : ℝ) (heta : 0≤eta) (hmod : ThirdVariationOscillationOn T eta S)
    (a s x : E) (ha : a ∈ S) (hb : a+s ∈ S) (hx : x ∈ S) (lambda : ℝ) :
    let delta := f (a+s)-f a-(D a s+D (a+s) s)/2
    let w := x-(a+(1/2 : ℝ) • s)-lambda • s
    ∃ R : ℝ,(D (a+s)-D a) s-12*lambda*delta-H x s s= -T (a+s) w s s+R ∧
      |R|≤eta*((1+|lambda-1/2|)*‖s‖+‖x-(a+s)‖)*‖s‖^2 := by
  dsimp only
  let b := a+s
  let delta := f b-f a-(D a s+D b s)/2
  let w := x-(a+(1/2 : ℝ) • s)-lambda • s
  have he := segment_trapezoid_endpoint_modulus f D H T S hS hD hH hT hc eta heta hmod a s ha hb
  have ht := hessian_diagonal_taylor_modulus H T S hS hT hc eta hmod b x s hb hx
  let e₁ := (D b-D a) s-6*delta-H b s s
  let e₂ := delta+T b s s s/12
  let e₃ := H x s s-H b s s-T b (x-b) s s
  refine ⟨e₁-12*(lambda-1/2)*e₂-e₃,?_,?_⟩
  · have hw : w=(x-b)+(1/2-lambda) • s := by dsimp only [w,b]; module
    rw [show x-(a+(1/2 : ℝ) • s)-lambda • s=w from rfl,hw]
    simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
    dsimp only [e₁,e₂,e₃]
    ring
  · have hbound : |e₁-12*(lambda-1/2)*e₂-e₃|≤|e₁|+12*|lambda-1/2| *|e₂|+|e₃| := by
      calc
        _ ≤ |e₁-12*(lambda-1/2)*e₂|+|e₃| := abs_sub _ _
        _ ≤ |e₁|+|12*(lambda-1/2)*e₂|+|e₃| := add_le_add (abs_sub _ _) le_rfl
        _ = _ := by rw [abs_mul,abs_mul]; norm_num
    calc
      _ ≤ |e₁|+12*|lambda-1/2| *|e₂|+|e₃| := hbound
      _ ≤ eta*‖s‖^3+12*|lambda-1/2| *(eta*‖s‖^3/12)+eta*‖x-b‖*‖s‖^2 :=
        add_le_add (add_le_add he.1 (mul_le_mul_of_nonneg_left he.2 (by positivity))) ht
      _ = _ := by dsimp only [b]; ring

/-- The original split condition gives a corrected-diagonal bound whose
small-modulus part depends only on the genuine segment length and current
distance to its endpoint. No uniform bound on lambda is needed.
Article: main_krylov, thm:ss1F, condition (S) and continuous D3. -/
theorem anchored_trapezoid_split_continuous (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (S : Set E) (hS : Convex ℝ S)
    (hD : ∀ z ∈ S,HasFDerivAt f (D z) z)
    (hH : ∀ z ∈ S,HasFDerivAt D (H z) z)
    (hT : ∀ z ∈ S,HasFDerivAt H (T z) z) (hc : ContinuousOn T S)
    (eta : ℝ) (heta : 0≤eta) (hmod : ThirdVariationOscillationOn T eta S)
    (a s x : E) (ha : a ∈ S) (hb : a+s ∈ S) (hx : x ∈ S) (lambda Cw B : ℝ)
    (hB : 0≤B)
    (hsplit : ‖x-(a+(1/2 : ℝ) • s)-lambda • s‖≤Cw*‖x-(a+s)‖)
    (hendpoint : ∀ u v w,|T (a+s) u v w|≤B*‖u‖*‖v‖*‖w‖) :
    let delta := f (a+s)-f a-(D a s+D (a+s) s)/2
    |(D (a+s)-D a) s-12*lambda*delta-H x s s|≤
      (B*Cw*‖x-(a+s)‖+eta*(‖s‖+(2+Cw)*‖x-(a+s)‖))*‖s‖^2 := by
  dsimp only
  let b := a+s
  let w := x-(a+(1/2 : ℝ) • s)-lambda • s
  have hw : w=(x-b)+(1/2-lambda) • s := by dsimp only [w,b]; module
  have hweighted : |lambda-1/2| *‖s‖≤(1+Cw)*‖x-b‖ := by
    have he : (1/2-lambda) • s=w-(x-b) := by rw [hw]; abel
    have hh := norm_sub_le w (x-b)
    rw [←he,norm_smul,Real.norm_eq_abs,abs_sub_comm (1/2 : ℝ) lambda] at hh
    nlinarith only [hh,hsplit]
  obtain ⟨R,he,hR⟩ := anchored_trapezoid_remainder_continuous f D H T S hS
    hD hH hT hc eta heta hmod a s x ha hb hx lambda
  rw [he]
  change |-T b w s s+R|≤
    (B*Cw*‖x-b‖+eta*(‖s‖+(2+Cw)*‖x-b‖))*‖s‖^2
  change |R|≤eta*((1+|lambda-1/2|)*‖s‖+‖x-b‖)*‖s‖^2 at hR
  have ht : |T b w s s|≤B*Cw*‖x-b‖*‖s‖^2 := by
    have hh := hendpoint w s s
    have hm := mul_le_mul_of_nonneg_left hsplit (by positivity : 0≤B*‖s‖^2)
    nlinarith only [hh,hm]
  have hmodulus : eta*((1+|lambda-1/2|)*‖s‖+‖x-b‖)*‖s‖^2≤
      eta*(‖s‖+(2+Cw)*‖x-b‖)*‖s‖^2 := by
    have hh := mul_le_mul_of_nonneg_left hweighted (mul_nonneg heta (sq_nonneg ‖s‖))
    nlinarith only [hh]
  have hsum := abs_add_le (-T b w s s) R
  rw [abs_neg] at hsum
  exact hsum.trans (by nlinarith only [ht,hR,hmodulus])

/-- Operator-norm oscillation controls every actual mixed tensor value.
Article: main_krylov, thm:ss1F, continuous D3 branch. -/
theorem thirdVariationOscillationOn_of_norm
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (eta : ℝ) (S : Set E)
    (hmod : ∀ p ∈ S,∀ q ∈ S,‖T p-T q‖≤eta) : ThirdVariationOscillationOn T eta S := by
  intro p hp q hq u v w
  have h₁ := (T p-T q).le_opNorm u
  have h₂ := ((T p-T q) u).le_opNorm v
  have h₃ := ((T p-T q) u v).le_opNorm w
  change ‖(T p-T q) u v w‖≤_
  exact h₃.trans ((mul_le_mul_of_nonneg_right
    (h₂.trans (mul_le_mul_of_nonneg_right
      (h₁.trans (mul_le_mul_of_nonneg_right (hmod p hp q hq) (norm_nonneg u))) (norm_nonneg v)))
    (norm_nonneg w)).trans_eq (by ring))

/-- Continuity of the actual third derivative supplies an arbitrarily
small common oscillation budget on a genuine shrinking ball.
Article: main_krylov, thm:ss1F, only continuous D3 required. -/
theorem thirdVariationOscillation_small_ball
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (xstar : E)
    (hc : ContinuousAt T xstar) (eta : ℝ) (heta : 0<eta) :
    ∃ r : ℝ,0<r ∧ ThirdVariationOscillationOn T eta (Metric.ball xstar r) := by
  obtain ⟨r,hr,hlocal⟩ := Metric.continuousAt_iff.mp hc (eta/2) (by positivity)
  refine ⟨r,hr,thirdVariationOscillationOn_of_norm T eta _ ?_⟩
  intro p hp q hq
  have hpp := hlocal hp
  have hqq := hlocal hq
  rw [dist_eq_norm] at hpp hqq
  have hh := norm_sub_le (T p-T xstar) (T q-T xstar)
  rw [sub_sub_sub_cancel_right] at hh
  exact hh.trans (by linarith only [hpp,hqq])


end
end krylov.Functions
