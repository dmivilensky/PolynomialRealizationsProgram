import chebyshev2.Numerics.FlowExistence
import chebyshev2.Numerics.ForwardTaylor

/-!
Article: chebyshev2, Lemma 21.
Lemma 21: complete-step existence, uniqueness, and Taylor propagation with the signed one-sided
slope.
Result: `chebyshev2.Numerics.validated_flow_step` supplies the stated article conclusion.
Source: Nedialkov, Jackson and Corliss, Validated solutions of initial value problems for ordinary
differential equations — validated Taylor flow with signed one-sided stability. The needed form is
proved here.
-/
namespace chebyshev2.Numerics
noncomputable section
open Set Real
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Pointwise equality on the specified domain: `EqOn y z (Icc a b)`.

Use: `chebyshev2.Numerics.validated_flow_step` uses this pointwise identity to establish
the identity stated in that declaration.

Article: chebyshev2, Lemma 21.

Source: Nedialkov, Jackson and Corliss, Validated solutions of initial value problems for
ordinary differential equations — validated Taylor flow with signed one-sided stability.

Proof: Use the identities/estimates `chebyshev2.Numerics.signed_linear_stability` with the
arguments shown in the proof.
-/
theorem riccati_unique {C A B y z : ℝ → ℝ} {a b : ℝ}
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hy : ContinuousOn y (Icc a b)) (hz : ContinuousOn z (Icc a b))
    (hdy : ∀ t∈Ioo a b,HasDerivAt y (C t+A t*y t+B t*y t^2) t)
    (hdz : ∀ t∈Ioo a b,HasDerivAt z (C t+A t*z t+B t*z t^2) t)
    (h0 : y a=z a) : EqOn y z (Icc a b) := by
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : ContinuousOn (fun t => A t+B t*(y t+z t)) (Icc a b) :=
    hA.add (hB.mul (hy.add hz))
  obtain ⟨L,hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  intro t ht
  have he := signed_linear_stability (e := fun t => y t-z t)
    (q := fun t => A t+B t*(y t+z t)) (hy.sub hz)
    (fun t ht => by convert (hdy t ht).sub (hdz t ht) using 1;ring)
    (fun t ht => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hL t ⟨ht.1.le,ht.2.le⟩)) ht
  simp only [h0,sub_self,abs_zero,zero_mul] at he
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm he (abs_nonneg _)))

/--
Smoothness to the stated order: `ContDiffOn ℝ N y (Icc a b)`.

Use: `chebyshev2.Numerics.validated_flow_step` uses this assertion to establish the
identity stated in that declaration.

Article: chebyshev2, Lemma 21 via `chebyshev2.Numerics.validated_flow_step`.

Source: Nedialkov, Jackson and Corliss, Validated solutions of initial value problems for
ordinary differential equations — validated Taylor flow with signed one-sided stability.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem riccati_solution_smooth {C A B y : ℝ → ℝ} {a b : ℝ} (N : ℕ)
    (hC : ContDiffOn ℝ N C (Icc a b)) (hA : ContDiffOn ℝ N A (Icc a b))
    (hB : ContDiffOn ℝ N B (Icc a b))
    (hd : ∀ t∈Icc a b,HasDerivWithinAt y (C t+A t*y t+B t*y t^2) (Icc a b) t) :
    ContDiffOn ℝ N y (Icc a b) := by
  -- The tactic block explicitly constructs the required witness or reduces the goal to the
  -- local facts stated below.
  let F := fun t v => C t+A t*v+B t*v^2
  have hm : MapsTo Prod.fst (Icc a b ×ˢ (univ : Set ℝ)) (Icc a b) := fun _ ht => ht.1
  apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (f := F) (u := univ)
    (n := (N:ℕ∞)) _ hd (fun _ _ => mem_univ _)
  exact ((hC.comp contDiffOn_fst hm).add ((hA.comp contDiffOn_fst hm).mul contDiffOn_snd)).add
    ((hB.comp contDiffOn_fst hm).mul (contDiffOn_snd.pow 2))

/--
The stated quantitative bound `|y (a+v)-∑ j∈Finset.range (N+1),normalizedWithin z (Icc a (a+h))
j a*v^j| ≤R*v^(N+1)+r*exp (L*v)`.

Use: `chebyshev2.Numerics.validated_flow_step` uses this bound to establish the identity
stated in that declaration.

Article: chebyshev2, Lemma 21.

Source: Nedialkov, Jackson and Corliss, Validated solutions of initial value problems for
ordinary differential equations — validated Taylor flow with signed one-sided stability.

Proof: Use the identities/estimates `chebyshev2.Numerics.riccati_stability`,
`chebyshev2.Numerics.forward_taylor_bound` with the arguments shown in the proof.
-/
theorem riccati_taylor_propagation {C A B y z : ℝ → ℝ} {a h l u m r R L v : ℝ}
    (N : ℕ) (hh : 0<h) (hv : v∈Icc (0:ℝ) h)
    (hy : ContinuousOn y (Icc a (a+h)))
    (hz : ContDiffOn ℝ (N+1) z (Icc a (a+h)))
    (hdy : ∀ t∈Ioo a (a+h),HasDerivAt y (C t+A t*y t+B t*y t^2) t)
    (hdz : ∀ t∈Ioo a (a+h),HasDerivAt z (C t+A t*z t+B t*z t^2) t)
    (hyY : ∀ t∈Icc a (a+h),y t∈Icc l u) (hzY : ∀ t∈Icc a (a+h),z t∈Icc l u)
    (hz0 : z a=m) (hr : |y a-m|≤r)
    (hR : ∀ t∈Icc a (a+h),|normalizedWithin z (Icc a (a+h)) (N+1) t|≤R)
    (hL : ∀ t∈Ioo a (a+h),∀ w∈Icc l u,A t+2*B t*w≤L) :
    |y (a+v)-∑ j∈Finset.range (N+1),normalizedWithin z (Icc a (a+h)) j a*v^j|
      ≤R*v^(N+1)+r*exp (L*v) := by
  -- Use the identities/estimates `chebyshev2.Numerics.riccati_stability`,
  -- `chebyshev2.Numerics.forward_taylor_bound` with the arguments shown in the proof.
  have ht : a+v∈Icc a (a+h) := ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have he := riccati_stability hy hz.continuousOn hdy hdz hyY hzY hL
    (by simpa only [hz0] using hr) ht
  have htay := forward_taylor_bound N hh hv hz hR
  have habs := abs_add_le (y (a+v)-z (a+v))
    (z (a+v)-∑ j∈Finset.range (N+1),normalizedWithin z (Icc a (a+h)) j a*v^j)
  rw [sub_add_sub_cancel] at habs
  simp only [add_sub_cancel_left] at he
  linarith

/--
The complete analytical flow lemma. The central solution is constructed; the bound applies to
every solution with initial value in Y0, without an assumed tube-membership or existence
premise for that central solution.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 21.

Source: Nedialkov, Jackson and Corliss, Validated solutions of initial value problems for
ordinary differential equations — validated Taylor flow with signed one-sided stability.

Proof: Use the identities/estimates `chebyshev2.Numerics.riccati_tube_exists`,
`chebyshev2.Numerics.riccati_solution_smooth`, `chebyshev2.Numerics.riccati_unique`
with the arguments shown in the proof.
-/
theorem validated_flow_step {C A B : ℝ → ℝ} {a h l u l0 u0 m r : ℝ}
    (N : ℕ) (hh : 0<h)
    (hC : ContDiffOn ℝ (N+1) C (Icc a (a+h)))
    (hA : ContDiffOn ℝ (N+1) A (Icc a (a+h)))
    (hB : ContDiffOn ℝ (N+1) B (Icc a (a+h)))
    (hlu : l≤u)
    (hr : ∀ w∈Icc l0 u0,|w-m|≤r)
    (htube : ∀ y0∈Icc (min l0 m) (max u0 m),∀ θ∈Icc (0:ℝ) h,
      ∀ t∈Icc a (a+h),∀ y∈Icc l u,y0+θ*(C t+A t*y+B t*y^2)∈Icc l u) :
    (∀ y0∈Icc (min l0 m) (max u0 m),∃ y : ℝ → ℝ,
      y a=y0 ∧ (∀ t∈Icc a (a+h),y t∈Icc l u) ∧
      ∀ t∈Icc a (a+h),HasDerivWithinAt y (C t+A t*y t+B t*y t^2) (Icc a (a+h)) t) ∧
    ∃ z : ℝ → ℝ,z a=m ∧ ContDiffOn ℝ (N+1) z (Icc a (a+h)) ∧
      (∀ t∈Icc a (a+h),z t∈Icc l u) ∧
      ∀ R L : ℝ,(∀ t∈Icc a (a+h),|normalizedWithin z (Icc a (a+h)) (N+1) t|≤R) →
        (∀ t∈Ioo a (a+h),∀ w∈Icc l u,A t+2*B t*w≤L) →
        ∀ y : ℝ → ℝ,ContinuousOn y (Icc a (a+h)) →
          (∀ t∈Ioo a (a+h),HasDerivAt y (C t+A t*y t+B t*y t^2) t) → y a∈Icc l0 u0 →
          ∀ v∈Icc (0:ℝ) h,
            |y (a+v)-∑ j∈Finset.range (N+1),normalizedWithin z (Icc a (a+h)) j a*v^j|
              ≤R*v^(N+1)+r*exp (L*v) ∧ y (a+v)∈Icc l u := by
  -- Use the identities/estimates `chebyshev2.Numerics.riccati_tube_exists`,
  -- `chebyshev2.Numerics.riccati_solution_smooth`,
  -- `chebyshev2.Numerics.riccati_unique` with the arguments shown in the proof.
  have hex : ∀ y0∈Icc (min l0 m) (max u0 m),∃ y : ℝ → ℝ,
      y a=y0 ∧ (∀ t∈Icc a (a+h),y t∈Icc l u) ∧
      ∀ t∈Icc a (a+h),HasDerivWithinAt y (C t+A t*y t+B t*y t^2) (Icc a (a+h)) t :=
    fun y0 hy0 => riccati_tube_exists hh.le hlu hC.continuousOn hA.continuousOn hB.continuousOn (htube y0 hy0)
  refine ⟨hex,?_⟩
  obtain ⟨z,hz0,hzY,hzd⟩ := hex m ⟨min_le_right _ _,le_max_right _ _⟩
  have hzs := riccati_solution_smooth (N+1) hC hA hB hzd
  refine ⟨z,hz0,hzs,hzY,fun R L hR hL y hy hyd hy0 v hv => ?_⟩
  obtain ⟨w,hw0,hwY,hwd⟩ := hex (y a) ⟨(min_le_left _ _).trans hy0.1,hy0.2.trans (le_max_left _ _)⟩
  have hwc := HasDerivWithinAt.continuousOn hwd
  have heq := riccati_unique hA.continuousOn hB.continuousOn hy hwc hyd
    (fun t ht => (hwd t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)) hw0.symm
  have hyY : ∀ t∈Icc a (a+h),y t∈Icc l u := fun t ht => by rw [heq ht];exact hwY t ht
  exact ⟨riccati_taylor_propagation N hh hv hy hzs hyd
    (fun t ht => (hzd t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    hyY hzY hz0 (hr _ hy0) hR hL,
    hyY (a+v) ⟨by linarith [hv.1],by linarith [hv.2]⟩⟩

end
end chebyshev2.Numerics
