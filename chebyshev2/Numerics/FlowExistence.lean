import chebyshev2.Numerics.RiccatiFlow

/-!
Article: chebyshev2, Lemma 21.
Existence on a complete validated step.
Use: `chebyshev2.Numerics.riccati_tube_exists` feeds
`chebyshev2.Numerics.flowTubeCheck_exists` (A successful rational tube check supplies the
whole-step existence premise for every initial value in the hull, including the Taylor centre).
Proof chain: `chebyshev2.Numerics.validated_flow_step` — chebyshev2, Lemma 21; Validated
signed-slope flow: existence, uniqueness and Taylor propagation.
-/
namespace chebyshev2.Numerics
noncomputable section
open Set Real MeasureTheory intervalIntegral Metric
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Defines `clamp` of type `ℝ` by `max l (min u x)`.

Use: `chebyshev2.Numerics.clamp_eq` rewrites with this definition to establish exact
identity `clamp l u x=x`.

Article: chebyshev2, Lemma 21 via `chebyshev2.Numerics.validated_flow_step`.
-/
def clamp (l u x : ℝ) : ℝ := max l (min u x)

/--
Membership in the specified domain/enclosure: `clamp l u x∈Icc l u`.

Use: `chebyshev2.Numerics.tube_exists` uses this assertion to establish constructs
witnesses with the exact properties `∃ y : ℝ → ℝ,y a=y0 ∧ (∀ t∈Icc a (a+h),y t∈Icc l u) ∧ ∀
t∈Icc a (a+h),HasDerivWithinAt y (F t (y t)) (Icc a (a+h)) t`.

Article: chebyshev2, Lemma 21 via `chebyshev2.Numerics.validated_flow_step`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem clamp_mem {l u : ℝ} (hlu : l≤u) (x : ℝ) : clamp l u x∈Icc l u :=
  ⟨le_max_left _ _,max_le hlu (min_le_left _ _)⟩

/--
Exact identity `clamp l u x=x`.

Use: `chebyshev2.Numerics.tube_exists` uses this identity to establish constructs witnesses
with the exact properties `∃ y : ℝ → ℝ,y a=y0 ∧ (∀ t∈Icc a (a+h),y t∈Icc l u) ∧ ∀ t∈Icc a
(a+h),HasDerivWithinAt y (F t (y t)) (Icc a (a+h)) t`.

Article: chebyshev2, Lemma 21 via `chebyshev2.Numerics.validated_flow_step`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem clamp_eq {l u x : ℝ} (hx : x∈Icc l u) : clamp l u x=x := by simp [clamp,min_eq_right hx.2,max_eq_right hx.1]

/--
The displayed Lipschitz bound: `LipschitzWith 1 (clamp l u)`.

Use: `chebyshev2.Numerics.tube_exists` uses this assertion to establish constructs
witnesses with the exact properties `∃ y : ℝ → ℝ,y a=y0 ∧ (∀ t∈Icc a (a+h),y t∈Icc l u) ∧ ∀
t∈Icc a (a+h),HasDerivWithinAt y (F t (y t)) (Icc a (a+h)) t`.

Article: chebyshev2, Lemma 21 via `chebyshev2.Numerics.validated_flow_step`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem clamp_lipschitz (l u : ℝ) : LipschitzWith 1 (clamp l u) :=
  (LipschitzWith.id.const_min u).const_max l

/--
Constructs witnesses with the exact properties `∃ y : ℝ → ℝ,y a=y0 ∧ (∀ t∈Icc a (a+h),y t∈Icc l
u) ∧ ∀ t∈Icc a (a+h),HasDerivWithinAt y (F t (y t)) (Icc a (a+h)) t`.

Use: `chebyshev2.Numerics.riccati_tube_exists` uses this identity to establish constructs
witnesses with the exact properties `∃ y : ℝ → ℝ,y a=y0 ∧ (∀ t∈Icc a (a+h),y t∈Icc l u) ∧ ∀
t∈Icc a (a+h),HasDerivWithinAt y (C t+A t*y t+B t*y t^2) (Icc a (a+h)) t`.

Article: chebyshev2, Lemma 21 via `chebyshev2.Numerics.validated_flow_step`.

Proof: Clamp the state variable to [l,u] so the vector field becomes globally Lipschitz in
state while preserving its values inside the tube. Apply Picard-Lindelof to this extended
field. The tube hypothesis places every Euler displacement y0+theta*F(t,y) in [l,u]; averaging
these displacements through the solution integral equation proves the obtained solution remains
in the tube. Clamping is then inactive and the solution satisfies the original ODE on the full
step.
-/
theorem tube_exists {F : ℝ → ℝ → ℝ} {a h l u y0 : ℝ} {M K : ℝ≥0}
    (hh : 0≤h) (hlu : l≤u)
    (hc : ContinuousOn (Function.uncurry F) (Icc a (a+h) ×ˢ Icc l u))
    (hlip : ∀ t∈Icc a (a+h),LipschitzOnWith K (F t) (Icc l u))
    (hbound : ∀ t∈Icc a (a+h),∀ y∈Icc l u,‖F t y‖≤M)
    (htube : ∀ θ∈Icc (0:ℝ) h,∀ t∈Icc a (a+h),∀ y∈Icc l u,
      y0+θ*F t y∈Icc l u) :
    ∃ y : ℝ → ℝ,y a=y0 ∧
      (∀ t∈Icc a (a+h),y t∈Icc l u) ∧
      ∀ t∈Icc a (a+h),HasDerivWithinAt y (F t (y t)) (Icc a (a+h)) t := by
  -- Extend the vector field by clamping only its state input; continuity and the tube
  -- Lipschitz constant survive this extension.
  let G := fun t y => F t (clamp l u y)
  have hGL : ∀ t∈Icc a (a+h),LipschitzWith K (G t) := by
    intro t ht
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (G t x) (G t y)≤K*dist (clamp l u x) (clamp l u y) :=
        (hlip t ht).dist_le_mul _ (clamp_mem hlu _) _ (clamp_mem hlu _)
      _≤K*dist x y := by
        gcongr
        simpa using (clamp_lipschitz l u).dist_le_mul x y
  -- Establish continuity hGc before using the function at limits or in calculus arguments.
  have hGc : ContinuousOn (Function.uncurry G) (Icc a (a+h) ×ˢ (univ : Set ℝ)) := by
    apply hc.comp (continuousOn_fst.prodMk ((clamp_lipschitz l u).continuous.continuousOn.comp
      continuousOn_snd (fun _ _ => mem_univ _)))
    intro p hp
    exact ⟨hp.1,clamp_mem hlu _⟩
  let radius : ℝ≥0 := ⟨M*h,mul_nonneg M.coe_nonneg hh⟩
  -- The global state extension now meets the actual Picard-Lindelof hypotheses with radius
  -- M*h.
  have hp : IsPicardLindelof G (⟨a,⟨le_rfl,by linarith⟩⟩ : Icc a (a+h)) y0 radius 0 M K := by
    constructor
    · exact fun t ht => (hGL t ht).lipschitzOnWith
    · intro x _
      exact hGc.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht,mem_univ _⟩)
    · exact fun t ht x _ => hbound t ht _ (clamp_mem hlu _)
    · simp only [NNReal.coe_zero,sub_self,add_sub_cancel_left,sub_zero]
      change M*max h 0≤M*h
      rw [max_eq_left hh]
  obtain ⟨y,hy0,hd⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  -- Establish continuity hyc before using the function at limits or in calculus arguments.
  have hyc : ContinuousOn y (Icc a (a+h)) := HasDerivWithinAt.continuousOn hd
  -- Establish continuity hF before using the function at limits or in calculus arguments.
  have hF : ContinuousOn (fun t => G t (y t)) (Icc a (a+h)) :=
    hGc.comp (continuousOn_id.prodMk hyc) (fun t ht => ⟨ht,mem_univ _⟩)
  -- Prove tube invariance from the integral equation and convexity of the interval, rather
  -- than assuming the constructed solution stays in the proposed tube.
  have hyY : ∀ t∈Icc a (a+h),y t∈Icc l u := by
    intro t ht
    have h0 : y0∈Icc l u := by
      simpa only [zero_mul,add_zero] using htube 0 ⟨le_rfl,hh⟩ a ⟨le_rfl,by linarith⟩ l ⟨le_rfl,hlu⟩
    rcases eq_or_lt_of_le ht.1 with he | hat
    · simpa only [← he,hy0] using h0
    have hsub : Icc a t⊆Icc a (a+h) := Icc_subset_Icc le_rfl ht.2
    have hi : IntervalIntegrable (fun s => G s (y s)) volume a t := by
      exact ContinuousOn.intervalIntegrable (by simpa [uIcc_of_le hat.le] using hF.mono hsub)
    have heq : (∫ s in a..t,G s (y s))=y t-y0 := by
      rw [← hy0]
      exact integral_eq_sub_of_hasDerivAt_of_le hat.le (hyc.mono hsub)
        (fun s hs => (hd s (hsub ⟨hs.1.le,hs.2.le⟩)).hasDerivAt (Icc_mem_nhds hs.1
          (hs.2.trans_le ht.2))) hi
    -- For fixed t, average Euler displacements over [a,t]. Each displacement lies in the tube
    -- by htube, and the average is the solution value y(t).
    let g := fun s => y0+(t-a)*G s (y s)
    have hgi : IntervalIntegrable g volume a t :=
      intervalIntegrable_const.add (hi.const_mul _)
    have hgb : ∀ s∈Icc a t,g s∈Icc l u :=
      fun s hs => htube (t-a) ⟨sub_nonneg.mpr hat.le,by linarith [ht.2]⟩ s (hsub hs) _ (clamp_mem hlu _)
    have hlo := integral_mono_on hat.le (intervalIntegrable_const (c := l)) hgi
      (fun s hs => (hgb s hs).1)
    have hhi := integral_mono_on hat.le hgi (intervalIntegrable_const (c := u))
      (fun s hs => (hgb s hs).2)
    have hg : (∫ s in a..t,g s)=(t-a)*y t := by
      change (∫ s in a..t,y0+(t-a)*G s (y s))=(t-a)*y t
      rw [integral_add intervalIntegrable_const (hi.const_mul _),intervalIntegral.integral_const_mul,heq]
      simp only [intervalIntegral.integral_const,smul_eq_mul]
      ring
    rw [hg] at hlo hhi
    simp only [intervalIntegral.integral_const,smul_eq_mul] at hlo hhi
    constructor <;> nlinarith
  -- Inside the proved tube, clamp is the identity, so the extended ODE is the original ODE.
  refine ⟨y,hy0,hyY,fun t ht => ?_⟩
  simpa only [G,clamp_eq (hyY t ht)] using hd t ht

/--
The existence assertion in Lemma 21 needs only continuous coefficients. The auxiliary global
bounds are constructed by compactness.

Constructs witnesses with the exact properties `∃ y : ℝ → ℝ,y a=y0 ∧ (∀ t∈Icc a (a+h),y t∈Icc l
u) ∧ ∀ t∈Icc a (a+h),HasDerivWithinAt y (C t+A t*y t+B t*y t^2) (Icc a (a+h)) t`.

Use: `chebyshev2.Numerics.flowTubeCheck_exists` uses this identity to establish constructs
witnesses with the exact properties `∃ y : ℝ → ℝ,y a=y0 ∧ (∀ t∈Icc a (a+h),y t∈Y) ∧ ∀ t∈Icc a
(a+h),HasDerivWithinAt y (C t+A t*y t+B t*y t^2) (Icc a (a+h)) t`.

Article: chebyshev2, Lemma 21 via `chebyshev2.Numerics.validated_flow_step`.

Proof: Use the identities/estimates `chebyshev2.Numerics.tube_exists` with the arguments
shown in the proof.
-/
theorem riccati_tube_exists {C A B : ℝ → ℝ} {a h l u y0 : ℝ}
    (hh : 0≤h) (hlu : l≤u)
    (hC : ContinuousOn C (Icc a (a+h))) (hA : ContinuousOn A (Icc a (a+h)))
    (hB : ContinuousOn B (Icc a (a+h)))
    (htube : ∀ θ∈Icc (0:ℝ) h,∀ t∈Icc a (a+h),∀ y∈Icc l u,
      y0+θ*(C t+A t*y+B t*y^2)∈Icc l u) :
    ∃ y : ℝ → ℝ,y a=y0 ∧ (∀ t∈Icc a (a+h),y t∈Icc l u) ∧
      ∀ t∈Icc a (a+h),HasDerivWithinAt y
        (C t+A t*y t+B t*y t^2) (Icc a (a+h)) t := by
  -- Use the identities/estimates `chebyshev2.Numerics.tube_exists` with the arguments
  -- shown in the proof.
  let F := fun t y => C t+A t*y+B t*y^2
  let S := Icc a (a+h) ×ˢ Icc l u
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : ContinuousOn (Function.uncurry F) S := by
    have hm : MapsTo Prod.fst S (Icc a (a+h)) := fun _ hp => hp.1
    exact ((hC.comp continuousOn_fst hm).add
      ((hA.comp continuousOn_fst hm).mul continuousOn_snd)).add
      ((hB.comp continuousOn_fst hm).mul (continuousOn_snd.pow 2))
  -- Establish continuity hs before using the function at limits or in calculus arguments.
  have hs : ContinuousOn (fun p : ℝ×ℝ => A p.1+2*B p.1*p.2) S := by
    have hm : MapsTo Prod.fst S (Icc a (a+h)) := fun _ hp => hp.1
    exact (hA.comp continuousOn_fst hm).add
      ((continuousOn_const.mul (hB.comp continuousOn_fst hm)).mul continuousOn_snd)
  obtain ⟨m,hm⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  obtain ⟨k,hk⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hs
  let M : ℝ≥0 := ⟨max 0 m,le_max_left _ _⟩
  let K : ℝ≥0 := ⟨max 0 k,le_max_left _ _⟩
  apply tube_exists (F := F) (M := M) (K := K) hh hlu hc _ _ htube
  · intro t ht
    apply (convex_Icc l u).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun y => A t+2*B t*y)
    · intro y _
      convert (((hasDerivAt_const y (C t)).add ((hasDerivAt_id y).const_mul (A t))).add
        (((hasDerivAt_id y).pow 2).const_mul (B t))).hasDerivWithinAt using 1
      · rfl
      · simp only [id_eq,Nat.cast_ofNat,mul_one,zero_add]
        ring
    · intro y hy
      change ‖A t+2*B t*y‖≤max 0 k
      exact (hk (t,y) ⟨ht,hy⟩).trans (le_max_right _ _)
  · intro t ht y hy
    exact (hm (t,y) ⟨ht,hy⟩).trans (le_max_right _ _)

/--
A successful rational tube check supplies the whole-step existence premise for every initial
value in the hull, including the Taylor centre.

Constructs witnesses with the exact properties `∃ y : ℝ → ℝ,y a=y0 ∧ (∀ t∈Icc a (a+h),y t∈Y) ∧
∀ t∈Icc a (a+h),HasDerivWithinAt y (C t+A t*y t+B t*y t^2) (Icc a (a+h)) t`.

Use: `chebyshev2.Numerics.FlowStep.check_range_sound` uses this identity to establish
membership in the specified domain/enclosure: `y (a+v)∈W.rangeEnclosure V`.

Article: chebyshev2, Lemma 21.

Proof: Use the identities/estimates `chebyshev2.Numerics.riccati_tube_exists`,
`chebyshev2.Numerics.flowTubeCheck_nonneg`, `chebyshev2.Numerics.flowTubeCheck_sound`
with the arguments shown in the proof.
-/
theorem flowTubeCheck_exists {CI AI BI Y0 Y : LeanCert.Core.IntervalRat} {m h : ℚ}
    (hcheck : flowTubeCheck Y0 Y CI AI BI m h=true)
    {C A B : ℝ → ℝ} {a y0 : ℝ}
    (hC : ContinuousOn C (Icc a (a+h))) (hA : ContinuousOn A (Icc a (a+h)))
    (hB : ContinuousOn B (Icc a (a+h)))
    (hCI : ∀ t∈Icc a (a+h),C t∈CI) (hAI : ∀ t∈Icc a (a+h),A t∈AI)
    (hBI : ∀ t∈Icc a (a+h),B t∈BI) (hy0 : y0∈hullPoint Y0 m) :
    ∃ y : ℝ → ℝ,y a=y0 ∧ (∀ t∈Icc a (a+h),y t∈Y) ∧
      ∀ t∈Icc a (a+h),HasDerivWithinAt y
        (C t+A t*y t+B t*y t^2) (Icc a (a+h)) t := by
  -- Use the identities/estimates `chebyshev2.Numerics.riccati_tube_exists`,
  -- `chebyshev2.Numerics.flowTubeCheck_nonneg`,
  -- `chebyshev2.Numerics.flowTubeCheck_sound` with the arguments shown in the proof.
  apply riccati_tube_exists (by exact_mod_cast flowTubeCheck_nonneg hcheck)
    (by exact_mod_cast Y.le) hC hA hB
  exact fun θ hθ t ht y hy => flowTubeCheck_sound hcheck (hCI t ht) (hAI t ht)
    (hBI t ht) hy hy0 hθ

end
end chebyshev2.Numerics
