import «2610.05164v2».LocalObstruction.FullGreen

/-!
Article: 2610.05164v2, Theorem 6.1.
The actual full resolvent kernel solves the free-kernel Fredholm equation.
Use: `«2610.05164v2».LocalObstruction.resolventGreen_abs_bound` feeds
`«2610.05164v2».LocalObstruction.sineGreenScale_formula` (sine Green Scale formula).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open MeasureTheory Real «2610.05164v2».Continuum
open scoped InnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
The stated quantitative bound `|resolventGreen m s x y|≤1/2`.

Use: `«2610.05164v2».LocalObstruction.sineGreenScale_formula` uses this bound to establish the
identity stated in that declaration.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_norm`,
`«2610.05164v2».LocalObstruction.fullResolvent_norm` with the arguments shown in the proof.
-/
theorem resolventGreen_abs_bound {m : ℝ → ℝ} (hm : Integrable m)
    (hn : ∀ x,0≤m x) {s : ℝ} (hs : 0≤s) (x y : ℝ) :
    |resolventGreen m s x y|≤1/2 := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.feature_norm`,
  -- `«2610.05164v2».LocalObstruction.fullResolvent_norm` with the arguments shown in the
  -- proof.
  unfold resolventGreen
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ‖feature x‖*‖fullResolvent m s (feature y)‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 := by simpa only [feature_norm,one_mul] using fullResolvent_norm hm hn hs (feature y)

 /--
The precise assertion is `resolventGreen m s x y+s/2*(∫ z, exp (-|y-z|)*(m z*resolventGreen m s
x z))= exp (-|x-y|)/2`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 6.1.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem resolventGreen_fredholm {m : ℝ → ℝ} (hm : Integrable m)
    (hn : ∀ x,0≤m x) {s : ℝ} (hs : 0≤s) (x y : ℝ) :
    resolventGreen m s x y+s/2*(∫ z, exp (-|y-z|)*(m z*resolventGreen m s x z))=
      exp (-|x-y|)/2 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have he := congrArg (fun u => inner ℝ (feature y) u) (fullResolvent_right hm hn hs (feature x))
  change inner ℝ (feature y) (fullResolvent m s (feature x)+
    (s/2) • densityOperator m (fullResolvent m s (feature x)))=inner ℝ (feature y) (feature x) at he
  rw [inner_add_right,real_inner_smul_right,densityOperator_inner hm,feature_inner] at he
  have hpair (z : ℝ) : inner ℝ (feature z) (fullResolvent m s (feature x))=2*resolventGreen m s x z := by
    rw [resolventGreen_symmetric hm hn hs x z]
    unfold resolventGreen
    ring
  simp only [hpair] at he
  have hi : (∫ z,m z*(inner ℝ (feature z) (feature y)*(2*resolventGreen m s x z)))=
      2*(∫ z,exp (-|y-z|)*(m z*resolventGreen m s x z)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by dsimp only;rw [feature_inner,abs_sub_comm z y];ring)
  rw [hi,abs_sub_comm y x] at he
  linear_combination he/2

 /--
The stated quantitative bound `0<resolventGreen m s x x`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 6.1.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.fullResolvent_right`,
`«2610.05164v2».Continuum.feature_norm`, `«2610.05164v2».Continuum.densityOperator_positive`
with the arguments shown in the proof.
-/
theorem resolventGreen_diagonal_positive {m : ℝ → ℝ} (hm : Integrable m)
    (hn : ∀ x,0≤m x) {s : ℝ} (hs : 0≤s) (x : ℝ) : 0<resolventGreen m s x x := by
  -- Use the identities/estimates `«2610.05164v2».LocalObstruction.fullResolvent_right`,
  -- `«2610.05164v2».Continuum.feature_norm`,
  -- `«2610.05164v2».Continuum.densityOperator_positive` with the arguments shown in the proof.
  let u := fullResolvent m s (feature x)
  have hright : fullPencil m s u=feature x := fullResolvent_right hm hn hs (feature x)
  have hne : u≠0 := by
    intro hz
    rw [hz,map_zero] at hright
    have h := congrArg norm hright
    simp only [norm_zero,feature_norm] at h
    norm_num at h
  have hp := (densityOperator_positive hm hn).re_inner_nonneg_left u
  change 0 ≤ inner ℝ (densityOperator m u) u at hp
  have hb : 0 < inner ℝ (fullPencil m s u) u := by
    change 0 < inner ℝ (u+(s/2) • densityOperator m u) u
    rw [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hne))
      (mul_nonneg (div_nonneg hs (by norm_num)) hp)
  rw [hright] at hb
  exact div_pos hb (by norm_num)

end
end «2610.05164v2».LocalObstruction
