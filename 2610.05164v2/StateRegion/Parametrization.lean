import «2610.05164v2».StateRegion.Coordinates

/-!
Article: 2610.05164v2, Lemma 8.
Parametrization.
Use: `«2610.05164v2».StateRegion.Scales.theta_at_zero` feeds
`«2610.05164v2».StateRegion.Scales.lower_boundary` (lower boundary).
Proof chain: `«2610.05164v2».StateRegion.Scales.mean_zero_boundary` — 2610.05164v2, Lemma 8;
Parametrization and compactness of the state region.
-/
namespace «2610.05164v2».StateRegion.Scales
noncomputable section
open Set
variable (S : Scales)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/--
Defines `square` of type `Set (ℝ × ℝ)` by `Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1`.

Use: `«2610.05164v2».StateRegion.Scales.V_continuousOn` uses this definition to establish
continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => S.V p.1 p.2) square`.

Article: 2610.05164v2, Proposition 7 via
`«2610.05164v2».StateRegion.Scales.normalized_compact`.
-/
def square : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1

/--
Continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => S.V p.1 p.2) square`.

Use: `«2610.05164v2».StateRegion.Scales.parametrization_continuousOn` uses this continuity
result to establish continuity on the stated domain: `ContinuousOn S.parametrization cube`.

Article: 2610.05164v2, Proposition 7 via
`«2610.05164v2».StateRegion.Scales.normalized_compact`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.D_pos` with the
arguments shown in the proof.
-/
theorem V_continuousOn : ContinuousOn (fun p : ℝ × ℝ => S.V p.1 p.2) square := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => S.f p.1) square := by
    apply ContinuousOn.div (by unfold k₀; fun_prop) (by unfold D; fun_prop)
    intro p hp
    exact (S.D_pos hp.1.2).ne'
  exact ((continuousOn_const.sub continuousOn_snd).mul hf).add
    (continuousOn_snd.mul continuousOn_fst)

/--
Continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => S.yPlus p.1 p.2) square`.

Use: `«2610.05164v2».StateRegion.Scales.thetaMinus_continuousOn` uses this continuity result to
establish continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => S.thetaMinus p.1
p.2) square`.

Article: 2610.05164v2, Proposition 7 via
`«2610.05164v2».StateRegion.Scales.normalized_compact`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos`,
`«2610.05164v2».StateRegion.Scales.yPlus_den_lower` with the arguments shown in the proof.
-/
theorem yPlus_continuousOn : ContinuousOn (fun p : ℝ × ℝ => S.yPlus p.1 p.2) square := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro p hp
  exact (S.k₀_pos.trans_le (S.yPlus_den_lower hp.1 hp.2)).ne'

/--
Continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => S.yMinus p.1 p.2) square`.

Use: `«2610.05164v2».StateRegion.Scales.thetaPlus_continuousOn` uses this continuity result to
establish continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => S.thetaPlus p.1 p.2)
square`.

Article: 2610.05164v2, Proposition 7 via
`«2610.05164v2».StateRegion.Scales.normalized_compact`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos`,
`«2610.05164v2».StateRegion.Scales.yMinus_den_lower` with the arguments shown in the proof.
-/
theorem yMinus_continuousOn : ContinuousOn (fun p : ℝ × ℝ => S.yMinus p.1 p.2) square := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro p hp
  exact (S.k₀_pos.trans_le (S.yMinus_den_lower hp.1.2 hp.2.1)).ne'

/--
Continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => S.thetaMinus p.1 p.2) square`.

Use: `«2610.05164v2».StateRegion.Scales.parametrization_continuousOn` uses this continuity
result to establish continuity on the stated domain: `ContinuousOn S.parametrization cube`.

Article: 2610.05164v2, Proposition 7 via
`«2610.05164v2».StateRegion.Scales.normalized_compact`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.yPlus_continuousOn`,
`«2610.05164v2».StateRegion.Scales.E_pos`, `«2610.05164v2».StateRegion.Scales.yPlus_bounds`
with the arguments shown in the proof.
-/
theorem thetaMinus_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => S.thetaMinus p.1 p.2) square := by
  apply ContinuousOn.div (by fun_prop)
    (continuousOn_const.add (continuousOn_const.mul S.yPlus_continuousOn))
  intro p hp
  exact (S.E_pos (S.yPlus_bounds hp.1 hp.2).1).ne'

/--
Continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => S.thetaPlus p.1 p.2) square`.

Use: `«2610.05164v2».StateRegion.Scales.parametrization_continuousOn` uses this continuity
result to establish continuity on the stated domain: `ContinuousOn S.parametrization cube`.

Article: 2610.05164v2, Proposition 7 via
`«2610.05164v2».StateRegion.Scales.normalized_compact`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.yMinus_continuousOn`,
`«2610.05164v2».StateRegion.Scales.E_pos`, `«2610.05164v2».StateRegion.Scales.yMinus_bounds`
with the arguments shown in the proof.
-/
theorem thetaPlus_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => S.thetaPlus p.1 p.2) square := by
  apply ContinuousOn.sub continuousOn_const
  apply ContinuousOn.div (by fun_prop)
    (continuousOn_const.add (continuousOn_const.mul S.yMinus_continuousOn))
  intro p hp
  exact (S.E_pos (hp.1.1.trans (S.yMinus_bounds hp.1 hp.2).1)).ne'

/--
Exact identity `S.thetaPlus u t - S.thetaMinus u t = S.k₀*S.a*S.b*u*(1-u)*t*(1-t)*S.D u /
((S.k₀+S.gap*t*(1-u))*(S.k₁-S.gap*u*t)* S.E (S.yPlus u t)*S.E (S.yMinus u t))`.

Use: `«2610.05164v2».StateRegion.Scales.theta_order` rewrites with this identity to establish
the stated quantitative bound `S.thetaMinus u t ≤ S.thetaPlus u t`.

Article: 2610.05164v2, Proposition 7 via
`«2610.05164v2».StateRegion.Scales.normalized_compact`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem theta_gap {u t : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    S.thetaPlus u t - S.thetaMinus u t =
    S.k₀*S.a*S.b*u*(1-u)*t*(1-t)*S.D u /
      ((S.k₀+S.gap*t*(1-u))*(S.k₁-S.gap*u*t)*
        S.E (S.yPlus u t)*S.E (S.yMinus u t)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have ha := (S.k₀_pos.trans_le (S.yMinus_den_lower hu.2 ht.1)).ne'
  have hb := (S.k₀_pos.trans_le (S.yPlus_den_lower hu ht)).ne'
  have hePlus := (S.E_pos (S.yPlus_bounds hu ht).1).ne'
  have heMinus := (S.E_pos (hu.1.trans (S.yMinus_bounds hu ht).1)).ne'
  dsimp [thetaPlus,thetaMinus]
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hePlus) heMinus)).mpr
  field_simp [hePlus,heMinus]
  simp only [E,yPlus,yMinus]
  dsimp only [k₀,k₁] at ha hb ⊢
  field_simp (disch := solve | (convert ha using 1 <;> ring) | (convert hb using 1; ring))
  dsimp [b,D,k₁]
  ring

/--
The stated quantitative bound `S.thetaMinus u t ≤ S.thetaPlus u t`.

Use: `«2610.05164v2».StateRegion.Scales.normalized_eq_image` uses this bound to establish exact
identity `S.normalized = S.parametrization '' cube`.

Article: 2610.05164v2, Proposition 7 via
`«2610.05164v2».StateRegion.Scales.normalized_compact`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.theta_gap`,
`«2610.05164v2».StateRegion.Scales.k₀_pos`, `«2610.05164v2».StateRegion.Scales.D_pos` with the
arguments shown in the proof.
-/
theorem theta_order {u t : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    S.thetaMinus u t ≤ S.thetaPlus u t := by
  -- Use the identities/estimates `«2610.05164v2».StateRegion.Scales.theta_gap`,
  -- `«2610.05164v2».StateRegion.Scales.k₀_pos`, `«2610.05164v2».StateRegion.Scales.D_pos` with
  -- the arguments shown in the proof.
  apply sub_nonneg.mp
  rw [S.theta_gap hu ht]
  have hk := S.k₀_pos
  have ha := S.a_pos
  have hb : 0 < S.b := add_pos S.a_pos S.gap_pos
  have hu₀ := hu.1
  have hu₁ := sub_nonneg.mpr hu.2
  have ht₀ := ht.1
  have ht₁ := sub_nonneg.mpr ht.2
  have hd := S.D_pos hu.2
  have hdPlus := S.k₀_pos.trans_le (S.yPlus_den_lower hu ht)
  have hdMinus := S.k₀_pos.trans_le (S.yMinus_den_lower hu.2 ht.1)
  have hePlus := S.E_pos (S.yPlus_bounds hu ht).1
  have heMinus := S.E_pos (hu.1.trans (S.yMinus_bounds hu ht).1)
  positivity

/--
Exact identity `S.yPlus u 0 = u ∧ S.yMinus u 0 = u`.

Use: `«2610.05164v2».StateRegion.Scales.theta_at_zero` uses this identity to establish exact
identity `S.thetaMinus u 0 = S.k*(1-u)/S.E u ∧ S.thetaPlus u 0 = S.k*(1-u)/S.E u`.

Article: 2610.05164v2, Lemma 8 via `«2610.05164v2».StateRegion.Scales.mean_zero_boundary`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₁_pos`,
`«2610.05164v2».StateRegion.Scales.k₀_pos` with the arguments shown in the proof.
-/
theorem y_at_zero {u : ℝ} (_hu : u ∈ Icc (0:ℝ) 1) :
    S.yPlus u 0 = u ∧ S.yMinus u 0 = u := by
  constructor
  · simp [yPlus, S.k₁_pos.ne']
  · simp [yMinus, S.k₀_pos.ne']

/--
Exact identity `S.yPlus u 1 = 0 ∧ S.yMinus u 1 = 1`.

Use: `«2610.05164v2».StateRegion.Scales.theta_at_one` uses this identity to establish exact
identity `S.thetaMinus u 1 = 1-u ∧ S.thetaPlus u 1 = 1-u`.

Article: 2610.05164v2, Lemma 8.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos`,
`«2610.05164v2».StateRegion.Scales.yMinus_den_lower` with the arguments shown in the proof.
-/
theorem y_at_one {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    S.yPlus u 1 = 0 ∧ S.yMinus u 1 = 1 := by
  constructor
  · simp [yPlus]
  · rw [yMinus,div_eq_one_iff_eq (S.k₀_pos.trans_le (S.yMinus_den_lower hu.2 (by norm_num))).ne']
    dsimp [k₀,k₁]
    ring

/--
Exact identity `S.thetaMinus u 0 = S.k*(1-u)/S.E u ∧ S.thetaPlus u 0 = S.k*(1-u)/S.E u`.

Use: `«2610.05164v2».StateRegion.Scales.lower_boundary` rewrites with this identity to
establish exact identity `1-(∫ w, S.g w ∂μ)=S.k*(1-u)/S.E u`.

Article: 2610.05164v2, Lemma 8 via `«2610.05164v2».StateRegion.Scales.mean_zero_boundary`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem theta_at_zero {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    S.thetaMinus u 0 = S.k*(1-u)/S.E u ∧ S.thetaPlus u 0 = S.k*(1-u)/S.E u := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  obtain ⟨hp,hm⟩ := S.y_at_zero hu
  constructor
  · simp only [thetaMinus,hp]
  · rw [thetaPlus,hm]
    field_simp [(S.E_pos hu.1).ne']
    dsimp [E,k₀]
    ring

/--
Exact identity `S.thetaMinus u 1 = 1-u ∧ S.thetaPlus u 1 = 1-u`.

Use: `«2610.05164v2».StateRegion.Scales.upper_boundary` rewrites with this identity to
establish exact identity `1-(∫ w, S.g w ∂μ)=1-u`.

Article: 2610.05164v2, Lemma 8.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.y_at_one`,
`«2610.05164v2».StateRegion.Scales.k₀_pos` with the arguments shown in the proof.
-/
theorem theta_at_one {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    S.thetaMinus u 1 = 1-u ∧ S.thetaPlus u 1 = 1-u := by
  -- Use the identities/estimates `«2610.05164v2».StateRegion.Scales.y_at_one`,
  -- `«2610.05164v2».StateRegion.Scales.k₀_pos` with the arguments shown in the proof.
  obtain ⟨hp,hm⟩ := S.y_at_one hu
  constructor
  · simp [thetaMinus,hp,E,S.k_pos.ne']
  · rw [thetaPlus,hm]
    change 1-S.k₀*u/(S.k+S.a*1) = 1-u
    rw [mul_one]
    change 1-S.k₀*u/S.k₀ = 1-u
    rw [mul_div_cancel_left₀ _ S.k₀_pos.ne']

/--
Exact identity `S.thetaMinus 0 t = 1 ∧ S.thetaPlus 0 t = 1`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 8.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem theta_at_left {t : ℝ} (_ht : t ∈ Icc (0:ℝ) 1) :
    S.thetaMinus 0 t = 1 ∧ S.thetaPlus 0 t = 1 := by
  constructor
  · simp [thetaMinus,yPlus,E,S.k_pos.ne']
  · simp [thetaPlus]

/--
Exact identity `S.thetaMinus 1 t = 0 ∧ S.thetaPlus 1 t = 0`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 8.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos` with the
arguments shown in the proof.
-/
theorem theta_at_right {t : ℝ} (_ht : t ∈ Icc (0:ℝ) 1) :
    S.thetaMinus 1 t = 0 ∧ S.thetaPlus 1 t = 0 := by
  -- Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos` with the arguments
  -- shown in the proof.
  constructor
  · simp [thetaMinus]
  · have hy : S.yMinus 1 t = 1 := by simp [yMinus,S.k₀_pos.ne']
    change 1-S.k₀*1/(S.k+S.a*S.yMinus 1 t) = 0
    rw [hy,mul_one,mul_one]
    change 1-S.k₀/S.k₀ = 0
    rw [div_self S.k₀_pos.ne',sub_self]

end
end «2610.05164v2».StateRegion.Scales
