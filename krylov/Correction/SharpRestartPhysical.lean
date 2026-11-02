import krylov.Correction.SharpRestart

/-!
Article: main_krylov, apG:restart, actual physical observed FC direction.
Use: obtain the printed restart constants for the genuine data-only
inverse solve, discharging old-span membership and measured conjugacy by
actual positive-root transport. Source: proved physical/canonical window
dictionary and the sharp observed restart theorem.
-/

/-!
Article: krylov, Lemma E.4 [apG:restart].

For the real observed FC direction, non-descent and short steps give the exact 2(1+√κ) and 4κ
gradient bounds.
The physical wrapper uses ratio²=κ and the canonical step norm ‖H_*^{1/2}d‖, matching the
corrected article.
-/
namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Secant krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original dimension-dependent budget implies the quarter bound
used for the new physical segment. Article: main_krylov, apG:restart. -/
theorem sharp_restart_epsilon_quarter (hn : 1≤n) (r epsilon : ℝ) (hr : 1≤r)
    (he : 0≤epsilon) (hsmall : Real.sqrt n*epsilon≤Real.sqrt 3/(8*r^2)) : epsilon≤1/4 := by
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hs : 1≤Real.sqrt n := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn'
  have hε : epsilon≤Real.sqrt n*epsilon := by nlinarith only [mul_le_mul_of_nonneg_right hs he]
  have hden : 0<8*r^2 := by positivity
  have hroot : Real.sqrt 3≤2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hbound : Real.sqrt 3/(8*r^2)≤1/4 := (div_le_iff₀ hden).mpr (by nlinarith)
  exact hε.trans (hsmall.trans hbound)

/-- The original real stored-window FC solve satisfies the exact
non-descent restart estimate in the true reference metric. Every old
physical step is proved nonzero before actual unit normalization.
Article: main_krylov, apG:restart(a). -/
theorem windowDirection_sharp_nondescent
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n)) (m r epsilon : ℝ) (hm : 0<m) (hr : 1≤r)
    (hlower : ∀ i,m^2≤hb.1.eigenvalues i) (hupper : ‖cgOperator base‖≤m^2*r^2)
    (hC : IsUnit (crossGram (windowImages W) (windowSteps W)).det)
    (hgram : ∀ i,(3/4 : ℝ)≤(crossGram_isHermitian (unitWindow (primalWindow base (windowSteps W)))).eigenvalues i)
    (he : 0≤epsilon) (hsmall : Real.sqrt W.length*epsilon≤Real.sqrt 3/(8*r^2))
    (hy : ∀ i,‖dualWindow base (windowImages W) i-primalWindow base (windowSteps W) i‖≤
      epsilon/2*‖primalWindow base (windowSteps W) i‖)
    (hslope : 0≤ inner ℝ g (windowDirection W g)) :
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    ‖J g‖≤2*(1+r)*‖observedProjection (unitWindow (primalWindow base (windowSteps W))) (J g)‖ := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  have hs := canonical_window_steps_ne_zero base hb W hC
  have hpair : inner ℝ (J g) (R (windowDirection W g))=inner ℝ g (windowDirection W g) := by
    rw [real_inner_comm,←canonical_search_pairing base hb,real_inner_comm]
  exact sharp_observed_nondescent _ _ base hb (J g) (R (windowDirection W g)) m r epsilon hm hr
    (spectral_lower_form base hb.1 hlower) hupper hgram he hsmall
    (unitWindow_pair_error _ _ hs hy) (windowDirection_canonical_conjugacy base hb W g hC)
    (windowDirection_canonical_span base hb W g) (hpair.symm ▸ hslope)

/-- The actual exact searched physical FC direction satisfies the sharp
short-step estimate with the necessary canonical direction norm. Its
new-operator 9/8 bound is derived from the original relative error budget.
Article: main_krylov, apG:restart(b), corrected canonical-norm statement. -/
theorem windowDirection_sharp_short_step
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n)) (m r epsilon alpha : ℝ) (hm : 0<m) (hr : 1≤r)
    (hlower : ∀ i,m^2≤hb.1.eigenvalues i) (hupper : ‖cgOperator base‖≤m^2*r^2)
    (hC : IsUnit (crossGram (windowImages W) (windowSteps W)).det)
    (hgram : ∀ i,(3/4 : ℝ)≤(crossGram_isHermitian (unitWindow (primalWindow base (windowSteps W)))).eigenvalues i)
    (hlen : W.length≤n) (he : 0≤epsilon) (hsmall : Real.sqrt n*epsilon≤Real.sqrt 3/(8*r^2))
    (hy : ∀ i,‖dualWindow base (windowImages W) i-primalWindow base (windowSteps W) i‖≤
      epsilon/2*‖primalWindow base (windowSteps W) i‖)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ‖canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤epsilon/2)
    (halpha : 0<alpha)
    (hline : -inner ℝ g (windowDirection W g)=alpha*inner ℝ (windowDirection W g) (A (windowDirection W g))) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    ‖J g‖≤4*r^2*(‖observedProjection (unitWindow (primalWindow base (windowSteps W))) (J g)‖+
      alpha*‖R (windowDirection W g)‖) := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  by_cases hn : n=0
  · subst n
    have hz : J g=0 := Subsingleton.elim _ _
    change ‖J g‖≤_
    rw [hz,norm_zero]
    positivity
  have hn' : 1≤n := Nat.one_le_iff_ne_zero.mpr hn
  have hquarter := sharp_restart_epsilon_quarter hn' r epsilon hr he hsmall
  have hs := canonical_window_steps_ne_zero base hb W hC
  have hlen' : (W.length : ℝ)≤n := by exact_mod_cast hlen
  have hsmall' : Real.sqrt W.length*epsilon≤Real.sqrt 3/(8*r^2) :=
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hlen') he).trans hsmall
  have hnA : ‖canonicalOperator base A‖≤(9/8 : ℝ) := by
    have hh := norm_add_le (canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    rw [sub_add_cancel] at hh
    have hi := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))
    linarith
  have hpair : inner ℝ (J g) (R (windowDirection W g))=inner ℝ g (windowDirection W g) := by
    rw [real_inner_comm,←canonical_search_pairing base hb,real_inner_comm]
  have hcurv : inner ℝ (R (windowDirection W g))
      (canonicalOperator base A (R (windowDirection W g)))=
      inner ℝ (windowDirection W g) (A (windowDirection W g)) := by
    rw [canonicalOperator_primal base hb,←canonical_search_pairing base hb]
  have hl : -inner ℝ (J g) (R (windowDirection W g))=
      alpha*inner ℝ (R (windowDirection W g)) (canonicalOperator base A (R (windowDirection W g))) := by
    rw [hpair,hcurv]
    exact hline
  exact sharp_observed_short_step _ _ base hb (J g) (R (windowDirection W g)) m r epsilon alpha hm hr
    (spectral_lower_form base hb.1 hlower) hupper hgram he hsmall'
    (unitWindow_pair_error _ _ hs hy) (windowDirection_canonical_conjugacy base hb W g hC)
    (windowDirection_canonical_span base hb W g) (canonicalOperator base A) hnA halpha hl

end
end krylov.Correction
