import krylov.Correction.SharpConstant

/-!
Article: main_krylov, s4:eq:K and apD:lemmas, scalar bounds and budget scaling.
Use: turn the attained scalar maximum into the homogeneous estimates used by
the actual compression, minimax and uniform remainder arguments.
Source: the proved scalar variational characterization and elementary inequalities.
-/

namespace krylov.Correction
noncomputable section

/-- A zero increment budget has zero second-order correction constant.
Use: handle degenerate profiles before normalizing their total budget.
Article: main_krylov, thm:C, W₀=0.
Proof: the defining expression has the total budget as its first factor. -/
theorem sharpConstant_zero (w : ℝ) : sharpConstant 0 w=0 := by
  simp [sharpConstant]

/-- The attained scalar maximum is nonnegative for all allowed budgets.
Use: justify order comparisons and the trivial zero-budget information bound.
Article: main_krylov, s4:eq:K, K≥0.
Proof: the admissible test value a=0 gives zero. -/
theorem sharpConstant_nonneg {W w : ℝ} (hW : 0 ≤ W) (hw : 0 ≤ w) :
    0 ≤ sharpConstant W w := by
  simpa only [mul_zero,zero_mul] using
    (sharpConstant_variational hW hw).2.2 0 (by simp)

/-- Every unit-quarter-circle objective satisfies the elementary upper bound.
Use: obtain an estimate independent of the maximizing parameter.
Article: main_krylov, apD:lemmas, K≤W²/2+Ww.
Proof: a²+c²=1 implies ac≤1/2, and a≤1 bounds the linear term. -/
theorem scalar_objective_upper {W w a : ℝ} (hW : 0 ≤ W) (hw : 0 ≤ w)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    W*a*(W*Real.sqrt (1-a^2)+w) ≤ W^2/2+W*w := by
  -- Keep the quadratic cross term and the linear final-budget term separate.
  let c := Real.sqrt (1-a^2)
  have hc : c^2=1-a^2 := Real.sq_sqrt (by nlinarith [ha.1,ha.2])
  have hac : a*c ≤ 1/2 := by nlinarith [sq_nonneg (a-c)]
  have hq := mul_le_mul_of_nonneg_left hac (sq_nonneg W)
  have hl := mul_le_mul_of_nonneg_left ha.2 (mul_nonneg hW hw)
  dsimp only [c] at hq
  nlinarith

/-- The scalar constant has the printed elementary upper estimate.
Use: control the second-order size uniformly over all budget profiles.
Article: main_krylov, apD:lemmas, K≤W²/2+Ww.
Proof: evaluate the scalar upper bound at the actual maximizing direction. -/
theorem sharpConstant_upper {W w : ℝ} (hW : 0 ≤ W) (hw : 0 ≤ w) :
    sharpConstant W w ≤ W^2/2+W*w := by
  obtain ⟨ha,he,_⟩ := sharpConstant_variational hW hw
  rw [he]
  exact scalar_objective_upper hW hw ha

/-- The pure final-correction budget gives a lower test value Ww.
Use: retain the endpoint a=1, including vanishing increment budgets.
Article: main_krylov, apD:lemmas, Ww≤K.
Proof: substitute the admissible endpoint a=1 in the proved maximum. -/
theorem sharpConstant_lower_linear {W w : ℝ} (hW : 0 ≤ W) (hw : 0 ≤ w) :
    W*w ≤ sharpConstant W w := by
  simpa using (sharpConstant_variational hW hw).2.2 1 (by simp)

/-- The balanced cross and compression direction gives the quadratic lower bound.
Use: identify the exact constant when the terminal correction perturbation vanishes.
Article: main_krylov, apD:lemmas, W²/2≤K.
Proof: choose a=c=√(1/2); its objective is W²/2 plus a nonnegative term. -/
theorem sharpConstant_lower_quadratic {W w : ℝ} (hW : 0 ≤ W) (hw : 0 ≤ w) :
    W^2/2 ≤ sharpConstant W w := by
  -- The balanced test direction has two equal nonnegative coordinates.
  let a := Real.sqrt (1/2 : ℝ)
  have ha₀ : 0 ≤ a := Real.sqrt_nonneg _
  have ha₂ : a^2=1/2 := Real.sq_sqrt (by norm_num)
  have ha₁ : a ≤ 1 := by nlinarith
  have hc : Real.sqrt (1-a^2)=a := by
    congr 1
    dsimp only [a] at ha₂ ⊢
    linarith
  have hm := (sharpConstant_variational hW hw).2.2 a ⟨ha₀,ha₁⟩
  rw [hc] at hm
  nlinarith [mul_nonneg (mul_nonneg hW hw) ha₀]

/-- The two elementary lower test values and the upper bound hold together.
Use: exactly the printed scalar sandwich, with every zero budget included.
Article: main_krylov, apD:lemmas, max(W²/2,Ww)≤K≤W²/2+Ww.
Proof: combine the two admissible tests and the attained upper bound. -/
theorem sharpConstant_bounds {W w : ℝ} (hW : 0 ≤ W) (hw : 0 ≤ w) :
    max (W^2/2) (W*w) ≤ sharpConstant W w ∧
      sharpConstant W w ≤ W^2/2+W*w :=
  ⟨max_le (sharpConstant_lower_quadratic hW hw) (sharpConstant_lower_linear hW hw),
    sharpConstant_upper hW hw⟩

/-- Without a terminal perturbation the exact sharp constant is W²/2.
Use: compare RFC with informed-base corrections at the correct normalization.
Article: main_krylov, s4:eq:K, K(W,0)=W²/2.
Proof: the two proved quadratic estimates coincide at w=0. -/
theorem sharpConstant_no_terminal {W : ℝ} (hW : 0 ≤ W) :
    sharpConstant W 0=W^2/2 := by
  have hu := sharpConstant_upper hW (le_refl 0)
  have hl := sharpConstant_lower_quadratic hW (le_refl 0)
  exact le_antisymm (by simpa only [mul_zero,add_zero] using hu) hl

/-- Rescaling both budgets rescales the actual sharp constant quadratically.
Use: quantify the leading loss of the budget slack in admissible twin scenarios.
Article: main_krylov, thm:C and s4:cor-Q, K(tW,tw)=t²K(W,w).
Proof: test the original maximizing parameter in the scaled problem and the
scaled maximizing parameter in the original problem; both objectives scale by t². -/
theorem sharpConstant_homogeneous {W w t : ℝ} (hW : 0 ≤ W) (hw : 0 ≤ w)
    (ht : 0 ≤ t) : sharpConstant (t*W) (t*w)=t^2*sharpConstant W w := by
  -- Compare both genuine maximizers, so no rescaled optimizer is assumed.
  obtain ⟨ha,he,hmax⟩ := sharpConstant_variational hW hw
  obtain ⟨hb,hf,hscaled⟩ := sharpConstant_variational (mul_nonneg ht hW) (mul_nonneg ht hw)
  apply le_antisymm
  · rw [hf]
    have hu := mul_le_mul_of_nonneg_left (hmax _ hb) (sq_nonneg t)
    convert hu using 1
    ring
  · have hl := hscaled _ ha
    rw [he]
    convert hl using 1
    ring

/-- The scalar maximum bounds the physical cross-action parameter t∈[0,W].
Use: connect the summed compression estimate directly to K without assuming W>0.
Article: main_krylov, thm:C, t(√(W²−t²)+w)≤K(W,w).
Proof: the positive-budget case uses a=t/W and the nonnegative square-root
scaling identity; the zero-budget case forces t=0. -/
theorem compression_scalar_bound {W w t : ℝ} (hW : 0 ≤ W) (hw : 0 ≤ w)
    (ht : 0 ≤ t) (htW : t ≤ W) :
    t*(Real.sqrt (W^2-t^2)+w) ≤ sharpConstant W w := by
  -- Only the positive-total-budget branch divides by the total budget.
  by_cases hz : W=0
  · subst W
    have htz : t=0 := le_antisymm htW ht
    simp [htz,sharpConstant_zero]
  have hWp : 0<W := lt_of_le_of_ne hW (Ne.symm hz)
  have ha : t/W ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht hW,(div_le_one hWp).mpr htW⟩
  have hs : W*Real.sqrt (1-(t/W)^2)=Real.sqrt (W^2-t^2) := by
    have h₁ := Real.sq_sqrt (show 0 ≤ 1-(t/W)^2 by nlinarith [ha.1,ha.2])
    have h₂ := Real.sq_sqrt (show 0 ≤ W^2-t^2 by nlinarith)
    have he : (W*Real.sqrt (1-(t/W)^2))^2 = W^2-t^2 := by
      rw [mul_pow,h₁]
      field_simp
    nlinarith [Real.sqrt_nonneg (W^2-t^2),
      mul_nonneg hW (Real.sqrt_nonneg (1-(t/W)^2))]
  have hm := (sharpConstant_variational hW hw).2.2 (t/W) ha
  rw [hs,mul_div_cancel₀ t hz] at hm
  exact hm

end
end krylov.Correction
