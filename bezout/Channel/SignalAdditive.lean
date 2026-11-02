import bezout.Probability.CovarianceSpectral
import bezout.Channel.SignalBounds

/-!
Article: bezout, Appendix D, deterministic additive-energy measurements.
Use: the actual terminal map from all stacked physical errors has gain equal
to the largest spectral response-row norm, attained in one spectral mode.
Proof: the exact physical response, rowwise Cauchy--Schwarz, and a normalized
physical response row at a maximizing eigenvalue.
-/

namespace bezout.Channel
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

/-- Interpret a Euclidean stack as one vector error at each physical call. -/
def stackedNoise (W : EuclideanSpace ℝ (J×Fin N)) (s : Fin N) : EuclideanSpace ℝ J :=
  WithLp.toLp 2 (fun j => W (j,s))

/-- The true map from stacked additive errors to the terminal vector. -/
def additiveOperator (h : bezout.History N) (lam : J → ℝ) :
    EuclideanSpace ℝ (J×Fin N) →L[ℝ] EuclideanSpace ℝ J :=
  (Matrix.toEuclideanLin (fun (j : J) (k : J×Fin N) => if j=k.1 then (h.response k.2).eval (lam j) else 0)).toContinuousLinearMap

/-- The stacked map acts by its own temporal response row in each spectral mode. -/
theorem additiveOperator_apply (h : bezout.History N) (lam : J → ℝ)
    (W : EuclideanSpace ℝ (J×Fin N)) (j : J) :
    additiveOperator h lam W j=∑ s, (h.response s).eval (lam j)*W (j,s) := by
  change (∑ k : J×Fin N, (if j=k.1 then (h.response k.2).eval (lam j) else 0)*W k)=_
  rw [Fintype.sum_prod_type]
  simp

/-- This operator is exactly the deviation in the actual noisy iteration. -/
theorem additiveOperator_physical (h : bezout.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) (W : EuclideanSpace ℝ (J×Fin N)) :
    (h.run (bezout.History.matrixEnd (Matrix.diagonal lam)) a (stackedNoise W)).output-
      (aeval (bezout.History.matrixEnd (Matrix.diagonal lam)) h.terminal) a=
        additiveOperator h lam W := by
  rw [h.physical_response,add_sub_cancel_left]
  ext j
  simp only [WithLp.ofLp_sum,Finset.sum_apply,diagonal_polynomial_apply,additiveOperator_apply]
  rfl

omit [DecidableEq J] in
/-- The Euclidean stack has exactly the total physical oracle-error energy. -/
theorem stackedNoise_energy (W : EuclideanSpace ℝ (J×Fin N)) :
    (∑ s, ‖stackedNoise W s‖^2)=‖W‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,stackedNoise]
  rw [Fintype.sum_prod_type,Finset.sum_comm]

variable [Nonempty J]

/-- The largest actual squared response-row norm on the finite spectrum. -/
def additiveEnergyMax (h : bezout.History N) (lam : J → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => bezout.Probability.varianceProfile h (lam j))

omit [DecidableEq J] in
/-- Every spectral response row is bounded by the actual finite maximum. -/
theorem responseEnergy_le_max (h : bezout.History N) (lam : J → ℝ) (j : J) :
    bezout.Probability.varianceProfile h (lam j)≤additiveEnergyMax h lam :=
  Finset.le_sup' (fun j => bezout.Probability.varianceProfile h (lam j)) (Finset.mem_univ j)

omit [DecidableEq J] in
/-- The finite spectral maximum is attained at an actual eigenvalue. -/
theorem additiveEnergyMax_attained (h : bezout.History N) (lam : J → ℝ) :
    ∃ j, additiveEnergyMax h lam=bezout.Probability.varianceProfile h (lam j) := by
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun j => bezout.Probability.varianceProfile h (lam j))
  exact ⟨j,hj⟩

omit [DecidableEq J] in
/-- The finite maximum squared response energy is nonnegative. -/
theorem additiveEnergyMax_nonneg (h : bezout.History N) (lam : J → ℝ) :
    0≤additiveEnergyMax h lam := by
  obtain ⟨j,hj⟩ := additiveEnergyMax_attained h lam
  rw [hj]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The true stacked additive map obeys the maximal spectral response bound. -/
theorem additiveOperator_action_sq_le (h : bezout.History N) (lam : J → ℝ)
    (W : EuclideanSpace ℝ (J×Fin N)) :
    ‖additiveOperator h lam W‖^2≤additiveEnergyMax h lam*‖W‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,additiveOperator_apply]
  calc
    _ ≤ ∑ j, bezout.Probability.varianceProfile h (lam j)*(∑ s, W (j,s)^2) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun s => (h.response s).eval (lam j)) (fun s => W (j,s)))
    _ ≤ ∑ j, additiveEnergyMax h lam*(∑ s, W (j,s)^2) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (responseEnergy_le_max h lam j)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = _ := by rw [← Finset.mul_sum,Fintype.sum_prod_type]

/-- A single-mode physical profile, normalized by its own response energy. -/
def additiveMaxProfile (h : bezout.History N) (lam : J → ℝ) (j0 : J) :
    EuclideanSpace ℝ (J×Fin N) :=
  WithLp.toLp 2 (fun k => if k.1=j0 then (h.response k.2).eval (lam j0)/
    Real.sqrt (bezout.Probability.varianceProfile h (lam j0)) else 0)

omit [Nonempty J] in
/-- A nonzero response row gives a unit-energy physical error profile. -/
theorem additiveMaxProfile_unit (h : bezout.History N) (lam : J → ℝ) (j0 : J)
    (hp : 0<bezout.Probability.varianceProfile h (lam j0)) :
    ‖additiveMaxProfile h lam j0‖=1 := by
  have hs : ‖additiveMaxProfile h lam j0‖^2=1 := by
    simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,additiveMaxProfile,
      Fintype.sum_prod_type]
    simp only [ite_pow,zero_pow (by omega : (2:ℕ)≠0)]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp only [div_pow]
    rw [← Finset.sum_div,Real.sq_sqrt hp.le]
    exact div_self hp.ne'
  nlinarith [norm_nonneg (additiveMaxProfile h lam j0)]

omit [Nonempty J] in
/-- Its actual output is the response-row norm in that same physical eigenmode. -/
theorem additiveMaxProfile_action (h : bezout.History N) (lam : J → ℝ) (j0 : J)
    (hp : 0<bezout.Probability.varianceProfile h (lam j0)) :
    additiveOperator h lam (additiveMaxProfile h lam j0)=
      Real.sqrt (bezout.Probability.varianceProfile h (lam j0)) • EuclideanSpace.single j0 1 := by
  ext j
  by_cases hj : j=j0
  · subst j
    simp only [additiveOperator_apply,additiveMaxProfile,ite_true,PiLp.smul_apply,
      smul_eq_mul,PiLp.single_apply,ite_true,mul_one]
    change (∑ s, (h.response s).eval (lam j0)*((h.response s).eval (lam j0)/
      Real.sqrt (bezout.Probability.varianceProfile h (lam j0))))=_
    simp_rw [← mul_div_assoc,← pow_two]
    rw [← Finset.sum_div]
    exact (div_eq_iff (Real.sqrt_pos.mpr hp).ne').mpr (Real.mul_self_sqrt hp.le).symm
  · simp [additiveOperator_apply,additiveMaxProfile,hj]

/-- The exact operator norm of the actual stacked additive terminal map. -/
theorem additiveOperator_norm (h : bezout.History N) (lam : J → ℝ) :
    ‖additiveOperator h lam‖=Real.sqrt (additiveEnergyMax h lam) := by
  have hn := additiveEnergyMax_nonneg h lam
  have hub : ‖additiveOperator h lam‖≤Real.sqrt (additiveEnergyMax h lam) := by
    apply (additiveOperator h lam).opNorm_le_bound (Real.sqrt_nonneg _)
    intro W
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt hn]
    exact additiveOperator_action_sq_le h lam W
  apply le_antisymm hub
  by_cases hp : 0<additiveEnergyMax h lam
  · obtain ⟨j,hj⟩ := additiveEnergyMax_attained h lam
    have hpj : 0<bezout.Probability.varianceProfile h (lam j) := hj ▸ hp
    have hb := (additiveOperator h lam).le_opNorm (additiveMaxProfile h lam j)
    rw [additiveMaxProfile_action h lam j hpj,additiveMaxProfile_unit h lam j hpj,
      norm_smul,PiLp.norm_single,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hb
    simpa [hj] using hb
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hp)]
    exact norm_nonneg _

/-- A maximizing spectral mode supplies an attaining physical error sequence;
zero response is handled by the zero-energy physical sequence. -/
theorem additiveOperator_sharp (h : bezout.History N) (lam : J → ℝ) :
    ∃ W : EuclideanSpace ℝ (J×Fin N), ‖W‖≤1 ∧
      ‖additiveOperator h lam W‖=Real.sqrt (additiveEnergyMax h lam) := by
  by_cases hp : 0<additiveEnergyMax h lam
  · obtain ⟨j,hj⟩ := additiveEnergyMax_attained h lam
    have hpj : 0<bezout.Probability.varianceProfile h (lam j) := hj ▸ hp
    refine ⟨additiveMaxProfile h lam j,(additiveMaxProfile_unit h lam j hpj).le,?_⟩
    rw [additiveMaxProfile_action h lam j hpj,norm_smul,PiLp.norm_single,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    simp [hj]
  · refine ⟨0,by simp,?_⟩
    simp [Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hp)]

/-- The measured actual physical additive response has exactly the maximal
spectral-row gain, with a physical error stream attaining it. -/
theorem additive_physical_sharp (h : bezout.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) :
    (∀ noise : Fin N → EuclideanSpace ℝ J, (∑ s, ‖noise s‖^2)≤1 →
      ‖(h.run (bezout.History.matrixEnd (Matrix.diagonal lam)) a noise).output-
        (aeval (bezout.History.matrixEnd (Matrix.diagonal lam)) h.terminal) a‖≤
          Real.sqrt (additiveEnergyMax h lam)) ∧
    ∃ noise : Fin N → EuclideanSpace ℝ J, (∑ s, ‖noise s‖^2)≤1 ∧
      ‖(h.run (bezout.History.matrixEnd (Matrix.diagonal lam)) a noise).output-
        (aeval (bezout.History.matrixEnd (Matrix.diagonal lam)) h.terminal) a‖=
          Real.sqrt (additiveEnergyMax h lam) := by
  constructor
  · intro noise hnoise
    let W : EuclideanSpace ℝ (J×Fin N) := WithLp.toLp 2 (fun k => noise k.2 k.1)
    have hw : stackedNoise W=noise := by
      funext s
      ext j
      rfl
    have henergy : ‖W‖≤1 := by
      have hh := stackedNoise_energy W
      rw [hw] at hh
      nlinarith [norm_nonneg W]
    rw [← hw,additiveOperator_physical]
    calc
      _ ≤ ‖additiveOperator h lam‖*‖W‖ := (additiveOperator h lam).le_opNorm W
      _ ≤ ‖additiveOperator h lam‖*1 := mul_le_mul_of_nonneg_left henergy (norm_nonneg _)
      _ = _ := by rw [mul_one,additiveOperator_norm]
  · obtain ⟨W,hW,he⟩ := additiveOperator_sharp h lam
    refine ⟨stackedNoise W,?_,?_⟩
    · rw [stackedNoise_energy]
      nlinarith [norm_nonneg W]
    · rw [additiveOperator_physical]
      exact he

end
end bezout.Channel
