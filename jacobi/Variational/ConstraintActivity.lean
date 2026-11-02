import jacobi.Variational.DensityCone

/-!
Article: jacobi, Theorem D.7.
A quadratic L1 expansion at a nonzero actual minimizer forces its constraint
active. An explicit short amplitude decrease preserves a slack threshold
and strictly lowers the genuine energy. No differentiability of the
constraint away from this one density is required.
Source: the amplitude descent argument in the proof of the multiplier rule.
Use: supplies the activity conclusion of the common multiplier rule, in particular for Fredholm.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter
set_option backward.isDefEq.respectTransparency false

/-- The quadratic spectral expansion alone forces an actual constrained minimizer onto its threshold.
Use: supplies the activity conclusion of the common multiplier rule, in particular for Fredholm.
Article: jacobi, Theorem D.7.
Proof: choose a positive amplitude decrement below both the L1 radius and
the slack divided by a bound for the linear and quadratic variation. The
rescaled density preserves the mass bound and threshold but lowers energy. -/
theorem spectral_constraint_active (m : Density) (hm : 0<m.mass)
    (Φ : Density → ℝ) (γ : ℝ → ℝ) {M T C r : ℝ}
    (hC : 0<C) (hr : 0<r) (hmM : m.mass≤M) (hmT : T≤Φ m)
    (hmin : ∀ q : Density,q.mass≤M → T≤Φ q → m.energy≤q.energy)
    (hvar : ∀ q : Density,(∫ x,|q.value x-m.value x|)≤r →
      |Φ q-Φ m-(∫ x,γ x*(q.value x-m.value x))|≤C*(∫ x,|q.value x-m.value x|)^2) :
    Φ m=T := by
  -- A slack constraint admits one explicitly controlled nontrivial amplitude decrease.
  apply le_antisymm _ hmT
  by_contra! hslack
  let I := ∫ x,γ x*m.value x
  let A := C*m.mass^2+|I|+1
  have hA : 0<A := by dsimp only [A]; positivity
  let ε := min (1/2:ℝ) (min (r/(m.mass+1)) ((Φ m-T)/(2*A)))
  have hε : 0<ε := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hε1 : ε≤1/2 := min_le_left _ _
  have hεr : ε≤r/(m.mass+1) := (min_le_right _ _).trans (min_le_left _ _)
  have hεA : ε≤(Φ m-T)/(2*A) := (min_le_right _ _).trans (min_le_right _ _)
  let q := m.scale (1-ε) (by linarith)
  have hqL : (∫ x,|q.value x-m.value x|)=ε*m.mass := by
    have he : (fun x => |q.value x-m.value x|)=fun x => ε*m.value x := by
      funext x
      change |(1-ε)*m.value x-m.value x|=ε*m.value x
      rw [show (1-ε)*m.value x-m.value x=-(ε*m.value x) by ring,abs_neg,
        abs_of_nonneg (mul_nonneg hε.le (m.nonneg x))]
    rw [he,integral_const_mul]
    rfl
  have hsmall : (∫ x,|q.value x-m.value x|)≤r := by
    rw [hqL]
    have hh := (le_div_iff₀ (by positivity : 0<m.mass+1)).mp hεr
    nlinarith
  have hqI : (∫ x,γ x*(q.value x-m.value x))=-ε*I := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change γ x*((1-ε)*m.value x-m.value x)=-ε*(γ x*m.value x)
      ring
  have hv := hvar q hsmall
  rw [hqL,hqI] at hv
  have hbudget := (le_div_iff₀ (by positivity : 0<2*A)).mp hεA
  have herr : C*(ε*m.mass)^2+ε*|I|<Φ m-T := by
    have hsq : ε^2≤ε := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0≤C*m.mass^2)
    have he : 0<ε*A := mul_pos hε hA
    dsimp only [A] at hbudget he
    nlinarith
  have hqT : T≤Φ q := by
    have hh := (neg_le_abs (Φ q-Φ m-(-ε*I))).trans hv
    have hI := mul_le_mul_of_nonneg_left (le_abs_self I) hε.le
    linarith
  have hqM : q.mass≤M := by
    rw [Density.scale_mass]
    exact (mul_le_of_le_one_left hm.le (by linarith : 1-ε≤1)).trans hmM
  have hqE : q.energy<m.energy := by
    rw [Density.scale_energy]
    exact mul_lt_of_lt_one_left (m.energy_pos hm)
      (Real.rpow_lt_one (by linarith : 0≤1-ε) (by linarith) (by norm_num : (0:ℝ)<3/2))
  exact (not_lt_of_ge (hmin q hqM hqT)) hqE

end
end jacobi.Variational
