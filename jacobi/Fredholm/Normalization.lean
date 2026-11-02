import jacobi.Fredholm.OptimizerShape
import jacobi.Fredholm.Parameters

/-!
Article: jacobi, Theorem D.7.
The two printed parameters are extracted from the genuine optimizing Green
diagonal. All inverse formulas and the amplitude normalization follow from
the proved central turn, rather than from an assumed candidate profile.
Source: the actual zero first integral and elementary rational algebra.
Use: distinguishes its full-support and compact-core branches.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Variational jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The actual Fredholm optimizer's printed shape parameter.
Use: distinguishes its full-support and compact-core branches.
Article: jacobi, Theorem D.7.
-/
def Optimizer.tau {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) : ℝ :=
  2*(P.g hs.le 0-P.edge)/(2*P.g hs.le 0-1)

/-- The actual Fredholm optimizer's printed determinant parameter.
Use: identifies its upper Green turn with the literal peak(chi).
Article: jacobi, Theorem D.7.
-/
def Optimizer.chi {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) : ℝ :=
  (2*P.g hs.le 0-1)/(2*P.g hs.le 0)

/-- Every genuine nonzero Fredholm optimizer gives parameters in the entire asserted domain.
Use: applies all common elliptic quadrature estimates to the actual optimizer.
Article: jacobi, Theorem D.7.
Proof: the true upper turn is strictly above its switching level, which is
at least one half; the two positive denominator inequalities are then exact. -/
theorem Optimizer.parameters {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    P.tau hs∈Ioc (0:ℝ) 1 ∧ P.chi hs∈Ioo (0:ℝ) 1 := by
  have he := (P.parameter_signs hs).1
  have hg := (P.shape hs).1
  have hg0 : 0<2*P.g hs.le 0 := by linarith
  have hden : 0<2*P.g hs.le 0-1 := by linarith
  refine ⟨⟨div_pos (by linarith) hden,?_⟩,div_pos hden hg0,?_⟩
  · exact (div_le_one hden).mpr (by linarith)
  · exact (div_lt_one hg0).mpr (by linarith)

/-- The genuine optimizing peak and switching level satisfy the printed inverse parameter formulas.
Use: identifies the actual autonomous Green equation with the normalized polynomial P.
Article: jacobi, Theorem D.7.
Proof: substitute the actual definitions and cancel only the proved
positive central Green level and its positive excess above one half. -/
theorem Optimizer.inverse_parameters {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    peak (P.chi hs)=P.g hs.le 0 ∧ jacobi.Fredholm.edge (P.tau hs) (P.chi hs)=P.edge ∧
      delta (P.tau hs) (P.chi hs)=P.g hs.le 0-P.edge := by
  -- The denominators come from the true strict upper turn of the optimizer.
  have hg := (P.shape hs).1
  have he := (P.parameter_signs hs).1
  have h0 : 2*P.g hs.le 0≠0 := ne_of_gt (by linarith)
  have h1 : 2*P.g hs.le 0-1≠0 := ne_of_gt (by linarith)
  have hg0 : P.g hs.le 0≠0 := ne_of_gt (by linarith)
  have hchi : 1-P.chi hs=(2*P.g hs.le 0)⁻¹ := by
    unfold Optimizer.chi
    field_simp [h0]
    ring
  unfold peak jacobi.Fredholm.edge delta
  rw [hchi]
  unfold Optimizer.tau Optimizer.chi
  constructor
  · field_simp [hg0]
  constructor
  · field_simp [h0,h1,hg0]
    ring
  · field_simp [h0,h1,hg0]

/-- The actual Green turning equation fixes precisely the printed amplitude normalization.
Use: closes the coefficient of the normalized density and every ensuing state quadrature.
Article: jacobi, Theorem D.7.
Proof: evaluate the proved zero first integral at the genuine zero-slope
central turn. Its positive-part factor is strictly positive. Substituting
the actual inverse parameters gives the squared amplitude identity; both
amplitudes are positive, so equality of their squares determines the sign. -/
theorem Optimizer.amplitude_eq {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    amplitude (P.tau hs) (P.chi hs)=P.A := by
  -- The positive turning gap removes the clipped branch at the actual peak.
  obtain ⟨hg,hzero,_,_⟩ := P.shape hs
  have hfirst := P.first_integral hs 0
  rw [hzero] at hfirst
  unfold phase at hfirst
  rw [max_eq_left (sub_pos.mpr hg).le] at hfirst
  have he := (P.parameter_signs hs).1
  have h0 : 2*P.g hs.le 0≠0 := ne_of_gt (by linarith)
  have h1 : 2*P.g hs.le 0-1≠0 := ne_of_gt (by linarith)
  have hgap : P.g hs.le 0-P.edge≠0 := (sub_pos.mpr hg).ne'
  have hg0 : P.g hs.le 0≠0 := ne_of_gt (by linarith)
  have hsq : P.A^2*(P.g hs.le 0-P.edge)^2=3*P.chi hs/P.tau hs := by
    unfold Optimizer.chi Optimizer.tau
    field_simp [h0,h1,hgap,hg0]
    nlinarith [hfirst]
  have hparams := P.parameters hs
  have hbounds := parameter_bounds hparams.1 hparams.2
  have hdelta := (P.inverse_parameters hs).2.2
  have hsqrt := sq_sqrt (div_pos (mul_pos (by norm_num : (0:ℝ)<3) hparams.2.1) hparams.1.1).le
  have ha : (amplitude (P.tau hs) (P.chi hs))^2=P.A^2 := by
    unfold amplitude
    rw [div_pow,hsqrt,hdelta,← hsq]
    field_simp [hgap]
  exact (sq_eq_sq₀ hbounds.2.2.2.le (P.parameter_signs hs).2.le).mp ha

/-- Full support is exactly the vanishing-mass-multiplier endpoint of the actual parameterization.
Use: the two alternatives in the Fredholm minimum have the correct complementarity condition.
Article: jacobi, Theorem D.7.
Proof: the positive actual peak denominator first identifies tau=1 with
the switching level one half; the strictly positive normal multiplier and
coupling then identify this level with the zero mass multiplier. -/
theorem Optimizer.free_iff {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    (P.tau hs=1 ↔ P.edge=(1/2:ℝ)) ∧ (P.edge=(1/2:ℝ) ↔ P.ell=0) := by
  -- Both equivalences cancel the actual strictly positive normalizing denominators.
  have hden : 2*P.g hs.le 0-1≠0 := by
    have hg := (P.shape hs).1
    have he := (P.parameter_signs hs).1
    linarith
  constructor
  · unfold Optimizer.tau
    rw [div_eq_one_iff_eq hden]
    constructor <;> intro hh <;> linarith
  · unfold Optimizer.edge
    constructor
    · intro hh
      exact (div_eq_zero_iff.mp (show P.ell/(2*P.mu*s)=0 by linarith)).resolve_right
        (mul_ne_zero (mul_ne_zero (by norm_num) P.mu_pos.ne') hs.ne')
    · intro hh
      simp only [hh,zero_div,add_zero]

end
end jacobi.Fredholm
