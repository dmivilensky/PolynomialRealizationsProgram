import krylov.Convergence.OneGradientLowerScalar

/-!
Article: main_krylov, thm:LB, original last-query curvature clipping.
Use: keep both true cubic sources inside an arbitrarily thin admissible
Jacobi fibre, while retaining the full sharp endpoint obstruction even
when the method chooses an arbitrarily remote final queried coordinate.
Source: Appendix G's M_p=min(M,2δ'/|p|), including its zero branch.
-/
namespace krylov.Convergence
noncomputable section

/-- Literal magnitude of the hidden cubic used in the original proof.
Article: main_krylov, thm:LB. -/
def oneGradientClippedMagnitude (M δ p : ℝ) : ℝ :=
  if p=0 then M else min M (2*δ/|p|)

/-- The real clipped source retains a nonnegative cubic coefficient and
never exceeds its prescribed original tensor budget. Article: thm:LB. -/
theorem oneGradientClippedMagnitude_bounds (M δ p : ℝ) (hM : 0≤M) (hδ : 0≤δ) :
    0≤oneGradientClippedMagnitude M δ p ∧oneGradientClippedMagnitude M δ p≤M ∧
      oneGradientClippedMagnitude M δ p*|p|≤2*δ := by
  by_cases hp : p=0
  · simp only [oneGradientClippedMagnitude,hp,abs_zero,mul_zero,ite_true]
    exact ⟨hM,le_rfl,by positivity⟩
  · have ha := abs_pos.mpr hp
    simp only [oneGradientClippedMagnitude,ite_eq_right hp]
    refine ⟨le_min hM (by positivity),min_le_left _ _,?_⟩
    exact (mul_le_mul_of_nonneg_right (min_le_right M (2*δ/|p|)) ha.le).trans_eq
      (div_mul_cancel₀ _ ha.ne')

/-- Curvature clipping does not weaken the sharp endpoint lower target
at a sufficiently small genuine starting scale. No upper bound on the
method's last queried coordinate is imposed. Article: main_krylov, thm:LB. -/
theorem oneGradientClippedMagnitude_lower
    (M δ p y ρ : ℝ) (hM : 0<M) (hδ : 0≤δ) (_hρ : 0≤ρ) (hρ1 : ρ≤1)
    (hy : |y|≤δ/M) (hsep : ρ*|y|≤|y-p|) :
    M*ρ*|y|^2≤oneGradientClippedMagnitude M δ p*|y| *|y-p| := by
  have hyM : M*|y|≤δ := by
    have hh := (le_div_iff₀ hM).mp hy
    nlinarith only [hh]
  have hh := oneGradientClippedMagnitude_bounds M δ p hM.le hδ
  by_cases hp : p=0
  · rw [oneGradientClippedMagnitude,ite_eq_left hp]
    have hmul := mul_le_mul_of_nonneg_left hsep (mul_nonneg hM.le (abs_nonneg y))
    nlinarith only [hmul]
  · have ha := abs_pos.mpr hp
    dsimp only [oneGradientClippedMagnitude]
    rw [ite_eq_right hp]
    by_cases hfull : M≤2*δ/|p|
    · rw [min_eq_left hfull]
      have hmul := mul_le_mul_of_nonneg_left hsep (mul_nonneg hM.le (abs_nonneg y))
      nlinarith only [hmul]
    · rw [min_eq_right (le_of_not_ge hfull)]
      have hlarge : 2*δ<M*|p| := (div_lt_iff₀ ha).mp (lt_of_not_ge hfull)
      have hfar : |p|/2≤|y-p| := by
        have habs : |p|≤|y|+|y-p| := by
          calc
            |p| = |y-(y-p)| := by congr 1;ring
            _ ≤ |y|+|y-p| := abs_sub _ _
        nlinarith only [habs,hlarge,hyM,hM]
      have hmul := mul_le_mul_of_nonneg_left hfar (by positivity : 0≤2*δ/|p| *|y|)
      have he : (2*δ/|p| *|y|)*(|p|/2)=δ*|y| := by field_simp
      rw [he] at hmul
      have hsmall : M*ρ*|y|^2≤δ*|y| := by
        calc
          _ ≤ M*|y|^2 := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ1 hM.le) (sq_nonneg (|y|))
          _ ≤ δ*|y| := by nlinarith only [mul_le_mul_of_nonneg_right hyM (abs_nonneg y)]
      exact hsmall.trans hmul

/-- Explicit uniform perturbation denominator, independent of the last
query and of the common output. It tends to zero with the fibre width
and starting scale. Article: main_krylov, thm:LB. -/
theorem oneGradientClippedMagnitude_relative_error
    (M δ p y c : ℝ) (hM : 0≤M) (hδ : 0≤δ) (_hc : 0≤c) :
    let Mp := oneGradientClippedMagnitude M δ p
    let T := (Mp/2*c)*|y| *|y-p|
    (Mp/2*c)*c*(|y|+|y-p|+c*T)≤
      c^2*(M*|y|+δ)+M*c^4/4*|y| *(M*|y|+2*δ) := by
  have hb := oneGradientClippedMagnitude_bounds M δ p hM hδ
  let Mp := oneGradientClippedMagnitude M δ p
  have hMp : 0≤Mp := hb.1
  have hMpM : Mp≤M := hb.2.1
  have hMpp : Mp*|p|≤2*δ := hb.2.2
  have hprod : Mp*|y-p|≤M*|y|+2*δ := by
    calc
      _ ≤ Mp*(|y|+|p|) := mul_le_mul_of_nonneg_left (abs_sub _ _) hMp
      _ ≤ M*|y|+2*δ := by nlinarith only [hMpp,mul_le_mul_of_nonneg_right hMpM (abs_nonneg y)]
  change (Mp/2*c)*c*(|y|+|y-p|+c*((Mp/2*c)*|y| *|y-p|))≤_
  have h1 : Mp*(|y|+|y-p|)≤2*M*|y|+2*δ := by
    nlinarith only [hprod,mul_le_mul_of_nonneg_right hMpM (abs_nonneg y)]
  have h2 := mul_le_mul_of_nonneg_left hprod (mul_nonneg hM (abs_nonneg y))
  have h3 := mul_le_mul_of_nonneg_left hMpM (by positivity : 0≤Mp*|y| *|y-p|)
  nlinarith only [mul_le_mul_of_nonneg_left h1 (by positivity : 0≤c^2/2),
    mul_le_mul_of_nonneg_left h2 (by positivity : 0≤c^4/4),
    mul_le_mul_of_nonneg_left h3 (by positivity : 0≤c^4/4)]

end
end krylov.Convergence
