import jacobi.Variational.Problem
import chebyshev2.GroundState.Uniqueness

/-!
Article: jacobi, Appendix D.1 (ground parameter).
The ground-state simplicity already proved in chebyshev2 is combined
with the actual sorted spectral selection. It produces a unit top vector,
a strictly positive gap to the second eigenvalue, and the sharp Rayleigh
bound on its orthogonal complement. These discharge the spectral hypotheses
of the quantitative first-variation theorem for arbitrary nonzero densities.
Source: compact self-adjoint spectral theory and simplicity of the positive ground state.
Use: supplies all spectral inputs to the quantitative operator first variation.
-/
namespace jacobi.Variational
noncomputable section
open Real MeasureTheory chebyshev2.Continuum chebyshev2.GroundState
open scoped InnerProductSpace Classical
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual sorted selection gives the sharp complementary gap at a simple positive top.
Use: supplies all spectral inputs to the quantitative operator first variation.
Article: jacobi, Appendix D.1 (ground parameter).
Proof: select the first actual eigenbasis vector. A second vector at the same
eigenvalue would be a scalar multiple of it by simplicity, contradicting orthonormality.
The existing sorted min--max bound then controls its orthogonal complement. -/
theorem simple_top_gap {T : E →L[ℝ] E} (D : PositiveSpectralData T)
    (hp : 0 < D.eigenvalue 0)
    (hs : ∀ e : E, ‖e‖=1 → T e=D.eigenvalue 0 • e →
      ∀ v : E, T v=D.eigenvalue 0 • v → ∃ c : ℝ, v=c • e) :
    ∃ e : E, ‖e‖=1 ∧ T e=D.eigenvalue 0 • e ∧
      0 < D.eigenvalue 0-D.eigenvalue 1 ∧
      ∀ h : E, inner ℝ e h=0 → inner ℝ h (T h)≤D.eigenvalue 1*‖h‖^2 := by
  -- The first sorted selector is nonempty because the top eigenvalue is positive.
  cases hi : spectralNext D.summable (spectralSelected D.summable 0) with
  | none =>
    have hz : D.eigenvalue 0=0 := by simp [PositiveSpectralData.eigenvalue,spectralSorted,hi]
    exact (hp.ne' hz).elim
  | some i =>
    have he : D.eigenvalue 0=D.eig i := spectralSorted_eq D.summable hi
    have hunit : ‖D.basis i‖=1 := D.basis.orthonormal.norm_eq_one i
    have hTe : T (D.basis i)=D.eigenvalue 0 • D.basis i := by rw [he,D.equation]
    have hsel : spectralSelected D.summable 1={i} := by
      rw [spectralSelected,hi]
      rfl
    refine ⟨D.basis i,hunit,hTe,?_,?_⟩
    · apply sub_pos.mpr
      by_contra! hle
      have heq := le_antisymm (D.eigenvalue_antitone (by omega : 0≤1)) hle
      cases hj : spectralNext D.summable (spectralSelected D.summable 1) with
      | none =>
        have hz : D.eigenvalue 1=0 := by simp [PositiveSpectralData.eigenvalue,spectralSorted,hj]
        exact (hp.ne' (heq.symm.trans hz)).elim
      | some j =>
        have hjn : j ≠ i := by
          have hh := (spectralNext_some D.summable hj).1
          simpa only [hsel,Finset.mem_singleton] using hh
        have hej : T (D.basis j)=D.eigenvalue 0 • D.basis j := by
          have hval : D.eigenvalue 1=D.eig j := spectralSorted_eq D.summable hj
          rw [D.equation,← heq,hval]
        obtain ⟨c,hc⟩ := hs _ hunit hTe _ hej
        have ho := D.basis.orthonormal.inner_eq_zero hjn.symm
        rw [hc,real_inner_smul_right,real_inner_self_eq_norm_sq,hunit] at ho
        have hz : D.basis j=0 := by simpa [show c=0 by simpa using ho] using hc
        have hh := D.basis.orthonormal.norm_eq_one j
        simp only [hz,norm_zero,zero_ne_one] at hh
    · intro h hh
      apply D.quadratic_le_eigenvalue 1 h
      intro j hj
      have hji : j=i := by simpa only [hsel,Finset.mem_singleton] using hj
      simpa only [hji] using hh

/-- Every actual nonzero density has the printed positive gap and complementary bound.
Use: removes simplicity and isolation premises from the top-eigenvalue first variation.
Article: jacobi, Appendix D.1 (ground parameter).
Proof: reuse the proved unique positive ground state and identify the actual
feature and kernel spectra; scalar multiples are normalized at the selected unit vector. -/
theorem density_top_gap (m : L1Source) (hm : 0 < m.mass) :
    ∃ e : FeatureSpace, ‖e‖=1 ∧ densityOperator m.value e=m.spectrum 0 • e ∧
      0 < m.spectrum 0-m.spectrum 1 ∧
      ∀ h : FeatureSpace, inner ℝ e h=0 →
        inner ℝ h (densityOperator m.value h)≤m.spectrum 1*‖h‖^2 := by
  -- Simplicity is taken from the existing actual ground-state theorem, not assumed.
  let D := densitySpectralData m.integrable m.nonneg
  have hD : D.eigenvalue=m.spectrum := density_kernel_eigenvalue_eq m.integrable m.nonneg D
  have hp : 0 < D.eigenvalue 0 := by rw [hD]; exact (top_density_attained m.integrable m.nonneg hm).1
  obtain ⟨u,_,_,_,_,_,hs,_⟩ := exists_unique_ground m.integrable m.nonneg hm
  have hsimple (e : FeatureSpace) (he : ‖e‖=1) (hTe : densityOperator m.value e=D.eigenvalue 0 • e)
      (v : FeatureSpace) (hTv : densityOperator m.value v=D.eigenvalue 0 • v) : ∃ c : ℝ, v=c • e := by
    rw [hD] at hTe hTv
    obtain ⟨a,ha⟩ := hs e hTe
    obtain ⟨b,hb⟩ := hs v hTv
    have ha0 : a ≠ 0 := by
      intro hz
      rw [hz,zero_smul] at ha
      simp only [ha,norm_zero,zero_ne_one] at he
    refine ⟨b/a,?_⟩
    rw [ha,hb,smul_smul,div_mul_cancel₀ _ ha0]
  simpa only [hD] using simple_top_gap D hp hsimple

end
end jacobi.Variational
