import nesterov.Stationary.Normalized
import nesterov.Rates.QuadraticMaximum

/-!
Article: Lemma `lem:iqc`, the precise middle-quadratic stability threshold r_c.
Use: the actual normalized recurrence polynomial, with an attained maximum
root modulus and its comparison to the full quadratic rate.
-/
namespace nesterov.IQC
noncomputable section
open Set
variable (M : StationaryMethod)

def middleRootNorms (μ L : ℝ) : Set ℝ :=
  {r | ∃ z : ℂ,M.characteristic ((L+μ)/2) z=0 ∧ r=‖z‖}
def middleRadius (μ L : ℝ) : ℝ := sSup (middleRootNorms M μ L)

theorem normalized_root_iff_middle {μ L : ℝ} (hμL : μ<L) (z : ℂ) :
    ((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 ↔
      M.characteristic ((L+μ)/2) z=0 := by
  rw [M.normalizedPolynomial_characteristic]
  have hr : -(2/(L-μ):ℝ)≠0 := neg_ne_zero.mpr
    (div_ne_zero (by norm_num : (2:ℝ)≠0) (ne_of_gt (sub_pos.mpr hμL)))
  have hn : (-(2/(L-μ):ℝ):ℂ)≠0 := by
    simpa only [Complex.ofReal_neg] using Complex.ofReal_ne_zero.mpr hr
  exact mul_eq_zero.trans (or_iff_right hn)

theorem middleRootNorms_nonempty (μ L : ℝ) : (middleRootNorms M μ L).Nonempty := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_root (M.characteristicPolynomial ((L+μ)/2))
    (by rw [Polynomial.degree_eq_natDegree (by
          intro h
          have hd := M.characteristicPolynomial_natDegree ((L+μ)/2)
          rw [h,Polynomial.natDegree_zero] at hd
          exact M.memory_pos.ne' hd.symm),M.characteristicPolynomial_natDegree]
        exact_mod_cast M.memory_pos.ne')
  change (M.characteristicPolynomial ((L+μ)/2)).eval z=0 at hz
  rw [M.characteristicPolynomial_eval] at hz
  exact ⟨‖z‖,z,hz,rfl⟩

theorem isCompact_middleRootNorms {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    IsCompact (middleRootNorms M μ L) := by
  let Z : Set ℂ := {z | M.characteristic ((L+μ)/2) z=0}
  have hclosed : IsClosed Z := by
    apply isClosed_eq _ continuous_const
    unfold StationaryMethod.characteristic
    fun_prop
  have hcompact : IsCompact Z := by
    apply (isCompact_closedBall (0:ℂ) (Rates.rate M μ L)).of_isClosed_subset hclosed
    intro z hz
    apply mem_closedBall_zero_iff.mpr
    exact Rates.characteristicRoot_norm_le_rate M hμ hμL
      (show (L+μ)/2∈Icc μ L by constructor <;> linarith) hz
  have he : norm '' Z=middleRootNorms M μ L := by
    ext r
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z,hz,rfl⟩
  rw [←he]
  exact hcompact.image continuous_norm

theorem middleRadius_isGreatest {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    IsGreatest (middleRootNorms M μ L) (middleRadius M μ L) := by
  obtain ⟨r,hr⟩ := (isCompact_middleRootNorms M hμ hμL).exists_isGreatest
    (middleRootNorms_nonempty M μ L)
  simpa only [middleRadius,hr.csSup_eq] using hr

theorem middleRadius_nonneg {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) : 0≤middleRadius M μ L := by
  obtain ⟨z,hz,he⟩ := (middleRadius_isGreatest M hμ hμL).1
  rw [he]
  exact norm_nonneg _

theorem normalized_root_norm_le {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) {z : ℂ}
    (hz : ((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0) :
    ‖z‖≤middleRadius M μ L :=
  (middleRadius_isGreatest M hμ hμL).2 ⟨z,(normalized_root_iff_middle M hμL z).mp hz,rfl⟩

theorem middleRadius_le_quadraticRate {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    middleRadius M μ L≤Rates.quadraticRate M μ L := by
  obtain ⟨z,hz,he⟩ := (middleRadius_isGreatest M hμ hμL).1
  rw [he]
  exact (Rates.quadraticRate_isGreatest M hμ hμL).2
    ⟨(L+μ)/2,⟨by linarith,by linarith⟩,z,hz,rfl⟩

end
end nesterov.IQC
