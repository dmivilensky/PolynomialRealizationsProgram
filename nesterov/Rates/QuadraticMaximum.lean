import nesterov.Rates.Limit
import nesterov.Stationary.SourceDictionary

/-!
Article: §4 after `eq:p`, the actual quadratic rate of every stationary method.
Use: the maximum over all scalar curvatures and all actual complex roots exists,
is positive, and bounds the full nonlinear rate from below.
-/
namespace nesterov.Rates
noncomputable section
open Set
open scoped BigOperators
variable (M : StationaryMethod)

def quadraticRootNorms (μ L : ℝ) : Set ℝ :=
  {r | ∃ lam ∈ Icc μ L, ∃ z : ℂ,M.characteristic lam z=0 ∧ r=‖z‖}

def quadraticRate (μ L : ℝ) : ℝ := sSup (quadraticRootNorms M μ L)

theorem quadraticRootNorms_nonempty {μ L : ℝ} (hμL : μ<L) :
    (quadraticRootNorms M μ L).Nonempty := by
  obtain ⟨lam,hlam,z,_,hz⟩ := M.exists_nonzero_characteristic_root hμL
  exact ⟨‖z‖,lam,hlam,z,hz,rfl⟩

theorem isCompact_quadraticRootNorms {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    IsCompact (quadraticRootNorms M μ L) := by
  let Z : Set (ℝ × ℂ) := {p | p.1∈Icc μ L ∧ M.characteristic p.1 p.2=0}
  have hclosed : IsClosed Z := by
    apply (isClosed_Icc.preimage continuous_fst).inter
    apply isClosed_eq _ continuous_const
    unfold StationaryMethod.characteristic
    fun_prop
  have hcompact : IsCompact Z := by
    apply (isCompact_Icc.prod (isCompact_closedBall (0:ℂ) (rate M μ L))).of_isClosed_subset hclosed
    intro p hp
    exact ⟨hp.1,by simpa using characteristicRoot_norm_le_rate M hμ hμL hp.1 hp.2⟩
  have he : (fun p : ℝ × ℂ => ‖p.2‖) '' Z=quadraticRootNorms M μ L := by
    ext x
    constructor
    · rintro ⟨⟨lam,z⟩,hp,rfl⟩
      exact ⟨lam,hp.1,z,hp.2,rfl⟩
    · rintro ⟨lam,hlam,z,hz,rfl⟩
      exact ⟨(lam,z),⟨hlam,hz⟩,rfl⟩
  rw [← he]
  exact hcompact.image (continuous_norm.comp continuous_snd)

theorem quadraticRate_isGreatest {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    IsGreatest (quadraticRootNorms M μ L) (quadraticRate M μ L) := by
  obtain ⟨r,hr⟩ := (isCompact_quadraticRootNorms M hμ hμL).exists_isGreatest
    (quadraticRootNorms_nonempty M hμL)
  simpa only [quadraticRate,hr.csSup_eq] using hr

theorem quadraticRate_le_rate {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    quadraticRate M μ L≤rate M μ L := by
  apply csSup_le (quadraticRootNorms_nonempty M hμL)
  rintro x ⟨lam,hlam,z,hz,rfl⟩
  exact characteristicRoot_norm_le_rate M hμ hμL hlam hz

theorem quadraticRate_pos {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    0<quadraticRate M μ L := by
  obtain ⟨lam,hlam,z,hz0,hz⟩ := M.exists_nonzero_characteristic_root hμL
  exact (norm_pos_iff.mpr hz0).trans_le
    ((quadraticRate_isGreatest M hμ hμL).2 ⟨lam,hlam,z,hz,rfl⟩)

end
end nesterov.Rates
