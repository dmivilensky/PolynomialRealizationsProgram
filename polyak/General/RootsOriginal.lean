import polyak.General.RootsDominant
import polyak.Dynamics.Scale

/-! Article: the tuning coordinates preserve the actual quadratic factor and actual rate. -/
namespace polyak.General
noncomputable section

theorem quadraticRootNorms_scaled {μ L α β : ℝ} (hα : 0<α) :
    Dynamics.quadraticRootNorms (α*μ) (α*L) 1 β=
      Dynamics.quadraticRootNorms μ L α β := by
  ext r
  constructor
  · rintro ⟨lam,hlam,z,hz,hr⟩
    refine ⟨lam/α,⟨(le_div_iff₀ hα).2 (by nlinarith [hlam.1]),
      (div_le_iff₀ hα).2 (by nlinarith [hlam.2])⟩,z,?_,hr⟩
    have he : α*(lam/α)=lam := mul_div_cancel₀ lam (ne_of_gt hα)
    simpa only [he,one_mul] using hz
  · rintro ⟨lam,hlam,z,hz,hr⟩
    exact ⟨α*lam,⟨mul_le_mul_of_nonneg_left hlam.1 hα.le,
      mul_le_mul_of_nonneg_left hlam.2 hα.le⟩,z,by simpa using hz,hr⟩

namespace Tuning
theorem ofOriginal_quadraticRate (μ L α β : ℝ) (hμ : 0<μ) (hL : μ<L)
    (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1) (hquad : α*L<2*(1+β)) :
    (ofOriginal μ L α β hμ hL hα hβ hβ1 hquad).rhoQ=
      Dynamics.quadraticRate μ L α β := by
  rw [← quadraticRate_eq,ofOriginal_x]
  change Dynamics.quadraticRate (α*μ) (α*L) 1 β= _
  unfold Dynamics.quadraticRate
  rw [quadraticRootNorms_scaled hα]

theorem ofOriginal_rate (μ L α β : ℝ) (hμ : 0<μ) (hL : μ<L)
    (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1) (hquad : α*L<2*(1+β)) :
    (ofOriginal μ L α β hμ hL hα hβ hβ1 hquad).rate=Dynamics.rate μ L α β := by
  unfold rate
  rw [ofOriginal_x]
  change Dynamics.rate (α*μ) (α*L) 1 β= _
  have he : α/α=1 := div_self (ne_of_gt hα)
  simpa only [he] using (Dynamics.rate_scale (μ:=μ) (L:=L) (α:=α) (β:=β) hα)
end Tuning
end
end polyak.General
