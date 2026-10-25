import polyak.ModeLocking.Analysis.CompactCover

/-! Compactness supplies every bound used to preserve all quadratic zeros. -/
noncomputable section
namespace polyak.ModeLocking.Analysis
open Set

theorem compact_abs_bound {a b:ℝ} {f:ℝ→ℝ} (hne:(Icc a b).Nonempty)
    (hc:ContinuousOn f (Icc a b)) : ∃M:ℝ,0≤M ∧ ∀x∈Icc a b,|f x|≤M := by
  obtain ⟨z,hz,hmax⟩:=isCompact_Icc.exists_isMaxOn hne hc.abs
  exact ⟨|f z|,abs_nonneg _,fun x hx=>hmax hx⟩

theorem finite_zero_perturbation {a b:ℝ} {Z:Finset ℝ} {f E:ℝ→ℝ}
    (hne:Z.Nonempty) (hz:∀z∈Z,z∈Icc a b)
    (hf:∀x∈Icc a b,ContDiffAt ℝ 2 f x)
    (hc2:ContinuousOn (iteratedDeriv 2 f) (Icc a b))
    (hzero:∀z∈Z,f z=0) (hslope:∀z∈Z,deriv f z=0)
    (hcurv:∀z∈Z,iteratedDeriv 2 f z<0)
    (hstrict:∀x∈Icc a b,x∉Z→f x<0)
    (hE:∀x∈Icc a b,ContDiffAt ℝ 2 E x)
    (hE2:ContinuousOn (iteratedDeriv 2 E) (Icc a b))
    (hEz:∀z∈Z,E z=0) (hEdz:∀z∈Z,deriv E z=0) :
    ∃r:ℝ,0<r ∧ ∀ε:ℝ,|ε|<r→Nonempty (NegativeJetCover a b Z (fun x=>f x+ε*E x)) := by
  obtain ⟨D⟩:=exists_negativeJetCover hne hz hf hc2 hzero hslope hcurv hstrict
  have hi:(Icc a b).Nonempty:=by obtain ⟨z,hzZ⟩:=hne;exact ⟨z,hz z hzZ⟩
  have hEc:ContinuousOn E (Icc a b):=fun x hx=>(hE x hx).continuousAt.continuousWithinAt
  obtain ⟨M0,hM0,hB0⟩:=compact_abs_bound hi hEc
  obtain ⟨M2,hM2,hB2⟩:=compact_abs_bound hi hE2
  exact D.perturb hE hEz hEdz hM0 hM2 hB0 hB2

end polyak.ModeLocking.Analysis
