import polyak.Numerics.Parametric.DyadicAnalytic
import polyak.Numerics.Parametric.Correlated

/-! Article: Appendix B, analytic roots of the correlated continuation checker. -/
noncomputable section
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine Filter
open scoped Topology ContDiff

theorem checkCorrelated_analytic_branch {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (cert : WeightedCertificate n) (cfg : DyadicConfig)
    (hc : checkCorrelated F I cert cfg=true) {s : ℝ} {x : Fin n → ℝ}
    (hs : s∈I) (hx : FinBoxMem x (coordinateBox cert.center cert.radius))
    (hz : system F s x=0) :
    ∃ g : ℝ → (Fin n → ℝ), AnalyticAt ℝ g s ∧ g s=x ∧
      ∀ᶠ t in 𝓝 s, system F t (g t)=0 := by
  have hd := hc
  simp only [checkCorrelated,memoMatrix_eq,memoFin_eq,Bool.and_eq_true,decide_eq_true_eq] at hd
  obtain ⟨⟨⟨hF,hJ⟩,_⟩,hcheck⟩ := hd
  simp only [weightedEnclosureCheck,enclosureCheck,Bool.and_eq_true,decide_eq_true_eq] at hcheck
  obtain ⟨hr,⟨⟨_,hq⟩,_⟩⟩ := hcheck
  let Fs := scaledSystem F cert.center cert.radius
  let y := normalizePoint cert.center cert.radius x
  have hF' : ∀ i, ADSupported (F i) :=
    fun i => ((F i).checkADSupported_eq_true_iff).mp (hF i)
  have hFs : ∀ i, ADSupported (Fs i) := fun i =>
    substitute_supported _ (scaledVariable_supported cert.center cert.radius) _ (hF' i)
  have hy := normalizePoint_mem cert.center cert.radius hr hx
  have he := chart_normalizePoint cert.center cert.radius hr x
  have hz' : system Fs s y=0 := by
    rw [scaledSystem_eval,he]
    exact hz
  have hcd := (joint_contDiff Fs hFs).contDiffAt (x := (s,y))
  have hi : (fderiv ℝ (joint Fs) (s,y) ∘L
      ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)).IsInvertible := by
    rw [joint_partial Fs hFs]
    apply isInvertible_of_defect (matrixCLM ((normalized cert).preconditioner.map fun q => (q : ℝ)))
    rw [← newton_fderiv _ Fs hFs]
    exact (fderiv_norm_le_of_enclosure Fs hFs (normalized cert).preconditioner
      (dyadicWeightedJacobian F I cert cfg) s y
      (dyadicJacobian_mem Fs hFs I (unitBox n) cfg hJ hs hy)).trans_lt (by exact_mod_cast hq)
  let g := hcd.implicitFunction (by simp) hi
  have hg : AnalyticAt ℝ g s := (hcd.contDiffAt_implicitFunction (by simp) hi).analyticAt
  have hg0 : g s=y := hcd.implicitFunction_apply_self (by simp) hi
  have hgz : ∀ᶠ t in 𝓝 s, system Fs t (g t)=0 := by
    simpa only [joint,hz',g] using hcd.eventually_apply_implicitFunction (by simp) hi
  refine ⟨fun t => chart cert.center cert.radius (g t),
    (chart_contDiff cert.center cert.radius).contDiffAt.analyticAt.comp hg,?_,?_⟩
  · change chart cert.center cert.radius (g s)=x
    rw [hg0]
    exact he
  · filter_upwards [hgz] with t ht
    rwa [scaledSystem_eval] at ht

end polyak.Numerics.Parametric
