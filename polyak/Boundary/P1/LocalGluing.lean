import polyak.Boundary.P1.CoreUnique
import polyak.Boundary.P1.LocalImplicit

/-! Algebraic contact uniqueness glues all local analytic P1 source extensions. -/
noncomputable section
namespace polyak.Boundary.P1
open Filter
open scoped Topology

theorem criticalPoint_admissible : ContactAdmissible (0,criticalPoint) := by
  norm_num [ContactAdmissible,criticalPoint,branchU,branchAtom,residualLinear,residualConstant]

theorem coreRoot_admissible {z : ℝ} {Z : Coordinates} (hz : 0≤z) (hz1 : z≤3/4)
    (hZ : regularSystem (z,Z)=0) (h : CoreBounds z Z) : ContactAdmissible (z,Z) := by
  by_cases hz0 : z=0
  · subst z
    rw [criticalPoint_unique Z hZ]
    exact criticalPoint_admissible
  · exact h.admissible (lt_of_le_of_ne hz (Ne.symm hz0)) hz1 hZ

/-- Every analytic implicit extension agrees with every admissible source selection nearby.
No endpoint interval inclusion or continuity of the selection is assumed. -/
theorem local_extension_unique {S : Set ℝ} {f g : ℝ → Coordinates} {s : ℝ}
    (hS : ∀ r∈S, 0≤r ∧ r≤3/4)
    (hf : ∀ r∈S, regularSystem (r,f r)=0)
    (ha : ∀ r∈S, ContactAdmissible (r,f r)) (hs : s∈S)
    (hg : AnalyticAt ℝ g s) (hself : g s=f s)
    (heq : ∀ᶠ r in 𝓝 s, regularSystem (r,g r)=0) :
    ∀ᶠ r in 𝓝 s, r∈S → f r=g r := by
  have had : ContactAdmissible (s,g s) := by rw [hself]; exact ha s hs
  have hc : ContinuousAt (fun r => (r,g r)) s := continuousAt_id.prodMk hg.continuousAt
  have hnear : ∀ᶠ r in 𝓝 s, ContactAdmissible (r,g r) :=
    hc (contactAdmissible_open.mem_nhds had)
  filter_upwards [heq,hnear] with r hr har
  intro hrS
  exact admissibleRoot_unique (hS r hrS).1 (hS r hrS).2 (hf r hrS) hr (ha r hrS) har

/-- At the compactified endpoint this identifies the checked branch with the actual local IFT branch. -/
theorem eq_localBranch_eventually {f : ℝ → Coordinates} {S : Set ℝ}
    (hS : ∀ r∈S, 0≤r ∧ r≤3/4)
    (hf : ∀ r∈S, regularSystem (r,f r)=0)
    (ha : ∀ r∈S, ContactAdmissible (r,f r)) (h0 : 0∈S) :
    ∀ᶠ r in 𝓝 (0 : ℝ), r∈S → f r=localBranch r := by
  apply local_extension_unique hS hf ha h0 localBranch_analyticAt
  · exact localBranch_zero.trans (criticalPoint_unique (f 0) (hf 0 h0)).symm
  · exact localBranch_equations

end polyak.Boundary.P1
