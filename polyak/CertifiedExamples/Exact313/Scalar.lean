import polyak.Certificates.PartII.Exact313.Root

/-! A genuine isolated real solution of the independently defined source.
Existence and local uniqueness follow from the kernel-checked Newton contraction. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open LeanCert.Core LeanCert.Engine Numerics.Parametric
namespace Proposal
abbrev certificate := polyak.Certificates.PartII.Exact313.certificate
abbrev piBox := polyak.Certificates.PartII.Exact313.piBox
abbrev config := polyak.Certificates.PartII.Exact313.config
abbrev accepted := polyak.Certificates.PartII.Exact313.accepted
end Proposal

def rootBox : IntervalRat := coordinateBox Proposal.certificate.center Proposal.certificate.radius 0

theorem pi_mem : Real.pi∈Proposal.piBox := by
  constructor
  · convert Real.pi_gt_d20.le using 1
    norm_num [Proposal.piBox,polyak.Certificates.PartII.Exact313.piBox]
  · convert Real.pi_lt_d20.le using 1
    norm_num [Proposal.piBox,polyak.Certificates.PartII.Exact313.piBox]

structure IsolatedCompatibilityRoot where
  value : ℝ
  mem : value∈rootBox
  zero : compatibility value=0
  unique : ∀ r ∈ rootBox, compatibility r = 0 → r = value

theorem isolatedCompatibilityRoot_exists : Nonempty IsolatedCompatibilityRoot := by
  obtain ⟨x,hx,huniq⟩ := checkDyadic_sound Code.equations Proposal.piBox
    Proposal.certificate Proposal.config Proposal.accepted Real.pi pi_mem
  have he : x=![x 0] := by ext i;fin_cases i;rfl
  have hz : compatibility (x 0)=0 := by
    have h := congrFun hx.2 0
    rw [he,Code.eval_compatibility] at h
    simpa using h
  refine ⟨⟨x 0,hx.1 0,hz,?_⟩⟩
  intro r hr hzero
  have hb : FinBoxMem ![r] (coordinateBox Proposal.certificate.center Proposal.certificate.radius) := by
    intro i
    fin_cases i
    exact hr
  have hs : system Code.equations Real.pi ![r]=0 := by
    ext i
    fin_cases i
    change system Code.equations Real.pi ![r] 0=0
    rwa [Code.eval_compatibility]
  exact congrFun (huniq ![r] ⟨hb,hs⟩) 0

def scalarRoot : IsolatedCompatibilityRoot := Classical.choice isolatedCompatibilityRoot_exists

theorem scalarRoot_positive : 0<scalarRoot.value := by
  have h := scalarRoot.mem.1
  norm_num [rootBox,coordinateBox,Proposal.certificate,
    polyak.Certificates.PartII.Exact313.certificate,IntervalRat.add,
    IntervalRat.singleton,symmetricInterval] at h
  linarith

theorem scalarRoot_G : ModeLocking.TwoLag.G 4 scalarRoot.value c₁ c₂=0 :=
  (compatibility_eq_zero_iff scalarRoot_positive.le).mp scalarRoot.zero

end polyak.CertifiedExamples.Exact313
