import polyak.CertifiedExamples.Plateaus.Sites
import polyak.Levels.Geometry.Windows

/-! Literal anchor fractions and uniqueness of the support point in the fourth window. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels

theorem row18_only_window_atom : ∀ω∈Set.range atoms18,Geometry.InWindow 4 ω→ω=atoms18 1 := by
  rintro ω ⟨i,rfl⟩ hi
  fin_cases i
  · have h:=hi.1
    norm_num [Geometry.InWindow,atoms18,gridAtom,General.Regions.rationalAngle] at h
    linarith [Real.pi_pos]
  · rfl

theorem row21_only_window_atom : ∀ω∈Set.range atoms21,Geometry.InWindow 4 ω→ω=atoms21 2 := by
  rintro ω ⟨i,rfl⟩ hi
  fin_cases i
  · have h:=hi.1
    norm_num [Geometry.InWindow,atoms21,gridAtom,General.Regions.rationalAngle] at h
    linarith [Real.pi_pos]
  · have h:=hi.1
    norm_num [Geometry.InWindow,atoms21,gridAtom,General.Regions.rationalAngle] at h
    linarith [Real.pi_pos]
  · rfl

theorem row18_anchor_fraction : (atoms18 1:ℝ)=2*Real.pi*(2/9) := by
  norm_num [atoms18,gridAtom,General.Regions.rationalAngle]
  ring

theorem row21_anchor_fraction : (atoms21 2:ℝ)=2*Real.pi*(5/21) := by
  norm_num [atoms21,gridAtom,General.Regions.rationalAngle]
  ring

end polyak.CertifiedExamples.Plateaus
