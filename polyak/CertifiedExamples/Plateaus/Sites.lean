import polyak.CertifiedExamples.Plateaus.Root
import polyak.Certificates.PartII.Plateaus.Numerical
import polyak.General.Regions.SingleFeasible

/-! Literal source tunings and rational frequency sites of the two selected
Table 2 rows. The kappa coordinates are actual roots obtained by IVT. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels
open polyak.Certificates.PartII.Plateaus

def gridAtom {d : ℕ} (L : ℕ) (hL : 2*(d+2)<L) (i : Fin d) : Frequency :=
  ⟨General.Regions.rationalAngle (3+i.val) L,
    (General.Regions.rationalAngle_mem (by omega) (by omega)).1.le,
    (General.Regions.rationalAngle_mem (by omega) (by omega)).2.le⟩

theorem gridAtom_coe {d : ℕ} (L : ℕ) (hL : 2*(d+2)<L) (i : Fin d) :
    (gridAtom L hL i:ℝ)=2*Real.pi*((3+i.val:ℕ):ℝ)/L := rfl

theorem gridAtom_interior {d : ℕ} (L : ℕ) (hL : 2*(d+2)<L) (i : Fin d) :
    0<(gridAtom L hL i:ℝ) ∧ (gridAtom L hL i:ℝ)<Real.pi :=
  General.Regions.rationalAngle_mem (by omega) (by omega)

theorem gridAtom_grid {d : ℕ} (L : ℕ) (hL : 2*(d+2)<L) (i : Fin d) :
    gridAtom L hL i∈periodicGrid L := by
  refine ⟨(gridAtom_interior L hL i).1,(3+i.val:ℕ),?_⟩
  rw [gridAtom_coe]
  have hn : (L:ℝ)≠0 := by exact_mod_cast (show L≠0 by omega)
  push_cast
  field_simp

theorem gridAtom_injective {d : ℕ} (L : ℕ) (hL : 2*(d+2)<L) :
    Function.Injective (gridAtom (d:=d) L hL) := by
  intro i j hij
  have hh:=congrArg (fun w:Frequency=>(w:ℝ)*(L:ℝ)) hij
  simp only [gridAtom_coe] at hh
  have hLne : (L:ℝ)≠0 := by exact_mod_cast (show L≠0 by omega)
  rw [div_mul_cancel₀ _ hLne,div_mul_cancel₀ _ hLne] at hh
  have hp : (2*Real.pi:ℝ)≠0 := by positivity
  have he := mul_left_cancel₀ hp hh
  have he' : 3+i.val=3+j.val := by exact_mod_cast he
  exact Fin.ext (by omega)

def atoms18 : Fin 2 → Frequency := gridAtom 18 (by norm_num)
def atoms21 : Fin 3 → Frequency := gridAtom 21 (by norm_num)

def tuning18 : Tuning where
  kappa := Classical.choose row18_boundary_root
  y := 2201327/1000000
  beta := 1567/2500
  kappa_gt_one := by
    have h := (Classical.choose_spec row18_boundary_root).1.1
    norm_num at h ⊢
    linarith
  beta_nonneg := by norm_num
  beta_lt_one := by norm_num
  y_pos := by norm_num
  y_lt := by norm_num

def tuning21 : Tuning where
  kappa := Classical.choose row21_boundary_root
  y := 89631/40000
  beta := 769/1250
  kappa_gt_one := by
    have h := (Classical.choose_spec row21_boundary_root).1.1
    norm_num at h ⊢
    linarith
  beta_nonneg := by norm_num
  beta_lt_one := by norm_num
  y_pos := by norm_num
  y_lt := by norm_num

theorem tuning18_root : determinant18 tuning18.kappa=0 :=
  (Classical.choose_spec row18_boundary_root).2

theorem tuning21_root : determinant21 tuning21.kappa=0 :=
  (Classical.choose_spec row21_boundary_root).2

theorem tuning18_kappa_mem : tuning18.kappa∈row18Kappa := by
  have h:=(Classical.choose_spec row18_boundary_root).1
  norm_num [LeanCert.Core.IntervalRat.mem_def,row18Kappa,tuning18,Set.mem_Icc] at h ⊢
  exact h

theorem tuning21_kappa_mem : tuning21.kappa∈row21Kappa := by
  have h:=(Classical.choose_spec row21_boundary_root).1
  norm_num [LeanCert.Core.IntervalRat.mem_def,row21Kappa,tuning21,Set.mem_Icc] at h ⊢
  exact h

end polyak.CertifiedExamples.Plateaus
