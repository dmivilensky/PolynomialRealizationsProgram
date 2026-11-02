import krylov.Tensor.HarmonicReferenceOperators

/-!
Article: main_krylov, thm:H, exact endpoint harmonic response geometry.
Use: multiply the actual first/last harmonic increments on the genuine CG
flags. The fresh vector and latest-model response are derived from their
original finite sums, rather than supplied as response fields.
Source: true unit CG projections and direct rank-two matrix evaluation.
-/

namespace krylov.Tensor
noncomputable section
open Matrix Finset krylov.Functions krylov.Reference krylov.Variation krylov.LinearAlgebra
  krylov.Correction krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The two actual nonzero harmonic increment slots of the finite reference.
Article: main_krylov, thm:H. -/
def harmonicEndpointIncrement (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (a : ℝ) (l : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (if l=0 then referenceHarmonicFirstMatrix A hA g a else 0) +
    (if l+2=referenceAtomCount A hA g then referenceHarmonicLastMatrix A hA g a else 0)

/-- The genuine newest direction is annihilated by every actual preterminal
CG old projection. Article: main_krylov, thm:H. -/
theorem harmonic_last_projection_zero (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 1 ≤ referenceAtomCount A hA g)
    (l : ℕ) (hl : l < referenceAtomCount A hA g-1) :
    (oldFlag A g l).starProjection
      (canonicalCGUnitStep A g (referenceAtomCount A hA g-1)) = 0 := by
  change ((oldFlag A g l).orthogonalProjectionOnto _ : EuclideanSpace ℝ (Fin n))=0
  rw [(oldFlag A g l).orthogonalProjectionOnto_eq_zero_iff.mpr
    (unitStep_prefix_oldFlag_orthogonal A hA g le_rfl (by omega) hl)]
  rfl

/-- The real fresh defect of the actual endpoint harmonic increments is the
printed first-direction coefficient. Article: main_krylov, thm:H. -/
theorem harmonicEndpoint_fresh (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 3 ≤ referenceAtomCount A hA g) (a : ℝ) :
    freshDefect A g (harmonicEndpointIncrement A hA g a) (referenceAtomCount A hA g) =
      ((a*‖canonicalCGStep A g 0‖-a*‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖)/Real.sqrt 2) •
        canonicalCGUnitStep A g 0 := by
  let N := referenceAtomCount A hA g
  let e := canonicalCGUnitStep A g 0
  let h := canonicalCGUnitStep A g (N-1)
  let p := a*‖canonicalCGStep A g 0‖/Real.sqrt 2
  let q := a*‖canonicalCGStep A g (N-1)‖/Real.sqrt 2
  let i0 : Fin N := ⟨0,by omega⟩
  let il : Fin N := ⟨N-1,by omega⟩
  have hframe := canonicalCG_frame A hA g
  have he := hframe.norm_eq_one i0
  have hh := hframe.norm_eq_one il
  have heh := hframe.inner_eq_zero (show i0 ≠ il by intro hz; have := congrArg Fin.val hz; dsimp only [i0,il] at this; omega)
  change inner ℝ e h=0 at heh
  have hhh : inner ℝ h h=1 := by rw [real_inner_self_eq_norm_sq,hh,one_pow]
  have hPe (l : ℕ) : (oldFlag A g l).starProjection e=e :=
    Submodule.starProjection_eq_self_iff.mpr (unitStep_mem_oldFlag A g (Nat.zero_le l))
  have hPh (l : ℕ) (hl : l∈range (N-1)) : (oldFlag A g l).starProjection h=0 :=
    harmonic_last_projection_zero A hA g (by omega) l (mem_range.mp hl)
  have hP : cgOperator (referenceHarmonicFirstMatrix A hA g a) h = p • e + (-p) • h := by
    rw [show cgOperator (referenceHarmonicFirstMatrix A hA g a) h =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (planarMatrix e h p p (-p)) h from rfl,
      planarMatrix_action]
    simp only [heh,hhh,mul_zero,mul_one,zero_add]
  have hQ : cgOperator (referenceHarmonicLastMatrix A hA g a) h = (-q) • e + (-q) • h := by
    rw [show cgOperator (referenceHarmonicLastMatrix A hA g a) h =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (planarMatrix e h q (-q) (-q)) h from rfl,
      planarMatrix_action]
    simp only [heh,hhh,mul_zero,mul_one,zero_add]
  have hadd (X Y : Matrix (Fin n) (Fin n) ℝ) : cgOperator (X+Y) h=cgOperator X h+cgOperator Y h := by
    simp only [cgOperator,map_add,_root_.add_apply]
  have hzero : cgOperator (0 : Matrix (Fin n) (Fin n) ℝ) h=0 := by simp only [cgOperator,map_zero,_root_.zero_apply]
  have ht (l : ℕ) (hl : l∈range (N-1)) :
      (oldFlag A g l).starProjection
        (cgOperator (harmonicEndpointIncrement A hA g a l) h) =
          (if l=0 then p • e else 0)+(if l=N-2 then (-q) • e else 0) := by
    have hlast : l+2=N ↔ l=N-2 := by have := mem_range.mp hl; omega
    unfold harmonicEndpointIncrement
    change (oldFlag A g l).starProjection (cgOperator
      ((if l=0 then referenceHarmonicFirstMatrix A hA g a else 0)+
        (if l+2=N then referenceHarmonicLastMatrix A hA g a else 0)) h)=_
    rw [hadd,map_add]
    simp only [hlast]
    split_ifs <;>
      simp only [hzero,map_zero,hP,hQ,
        map_add,map_smul,hPe,hPh l hl,smul_zero,add_zero,zero_add]
  unfold freshDefect
  change (∑ l∈range (N-1), (oldFlag A g l).starProjection
    (cgOperator (harmonicEndpointIncrement A hA g a l) h))=_
  rw [sum_congr rfl ht,sum_add_distrib]
  simp only [sum_ite_eq',mem_range,show 0<N-1 by omega,show N-2<N-1 by omega,ite_true]
  change p • e+(-q) • e=_
  rw [← add_smul]
  congr 1
  dsimp only [p,q]
  ring

/-- The actual latest-information staircase acts on the true first reference
direction by precisely the printed planar block. Article: main_krylov, thm:H. -/
theorem harmonicEndpoint_staircase_first (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 3 ≤ referenceAtomCount A hA g) (a : ℝ) :
    let e := canonicalCGUnitStep A g 0
    let h := canonicalCGUnitStep A g (referenceAtomCount A hA g-1)
    let p := a*‖canonicalCGStep A g 0‖/Real.sqrt 2
    let q := a*‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖/Real.sqrt 2
    staircaseOperator A g (harmonicEndpointIncrement A hA g a)
      (referenceHarmonicLastMatrix A hA g a) (referenceAtomCount A hA g) e =
        (p+2*q) • e+(-q) • h := by
  dsimp only
  let N := referenceAtomCount A hA g
  let e := canonicalCGUnitStep A g 0
  let h := canonicalCGUnitStep A g (N-1)
  let p := a*‖canonicalCGStep A g 0‖/Real.sqrt 2
  let q := a*‖canonicalCGStep A g (N-1)‖/Real.sqrt 2
  let i0 : Fin N := ⟨0,by omega⟩
  let il : Fin N := ⟨N-1,by omega⟩
  have hframe := canonicalCG_frame A hA g
  have he := hframe.norm_eq_one i0
  have hh := hframe.norm_eq_one il
  have heh := hframe.inner_eq_zero (show i0 ≠ il by intro hz; have := congrArg Fin.val hz; dsimp only [i0,il] at this; omega)
  change inner ℝ e h=0 at heh
  have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he,one_pow]
  have hhe : inner ℝ h e=0 := by rw [real_inner_comm]; exact heh
  have hPe (l : ℕ) : (oldFlag A g l).starProjection e=e :=
    Submodule.starProjection_eq_self_iff.mpr (unitStep_mem_oldFlag A g (Nat.zero_le l))
  have hPh (l : ℕ) (hl : l∈range (N-1)) : (oldFlag A g l).starProjection h=0 :=
    harmonic_last_projection_zero A hA g (by omega) l (mem_range.mp hl)
  have hP : cgOperator (referenceHarmonicFirstMatrix A hA g a) e = p • e+p • h := by
    rw [show cgOperator (referenceHarmonicFirstMatrix A hA g a) e =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (planarMatrix e h p p (-p)) e from rfl,
      planarMatrix_action]
    simp only [hee,hhe,mul_zero,mul_one,add_zero]
  have hQ : cgOperator (referenceHarmonicLastMatrix A hA g a) e = q • e+(-q) • h := by
    rw [show cgOperator (referenceHarmonicLastMatrix A hA g a) e =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (planarMatrix e h q (-q) (-q)) e from rfl,
      planarMatrix_action]
    simp only [hee,hhe,mul_zero,mul_one,add_zero]
  have hadd (X Y : Matrix (Fin n) (Fin n) ℝ) : cgOperator (X+Y) e=cgOperator X e+cgOperator Y e := by
    simp only [cgOperator,map_add,_root_.add_apply]
  have hzero : cgOperator (0 : Matrix (Fin n) (Fin n) ℝ) e=0 := by simp only [cgOperator,map_zero,_root_.zero_apply]
  have ht (l : ℕ) (hl : l∈range (N-1)) :
      (oldFlag A g l).starProjection (cgOperator (harmonicEndpointIncrement A hA g a l)
        ((oldFlag A g l).starProjection e)) =
          (if l=0 then p • e else 0)+(if l=N-2 then q • e else 0) := by
    rw [hPe]
    have hlast : l+2=N ↔ l=N-2 := by have := mem_range.mp hl; omega
    unfold harmonicEndpointIncrement
    change (oldFlag A g l).starProjection (cgOperator
      ((if l=0 then referenceHarmonicFirstMatrix A hA g a else 0)+
        (if l+2=N then referenceHarmonicLastMatrix A hA g a else 0)) e)=_
    rw [hadd,map_add]
    simp only [hlast]
    split_ifs <;>
      simp only [hzero,map_zero,hP,hQ,
        map_add,map_smul,hPe,hPh l hl,smul_zero,add_zero,zero_add]
  rw [staircaseOperator_apply]
  change (∑ l∈range (N-1), (oldFlag A g l).starProjection
    (cgOperator (harmonicEndpointIncrement A hA g a l) ((oldFlag A g l).starProjection e)))+
      cgOperator (referenceHarmonicLastMatrix A hA g a) e=(p+2*q) • e+(-q) • h
  rw [sum_congr rfl ht,sum_add_distrib,hQ]
  simp only [sum_ite_eq',mem_range,show 0<N-1 by omega,show N-2<N-1 by omega,ite_true]
  module

/-- The genuine harmonic endpoint product has exactly the article's leading
one-half planar vector before taking its norm. Article: main_krylov, thm:H. -/
theorem harmonicEndpoint_staircase_fresh (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 3 ≤ referenceAtomCount A hA g) (a : ℝ) :
    let e := canonicalCGUnitStep A g 0
    let h := canonicalCGUnitStep A g (referenceAtomCount A hA g-1)
    let p := a*‖canonicalCGStep A g 0‖/Real.sqrt 2
    let q := a*‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖/Real.sqrt 2
    staircaseOperator A g (harmonicEndpointIncrement A hA g a)
      (referenceHarmonicLastMatrix A hA g a) (referenceAtomCount A hA g)
      (freshDefect A g (harmonicEndpointIncrement A hA g a) (referenceAtomCount A hA g)) =
        (p-q) • ((p+2*q) • e+(-q) • h) := by
  dsimp only
  rw [harmonicEndpoint_fresh A hA g hN a,map_smul,harmonicEndpoint_staircase_first A hA g hN a]
  congr 1
  ring

/-- The true endpoint harmonic product has exactly its printed two-dimensional
Euclidean norm. Article: main_krylov, thm:H. -/
theorem harmonicEndpoint_product_norm (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 3 ≤ referenceAtomCount A hA g) (a : ℝ) :
    let p := a*‖canonicalCGStep A g 0‖/Real.sqrt 2
    let q := a*‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖/Real.sqrt 2
    ‖staircaseOperator A g (harmonicEndpointIncrement A hA g a)
      (referenceHarmonicLastMatrix A hA g a) (referenceAtomCount A hA g)
      (freshDefect A g (harmonicEndpointIncrement A hA g a) (referenceAtomCount A hA g))‖ =
        |p-q| * Real.sqrt ((p+2*q)^2+q^2) := by
  dsimp only
  rw [harmonicEndpoint_staircase_fresh A hA g hN a,norm_smul,Real.norm_eq_abs]
  congr 1
  let N := referenceAtomCount A hA g
  let i0 : Fin N := ⟨0,by omega⟩
  let il : Fin N := ⟨N-1,by omega⟩
  have hframe := canonicalCG_frame A hA g
  have he := hframe.norm_eq_one i0
  have hh := hframe.norm_eq_one il
  have heh := hframe.inner_eq_zero (show i0 ≠ il by intro hz; have := congrArg Fin.val hz; dsimp only [i0,il] at this; omega)
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [planar_coordinates_norm_sq _ _ he hh heh,Real.sq_sqrt (by positivity)]
  ring

end
end krylov.Tensor
