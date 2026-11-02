import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-!
Article: main_krylov, thm:Ip, stored versus probe-augmented independence.
Use: compute exactly the loss of oldest-column distance after adding the
genuine new probe direction. Source: actual orthogonal projections and
Pythagoras, including an arbitrary nonorthogonal stored subspace.
-/
namespace krylov.LinearAlgebra
noncomputable section
open Submodule
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Adding a unit direction orthogonal to the old subspace adds exactly
its actual scalar orthogonal projection.
Article: main_krylov, thm:Ip, RFC distance identity. -/
theorem starProjection_sup_unit (V : Submodule ℝ E) (delta x : E)
    (hd : delta∈Vᗮ) (hn : ‖delta‖=1) :
    (V⊔ℝ ∙ delta).starProjection x=V.starProjection x+
      (inner ℝ delta (x-V.starProjection x)) • delta := by
  let r := x-V.starProjection x
  let c := inner ℝ delta r
  have hr : r∈Vᗮ := V.sub_starProjection_mem_orthogonal x
  have hq : V.starProjection x+c • delta∈V⊔ℝ ∙ delta :=
    (V⊔ℝ ∙ delta).add_mem ((show V≤V⊔ℝ ∙ delta from le_sup_left) (V.starProjection_apply_mem x))
      ((V⊔ℝ ∙ delta).smul_mem c ((show ℝ ∙ delta≤V⊔ℝ ∙ delta from le_sup_right) (mem_span_singleton_self delta)))
  have hrV : r-c • delta∈Vᗮ := Vᗮ.sub_mem hr (Vᗮ.smul_mem c hd)
  have hrD : r-c • delta∈(ℝ ∙ delta)ᗮ := by
    rw [mem_orthogonal_singleton_iff_inner_right,inner_sub_right,real_inner_smul_right,
      real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
    exact sub_self c
  apply (V⊔ℝ ∙ delta).eq_starProjection_of_mem_orthogonal hq
  rw [←inf_orthogonal,mem_inf]
  have he : x-(V.starProjection x+c • delta)=r-c • delta := by dsimp only [r];module
  rw [he]
  exact ⟨hrV,hrD⟩

/-- Exact squared distance identity for the actual augmented subspace,
with no independence or convergence certificate.
Article: main_krylov, thm:Ip, RFC projected oldest column. -/
theorem starProjection_sup_unit_distance (V : Submodule ℝ E) (delta x : E)
    (hd : delta∈Vᗮ) (hn : ‖delta‖=1) :
    ‖x-(V⊔ℝ ∙ delta).starProjection x‖^2=
      ‖x-V.starProjection x‖^2-(inner ℝ (x-V.starProjection x) delta)^2 := by
  rw [starProjection_sup_unit V delta x hd hn]
  have he : x-(V.starProjection x+(inner ℝ delta (x-V.starProjection x)) • delta)=
      (x-V.starProjection x)-(inner ℝ delta (x-V.starProjection x)) • delta := by module
  rw [he,norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,hn,
    one_pow,mul_one,sq_abs]
  have hc : inner ℝ delta (x-V.starProjection x)=inner ℝ (x-V.starProjection x) delta := real_inner_comm _ _
  rw [hc]
  ring

/-- Projecting the new direction off the stored subspace and normalizing
it leaves the actual augmented span unchanged.
Article: main_krylov, thm:Ip. -/
theorem sup_span_projected_normalized (V : Submodule ℝ E) (d : E)
    (ht : d-V.starProjection d≠0) :
    V⊔ℝ ∙ ((‖d-V.starProjection d‖⁻¹ : ℝ) • (d-V.starProjection d))=V⊔ℝ ∙ d := by
  let t := d-V.starProjection d
  let delta := (‖t‖⁻¹ : ℝ) • t
  have hdelta : delta∈V⊔ℝ ∙ d := (V⊔ℝ ∙ d).smul_mem _
    ((V⊔ℝ ∙ d).sub_mem ((show ℝ ∙ d≤V⊔ℝ ∙ d from le_sup_right) (mem_span_singleton_self d))
      ((show V≤V⊔ℝ ∙ d from le_sup_left) (V.starProjection_apply_mem d)))
  have hdecomp : d=V.starProjection d+‖t‖ • delta := by
    simp only [delta,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr ht),one_smul,t,add_sub_cancel]
  apply le_antisymm
  · exact sup_le le_sup_left ((span_singleton_le_iff_mem _ _).mpr hdelta)
  · apply sup_le le_sup_left
    apply (span_singleton_le_iff_mem _ _).mpr
    have hm : V.starProjection d+‖t‖ • delta∈V⊔ℝ ∙ delta :=
      (V⊔ℝ ∙ delta).add_mem ((show V≤V⊔ℝ ∙ delta from le_sup_left) (V.starProjection_apply_mem d))
        ((V⊔ℝ ∙ delta).smul_mem _ ((show ℝ ∙ delta≤V⊔ℝ ∙ delta from le_sup_right) (mem_span_singleton_self delta)))
    exact (congrArg (fun z : E=>z∈V⊔ℝ ∙ delta) hdecomp).mpr hm

/-- The exact requested RFC identity: adding the real current direction
removes precisely its squared normalized residual pairing from the
oldest-column distance. Article: main_krylov, thm:Ip, refined RFC Delta. -/
theorem starProjection_augmented_distance (V : Submodule ℝ E) (d x : E)
    (ht : d-V.starProjection d≠0) :
    let delta := (‖d-V.starProjection d‖⁻¹ : ℝ) • (d-V.starProjection d)
    ‖x-(V⊔ℝ ∙ d).starProjection x‖^2=
      ‖x-V.starProjection x‖^2-(inner ℝ (x-V.starProjection x) delta)^2 := by
  let delta := (‖d-V.starProjection d‖⁻¹ : ℝ) • (d-V.starProjection d)
  have hd : delta∈Vᗮ := Vᗮ.smul_mem _ (V.sub_starProjection_mem_orthogonal d)
  have hn : ‖delta‖=1 := norm_smul_inv_norm ht
  have hh := starProjection_sup_unit_distance V delta x hd hn
  have hproj := congrArg (fun W : Submodule ℝ E=>W.starProjection x)
    (sup_span_projected_normalized V d ht)
  rw [hproj] at hh
  exact hh

end
end krylov.LinearAlgebra
