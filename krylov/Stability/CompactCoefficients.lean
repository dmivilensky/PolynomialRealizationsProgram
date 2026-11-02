import krylov.Stability.CompactTaylor
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
Article: main_krylov, lem:U(b), regularity and compact-uniform variation of Taylor coefficients.
Use: coefficients are the genuine iterated Fréchet derivatives; lower degrees
have a linear base-change modulus and the top degree has a uniform continuity modulus.
Source: mathlib's iterated derivative regularity, mean-value theorem and Heine--Cantor theorem.
-/

namespace krylov.Stability
noncomputable section
open Set Metric
open scoped Topology
variable {Z F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual homogeneous Taylor coefficient as a continuous multilinear map.
Use: its base variation controls every degree-k perturbation polynomial at once.
Article: main_krylov, lem:U(b), P_k and its reference coefficients. -/
def taylorCoefficient (f : Z → F) (k : ℕ) (x : Z) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => Z) F :=
  (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x

/-- A genuine degree-k Taylor coefficient of a C^r map is C^(r−k) in the base point.
Use: discharge the coefficient-regularity statement directly from the actual cycle map.
Article: main_krylov, lem:U(b), coefficient base regularity.
Proof: apply the iterated Fréchet derivative regularity theorem and constant scalar multiplication. -/
theorem taylorCoefficient_contDiffAt (f : Z → F) (r k : ℕ) (x : Z)
    (hf : ContDiffAt ℝ r f x) (hk : k≤r) :
    ContDiffAt ℝ (r-k : ℕ) (taylorCoefficient f k) x := by
  have hd : ContDiffAt ℝ (r-k : ℕ) (iteratedFDeriv ℝ k f) x :=
    hf.iteratedFDeriv_right (by exact_mod_cast (Nat.sub_add_cancel hk).le)
  exact hd.const_smul (k.factorial : ℝ)⁻¹

/-- Genuine coefficient continuity holds throughout the actual smooth open domain, including the top degree.
Use: obtain a compact-uniform continuity modulus for P_r.
Article: main_krylov, lem:U(b), top-degree continuity.
Proof: each actual iterated derivative is continuous at every interior smooth point. -/
theorem taylorCoefficient_continuousOn (f : Z → F) (r k : ℕ) (U : Set Z)
    (hU : IsOpen U) (hf : ContDiffOn ℝ r f U) (hk : k≤r) :
    ContinuousOn (taylorCoefficient f k) U := by
  intro x hx
  exact ((hf.contDiffAt (hU.mem_nhds hx)).continuousAt_iteratedFDeriv
    (by exact_mod_cast hk)).const_smul (k.factorial : ℝ)⁻¹ |>.continuousWithinAt

variable [ProperSpace Z]

/-- A genuine C¹ map has a uniform local Lipschitz bound near every compact subset of its smooth domain.
Use: lower-degree Taylor coefficients acquire the printed linear base-change modulus.
Article: main_krylov, lem:U(b), compact O(η) variation.
Proof: bound the true first derivative on a compact common tube and apply
the mean-value theorem on each actual short convex reference ball. -/
theorem compact_local_lipschitz (f : Z → F) (U K : Set Z) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K⊆U) (hf : ContDiffOn ℝ 1 f U) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ y : Z, ‖y-x‖≤δ → ‖f y-f x‖≤C*‖y-x‖ := by
  -- One genuine derivative bound controls all short reference balls, even when K itself is nonconvex.
  obtain ⟨δ,C,hδ,hC,hδU,hD⟩ := compact_derivative_tube f 1 U K hU hK hKU hf
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx y hy
  have ht (z : Z) (hz : z∈closedBall x δ) : z∈cthickening δ K :=
    mem_cthickening_of_dist_le z x δ K hx hz
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hf.contDiffAt (hU.mem_nhds (hδU (ht z hz)))).differentiableAt (by simp))
    (fun z hz => by simpa only [norm_iteratedFDeriv_one] using hD 1 le_rfl z (ht z hz))
    (convex_closedBall x δ) (mem_closedBall_self hδ.le) (by simpa only [mem_closedBall, dist_eq_norm] using hy)

/-- Every genuine Taylor coefficient below the top degree has a compact-uniform linear base-change estimate.
Use: the constant belongs to the actual coefficient function and the actual compact reference set.
Article: main_krylov, lem:U(b), k<r.
Proof: the actual degree-k coefficient has one continuous derivative when
k<r; apply the proved compact common-neighborhood Lipschitz theorem. -/
theorem compact_taylorCoefficient_lipschitz (f : Z → F) (r k : ℕ) (U K : Set Z)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K⊆U) (hf : ContDiffOn ℝ r f U) (hk : k<r) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ y : Z, ‖y-x‖≤δ →
      ‖taylorCoefficient f k y-taylorCoefficient f k x‖≤C*‖y-x‖ := by
  apply compact_local_lipschitz _ U K hU hK hKU
  intro x hx
  exact ((taylorCoefficient_contDiffAt f r k x (hf.contDiffAt (hU.mem_nhds hx)) hk.le).of_le
    (by exact_mod_cast (show 1≤r-k by omega))).contDiffWithinAt

omit [ProperSpace Z] in
/-- The genuine top-degree Taylor coefficient has a uniform base-change modulus on compact reference sets.
Use: this is the printed o_K(1) coefficient variation at degree r under C^r regularity.
Article: main_krylov, lem:U(b), k=r.
Proof: the actual top derivative is continuous on the smooth open domain;
Heine--Cantor makes that actual coefficient function uniformly continuous on K. -/
theorem compact_taylorCoefficient_uniform (f : Z → F) (r : ℕ) (U K : Set Z)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K⊆U) (hf : ContDiffOn ℝ r f U) :
    ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ x∈K, ∀ y∈K, ‖y-x‖<δ →
      ‖taylorCoefficient f r y-taylorCoefficient f r x‖<ε := by
  -- Uniform continuity concerns the genuine top derivative on the actual compact reference set.
  have hu := hK.uniformContinuousOn_of_continuous
    ((taylorCoefficient_continuousOn f r r U hU hf le_rfl).mono hKU)
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy hxy
  simpa only [dist_eq_norm] using hbound y hy x hx (by simpa only [dist_eq_norm] using hxy)

omit [ProperSpace Z] in
/-- Genuine local Lipschitz continuity of the top derivative gives the printed compact-uniform linear top-coefficient variation.
Use: this is the source's stronger C^(r,1) specialization, stated through its actual top Fréchet derivative.
Article: main_krylov, lem:U(b), C^(r,1) top-degree estimate.
Proof: compactness upgrades the actual locally Lipschitz derivative to a
Lipschitz bound on K; multiplying by its fixed reciprocal factorial gives the coefficient bound. -/
theorem compact_topCoefficient_lipschitz (f : Z → F) (r : ℕ) (U K : Set Z)
    (hK : IsCompact K) (hKU : K⊆U) (hl : LocallyLipschitzOn U (iteratedFDeriv ℝ r f)) :
    ∃ C : ℝ, 0≤C ∧ ∀ x∈K, ∀ y∈K,
      ‖taylorCoefficient f r y-taylorCoefficient f r x‖≤C*‖y-x‖ := by
  -- The local Lipschitz assumption is on the genuine top derivative, not on an assumed Taylor remainder.
  obtain ⟨C,hC⟩ := (hl.mono hKU).exists_lipschitzOnWith_of_compact hK
  refine ⟨(r.factorial : ℝ)⁻¹*C,mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) C.coe_nonneg,?_⟩
  intro x hx y hy
  have ht := hC.dist_le_mul y hy x hx
  rw [taylorCoefficient, taylorCoefficient, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  simpa only [dist_eq_norm, mul_assoc] using
    mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr (Nat.cast_nonneg r.factorial))

omit [ProperSpace Z] in
/-- A genuine coefficient base-change norm controls every actual homogeneous perturbation polynomial with the same degree.
Use: turn the compact coefficient moduli into the source's ‖Θ‖^k polynomial variation estimates.
Article: main_krylov, lem:U(b), variation of P_k.
Proof: apply the genuine continuous multilinear operator norm to k copies of the actual perturbation. -/
theorem taylorCoefficient_action_variation (f : Z → F) (k : ℕ) (x y h : Z) {ε : ℝ}
    (he : ‖taylorCoefficient f k y-taylorCoefficient f k x‖≤ε) :
    ‖taylorCoefficient f k y (fun _ => h)-taylorCoefficient f k x (fun _ => h)‖≤ε*‖h‖^k := by
  have ht := (taylorCoefficient f k y-taylorCoefficient f k x).le_opNorm (fun _ => h)
  simp only [_root_.sub_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at ht
  exact ht.trans (mul_le_mul_of_nonneg_right he (pow_nonneg (norm_nonneg _) _))

end
end krylov.Stability
