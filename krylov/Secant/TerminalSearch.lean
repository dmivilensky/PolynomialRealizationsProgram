import krylov.Secant.TerminalPrefix
import krylov.Reference.CanonicalGradient

/-!
Article: main_krylov, lem:terminal-fibre, actual physical terminal search.
Use: identify the common actual physical probe, line length and canonical
post-search gradient through the genuine positive-root change of coordinates.
Source: symmetry/invertibility of the actual metric root and exact planar action.
-/

namespace krylov.Secant
noncomputable section
open Matrix krylov.LinearAlgebra krylov.Reference
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- The true canonical action of each actual physical terminal segment is its prescribed planar action.
Use: the terminal probe is an equality of the real physical oracle observations.
Article: main_krylov, lem:terminal-fibre, canonical last probe.
Proof: cancel the actual inverse root against the left physical congruence factor. -/
theorem physicalTerminal_canonical_action (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (e h d : EuclideanSpace ℝ (Fin n)) (x y z : ℕ → ℝ) (N k : ℕ) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (physicalTerminalSegments base e h x y z N k) d)=
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (terminalSegments e h x y z N k)
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) d) := by
  rw [← mul_apply_eq_comp, ← map_mul]
  simp only [physicalTerminalSegments, ← Matrix.mul_assoc,
    nonsing_inv_mul _ (metricRoot_det_unit base hbase), Matrix.one_mul]
  rw [map_mul, mul_apply_eq_comp]

/-- The actual physical operator queried on the normalized terminal reference direction has the common printed probe.
Use: hidden diagonal allocations cannot affect the final physical line-search observation.
Article: main_krylov, lem:terminal-fibre, A_(n−1)A^(−1/2)h=A^(1/2)(h+xe).
Proof: the two adjacent actual metric factors cancel, and the actual planar
terminal probe is the already proved h+xe. -/
theorem physicalTerminal_normalized_last_probe (base : Matrix (Fin n) (Fin n) ℝ)
    (hbase : base.PosDef) (e h : EuclideanSpace ℝ (Fin n)) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (x y z : ℕ → ℝ) (N : ℕ) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (physicalTerminalSegments base e h x y z N N)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ h)=
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)
          (h+(∑ l ∈ Finset.range N, x l) • e) := by
  simp only [physicalTerminalSegments, map_mul, mul_apply_eq_comp]
  have he : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ h)=h := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_nonsing_inv _ (metricRoot_det_unit base hbase),
      map_one, one_apply_eq_self]
  rw [he, terminalSegments_last_probe e h hh heh]

/-- The actual physical terminal search has its true common line length and the printed exact canonical residual.
Use: arbitrary allowed direction scales are retained through the actual physical oracle calculation.
Article: main_krylov, lem:terminal-fibre, reference last line and ρ=x√c e.
Proof: genuine primal/dual pairing invariance gives the line length a/t;
the actual final planar probe and true gradient update cancel the h component. -/
theorem physical_terminal_search (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (e h g d : EuclideanSpace ℝ (Fin n)) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (x y z : ℕ → ℝ) (N : ℕ) (a t : ℝ) (ht : t≠0)
    (hg : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ g=-a • h)
    (hd : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) d=t • h) :
    let Z := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (physicalTerminalSegments base e h x y z N N) d
    (lineLength g d Z=lineLength g d (cgOperator base d)) ∧
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ (searchedGradient g d Z)=
      ((∑ l ∈ Finset.range N, x l)*a) • e) := by
  dsimp only
  let Z := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (physicalTerminalSegments base e h x y z N N) d
  have hhe : inner ℝ h e=0 := (real_inner_comm e h).trans heh
  have hz : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ Z=
      t • (h+(∑ l ∈ Finset.range N, x l) • e) := by
    rw [physicalTerminal_canonical_action base hbase, hd, map_smul,
      terminalSegments_last_probe e h hh heh]
  have hl : lineLength g d Z=a/t := by
    rw [lineLength, canonical_search_pairing base hbase d g, canonical_search_pairing base hbase d Z,
      hg, hd, hz]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_right, hhe,
      real_inner_self_eq_norm_sq, hh, one_pow, mul_one, mul_zero, add_zero]
    field_simp
  have href : lineLength g d (cgOperator base d)=a/t := by
    rw [lineLength, canonical_search_pairing base hbase d g,
      canonical_search_pairing base hbase d (cgOperator base d), canonical_reference_action base hbase,
      hg, hd]
    simp only [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hh, one_pow, mul_one]
    simp only [norm_smul, Real.norm_eq_abs, sq_abs, hh, mul_one]
    field_simp
  refine ⟨hl.trans href.symm, ?_⟩
  -- The genuine physical update is transported linearly only after its true scalar has been identified.
  change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ (searchedGradient g d Z)=_
  rw [searchedGradient, map_add, map_smul, hg, hz, hl, smul_smul, div_mul_cancel₀ _ ht, smul_add, smul_smul]
  module

end
end krylov.Secant
