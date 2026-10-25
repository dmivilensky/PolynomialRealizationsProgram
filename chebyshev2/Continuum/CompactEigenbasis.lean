import chebyshev2.Continuum.HilbertSchmidt
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
Article: chebyshev2, Theorem 2.3.
A genuine Hilbert eigenbasis for a compact symmetric operator, obtained by joining bases of its
closed eigenspaces and using mathlib's spectral theorem.
Use: `chebyshev2.Continuum.exists_compact_eigenbasis` feeds
`chebyshev2.Continuum.compact_traceBound_has_summable_eigenbasis` (compact trace Bound has
summable eigenbasis).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Continuum
noncomputable section
open Module Module.End Set
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
A genuine Hilbert eigenbasis for a compact symmetric operator, obtained by joining bases of its
closed eigenspaces and using mathlib's spectral theorem.

Constructs witnesses with the exact properties `∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (eig :
ι → ℝ), ∀ i, T (b i) = eig i • b i`.

Use: `chebyshev2.Continuum.compact_traceBound_has_summable_eigenbasis` uses this identity
to construct witnesses satisfying `∃ (ι : Type u) (b : HilbertBasis ι
ℝ E) (eig : ι → ℝ), (∀ i, T (b i) = eig i • b i) ∧ Summable (fun i => |eig i|) ∧ (∑' i, |eig
i|) ≤ C`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Separate `i.1 = j.1` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem exists_compact_eigenbasis (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.IsSymmetric) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (eig : ι → ℝ), ∀ i, T (b i) = eig i • b i := by
  -- Separate `i.1 = j.1` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  classical
  have hb (μ : ℝ) := exists_hilbertBasis ℝ (eigenspace T.toLinearMap μ)
  choose w b _ using hb
  let ι := Σ μ : ℝ, w μ
  let v : ι → E := fun i => (b i.1 i.2 : E)
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases h : i.1 = j.1
    · obtain ⟨μ,i⟩ := i
      obtain ⟨ν,j⟩ := j
      dsimp at h
      subst ν
      have he : (Sigma.mk μ i : ι) = Sigma.mk μ j ↔ i = j := by
        constructor
        · intro h
          exact eq_of_heq (Sigma.mk.inj h).2
        · intro h
          exact congrArg (fun k : w μ => (⟨μ,k⟩ : ι)) h
      simpa only [v, Submodule.coe_inner, he] using
        (orthonormal_iff_ite.mp (b μ).orthonormal i j)
    · have hij : i ≠ j := fun he => h (congrArg Sigma.fst he)
      rw [ite_eq_right_iff.mpr (fun he => (hij he).elim)]
      exact hs.orthogonalFamily_eigenspaces h (b i.1 i.2) (b j.1 j.2)
  have hsp : (Submodule.span ℝ (range v))ᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro u hu
    have hu' : u ∈ (⨆ μ : ℝ, eigenspace T.toLinearMap μ)ᗮ := by
      rw [← Submodule.iInf_orthogonal]
      apply (Submodule.mem_iInf _).mpr
      intro μ z hz
      let L : eigenspace T.toLinearMap μ →L[ℝ] ℝ :=
        (innerSL ℝ u).comp (eigenspace T.toLinearMap μ).subtypeL
      have hi := L.hasSum ((b μ).hasSum_repr ⟨z,hz⟩)
      have he (i : w μ) : L (((b μ).repr ⟨z,hz⟩ i) • b μ i) = 0 := by
        have hh := hu (v ⟨μ,i⟩) (Submodule.subset_span ⟨⟨μ,i⟩,rfl⟩)
        change inner ℝ u (((b μ).repr ⟨z,hz⟩ i) • (b μ i : E)) = 0
        rw [real_inner_smul_right, real_inner_comm]
        simp only [v] at hh
        rw [hh, mul_zero]
      have hz' : inner ℝ u z = 0 := by
        have hzero : HasSum (fun _ : w μ => (0 : ℝ)) (L ⟨z,hz⟩) := by
          simpa only [he] using hi
        exact hzero.unique hasSum_zero
      exact (real_inner_comm _ _).trans hz'
    rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs] at hu'
    exact hu'
  let B := HilbertBasis.mkOfOrthogonalEqBot hv hsp
  refine ⟨ι, B, Sigma.fst, ?_⟩
  intro i
  have he : B i = v i := congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot hv hsp) i
  rw [he]
  exact mem_eigenspace_iff.mp (b i.1 i.2).property

end
end chebyshev2.Continuum
