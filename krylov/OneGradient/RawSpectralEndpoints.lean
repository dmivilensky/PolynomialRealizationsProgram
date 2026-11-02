import krylov.OneGradient.RawLastNormal
import krylov.OneGradient.SpectralFibreParameters
import krylov.LinearAlgebra.LastDiagonalBand
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), actual supplied-Jacobi spectral endpoints.
Use: identify the original physical information-fibre endpoints directly
with the genuine supplied leading matrix and cross column.
Source: proved actual last-Lanczos diagonal dictionary, closed physical
fibre interval and the true supplied-coordinate scalar Schur interval.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix chebyshev1 krylov.Reference krylov.Realization krylov.LinearAlgebra
variable {n : ℕ}

/-- The original physical Gauss--Radau pivot endpoints of a genuine supplied
irreducible Jacobi reference equal the literal supplied-coordinate inverse
Schur expressions, without an assumed Lanczos frame identification.
Use: sharp spectral limiting families retain the source's actual measured
information fibre and its real endpoints.
Article: main_krylov, s5:fibre(b), genuine raw/physical endpoint dictionary.
Proof: the actual last Lanczos normal and pivot identify every physical
completion with its literal final-diagonal update. The already proved true
physical interval and actual supplied-coordinate Schur interval therefore
describe exactly the same nonempty set. Their actual endpoint membership
gives both inequalities between each pair of real endpoints. -/
theorem raw_physical_spectral_endpoint_formulas
    (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin (n+1),i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin (n+1),i.val+1=j.val → T i j < 0)
    (hg : WithLp.toLp 2 (JacobiData.site (n+1) 0)≠0)
    (hc : (activeSpectralValues T hT.1 (WithLp.toLp 2 (JacobiData.site (n+1) 0))).card=n+1)
    (mu upper : ℝ) (hlo : (lastLeading T-mu • 1).PosDef) (hhi : (upper • 1-lastLeading T).PosDef)
    (hband : (T-mu • 1).PosSemidef ∧ (upper • 1-T).PosSemidef) :
    let g := WithLp.toLp 2 (JacobiData.site (n+1) 0)
    spectralLowerPivot T hT g hg hc mu=mu+lastCross T ⬝ᵥ ((lastLeading T-mu • 1)⁻¹*ᵥ lastCross T) ∧
      spectralUpperPivot T hT g hg hc upper=upper-lastCross T ⬝ᵥ ((upper • 1-lastLeading T)⁻¹*ᵥ lastCross T) := by
  let g : EuclideanSpace ℝ (Fin (n+1)) := WithLp.toLp 2 (JacobiData.site (n+1) 0)
  let lo := spectralLowerPivot T hT g hg hc mu
  let hi := spectralUpperPivot T hT g hg hc upper
  let a := mu+lastCross T ⬝ᵥ ((lastLeading T-mu • 1)⁻¹*ᵥ lastCross T)
  let b := upper-lastCross T ⬝ᵥ ((upper • 1-lastLeading T)⁻¹*ᵥ lastCross T)
  have hC (c : ℝ) : lanczosCompletion T hT g hg hc c=lastDiagonalUpdate T c :=
    (raw_lanczos_completion_diagonal T hT htri hneg hg hc c).trans (last_diagonal_update_rankOne T c).symm
  have hself : lastDiagonalUpdate T (T (Fin.last n) (Fin.last n))=T := by
    rw [last_diagonal_update_rankOne,sub_self,zero_smul,add_zero]
  have hne : ∃ c : ℝ,(lanczosCompletion T hT g hg hc c-mu • 1).PosSemidef ∧
      (upper • 1-lanczosCompletion T hT g hg hc c).PosSemidef := by
    refine ⟨T (Fin.last n) (Fin.last n),?_⟩
    rw [hC,hself]
    exact hband
  obtain ⟨horder,hphysical⟩ := physical_spectral_fibre_interval T hT g hg hc mu upper hne
  have he (c : ℝ) : (lo≤c ∧ c≤hi) ↔ (a≤c ∧ c≤b) := by
    have hp := hphysical c
    rw [hC c] at hp
    have hr := last_diagonal_update_band_iff T hT.1.isSymm mu upper c hlo hhi
    exact hp.symm.trans hr
  have hab : a≤b := by
    have hh := (last_diagonal_update_band_iff T hT.1.isSymm mu upper (T (Fin.last n) (Fin.last n)) hlo hhi).mp
      (by rw [hself];exact hband)
    exact hh.1.trans hh.2
  have hlo1 := (he lo).mp ⟨le_rfl,horder⟩
  have hlo2 := (he a).mpr ⟨le_rfl,hab⟩
  have hhi1 := (he hi).mp ⟨horder,le_rfl⟩
  have hhi2 := (he b).mpr ⟨hab,le_rfl⟩
  exact ⟨le_antisymm hlo2.1 hlo1.1,le_antisymm hhi1.2 hhi2.2⟩

end
end krylov.OneGradient
