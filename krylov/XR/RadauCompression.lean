import krylov.XR.RadauFrame

/-!
Article: main_krylov, apG:radau-adequate, constructive strict-interior extension.
Use: prove that a genuinely small perturbation of a full-rank physical
compression remains spectrally feasible inside the original strict class
bounds. Source: explicit positive-form decomposition and the already
proved inverse-Gram spectral extension, rather than assumed feasibility.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Completion krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator MatrixOrder
variable {n p : ℕ}

/-- Actual small compressed error preserves both strict shifted pencils
and constructs a genuine physical symmetric matrix in the original
spectral band with exactly the prescribed compression.
Article: main_krylov, apG:radau-adequate. -/
theorem radau_nearby_compression (Z : Matrix (Fin n) (Fin p) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : Q.IsHermitian)
    (mu a b upper gamma delta : ℝ) (hmu : mu<a) (hupper : b<upper) (hband : mu≤upper)
    (hgamma : 0<gamma) (hdelta : 0≤delta)
    (hHlo : (H-a • 1).PosSemidef) (hHhi : (b • 1-H).PosSemidef)
    (hgain : (Zᵀ*Z-gamma • 1).PosSemidef)
    (herror : ‖Q-Zᵀ*H*Z‖≤delta)
    (hsmalllo : delta<(a-mu)*gamma) (hsmallhi : delta<(upper-b)*gamma) :
    (Q-mu • (Zᵀ*Z)).PosDef ∧ (upper • (Zᵀ*Z)-Q).PosDef ∧
      ∃ B : Matrix (Fin n) (Fin n) ℝ,B.IsSymm ∧ (B-mu • 1).PosSemidef ∧
        (upper • 1-B).PosSemidef ∧ Zᵀ*B*Z=Q := by
  let G := Zᵀ*Z
  let A := Zᵀ*H*Z
  let D := Q-A
  have hAs : A.IsHermitian := by
    simpa only [A,conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_mul Z hH
  have hDs : D.IsHermitian := hQ.sub hAs
  have herr := (spectral_norm_iff_shifted_posSemidef D hDs hdelta).mp herror
  have hG : G.PosDef := by
    have hh := (Matrix.PosDef.one.smul hgamma).add_posSemidef hgain
    convert hh using 1
    dsimp only [G]
    module
  have hloZ : (Zᵀ*(H-a • 1)*Z).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hHlo.conjTranspose_mul_mul_same Z
  have hhiZ : (Zᵀ*(b • 1-H)*Z).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hHhi.conjTranspose_mul_mul_same Z
  have hlo : (Q-mu • G).PosDef := by
    have hh := (Matrix.PosDef.one.smul (sub_pos.mpr hsmalllo)).add_posSemidef
      (herr.2.add (hloZ.add (hgain.smul (sub_nonneg.mpr hmu.le))))
    convert hh using 1
    simp only [D,A,G,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]
    module
  have hhi : (upper • G-Q).PosDef := by
    have hh := (Matrix.PosDef.one.smul (sub_pos.mpr hsmallhi)).add_posSemidef
      (herr.1.add (hhiZ.add (hgain.smul (sub_nonneg.mpr hupper.le))))
    convert hh using 1
    simp only [D,A,G,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]
    module
  obtain ⟨B,hBlo,hBhi,hBQ⟩ :=
    (spectral_extension_iff Z hG Q mu upper hband).mp ⟨hlo.posSemidef,hhi.posSemidef⟩
  have hBs : B.IsSymm := by
    have hh := hBlo.1.isSymm.eq
    simp only [transpose_sub,transpose_smul,transpose_one] at hh
    calc
      _ = (Bᵀ-mu • 1)+mu • 1 := by abel
      _ = (B-mu • 1)+mu • 1 := congrArg (fun X=>X+mu • 1) hh
      _ = _ := sub_add_cancel _ _
  exact ⟨hlo,hhi,B,hBs,hBlo,hBhi,hBQ⟩

end
end krylov.XR
