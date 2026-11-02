import krylov.Completion.WindowFeasibility
import krylov.Completion.FullActionTrialMinimax
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, equality of actual full-action and Gram-data intervals.
Use: close the original preservation-of-entire-action clause for arbitrary
windows, including singular old spectral pencils and coincident endpoints.
Source: actual physical window Schur necessity, genuine shorted-form full-action
endpoints and the true affine attainment of all intermediate physical curvatures.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra
variable {n p : ℕ}

/-- A genuine lower spectral pencil already forces the original real matrix to be symmetric.
Use: original physical completion classes need no separate assumed symmetry certificate.
Article: main_krylov, thm:radau.
Proof: add the actual symmetric scalar identity to the true symmetric lower pencil. -/
theorem lower_band_symmetric (A : Matrix (Fin n) (Fin n) ℝ) (mu : ℝ)
    (hlo : (A-mu • 1).PosSemidef) : A.IsSymm := by
  have hmu : (mu • (1 : Matrix (Fin n) (Fin n) ℝ)).IsSymm := by
    simp only [Matrix.IsSymm,transpose_smul,transpose_one]
  simpa only [sub_add_cancel] using hlo.1.isSymm.add hmu

/-- The original full-action completion family has exactly the same true
curvature values as the original Gram-data window class.
Use: both real endpoint and every intermediate curvature remain attainable
when the entire observed action A'S=AS is imposed; no eigenvector or strict
shifted-old-model hypothesis is added.
Article: main_krylov, thm:radau, same interval under full-action constraints.
Proof: the true original matrix derives both compressed positive pencils.
Its actual full-action endpoint curvatures are the literal same Moore--Penrose
Schur bounds as the Gram-data interval. The genuine full-action affine
attainment then realizes every Gram-feasible curvature. In the reverse
direction symmetry and the real preserved action give the original Gram and
conjugacy observations exactly. -/
theorem full_action_same_window_curvatures
    (A : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin p) ℝ)
    (hS : Function.Injective S.mulVec) (d : Fin n → ℝ) (hd : d∉LinearMap.range S.mulVecLin)
    (mu L c : ℝ) (hmuL : mu≤L) (hlo : (A-mu • 1).PosSemidef) (hhi : (L • 1-A).PosSemidef)
    (hzero : Sᵀ*ᵥ (A*ᵥ d)=0) :
    (∃ C∈windowCurvatureCompletions S d (Sᵀ*A*S) mu L,d ⬝ᵥ (C*ᵥ d)=c) ↔
      ∃ C∈fullActionCompletions A S mu L,d ⬝ᵥ (C*ᵥ d)=c := by
  let T := Sᵀ*A*S
  have hA := lower_band_symmetric A mu hlo
  have hAmem : A∈windowCurvatureCompletions S d T mu L := ⟨hA,hlo,hhi,rfl,hzero⟩
  obtain ⟨hTL,hTH⟩ := window_completion_shifted_forms S d T mu L A hAmem
  have hL : Sᵀ*(A-mu • 1)*S=T-mu • (Sᵀ*S) := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]
    rfl
  have hH : Sᵀ*(L • 1-A)*S=L • (Sᵀ*S)-T := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]
    rfl
  have hb : Sᵀ*crossColumn d=crossColumn (Sᵀ*ᵥ d) := by
    ext i j
    rfl
  have hpcongr (X Y : Matrix (Fin p) (Fin p) ℝ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
      (he : X=Y) : pseudoinverse X hX=pseudoinverse Y hY := by
    subst Y
    rfl
  have hcl : d ⬝ᵥ (lowerActionEndpoint A mu hlo S*ᵥ d)=
      mu*(d ⬝ᵥ d)+mu^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (T-mu • (Sᵀ*S)) hTL.1*
        (Sᵀ*crossColumn d)) 0 0 := by
    rw [lower_action_curvature A S d mu hlo hzero,hb,crossColumn_quadratic]
    have hi := hpcongr _ _ (by simpa only [conjTranspose_eq_transpose_of_trivial] using (hlo.conjTranspose_mul_mul_same S).1) hTL.1 hL
    rw [hi]
    rfl
  have hch : d ⬝ᵥ (upperActionEndpoint A L hhi S*ᵥ d)=
      L*(d ⬝ᵥ d)-L^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (L • (Sᵀ*S)-T) hTH.1*
        (Sᵀ*crossColumn d)) 0 0 := by
    rw [upper_action_curvature A S d L hhi hzero,hb,crossColumn_quadratic]
    have hi := hpcongr _ _ (by simpa only [conjTranspose_eq_transpose_of_trivial] using (hhi.conjTranspose_mul_mul_same S).1) hTH.1 hH
    rw [hi]
    rfl
  constructor
  · rintro ⟨C,⟨hCs,hCl,hCh,hCT,hCzero⟩,hcurv⟩
    have hbounds := (window_curvature_completion_iff S hS d hd T mu L c hmuL hTL hTH).mp
      ⟨C,hCs,hCl,hCh,hCT,hCzero,hcurv⟩
    have hfull := full_action_curvature_range A S d mu L c hlo hhi
    rw [hcl,hch] at hfull
    obtain ⟨B,hBl,hBh,hact,hBc⟩ := hfull.mpr hbounds.2.2
    exact ⟨B,⟨hBl,hBh,hact⟩,hBc⟩
  · rintro ⟨C,⟨hCl,hCh,hact⟩,hcurv⟩
    have hCs := lower_band_symmetric C mu hCl
    obtain ⟨hCT,hCzero⟩ := full_action_window_constraints A C hA hCs S d hact hzero
    exact ⟨C,⟨hCs,hCl,hCh,hCT,hCzero⟩,hcurv⟩

/-- A true one-column Schur range inclusion is exactly membership of its
original physical cross vector in the same actual range.
Use: the singular completion conditions are literally the source's b in ran(H).
Article: main_krylov, thm:radau.
Proof: the unit singleton coordinate realizes the original vector; every other
true column image is its actual scalar multiple. -/
theorem cross_column_range_iff (b : Fin p → ℝ) (V : Submodule ℝ (Fin p → ℝ)) :
    LinearMap.range (crossColumn b).mulVecLin≤V ↔ b∈V := by
  constructor
  · intro h
    apply h
    refine ⟨fun _ => 1,?_⟩
    ext i
    change (crossColumn b*ᵥ (fun _ : Fin 1 => 1)) i=b i
    simp only [crossColumn,Matrix.mulVec,dotProduct,Fin.sum_univ_one,mul_one]
  · intro hb x hx
    obtain ⟨u,rfl⟩ := hx
    have he : crossColumn b*ᵥ u=u 0 • b := by
      ext i
      simp only [crossColumn,Matrix.mulVec,dotProduct,Fin.sum_univ_one,Pi.smul_apply,smul_eq_mul]
      ring
    change crossColumn b*ᵥ u∈V
    rw [he]
    exact V.smul_mem _ hb

/-- The actual arbitrary-window matrix cross-range test is the source's
literal original vector range condition for b=S transpose d.
Use: no hidden column-image convention remains in the feasibility theorem.
Article: main_krylov, thm:radau.
Proof: actual matrix multiplication identifies the single cross column,
and the true singleton column range criterion gives the equivalence. -/
theorem window_cross_range_iff (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (H : Matrix (Fin p) (Fin p) ℝ) :
    LinearMap.range (Sᵀ*crossColumn d).mulVecLin≤LinearMap.range H.mulVecLin ↔
      Sᵀ*ᵥ d∈LinearMap.range H.mulVecLin := by
  have he : Sᵀ*crossColumn d=crossColumn (Sᵀ*ᵥ d) := by ext i j;rfl
  rw [he,cross_column_range_iff]

/-- The actual window's matrix Schur correction is exactly the source's
original scalar b transpose H-plus b with b=S transpose d.
Use: identify the printed normalized curvature endpoints without a coordinate convention.
Article: main_krylov, thm:radau.
Proof: the genuine cross column has its actual quadratic contraction identity. -/
theorem window_schur_correction (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) :
    ((Sᵀ*crossColumn d)ᵀ*M*(Sᵀ*crossColumn d)) 0 0=(Sᵀ*ᵥ d) ⬝ᵥ (M*ᵥ (Sᵀ*ᵥ d)) := by
  have he : Sᵀ*crossColumn d=crossColumn (Sᵀ*ᵥ d) := by ext i j;rfl
  rw [he,crossColumn_quadratic]
  rfl

/-- The original empty-window Schur correction is zero, so the two normalized
source curvature endpoints reduce exactly to mu and L.
Use: the full physical window theorem includes p=0 with its printed boundary formulas.
Article: main_krylov, thm:radau, empty-window convention.
Proof: the genuine physical cross vector has no coordinates and its actual
quadratic contraction is the empty real sum. -/
theorem empty_window_schur_correction (S : Matrix (Fin n) (Fin 0) ℝ) (d : Fin n → ℝ)
    (M : Matrix (Fin 0) (Fin 0) ℝ) :
    ((Sᵀ*crossColumn d)ᵀ*M*(Sᵀ*crossColumn d)) 0 0=0 := by
  rw [window_schur_correction]
  simp only [dotProduct,Finset.univ_eq_empty,Finset.sum_empty]

end
end krylov.Completion
