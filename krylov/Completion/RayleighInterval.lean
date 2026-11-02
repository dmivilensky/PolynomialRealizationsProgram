import krylov.Completion.WindowCompletion
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, printed Rayleigh interval.
Use: identify the interval of actual physical directional Rayleigh quotients,
including singular endpoints, with the article's normalized Schur formulas.
Source: the proved physical arbitrary-window completion and positive direction norm.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra
variable {n p : ℕ}

/-- Nonzero scalar multiplication preserves the entire actual cross-block range.
Use: express the two singular Schur range tests using the article's unscaled b.
Article: main_krylov, thm:radau.
Proof: scale the preimage in one direction and divide it by the nonzero scalar
in the other; no rank or invertibility of the old shifted block is required. -/
theorem scaled_cross_range (b : Matrix (Fin p) (Fin 1) ℝ) (c : ℝ) (hc : c≠0) :
    LinearMap.range (c • b).mulVecLin=LinearMap.range b.mulVecLin := by
  ext v
  constructor
  · rintro ⟨u,rfl⟩
    refine ⟨c • u,?_⟩
    change b*ᵥ (c • u)=(c • b)*ᵥ u
    rw [mulVec_smul,smul_mulVec]
  · rintro ⟨u,rfl⟩
    refine ⟨c⁻¹ • u,?_⟩
    change (c • b)*ᵥ (c⁻¹ • u)=b*ᵥ u
    rw [smul_mulVec,mulVec_smul,smul_smul,mul_inv_cancel₀ hc,one_smul]

/-- The original arbitrary-window hypotheses force a strictly positive genuine
squared direction norm.
Use: justify normalization of all feasible physical curvatures.
Article: main_krylov, thm:radau.
Proof: zero belongs to the old range, so the new direction is nonzero; apply
the actual positive identity form. -/
theorem outside_range_direction_positive (S : Matrix (Fin n) (Fin p) ℝ)
    (d : Fin n → ℝ) (hd : d∉LinearMap.range S.mulVecLin) : 0<d ⬝ᵥ d := by
  have hn : d≠0 := by
    rintro rfl
    exact hd ⟨0,Matrix.mulVec_zero S⟩
  simpa only [star_trivial,Matrix.one_mulVec] using
    (Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef).dotProduct_mulVec_pos hn

/-- The actual physical Rayleigh range equals the printed closed singular-Schur
interval; its endpoints and every intermediate point are genuinely attained.
Use: the theorem includes arbitrary nonorthogonal old windows and zero-dimensional
old blocks, and does not replace singular inverses by ordinary inverses.
Article: main_krylov, thm:radau, Gram-only Rayleigh range.
Proof: rescale the proved physical curvature completion by the independently
proved positive squared norm of the actual new direction. -/
theorem window_rayleigh_interval
    (S : Matrix (Fin n) (Fin p) ℝ) (hS : Function.Injective S.mulVec)
    (d : Fin n → ℝ) (hd : d∉LinearMap.range S.mulVecLin)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu L x : ℝ) (hmu : 0<mu) (hmuL : mu≤L)
    (hlo : (T-mu • (Sᵀ*S)).PosSemidef) (hhi : (L • (Sᵀ*S)-T).PosSemidef)
    (hrlo : LinearMap.range (Sᵀ*crossColumn d).mulVecLin≤
      LinearMap.range (T-mu • (Sᵀ*S)).mulVecLin)
    (hrhi : LinearMap.range (Sᵀ*crossColumn d).mulVecLin≤
      LinearMap.range (L • (Sᵀ*S)-T).mulVecLin) :
    (∃ A : Matrix (Fin n) (Fin n) ℝ,A.IsSymm ∧
      (A-mu • 1).PosSemidef ∧ (L • 1-A).PosSemidef ∧
        Sᵀ*A*S=T ∧ Sᵀ*ᵥ (A*ᵥ d)=0 ∧ (d ⬝ᵥ (A*ᵥ d))/(d ⬝ᵥ d)=x) ↔
      mu+mu^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (T-mu • (Sᵀ*S)) hlo.1*
        (Sᵀ*crossColumn d)) 0 0/(d ⬝ᵥ d)≤x ∧
      x≤L-L^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (L • (Sᵀ*S)-T) hhi.1*
        (Sᵀ*crossColumn d)) 0 0/(d ⬝ᵥ d) := by
  have hD := outside_range_direction_positive S d hd
  have hrlo' : LinearMap.range ((-mu) • (Sᵀ*crossColumn d)).mulVecLin≤
      LinearMap.range (T-mu • (Sᵀ*S)).mulVecLin := by
    rw [scaled_cross_range _ _ (neg_ne_zero.mpr hmu.ne')]
    exact hrlo
  have hrhi' : LinearMap.range (L • (Sᵀ*crossColumn d)).mulVecLin≤
      LinearMap.range (L • (Sᵀ*S)-T).mulVecLin := by
    rw [scaled_cross_range _ _ (hmu.trans_le hmuL).ne']
    exact hrhi
  have he : (∃ A : Matrix (Fin n) (Fin n) ℝ,A.IsSymm ∧
      (A-mu • 1).PosSemidef ∧ (L • 1-A).PosSemidef ∧
        Sᵀ*A*S=T ∧ Sᵀ*ᵥ (A*ᵥ d)=0 ∧ (d ⬝ᵥ (A*ᵥ d))/(d ⬝ᵥ d)=x) ↔
      ∃ A : Matrix (Fin n) (Fin n) ℝ,A.IsSymm ∧
      (A-mu • 1).PosSemidef ∧ (L • 1-A).PosSemidef ∧
        Sᵀ*A*S=T ∧ Sᵀ*ᵥ (A*ᵥ d)=0 ∧ d ⬝ᵥ (A*ᵥ d)=x*(d ⬝ᵥ d) := by
    simp only [div_eq_iff hD.ne']
  rw [he,window_curvature_completion_iff S hS d hd T mu L (x*(d ⬝ᵥ d)) hmuL hlo hhi]
  simp only [hrlo',hrhi',true_and]
  have h1 : mu+mu^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (T-mu • (Sᵀ*S)) hlo.1*
      (Sᵀ*crossColumn d)) 0 0/(d ⬝ᵥ d)=
      (mu*(d ⬝ᵥ d)+mu^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (T-mu • (Sᵀ*S)) hlo.1*
        (Sᵀ*crossColumn d)) 0 0)/(d ⬝ᵥ d) := by field_simp
  have h2 : L-L^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (L • (Sᵀ*S)-T) hhi.1*
      (Sᵀ*crossColumn d)) 0 0/(d ⬝ᵥ d)=
      (L*(d ⬝ᵥ d)-L^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (L • (Sᵀ*S)-T) hhi.1*
        (Sᵀ*crossColumn d)) 0 0)/(d ⬝ᵥ d) := by field_simp
  rw [h1,h2,div_le_iff₀ hD,le_div_iff₀ hD]

end
end krylov.Completion
