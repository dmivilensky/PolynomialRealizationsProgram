import krylov.Reference.CGGeometry
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), genuine CG orthogonal covariance.
Use: transport the actual reference recurrence and its measured coefficients between the printed positive-edge and normalized residual Jacobi orientations.
Source: the original genuine exact-line CG executor and actual preservation of real inner products.
-/

namespace krylov.Reference
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The actual exact line length is preserved by a genuine inner-product-preserving linear map.
Use: The actual exact line length is preserved by a genuine inner-product-preserving linear map.
Article: main_krylov, prop:phi(b), genuine CG orthogonal covariance.
Proof: Its true numerator and curvature pairing are preserved. -/
theorem lineLength_isometric (J : E →L[ℝ] F)
    (hJ : ∀ v w,inner ℝ (J v) (J w)=inner ℝ v w) (g d z : E) :
    lineLength (J g) (J d) (J z)=lineLength g d z := by
  simp only [lineLength,hJ]

/-- The actual exact-search gradient commutes with a genuine isometric linear map.
Use: The actual exact-search gradient commutes with a genuine isometric linear map.
Article: main_krylov, prop:phi(b), genuine CG orthogonal covariance.
Proof: Use the true preserved line length and actual linear map operations. -/
theorem searchedGradient_isometric (J : E →L[ℝ] F)
    (hJ : ∀ v w,inner ℝ (J v) (J w)=inner ℝ v w) (g d z : E) :
    searchedGradient (J g) (J d) (J z)=J (searchedGradient g d z) := by
  simp only [searchedGradient,lineLength_isometric J hJ,map_add,map_smul]

/-- The actual norm is preserved by every genuine real inner-product-preserving map.
Use: The actual norm is preserved by every genuine real inner-product-preserving map.
Article: main_krylov, prop:phi(b), genuine CG orthogonal covariance.
Proof: Compare genuine squared norms and their actual nonnegative signs. -/
theorem norm_isometric (J : E →L[ℝ] F)
    (hJ : ∀ v w,inner ℝ (J v) (J w)=inner ℝ v w) (v : E) : ‖J v‖=‖v‖ := by
  have h := hJ v v
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg v,norm_nonneg (J v)]

/-- The entire actual CG gradient and direction transcript is covariant under a genuine intertwining isometry, including stopped tails.
Use: The entire actual CG gradient and direction transcript is covariant under a genuine intertwining isometry, including stopped tails.
Article: main_krylov, prop:phi(b), genuine CG orthogonal covariance.
Proof: Induct through the original true oracle query, exact search and actual residual-norm update. -/
theorem cgRun_isometric (J : E →L[ℝ] F)
    (hJ : ∀ v w,inner ℝ (J v) (J w)=inner ℝ v w)
    (Q : E →L[ℝ] E) (P : F →L[ℝ] F) (hPQ : ∀ v,P (J v)=J (Q v)) (g : E) (k : ℕ) :
    (cgRun P (J g) k).gradient=J (cgRun Q g k).gradient ∧
      (cgRun P (J g) k).direction=J (cgRun Q g k).direction := by
  -- Execute the genuine reference recurrence through the actual intertwining map, retaining every real scalar coefficient.
  have hnorm := norm_isometric J hJ
  induction k with
  | zero => simp only [cgRun,map_neg,and_self]
  | succ k ih =>
    simp only [cgRun,cgAdvance,ih.1,ih.2,hPQ,searchedGradient_isometric J hJ,
      hnorm,map_add,map_neg,map_smul,and_self]
/-- Every actual measured CG line length is unchanged by genuine isometric operator intertwining.
Use: Every actual measured CG line length is unchanged by genuine isometric operator intertwining.
Article: main_krylov, prop:phi(b), genuine CG orthogonal covariance.
Proof: Use the true transported actual gradient, direction and probe. -/
theorem cg_length_isometric (J : E →L[ℝ] F)
    (hJ : ∀ v w,inner ℝ (J v) (J w)=inner ℝ v w)
    (Q : E →L[ℝ] E) (P : F →L[ℝ] F) (hPQ : ∀ v,P (J v)=J (Q v)) (g : E) (k : ℕ) :
    CG.length P (J g) k=CG.length Q g k := by
  have h := cgRun_isometric J hJ Q P hPQ g k
  change lineLength (cgRun P (J g) k).gradient (cgRun P (J g) k).direction
    (P (cgRun P (J g) k).direction)=_
  rw [h.1,h.2,hPQ]
  exact lineLength_isometric J hJ _ _ _

/-- Every actual measured CG recurrence ratio is unchanged by genuine isometric operator intertwining.
Use: Every actual measured CG recurrence ratio is unchanged by genuine isometric operator intertwining.
Article: main_krylov, prop:phi(b), genuine CG orthogonal covariance.
Proof: Use the true transported actual residual norms at both genuine consecutive indices. -/
theorem cg_beta_isometric (J : E →L[ℝ] F)
    (hJ : ∀ v w,inner ℝ (J v) (J w)=inner ℝ v w)
    (Q : E →L[ℝ] E) (P : F →L[ℝ] F) (hPQ : ∀ v,P (J v)=J (Q v)) (g : E) (k : ℕ) :
    CG.beta P (J g) k=CG.beta Q g k := by
  change ‖(cgRun P (J g) (k+1)).gradient‖^2/‖(cgRun P (J g) k).gradient‖^2=_
  rw [(cgRun_isometric J hJ Q P hPQ g (k+1)).1,(cgRun_isometric J hJ Q P hPQ g k).1,
    norm_isometric J hJ,norm_isometric J hJ]

end
end krylov.Reference
