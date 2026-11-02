import krylov.Envelope.LanczosSpectralContinuation
import krylov.Envelope.RawSchurBounds
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), actual CG continuation geometry in the true Ritz interval.
Use: locate every genuine continuation zero and establish actual positivity and monotonicity below the original compression spectrum.
Source: the actual measured Schur spectral product and proved genuine principal inverse spectral enclosure.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.LinearAlgebra Matrix Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every real zero of the original measured CG continuation lies in the genuine positive spectral interval of its actual Lanczos prefix.
Use: Every real zero of the original measured CG continuation lies in the genuine positive spectral interval of its actual Lanczos prefix.
Article: main_krylov, prop:phi(a), actual CG continuation geometry in the true Ritz interval.
Proof: Identify the true Schur eigenvalue zero and apply the actual principal inverse spectral bound. -/
theorem lanczos_phi_root_interval (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,CG.gradient Q g i≠0) (j : ℕ) (hj : j≤m)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ i,a≤(CG.lanczosMatrix_posDef Q hQ hpos g m hpre).1.eigenvalues i)
    (hhi : ∀ i,(CG.lanczosMatrix_posDef Q hQ hpos g m hpre).1.eigenvalues i≤b)
    (lam : ℝ) (hz : (phi (CG.length Q g) (CG.beta Q g) j (m-j)).eval lam=0) :
    lam∈Set.Icc a b := by
  have hT := CG.lanczosMatrix_posDef Q hQ hpos g m hpre
  have hS := rawSchurComplement_posDef _ hT j hj
  rw [lanczos_phi_spectral Q hQ hpos g m hpre j hj] at hz
  obtain ⟨i,hi⟩ := (spectralContinuation_roots _ hS lam).mp hz
  rw [← hi]
  exact rawSchur_spectral_interval _ hT j hj a b ha hb hlo hhi i

/-- The original measured CG continuation is positive below the genuine lower Ritz bound.
Use: The original measured CG continuation is positive below the genuine lower Ritz bound.
Article: main_krylov, prop:phi(a), actual CG continuation geometry in the true Ritz interval.
Proof: Every actual Schur spectral factor is positive there. -/
theorem lanczos_phi_positive_below (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,CG.gradient Q g i≠0) (j : ℕ) (hj : j≤m)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ i,a≤(CG.lanczosMatrix_posDef Q hQ hpos g m hpre).1.eigenvalues i)
    (hhi : ∀ i,(CG.lanczosMatrix_posDef Q hQ hpos g m hpre).1.eigenvalues i≤b)
    (lam : ℝ) (hlam : lam<a) :
    0 < (phi (CG.length Q g) (CG.beta Q g) j (m-j)).eval lam := by
  have hT := CG.lanczosMatrix_posDef Q hQ hpos g m hpre
  rw [lanczos_phi_spectral Q hQ hpos g m hpre j hj]
  exact spectralContinuation_pos _ (rawSchurComplement_posDef _ hT j hj) lam
    (fun i => hlam.trans_le (rawSchur_spectral_interval _ hT j hj a b ha hb hlo hhi i).1)

/-- The original measured CG continuation is nonincreasing below the actual lower Ritz bound.
Use: The original measured CG continuation is nonincreasing below the actual lower Ritz bound.
Article: main_krylov, prop:phi(a), actual CG continuation geometry in the true Ritz interval.
Proof: Use the genuine Schur spectral enclosure and the true positive factor product comparison. -/
theorem lanczos_phi_antitone_below (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,CG.gradient Q g i≠0) (j : ℕ) (hj : j≤m)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ i,a≤(CG.lanczosMatrix_posDef Q hQ hpos g m hpre).1.eigenvalues i)
    (hhi : ∀ i,(CG.lanczosMatrix_posDef Q hQ hpos g m hpre).1.eigenvalues i≤b)
    (x y : ℝ) (hxy : x≤y) (hy : y<a) :
    (phi (CG.length Q g) (CG.beta Q g) j (m-j)).eval y≤
      (phi (CG.length Q g) (CG.beta Q g) j (m-j)).eval x := by
  have hT := CG.lanczosMatrix_posDef Q hQ hpos g m hpre
  rw [lanczos_phi_spectral Q hQ hpos g m hpre j hj]
  exact spectralContinuation_antitone _ (rawSchurComplement_posDef _ hT j hj) x y hxy
    (fun i => hy.trans_le (rawSchur_spectral_interval _ hT j hj a b ha hb hlo hhi i).1)

/-- The original measured CG continuation is strictly decreasing below the actual lower Ritz bound when its true suffix is nonempty.
Use: The original measured CG continuation is strictly decreasing below the actual lower Ritz bound when its true suffix is nonempty.
Article: main_krylov, prop:phi(a), actual CG continuation geometry in the true Ritz interval.
Proof: The real positive suffix dimension supplies a strictly decreasing genuine spectral factor. -/
theorem lanczos_phi_strictAnti_below (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,CG.gradient Q g i≠0) (j : ℕ) (hj : j<m)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ i,a≤(CG.lanczosMatrix_posDef Q hQ hpos g m hpre).1.eigenvalues i)
    (hhi : ∀ i,(CG.lanczosMatrix_posDef Q hQ hpos g m hpre).1.eigenvalues i≤b)
    (x y : ℝ) (hxy : x<y) (hy : y<a) :
    (phi (CG.length Q g) (CG.beta Q g) j (m-j)).eval y<
      (phi (CG.length Q g) (CG.beta Q g) j (m-j)).eval x := by
  have hT := CG.lanczosMatrix_posDef Q hQ hpos g m hpre
  have : Nonempty (Fin (m-j)) := ⟨⟨0,by omega⟩⟩
  rw [lanczos_phi_spectral Q hQ hpos g m hpre j hj.le]
  exact spectralContinuation_strictAnti _ (rawSchurComplement_posDef _ hT j hj.le) x y hxy
    (fun i => hy.trans_le (rawSchur_spectral_interval _ hT j hj.le a b ha hb hlo hhi i).1)
end
end krylov.Envelope
