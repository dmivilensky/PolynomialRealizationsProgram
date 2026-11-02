import krylov.Envelope.LanczosPhiGeometry
import krylov.Reference.LanczosStrictWindow
import krylov.Reference.Stopping
import krylov.LinearAlgebra.SpectralEndpoints
import krylov.LinearAlgebra.SpectralUpperForm
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine original CG continuation Ritz geometry.
Use: locate actual continuation zeros in the true smallest-to-largest Ritz interval and prove that entire interval lies strictly inside the original spectral bounds before actual exhaustion.
Source: genuine measured Schur continuation, actual principal inverse enclosure, true attained finite spectral extrema and the original active-atom CG nonstagnation theorem.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.LinearAlgebra Matrix Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual continuation zero lies between the true smallest and largest eigenvalues of its genuine computed Lanczos prefix.
Use: Every actual continuation zero lies between the true smallest and largest eigenvalues of its genuine computed Lanczos prefix.
Article: main_krylov, prop:phi(a), genuine original CG continuation Ritz geometry.
Proof: Use the genuine attained spectral endpoint bounds in the actual Schur zero enclosure. -/
theorem lanczos_phi_ritz_interval (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ) [Nonempty (Fin m)]
    (hpre : ∀ i<m,CG.gradient Q g i≠0) (j : ℕ) (hj : j≤m)
    (lam : ℝ) (hz : (phi (CG.length Q g) (CG.beta Q g) j (m-j)).eval lam=0) :
    lam∈Set.Icc (spectralLower _ (CG.lanczosMatrix_posDef Q hQ hpos g m hpre).1)
      (spectralUpper _ (CG.lanczosMatrix_posDef Q hQ hpos g m hpre).1) := by
  have hT := CG.lanczosMatrix_posDef Q hQ hpos g m hpre
  exact lanczos_phi_root_interval Q hQ hpos g m hpre j hj _ _
    (spectralLower_pos _ hT) (spectralUpper_pos _ hT)
    (spectralLower_le _ hT.1) (le_spectralUpper _ hT.1) lam hz

/-- The actual closed extreme-Ritz interval of a genuinely nonterminal CG prefix lies strictly inside the original physical spectral window.
Use: The actual closed extreme-Ritz interval of a genuinely nonterminal CG prefix lies strictly inside the original physical spectral window.
Article: main_krylov, prop:phi(a), genuine original CG continuation Ritz geometry.
Proof: Actual active atom count supplies the genuine extra residual; physical spectral quadratic bounds then give both true strict Ritz margins. -/
theorem cg_ritz_strict_interval {n : ℕ} (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (m : ℕ) [Nonempty (Fin m)]
    (hcount : m<referenceAtomCount base hb g) (mu L : ℝ)
    (hlo : ∀ i,mu≤hb.1.eigenvalues i) (hhi : ∀ i,hb.1.eigenvalues i≤L) :
    let hT := CG.lanczosMatrix_posDef (cgOperator base) (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 g m (fun i hi => cg_nonstagnation base hb g i (by omega))
    Set.Icc (spectralLower _ hT.1) (spectralUpper _ hT.1) ⊆ Set.Ioo mu L := by
  -- Derive the extra genuine active CG node from the actual spectral atom count before using strict prefix positivity.
  have hstrict := CG.lanczosMatrix_strict_window (cgOperator base) (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g m
    (fun i hi => cg_nonstagnation base hb g i (by omega)) mu L
    (spectral_lower_form base hb.1 hlo) (spectral_upper_form base hb.1 hhi)
  exact spectral_interval_inside _ _ mu L (fun i => (hstrict i).1) (fun i => (hstrict i).2)

/-- Every true measured continuation zero of an actually nonterminal CG prefix lies strictly inside the original physical spectral window.
Use: Every true measured continuation zero of an actually nonterminal CG prefix lies strictly inside the original physical spectral window.
Article: main_krylov, prop:phi(a), genuine original CG continuation Ritz geometry.
Proof: Combine the real extreme-Ritz enclosure with its genuine strict physical endpoint margins. -/
theorem cg_phi_zeros_interior {n : ℕ} (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (m : ℕ) [Nonempty (Fin m)]
    (hcount : m<referenceAtomCount base hb g) (mu L : ℝ)
    (hlo : ∀ i,mu≤hb.1.eigenvalues i) (hhi : ∀ i,hb.1.eigenvalues i≤L)
    (j : ℕ) (hj : j≤m) (lam : ℝ)
    (hz : (phi (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g) j (m-j)).eval lam=0) :
    lam∈Set.Ioo mu L := by
  exact cg_ritz_strict_interval base hb g m hcount mu L hlo hhi
    (lanczos_phi_ritz_interval (cgOperator base) (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 g m (fun i hi => cg_nonstagnation base hb g i (by omega)) j hj lam hz)
end
end krylov.Envelope
