import krylov.Reference.HeavyBallRadius
import krylov.Reference.LanczosStrictWindow
import krylov.LinearAlgebra.SpectralUpperForm
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), genuine heavy-ball spectral support.
Use: prove the actual finite heavy-ball matrix spectrum is strictly inside its printed physical endpoint window.
Source: true physical Gershgorin rows, original quadratic spectral bounds, actual first-site CG reconstruction and genuine strict irreducible leading-prefix positivity.
-/

namespace krylov.Reference
noncomputable section
open krylov.Realization krylov.LinearAlgebra Matrix
open scoped BigOperators

/-- Every genuine eigenvalue of the actual heavy-ball matrix belongs to the printed physical squared-parameter window.
Use: Every genuine eigenvalue of the actual heavy-ball matrix belongs to the printed physical squared-parameter window.
Article: main_krylov, prop:phi(b), genuine heavy-ball spectral support.
Proof: Its actual Gershgorin radii retain the true first-row boundary; positive parameter inequalities give the real endpoint row bounds. -/
theorem heavyBall_spectral_window (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (hq1 : q≤1) (N : ℕ) :
    ∀ i,d*(1-q)^2≤(heavyBallMatrix_posDef d q hd N).1.eigenvalues i ∧
      (heavyBallMatrix_posDef d q hd N).1.eigenvalues i≤d*(1+q)^2 := by
  -- The actual first-row diagonal margin is retained before either physical Gershgorin endpoint is estimated.
  apply eigenvalues_interval_of_rows
  · intro i
    have hr := heavyBall_row_radius d q hd hq i
    have hdg : heavyBallMatrix d q N i i=if i.val=0 then d else d*(1+q^2) := by
      simp [heavyBallMatrix]
    rw [hdg]
    by_cases hi : i.val=0
    · rw [ite_eq_left hi]
      simp only [hi,lt_self_iff_false,ite_false,add_zero] at hr
      have hh : 0≤d*q*(1-q) := mul_nonneg (mul_nonneg hd.le hq.le) (sub_nonneg.mpr hq1)
      nlinarith [hr]
    · rw [ite_eq_right hi]
      rw [ite_eq_left (show 0 < i.val by omega)] at hr
      nlinarith [hr]
  · intro i
    have hr := heavyBall_row_radius d q hd hq i
    have hdg : heavyBallMatrix d q N i i=if i.val=0 then d else d*(1+q^2) := by
      simp [heavyBallMatrix]
    rw [hdg]
    by_cases hi : i.val=0
    · rw [ite_eq_left hi]
      simp only [hi,lt_self_iff_false,ite_false,add_zero] at hr
      have hh : 0≤d*q := mul_nonneg hd.le hq.le
      have hs : 0≤d*q^2 := mul_nonneg hd.le (sq_nonneg q)
      nlinarith [hr]
    · rw [ite_eq_right hi]
      rw [ite_eq_left (show 0 < i.val by omega)] at hr
      nlinarith [hr]

/-- Every genuine finite heavy-ball matrix eigenvalue lies strictly inside its actual physical squared-parameter window.
Use: Every genuine finite heavy-ball matrix eigenvalue lies strictly inside its actual physical squared-parameter window.
Article: main_krylov, prop:phi(b), genuine heavy-ball spectral support.
Proof: Use the true one-site-longer heavy-ball matrix, its actual fully active first-site CG compression and the proved genuine strict Ritz prefix theorem. -/
theorem heavyBall_strict_spectral_window (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (hq1 : q≤1) (N : ℕ) :
    ∀ i,d*(1-q)^2<(heavyBallMatrix_posDef d q hd N).1.eigenvalues i ∧
      (heavyBallMatrix_posDef d q hd N).1.eigenvalues i<d*(1+q)^2 := by
  -- A real additional heavy-ball site supplies the genuine nonzero extra edge needed for strict finite spectral margins.
  let T := heavyBallMatrix d q (N+1)
  have hT := heavyBallMatrix_posDef d q hd (N+1)
  have ht := heavyBallMatrix_tridiagonal d q (N+1)
  have hn := heavyBallMatrix_adjacent_neg d q hd hq (N+1)
  let g : EuclideanSpace ℝ (Fin (N+1)) := WithLp.toLp 2 (chebyshev1.JacobiData.site (N+1) 0)
  have hpre : ∀ i<N+1,CG.gradient (cgOperator T) g i≠0 := raw_cg_nonstagnation T hT ht hn
  have hwin := heavyBall_spectral_window d q hd hq hq1 (N+1)
  have hstrict := CG.lanczosMatrix_strict_window (cgOperator T) (cgOperator_positive T hT).1
    (cgOperator_positive T hT).2 g N hpre (d*(1-q)^2) (d*(1+q)^2)
    (spectral_lower_form T hT.1 (fun i => (hwin i).1))
    (spectral_upper_form T hT.1 (fun i => (hwin i).2))
  -- The true measured prefix is exactly the original shorter physical heavy-ball matrix.
  have he : CG.lanczosMatrix (cgOperator T) g N=heavyBallMatrix d q N := by
    rw [raw_lanczosMatrix_prefix T hT ht hn N (by omega)]
    exact heavyBallMatrix_prefix d q (N+1) N (by omega)
  have hp := CG.lanczosMatrix_posDef (cgOperator T) (cgOperator_positive T hT).1
    (cgOperator_positive T hT).2 g N (fun i hi => hpre i (by omega))
  have hL : (CG.lanczosMatrix (cgOperator T) g N-(d*(1-q)^2) • 1).PosDef :=
    (positive_lower_shift_iff _ hp.1 _).mpr (fun i => (hstrict i).1)
  have hH : ((d*(1+q)^2) • 1-CG.lanczosMatrix (cgOperator T) g N).PosDef :=
    (positive_upper_shift_iff _ hp.1 _).mpr (fun i => (hstrict i).2)
  rw [he] at hL hH
  intro i
  exact ⟨(positive_lower_shift_iff _ (heavyBallMatrix_posDef d q hd N).1 _).mp hL i,
    (positive_upper_shift_iff _ (heavyBallMatrix_posDef d q hd N).1 _).mp hH i⟩
end
end krylov.Reference
