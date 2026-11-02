import krylov.Methods.DirectionImageError
import krylov.Methods.DirectionReference
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, true native direction-basis reference weights.
Use: prove the actual reference virtual solve has only its newest direction
coefficient, before differentiating the genuine replay-error recursion.
Source: actual quadratic virtual correction and true independent native
reference direction arrays, with finite coefficient uniqueness.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual native direction-basis reference virtual coefficients are
exactly the newest missed CG length and zero in every older coordinate.
Use: the first variation of the true replay recursion therefore has just its
one genuine preceding image-error term.
Article: main_krylov, thm:I, w_j^0=(alpha_(j-1)-tau_(j-1)) u_0 in newest-first coordinates.
Proof: the native coefficient vector synthesizes the actual next virtual
correction, which genuine quadratic consistency identifies as the missed
newest CG direction. The real nonzero reference Gram determinant proves
independence, so equality of actual physical syntheses fixes every coefficient. -/
theorem xrfcD_reference_coefficients (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k<N) :
    xrfcDArrayCoefficients trial (fun _ => Q) g (k+1)=fun i : Fin (k+1) =>
      if i=0 then CG.length Q g k-trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g k) else 0 := by
  let D := fun i : Fin (k+1) => xrfcDExecutedDirection trial (fun _ => Q) g (k+1-1-i.val)
  let Y := fun i : Fin (k+1) => xrfcDExecutedImage trial (fun _ => Q) g (k+1-1-i.val)
  let rho := CG.length Q g k-trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g k)
  let w := xrfcDArrayCoefficients trial (fun _ => Q) g (k+1)
  let c := fun i : Fin (k+1) => if i=0 then rho else 0
  have hY : Y=fun i => Q (D i) := by
    funext i
    dsimp only [Y,D]
    rw [xrfcD_executed_image_reference trial Q hQ hpos g N hpre ht _ (by omega),
      xrfcD_executed_direction_reference trial Q hQ hpos g N hpre ht _ (by omega)]
  have hu : IsUnit (correctionCompression D Q).det := by
    rw [← pairModel_quadratic D Q hQ,← hY]
    exact isUnit_iff_ne_zero.mpr (xrfcD_full_array_domains trial Q hQ hpos g N hpre ht (k+1) (by omega)).2
  have hLI := compression_unit_independent D Q hu
  have hcorr := (xrfcD_virtual_coordinates trial (fun _ => Q) g (k+1)).1
  have hmiss := xrfcD_next_correction fullMemory trial Q hQ hpos g N hpre
    (fun _ _ hi => hi) ht k hk
  have hactual : combine D w=rho • CG.direction Q g k := hcorr.symm.trans hmiss
  have hcandidate : combine D c=rho • CG.direction Q g k := by
    simp only [combine,c,ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [show D 0=CG.direction Q g k by
      exact xrfcD_executed_direction_reference trial Q hQ hpos g N hpre ht k hk.le]
  have hsynth : combine D w=combine D c := hactual.trans hcandidate.symm
  change w=c
  funext i
  apply sub_eq_zero.mp
  apply Fintype.linearIndependent_iff.mp hLI (fun j => w j-c j) _ i
  simp only [sub_smul,Finset.sum_sub_distrib]
  change combine D w-combine D c=0
  rw [hsynth,sub_self]

/-- The same genuine newest-only native solve in a dimension-independent
value-index form, valid at every positive actual reference prefix.
Use: avoid changing dependent finite-index numerals when identifying the
actual terminal source dimension.
Article: main_krylov, thm:I.
Proof: rewrite the proved actual successor solve in value coordinates and
identify the true positive prefix with its predecessor plus one. -/
theorem xrfcD_reference_coefficients_at (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) (hkp : 0<k) :
    xrfcDArrayCoefficients trial (fun _ => Q) g k=fun i : Fin k =>
      if i.val=0 then CG.length Q g (k-1)-
        trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g (k-1)) else 0 := by
  cases k with
  | zero => omega
  | succ k =>
    simpa only [Nat.add_sub_cancel,Fin.ext_iff,Fin.val_zero] using
      xrfcD_reference_coefficients trial Q hQ hpos g N hpre ht k (by omega)

end
end krylov.Methods
