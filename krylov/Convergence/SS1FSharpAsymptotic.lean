import krylov.Convergence.SS1FOriginalRegularity
import krylov.Convergence.SS1FSharpWindow
import krylov.Convergence.WindowWeightedAges

/-!
Article: main_krylov, thm:ss1F, exact actual matrix asymptotics.
Use: apply the sharp true source polynomial to the genuine recursive
execution. Its extra newer-age factors are little-o of the original
T3-weighted newer plus L3-weighted oldest-squared scale, including T3=0.
Source: actual SS1-F superlinearity, the true oldest/adjacent matrix bound,
and elementary weighted little-o product rules.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Functions krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- The actual corrected matrix has the original sharp leading constants
with a source-derived little-o remainder, in every dimension at least two. -/
theorem ss1FSequence_sharp_matrix_asymptotic
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    (T : EuclideanSpace ℝ (Fin (n+2)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+2))))
    (S : Set (EuclideanSpace ℝ (Fin (n+2)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈S) (hnbhd : S∈𝓝 0)
    {R : ℝ} (hR : 0≤R) (hbounded : ∀ z∈S,‖z‖≤R) {L₃ : ℝ≥0} (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hLip : ∀ z∈S,∀ w∈S,∀ h,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L₃:ℝ)*‖z-w‖)
    (split : (Fin (n+3) → EuclideanSpace ℝ (Fin (n+2))) → Fin (n+2) → ℝ)
    (seed : Fin (n+3) → EuclideanSpace ℝ (Fin (n+2)))
    (hconv : Tendsto (ss1FSequence f G split seed) atTop (𝓝 0))
    {Cw σ : ℝ} (hCw : 0≤Cw) (hσ : 0<σ)
    (hw : ∀ᶠ k in atTop,∀ i : Fin (n+2),
      ‖splitRemainder (ss1FSequence f G split seed (k+i.val))
        (windowStep (ss1FSequence f G split seed) k i)
        (ss1FSequence f G split seed (k+n+2))
        (split (fun j=>ss1FSequence f G split seed (k+j.val)) i)‖≤
      Cw*‖ss1FSequence f G split seed (k+n+2)-ss1FSequence f G split seed (k+i.val+1)‖)
    (hind : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k)))) :
    let B := ‖canonicalVariation (T 0)‖
    let x := ss1FSequence f G split seed
    ∃ r : ℕ → ℝ,r =o[atTop] (fun k=>B*‖x (k+1)‖+(L₃:ℝ)*‖x k‖^2) ∧
      ∀ᶠ k in atTop,
        ‖ss1FNormalizedError f G (windowAnchor (n:=n+2) x k) (windowStep x k)
          (split (fun i=>x (k+i.val)))‖≤
            ((Cw+1/2)*B*‖x (k+1)‖+(L₃:ℝ)/12*‖x k‖^2)+r k := by
  dsimp only
  let B := ‖canonicalVariation (T 0)‖
  let x := ss1FSequence f G split seed
  let d : ℝ := ((n+2:ℕ):ℝ)
  let Kb := 2+Cw+d*(1+2*Cw)
  let Kl := 4+4*Cw
  let Kll := Kl*(1+4*d)+1
  let r := fun k=>Kb*B*‖x (k+2)‖+Kl*(L₃:ℝ)*‖x k‖*‖x (k+1)‖+Kll*(L₃:ℝ)*‖x (k+1)‖^2
  have hB : 0≤B := norm_nonneg (canonicalVariation (T 0))
  have hH := hessian_lipschitz_of_scalar_third H T S hS h₀ hT L₃ hLip hR hbounded
  have hsuper := ss1FSequence_superlinear f G H T S hS h₀ hnbhd hH hH₀ hf hG hG₀ hT hLip
    hB (canonicalVariation_unit_diagonal_bound (T 0)) split seed hconv hCw hσ hw hind
  have hages := superlinear_weighted_age_remainders x hsuper hB L₃.coe_nonneg
  have hr : r =o[atTop] (fun k=>B*‖x (k+1)‖+(L₃:ℝ)*‖x k‖^2) := by
    have hh := ((hages.1.const_mul_left Kb).add (hages.2.1.const_mul_left Kl)).add
      (hages.2.2.const_mul_left Kll)
    apply hh.congr_left
    intro k
    dsimp only [r]
    ring
  refine ⟨r,hr,?_⟩
  have hmono : ∀ᶠ k in atTop,‖x (k+1)‖≤‖x k‖ := by
    simpa only [one_mul,norm_norm] using hsuper.def (by norm_num : (0:ℝ)<1)
  have hmem : ∀ᶠ k in atTop,x k∈S := hconv.eventually hnbhd
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hmono.and (hmem.and (hw.and hind)))
  have htail (k : ℕ) (hk : N≤k) (j : ℕ) : ‖x (k+j)‖≤‖x k‖ := by
    induction j with
    | zero => simp only [Nat.add_zero]; exact le_rfl
    | succ j ih => exact ((hN (k+j) (by omega)).1).trans ih
  filter_upwards [eventually_ge_atTop N] with k hk
  let a := windowAnchor (n:=n+2) x k
  let s := windowStep (n:=n+2) x k
  let l := split (fun i=>x (k+i.val))
  have hs (i : Fin (n+2)) : s i≠0 := by
    intro hz
    have hh := windowMatrix_step_ne_zero (unitWindow s) (hN k hk).2.2.2.1 i
    apply hh
    simp only [unitWindow,krylov.Methods.rescaleWindow,hz,smul_zero]
  have hm (j : ℕ) : x (k+j)∈S := (hN (k+j) (by omega)).2.1
  have hnew (i : Fin (n+2)) (hi : i≠0) : ‖a i‖≤‖x (k+1)‖ := by
    have hip : 0 < i.val := Nat.pos_of_ne_zero (fun hz=>hi (Fin.ext hz))
    convert htail (k+1) (by omega) (i.val-1) using 1
    dsimp only [a,windowAnchor]
    congr 2
    omega
  have hnewer (i : Fin (n+2)) (hi0 : i≠0) (hi1 : i≠1) : ‖a i‖≤‖x (k+2)‖ := by
    have h0 : i.val≠0 := fun hz=>hi0 (Fin.ext hz)
    have h1 : i.val≠1 := fun hz=>hi1 (Fin.ext (by simpa using hz))
    convert htail (k+2) (by omega) (i.val-2) using 1
    dsimp only [a,windowAnchor]
    congr 2
    omega
  have hend (i : Fin (n+2)) (hi : i≠0) : ‖a i+s i‖≤‖x (k+2)‖ := by
    have hip : 0 < i.val := Nat.pos_of_ne_zero (fun hz=>hi (Fin.ext hz))
    have he : a i+s i=x (k+i.val+1) := by simp only [a,s,windowAnchor,windowStep,add_sub_cancel]
    rw [he]
    convert htail (k+2) (by omega) (i.val-1) using 1
    congr 2
    omega
  have hxr : ‖x (k+n+2)‖≤‖x (k+2)‖ := by
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using htail (k+2) (by omega) n
  have hh := ss1F_sharp_age_bound f G H T S hS h₀ hH₀ hf hG hT L₃ hLip hB hCw
    (norm_nonneg (x (k+2))) ((hN (k+1) (by omega)).1)
    (canonicalVariation_unit_diagonal_bound (T 0)) a s l (x (k+n+2))
    (fun i=>hm i.val) (fun i=>by
      simpa only [a,s,windowAnchor,windowStep,add_sub_cancel,Nat.add_assoc] using hm (i.val+1)) (by simpa only [Nat.add_assoc] using hm (n+2)) hs
    (by simp only [a,windowAnchor,Fin.val_zero,Nat.add_zero]; exact le_rfl)
    (by simp only [a,s,windowAnchor,windowStep,Fin.val_zero,Nat.add_zero,add_sub_cancel]; exact le_rfl)
    hnew hnewer hend hxr
    (by simpa only [a,s,l,windowAnchor,windowStep,add_sub_cancel] using (hN k hk).2.2.1)
  simpa only [r,Kb,Kl,Kll,d,add_assoc] using hh

end
end krylov.Convergence
