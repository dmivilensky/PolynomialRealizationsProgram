import krylov.Convergence.SS1OldestAsymptotic
import krylov.Convergence.OldestMultiplicative
import krylov.Convergence.SS1ZeroLipschitz

/-!
Article: main_krylov, thm:Ip, literal sharp SS1 oldest coefficient.
Use: finish the exact 1+o(1) packaging with the true oldest distance and
include the exact quadratic case without dividing by a zero constant.
Source: proved genuine source asymptotics and actual oldest-dual geometry.
-/

/-!
Article: krylov, Theorem E.19 [thm:Ip].

Actual SS1 and ordinary sliding RFC have the stored-only oldest-distance sharp product
coefficient, superlinearity and characteristic-root order, with the correct physical metrics
and gradient clock.
The eventual gate conclusion concerns ordinary RFC’s canonical defect gate, not an unrelated
fixed spectral threshold. The latter requires its own quantitative hypothesis.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Actual SS1 has exactly the printed oldest-distance coefficient and
one genuine multiplicative factor tending to one, including LH=0. -/
theorem ss1Sequence_printed_oldest_bound
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0) {L : ℝ≥0}
    (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1Sequence G seed) atTop (𝓝 0)) {σ : ℝ} (hσ : 0<σ)
    (hind : ∀ᶠ k in atTop,IsUnit (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k)))) :
    ∃ theta : ℕ → ℝ,Tendsto theta atTop (𝓝 0) ∧∀ᶠ k in atTop,
      ‖ss1Sequence G seed (k+n+2)‖≤(1+theta k)*
        ((L:ℝ)/(2*(slidingOldestDistance (ss1Sequence G seed) k)^2))*
        ‖ss1Sequence G seed (k+n+1)‖*‖ss1Sequence G seed k‖ := by
  let x := ss1Sequence G seed
  have ha (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val)) atTop (𝓝 0) := hconv.comp (tendsto_add_atTop_nat i.val)
  have hb (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.add_assoc] using hconv.comp (tendsto_add_atTop_nat (i.val+1))
  have hx : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.add_assoc] using hconv.comp (tendsto_add_atTop_nat (n+1))
  by_cases hL : L=0
  · subst L
    have hmem : ∀ᶠ k in atTop,(∀ i : Fin (n+1),x (k+i.val)∈S) ∧
        (∀ i : Fin (n+1),x (k+i.val+1)∈S) ∧x (k+n+1)∈S :=
      ((Filter.eventually_all.mpr fun i=>(ha i).eventually hnbhd).and
        (Filter.eventually_all.mpr fun i=>(hb i).eventually hnbhd)).and (hx.eventually hnbhd) |>.mono
          fun _ h=>⟨h.1.1,h.1.2,h.2⟩
    refine ⟨fun _=>0,tendsto_const_nhds,?_⟩
    filter_upwards [hmem,hind] with k hm hv
    have hz := ss1Point_eq_zero_of_zero_lipschitz G H S hS h₀ hH hH₀ hG hG₀
      (fun i : Fin (n+1)=>x (k+i.val)) (fun i=>x (k+i.val+1)) (x (k+n+1)) hm.1 hm.2.1 hm.2.2 hv.1
    change ss1Point (windowStep (n:=n+1) (ss1Sequence G seed) k)
      (windowImage G (ss1Sequence G seed) k) (G (ss1Sequence G seed (k+n+1))) (ss1Sequence G seed (k+n+1))=0 at hz
    rw [←ss1Sequence_step G seed k] at hz
    simp only [hz,NNReal.coe_zero,zero_div,zero_mul,mul_zero,norm_zero,le_refl]
  · have hLpos : 0<(L:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hL)
    obtain ⟨r,hr,hbnd⟩ := ss1Sequence_oldest_asymptotic G H S hS h₀ hnbhd hH hH₀ hG hG₀ seed hconv hσ hind
    have hD : ∀ᶠ k in atTop,σ≤slidingOldestDistance x k ∧slidingOldestDistance x k≤1 := by
      filter_upwards [hind] with k hk
      let V := windowMatrix (unitWindow (windowStep (n:=n+1) x k))
      have hlo := hk.2.trans (oldest_distance_leastGain V hk.1)
      have hs (i : Fin (n+1)) : windowStep x k i≠0 := by
        intro hz
        apply windowMatrix_step_ne_zero (unitWindow (windowStep x k)) hk.1 i
        simp only [unitWindow,rescaleWindow,hz,smul_zero]
      have hu := Metric.infDist_le_dist_of_mem (s:=(newerColumnSpan V:Set _))
        (x:=euclideanColumn V 0) (newerColumnSpan V).zero_mem
      have hn : ‖euclideanColumn V 0‖=1 := unitWindow_norm _ hs 0
      exact ⟨hlo,by simpa only [slidingOldestDistance,V,dist_zero_right,hn] using hu⟩
    have hsup := ss1Sequence_superlinear G H S hS h₀ hnbhd hH hH₀ hG hG₀ seed hconv hσ hind
    obtain ⟨theta,htheta,he⟩ := oldest_multiplicative_factor (fun k=>‖x k‖) (fun k=>‖x (k+1)‖)
      (slidingOldestDistance x) (fun _=>1) r hσ hLpos (fun _=>norm_nonneg _) hD tendsto_const_nhds hsup.norm_left hr
    refine ⟨theta,htheta,?_⟩
    filter_upwards [hbnd,he] with k hk hek
    simp only [one_mul] at hek
    rw [hek] at hk
    convert hk using 1
    ring

end
end krylov.Convergence
