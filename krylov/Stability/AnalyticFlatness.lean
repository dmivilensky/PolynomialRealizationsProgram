import krylov.Stability.CompactAnalytic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
Article: main_krylov, lem:U and thm:C, identification of compact remainder jets.
Use: upgrade proved pointwise remainder orders to compact-uniform orders
once genuine joint analyticity has been established in the original variables.
Source: mathlib's uniqueness of homogeneous analytic coefficients and actual
iterated Fréchet derivatives, followed by the existing compact Taylor tube.
-/

namespace krylov.Stability
noncomputable section
open Filter Asymptotics Topology Finset
variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A proved order-r analytic remainder has every genuine diagonal coefficient below r equal to zero.
Use: identify vanishing Taylor jets from actual remainder bounds, without assuming those jets.
Article: main_krylov, lem:U and thm:C, uniqueness of the actual leading expansion.
Source: mathlib Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero.
Proof: induct through the actual analytic partial sums. Previously vanishing
coefficients leave only the current homogeneous term; the true analytic
remainder and the given order bound put it one order above its degree.
The proved homogeneous uniqueness theorem forces its diagonal to vanish.
-/
theorem analytic_diagonal_zero_of_order (f : P → F) (p : FormalMultilinearSeries ℝ P F)
    (hp : HasFPowerSeriesAt f p 0) (r : ℕ)
    (hf : f =O[𝓝 (0 : P)] (fun z => ‖z‖^r)) :
    ∀ j<r, ∀ z, p j (fun _ => z)=0 := by
  -- Remove only coefficients whose vanishing has already been proved.
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj z
    have hsum (y : P) : p.partialSum (j+1) y=p j (fun _ => y) := by
      apply sum_eq_single j
      · intro i hi hij
        have hlt : i<j := by have := mem_range.mp hi; omega
        exact ih i hlt (hlt.trans hj) y
      · intro hnot
        exact False.elim (hnot (mem_range.mpr (by omega)))
    have hpow : (fun y : P => ‖y‖^r) =O[𝓝 0] (fun y => ‖y‖^(j+1)) := by
      rcases eq_or_lt_of_le (by omega : j+1≤r) with he | he
      · rw [he]
      · exact (isLittleO_norm_pow_norm_pow he).isBigO
    have htail : (fun y : P => f y-p j (fun _ => y)) =O[𝓝 0] (fun y => ‖y‖^(j+1)) := by
      simpa only [zero_add,hsum] using hp.isBigO_sub_partialSum_pow (j+1)
    have hterm : (fun y : P => p j (fun _ => y)) =O[𝓝 0] (fun y => ‖y‖^(j+1)) := by
      simpa only [sub_sub_cancel] using (hf.trans hpow).sub htail
    exact hterm.continuousMultilinearMap_apply_eq_zero z

variable {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace F]

/-- A jointly analytic remainder with a proved order-r fibre has zero true Taylor polynomial along every perturbation direction below that order.
Use: connect pointwise source expansions with the actual derivatives used by compact Taylor estimates.
Article: main_krylov, lem:U and thm:C, identification of the scenario Taylor jet.
Proof: translate the genuine joint series to zero and restrict it through
the actual perturbation inclusion. The proved fibre order annihilates its
diagonal coefficients. The actual factorial/iterated-derivative identity
then annihilates every term of the true perturbation Taylor polynomial.
-/
theorem analytic_fibre_taylor_zero (f : R × P → F) (x : R) (r : ℕ)
    (ha : AnalyticAt ℝ f (x,0))
    (hf : (fun z : P => f (x,z)) =O[𝓝 0] (fun z => ‖z‖^r)) (z : P) :
    taylorPolynomial f r (x,0) (0,z)=0 := by
  -- Restrict the actual joint power series, rather than introducing a separate jet premise.
  obtain ⟨p,hp⟩ := ha
  have hs : HasFPowerSeriesAt (fun q : R × P => f ((x,0)+q)) p 0 := by
    simpa only [add_neg_cancel,sub_neg_eq_add,add_comm] using hp.comp_sub (-(x,0))
  let u := ContinuousLinearMap.inr ℝ R P
  have hu : HasFPowerSeriesAt (fun z : P => f (x,z)) (p.compContinuousLinearMap u) 0 := by
    simpa only [u,Function.comp_def,ContinuousLinearMap.inr_apply,map_zero,
      Prod.add_def,add_zero,zero_add] using hs.compContinuousLinearMap (u := u) (x := (0 : P))
  have hz := analytic_diagonal_zero_of_order _ _ hu r hf
  obtain ⟨ρ,hball⟩ := hp
  apply sum_eq_zero
  intro j hj
  have hcoeff : p j (fun _ => (0,z))=0 := by
    simpa only [FormalMultilinearSeries.compContinuousLinearMap_apply,Function.comp_def,
      u,ContinuousLinearMap.inr_apply] using hz j (mem_range.mp hj) z
  rw [← hball.factorial_smul (0,z) j,hcoeff,nsmul_zero,smul_zero]

variable [ProperSpace R] [ProperSpace P]

/-- Genuine joint analyticity and proved pointwise fibre orders give a single compact-uniform remainder radius and constant.
Use: no uniform remainder or vanishing-jet hypothesis is added to the original source scenarios.
Article: main_krylov, lem:U and thm:C, compact-uniform higher-order remainders.
Proof: the actual compact analytic Taylor tube supplies common constants.
The preceding theorem identifies every genuine perturbation Taylor term
as zero from the proved pointwise order. The product norm of (0,z) is ‖z‖,
so the same common bound holds in the original perturbation norm.
-/
theorem compact_analytic_flat_fibres (f : R × P → F) (K : Set R) (hK : IsCompact K)
    (r : ℕ) (hr : 0<r) (ha : ∀ x∈K, AnalyticAt ℝ f (x,0))
    (hf : ∀ x∈K, (fun z : P => f (x,z)) =O[𝓝 0] (fun z => ‖z‖^r)) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ z : P, ‖z‖≤δ → ‖f (x,z)‖≤C*‖z‖^r := by
  -- One actual compact analytic tube covers every reference and every scenario direction.
  let L := (fun x : R => (x,(0 : P))) '' K
  have hL : IsCompact L := hK.image (continuous_id.prodMk continuous_const)
  have hLa : ∀ q∈L, AnalyticAt ℝ f q := by
    rintro _ ⟨x,hx,rfl⟩
    exact ha x hx
  obtain ⟨δ,C,hδ,hC,hT⟩ := compact_analytic_taylor f L hL hLa r
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx z hz
  have ht := hT (x,0) ⟨x,hx,rfl⟩ (0,z)
    (by simpa only [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg z)] using hz) r hr le_rfl
  rw [analytic_fibre_taylor_zero f x r (ha x hx) (hf x hx) z] at ht
  simpa only [Prod.add_def,add_zero,zero_add,sub_zero,Prod.norm_def,norm_zero,
    max_eq_right (norm_nonneg z)] using ht

/-- The compact analytic fibre remainder retains any genuine positive continuous reference weight.
Use: preserve the source initial-error normalization in the same common higher-order tube.
Article: main_krylov, lem:U and thm:C, weighted compact-uniform cubic remainder.
Proof: apply the existing weighted compact reference Taylor theorem on the
actual open analytic locus. The true perturbation Taylor polynomial vanishes
by the proved pointwise order, giving the weighted estimate directly.
-/
theorem compact_analytic_flat_weighted_fibres (f : R × P → F) (K : Set R) (hK : IsCompact K)
    (r : ℕ) (hr : 0<r) (ha : ∀ x∈K, AnalyticAt ℝ f (x,0))
    (hf : ∀ x∈K, (fun z : P => f (x,z)) =O[𝓝 0] (fun z => ‖z‖^r))
    (e : R → ℝ) (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ z : P, ‖z‖≤δ → ‖f (x,z)‖≤C*‖z‖^r*e x := by
  -- The actual weighted compact Taylor tube precedes the vanishing-jet identification.
  obtain ⟨δ,C,hδ,hC,hT⟩ := compact_reference_taylor f e r {q | AnalyticAt ℝ f q} K
    (isOpen_analyticAt ℝ f) hK ha (fun _ hq => hq.contDiffAt.contDiffWithinAt) he hepos
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx z hz
  have ht := hT x hx z hz r hr le_rfl
  rw [analytic_fibre_taylor_zero f x r (ha x hx) (hf x hx) z,sub_zero] at ht
  exact ht

end
end krylov.Stability
