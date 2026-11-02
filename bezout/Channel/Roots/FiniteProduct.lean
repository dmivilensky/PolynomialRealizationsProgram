import bezout.Channel.Roots.Actual
import bezout.Probability.SignPermutation

/-!
Article: bezout, Proposition D.1, finite commuting-channel root-step products.
Use: the terminal of the actual oracle iteration equals the full random
multiplier, not merely its first variation. Paired reordering preserves every
sample, and iid reindexing preserves its entire terminal distribution.
Proof: induct on the executed physical current register; commutative products
then erase the chronological order of paired roots and channel values.
-/

namespace bezout.Channel.Roots
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators Matrix
open bezout.Algorithms bezout.Comparisons.Competitors

/-- The full finite-noise scalar multiplier on one actual spectral mode. -/
def finiteMultiplier {N : ℕ} (α : Fin N → ℝ) (lam δ : ℝ) (ξ : Fin N → ℝ) : ℝ :=
  ∏ s, (1-α s*lam-δ*α s*ξ s)

/-- A genuinely time-varying commuting channel oracle in spectral coordinates. -/
def modeOracle {ι : Type*} {N : ℕ} (eig : ι → ℝ) (δ : ℝ) (ξ : Fin N → ℝ) :
    Fin N → (ι → ℝ) → (ι → ℝ) := fun s y j => (eig j+δ*ξ s)*y j

/-- The current physical register equals its finite product after every executed prefix. -/
theorem modePrefix_product {ι : Type*} {N : ℕ} (α : Fin N → ℝ) (eig : ι → ℝ)
    (δ : ℝ) (ξ : Fin N → ℝ) (initial : ι → ℝ) (k : ℕ) (hk : k≤N) (j : ι) :
    ((((Stepsize.config (extend α)).program N).runPrefix (modeOracle eig δ ξ) initial k).vectors 0) j =
      (∏ s ∈ Finset.range k, (1-extend α s*(eig j+δ*extend ξ s)))*initial j := by
  induction k with
  | zero => simp [RegisterProgram.runPrefix,RegisterProgram.initialState,Momentum.program,Stepsize.config]
  | succ k ih =>
    have hkN : k<N := by omega
    let old := ((Stepsize.config (extend α)).program N).runPrefix (modeOracle eig δ ξ) initial k
    have hv : old.vectors=![old.vectors 0,old.vectors 1,old.vectors 2] := by
      ext r
      fin_cases r <;> rfl
    have hs := (Stepsize.config (extend α)).stage_vectors N ⟨k,hkN⟩ (modeOracle eig δ ξ)
      (old.vectors 0) (old.vectors 1) (old.vectors 2) old.calls
    rw [← hv] at hs
    change (((Stepsize.config (extend α)).program N).stage (modeOracle eig δ ξ) ⟨k,hkN⟩ old).vectors=_ at hs
    rw [RegisterProgram.runPrefix,dite_eq_left hkN]
    change ((((Stepsize.config (extend α)).program N).stage (modeOracle eig δ ξ) ⟨k,hkN⟩ old).vectors 0) j=_
    rw [hs]
    simp only [Stepsize.config,Momentum.query,Bool.false_eq_true,ite_false,
      zero_smul,sub_zero,Matrix.cons_val_zero,Pi.sub_apply,
      Pi.smul_apply,smul_eq_mul,modeOracle,add_zero,one_mul]
    change (old.vectors 0) j-extend α k*((eig j+δ*ξ ⟨k,hkN⟩)*(old.vectors 0) j)=_
    have hi := ih (by omega)
    change (old.vectors 0) j=_ at hi
    rw [hi,Finset.prod_range_succ]
    simp only [extend, hkN,dite_true]
    ring

/-- The full finite product is the actual terminal, for every channel stream and mode family. -/
theorem history_mode_product {ι : Type*} {N : ℕ} (α : Fin N → ℝ) (eig : ι → ℝ)
    (δ : ℝ) (ξ : Fin N → ℝ) (initial : ι → ℝ) :
    (history α).oracleOutput initial (modeOracle eig δ ξ) =
      fun j => finiteMultiplier α (eig j) δ ξ*initial j := by
  rw [history,Stepsize.history,← Momentum.output_eq_history]
  ext j
  change ((((Stepsize.config (extend α)).program N).runPrefix (modeOracle eig δ ξ) initial N).vectors 0) j=_
  rw [modePrefix_product α eig δ ξ initial N le_rfl j,Finset.prod_range]
  unfold finiteMultiplier
  congr 1
  apply Finset.prod_congr rfl
  intro s _
  simp only [extend_fin]
  ring

/-- Paired reordering of steps and channel samples preserves every finite multiplier. -/
theorem finiteMultiplier_paired_permute {N : ℕ} (α : Fin N → ℝ) (lam δ : ℝ)
    (ξ : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    finiteMultiplier (α ∘ e) lam δ (ξ ∘ e)=finiteMultiplier α lam δ ξ :=
  Equiv.prod_comp e (fun s => 1-α s*lam-δ*α s*ξ s)

/-- Reordering only the root steps is equivalent to oppositely reordering the finite channel. -/
theorem finiteMultiplier_permute {N : ℕ} (α : Fin N → ℝ) (lam δ : ℝ)
    (ξ : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    finiteMultiplier (α ∘ e) lam δ ξ=finiteMultiplier α lam δ (ξ ∘ e.symm) := by
  have h := finiteMultiplier_paired_permute α lam δ (ξ ∘ e.symm) e
  simpa only [Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] using h

/-- The actual terminal vector is samplewise invariant under paired root/channel permutations. -/
theorem history_mode_paired_permute {ι : Type*} {N : ℕ} (α : Fin N → ℝ) (eig : ι → ℝ)
    (δ : ℝ) (ξ : Fin N → ℝ) (initial : ι → ℝ) (e : Equiv.Perm (Fin N)) :
    (history (α ∘ e)).oracleOutput initial (modeOracle eig δ (ξ ∘ e))=
      (history α).oracleOutput initial (modeOracle eig δ ξ) := by
  simp only [history_mode_product,finiteMultiplier_paired_permute]

/-- The entire actual finite-noise terminal distribution is root-order invariant. -/
theorem terminal_distribution_permute {ι : Type*} [MeasurableSpace (ι → ℝ)] {N : ℕ}
    (α : Fin N → ℝ) (eig : ι → ℝ) (δ : ℝ) (initial : ι → ℝ) (e : Equiv.Perm (Fin N)) :
    Measure.map (fun ω : Fin N → Bool => (history (α ∘ e)).oracleOutput initial
      (modeOracle eig δ (fun s => Probability.SignProducts.sign s ω))) (Probability.Signs.law N)=
    Measure.map (fun ω : Fin N → Bool => (history α).oracleOutput initial
      (modeOracle eig δ (fun s => Probability.SignProducts.sign s ω))) (Probability.Signs.law N) := by
  let f : (Fin N → Bool) → (ι → ℝ) := fun ω => (history α).oracleOutput initial
    (modeOracle eig δ (fun s => Probability.SignProducts.sign s ω))
  have he : (fun ω : Fin N → Bool => (history (α ∘ e)).oracleOutput initial
      (modeOracle eig δ (fun s => Probability.SignProducts.sign s ω)))=
      fun ω => f (Probability.SignProducts.permute e.symm ω) := by
    funext ω
    simp only [history_mode_product,finiteMultiplier_permute,f]
    rfl
  rw [he]
  exact Probability.SignProducts.map_permute e.symm f (measurable_of_finite f)

/-- Every iid sign law, including biased signs, is invariant under temporal reindexing. -/
theorem iid_measurePreserving_permute {N : ℕ} (ν : Measure Bool) [IsProbabilityMeasure ν]
    (e : Equiv.Perm (Fin N)) :
    MeasurePreserving (Probability.SignProducts.permute e)
      (Measure.pi (fun _ : Fin N => ν)) (Measure.pi (fun _ : Fin N => ν)) := by
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin N => Bool) e.symm :
      (Fin N → Bool) → (Fin N → Bool)) = Probability.SignProducts.permute e := by
    funext ω s
    have h := MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : Fin N => Bool) ω (e s)
    simpa only [Equiv.symm_apply_apply,Probability.SignProducts.permute] using h
  simpa only [he] using measurePreserving_piCongrLeft (fun _ : Fin N => ν) e.symm

/-- Root ordering preserves the actual finite terminal law for an arbitrary iid sign source. -/
theorem terminal_distribution_iid {ι : Type*} [MeasurableSpace (ι → ℝ)] {N : ℕ}
    (α : Fin N → ℝ) (eig : ι → ℝ) (δ : ℝ) (initial : ι → ℝ)
    (ν : Measure Bool) [IsProbabilityMeasure ν] (e : Equiv.Perm (Fin N)) :
    Measure.map (fun ω : Fin N → Bool => (history (α ∘ e)).oracleOutput initial
      (modeOracle eig δ (fun s => Probability.SignProducts.sign s ω)))
        (Measure.pi (fun _ : Fin N => ν))=
    Measure.map (fun ω : Fin N → Bool => (history α).oracleOutput initial
      (modeOracle eig δ (fun s => Probability.SignProducts.sign s ω)))
        (Measure.pi (fun _ : Fin N => ν)) := by
  let f : (Fin N → Bool) → (ι → ℝ) := fun ω => (history α).oracleOutput initial
    (modeOracle eig δ (fun s => Probability.SignProducts.sign s ω))
  have he : (fun ω : Fin N → Bool => (history (α ∘ e)).oracleOutput initial
      (modeOracle eig δ (fun s => Probability.SignProducts.sign s ω)))=
      fun ω => f (Probability.SignProducts.permute e.symm ω) := by
    funext ω
    simp only [history_mode_product,finiteMultiplier_permute,f]
    rfl
  rw [he]
  change Measure.map (f ∘ Probability.SignProducts.permute e.symm) _ = _
  rw [← Measure.map_map (measurable_of_finite f) (iid_measurePreserving_permute ν e.symm).measurable,
    (iid_measurePreserving_permute ν e.symm).map_eq]

end
end bezout.Channel.Roots
