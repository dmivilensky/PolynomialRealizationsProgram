import krylov.Envelope.FirstJets

/-!
Article: main_krylov, apB:lem:filtration, true observed first-jet subspaces.
Use: encode reference-value and derivative-modulo-K coherence as an actual
linear subspace of vector/derivative pairs; primitive smooth coefficients
then preserve that real subspace by the genuine derivative product rule.
Source: finite observed scalar-vector differentiation and actual linear
subspace closure, without a presumed method response or expansion.
-/

namespace krylov.Envelope
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- The true linear space of vector/derivative pairs compatible with the given actual reference flag and linear derivative lift.
Use: The true linear space of vector/derivative pairs compatible with the given actual reference flag and linear derivative lift.
Article: main_krylov, apB:lem:filtration, true observed first-jet subspaces.
Proof: Both the real reference vector and its genuine derivative remainder lie in the actual flag. -/
def jetSubspace (K : Submodule ℝ E) (L : E →ₗ[ℝ] E) : Submodule ℝ (E × E) where
  carrier := {v | v.1∈K ∧ v.2-L v.1∈K}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    refine ⟨K.add_mem hv.1 hw.1,?_⟩
    change v.2+w.2-L (v.1+w.1)∈K
    rw [map_add]
    convert K.add_mem hv.2 hw.2 using 1;abel
  smul_mem' := by
    intro c v hv
    refine ⟨K.smul_mem c hv.1,?_⟩
    change c • v.2-L (c • v.1)∈K
    rw [map_smul,← smul_sub]
    exact K.smul_mem c hv.2

/-- Changing only a genuine observed scalar coefficient contributes an admissible actual vertical first jet.
Use: Changing only a genuine observed scalar coefficient contributes an admissible actual vertical first jet.
Article: main_krylov, apB:lem:filtration, true observed first-jet subspaces.
Proof: The true zero reference vector has zero lifted derivative, and its actual coefficient derivative multiplies a vector in the genuine reference flag. -/
theorem jetSubspace_vertical (K : Submodule ℝ E) (L : E →ₗ[ℝ] E) {v : E} (hv : v∈K) :
    ((0,v) : E × E)∈jetSubspace K L := by
  change 0∈K ∧ v-L 0∈K
  simpa only [map_zero,sub_zero] using And.intro K.zero_mem hv

/-- Genuine first-jet coherence persists under an actual flag enlargement with a truly compatible earlier derivative lift.
Use: Genuine first-jet coherence persists under an actual flag enlargement with a truly compatible earlier derivative lift.
Article: main_krylov, apB:lem:filtration, true observed first-jet subspaces.
Proof: Transfer both actual reference membership and the true derivative remainder through the proved subspace inclusion. -/
theorem jetSubspace_mono {K K' : Submodule ℝ E} {L L' : E →ₗ[ℝ] E}
    (hK : K ≤ K') (hL : ∀ v∈K, L' v=L v) : jetSubspace K L ≤ jetSubspace K' L' := by
  intro v hv
  refine ⟨hK hv.1,?_⟩
  rw [hL v.1 hv.1]
  exact hK hv.2

/-- Every real smooth finite observed-vector coefficient decision preserves the genuine first-jet subspace of its actual observations.
Use: Every real smooth finite observed-vector coefficient decision preserves the genuine first-jet subspace of its actual observations.
Article: main_krylov, apB:lem:filtration, true observed first-jet subspaces.
Proof: Differentiate the actual finite scalar-vector decision. Its true first jet is the sum of the actual observation jets weighted by reference coefficients and the admissible genuine vertical jets weighted by scalar derivatives. -/
theorem observed_combination_jet (K : Submodule ℝ E) (L : E →ₗ[ℝ] E)
    (c : ι → ℝ → ℝ) (v : ι → ℝ → E) (dc : ι → ℝ) (dv : ι → E) (t : ℝ)
    (hc : ∀ i, HasDerivAt (c i) (dc i) t) (hv : ∀ i, HasDerivAt (v i) (dv i) t)
    (hjet : ∀ i, (v i t,dv i)∈jetSubspace K L) :
    ((∑ i, c i t • v i t),deriv (fun x => ∑ i, c i x • v i x) t)∈jetSubspace K L := by
  -- The actual product-rule jet is a sum of genuine observation jets and coefficient-derivative vertical jets.
  rw [(hasDerivAt_observedCombination c v dc dv t hc hv).deriv]
  have he : ((∑ i, c i t • v i t),(∑ i, (c i t • dv i+dc i • v i t)))=
      ∑ i, (c i t • ((v i t,dv i) : E × E)+dc i • ((0,v i t) : E × E)) := by
    apply Prod.ext <;> simp [Prod.fst_sum,Prod.snd_sum]
  rw [he]
  exact (jetSubspace K L).sum_mem fun i _ => (jetSubspace K L).add_mem
    ((jetSubspace K L).smul_mem _ (hjet i))
    ((jetSubspace K L).smul_mem _ (jetSubspace_vertical K L (hjet i).1))
end
end krylov.Envelope
