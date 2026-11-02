import jacobi.Variational.ClosedTransfer
import jacobi.Variational.LowerConstant

/-!
All calibrated lower bounds on the entire closed polynomial fibre.
The closed Transfer theorem constructs the same root-normalized continuum
competitors as the original transfer, so all four existing calibrations
apply without additional assumptions, including the root-mass bound.
Use: AllThreeTerm keeps only the homogeneous three branches when rescaling
the Nesterov edge spectrum by one quarter.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
Article role: the transferred lower bounds and the retained homogeneous lower constant.
-/
namespace jacobi.Variational
noncomputable section
open Real Set Filter
open scoped Topology ENNReal

/-- The three homogeneous branches of the calibrated lower bound.
The root-mass calibration is deliberately absent because amplitude scaling
changes its admissible set differently. This is the actual variational
quantity used in the Nesterov comparison, not a proposed numeric value.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
def homogeneousLowerConstant (Λ : EdgeSpectrum) : ℝ≥0∞ :=
  max (max (relaxedInfimum {Observation.second} Λ.mass (threshold Λ))
    (jacobi.Keller.Kel (Λ.value 0) Λ.mass))
    (⨆ s:{s:ℝ // 0<s ∧ s<1/Λ.value 0},fredholmInfimum s.val Λ.mass (Λ.fredholm s.val))

/-- Keeping three branches never increases the full four-branch constant.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem homogeneousLowerConstant_le (Λ : EdgeSpectrum) :
    homogeneousLowerConstant Λ≤lowerConstant Λ :=
  max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))

/-- The full calibrated lower constant transfers to the entire closed
fibre, including repeated endpoint roots, arbitrary restarts, all moment
constraints, the Fredholm supremum and the root-mass supremum.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem closed_lowerConstant_transfer (N : ℕ → ℕ) (S : ∀ n,jacobi.Finite.ClosedNodes (N n))
    (hN : ∀ n,0<N n) (hNlim : Tendsto N atTop atTop) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (jacobi.Finite.closedFibreSpectrum (S n)) Λ.value)
      atTop (𝓝 0)) :
    lowerConstant Λ≤liminf (fun n => closedFibreEnergyInfimum (S n)) atTop := by
  obtain ⟨hm,hF⟩ := closed_fibre_transfer N S hN hNlim Λ hd
  apply max_le
  · apply max_le
    · exact (relaxed_le_root _ _ _).trans (hm {Observation.second})
    · have he : jacobi.Keller.Kel (Λ.value 0) Λ.mass=
          relaxedInfimum {Observation.top} Λ.mass (threshold Λ) := by
        unfold jacobi.Keller.Kel relaxedInfimum
        congr 1
        ext m
        simp only [mem_singleton_iff,forall_eq,threshold]
      rw [he]
      exact (relaxed_le_root _ _ _).trans (hm {Observation.top})
  · apply max_le
    · exact iSup_le (fun s => (fredholm_le_root s.val Λ.mass (Λ.fredholm s.val)).trans
        (hF s.val s.property.1.le))
    · apply iSup_le
      intro p
      exact (jacobi.RootMass.root_calibration (a := p.val.2/2) (by linarith [p.property.2])
        p.property.1 (threshold Λ) Λ.second_pos).trans (hm {Observation.second})

end
end jacobi.Variational
