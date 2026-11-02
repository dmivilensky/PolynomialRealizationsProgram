import jacobi.Variational.Transfer
import jacobi.RootMass.Calibration
import jacobi.Keller.Calibration
import jacobi.Elliptic.ExactValue

/-!
Article: jacobi, Theorem 3.2.
The actual lower constant is the printed maximum of all four original
calibrations, including the full Fredholm and root-mass suprema. The
already proved general Transfer theorem gives its complete finite-fibre
lower bound, independently of Bessel theory and the finite candidate.
Use: rootCalibrationValue selects the unique actual positive quadrature root in the original full root-mass lower calibration.
-/
namespace jacobi.Variational
noncomputable section
open Real Set Filter
open scoped Topology ENNReal

/-- The true second moment of every original edge spectrum is positive.
Use: rootCalibrationValue selects the unique actual positive quadrature
root in the original full root-mass lower calibration.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: the positive first squared entry contributes to its genuinely
summable series of nonnegative squared eigenvalues. -/
theorem EdgeSpectrum.second_pos (Λ:EdgeSpectrum) : 0<Λ.second := by
  have hs := jacobi.Continuum.summable_powers Λ.summable (fun k => (Λ.positive k).le) (by decide : 0<2)
  exact (sq_pos_of_pos (Λ.positive 0)).trans_le (hs.le_tsum 0 (fun k _ => sq_nonneg _))

/-- The genuine original root-mass quadrature lower value at the unique
positive root for the actual edge spectrum.
Use: lowerConstant takes the full printed supremum over b and eta.
Article: jacobi, Section 3.2 (sharp comparison at U).
-/
def rootCalibrationValue (Λ:EdgeSpectrum) (b eta:ℝ) (hb:0<b) (heta:-(34/5:ℝ)≤eta) : ℝ :=
  jacobi.RootMass.ellH (eta/2) b Λ.mass (by linarith)
    (jacobi.RootMass.parameter (eta/2) b Λ.second (by linarith) hb Λ.second_pos)

/-- The actual printed lower constant combines all four original
analytic calibrations, retaining both complete parameter suprema.
Use: lowerConstant_transfer supplies precisely the lower side of
Theorem 4.1 after specialization to the actual Bessel spectrum.
Article: jacobi, Theorem 3.2.
-/
def lowerConstant (Λ:EdgeSpectrum) : ℝ≥0∞ :=
  max (max (relaxedInfimum {Observation.second} Λ.mass (threshold Λ))
    (jacobi.Keller.Kel (Λ.value 0) Λ.mass))
    (max (⨆s:{s:ℝ // 0<s ∧ s<1/Λ.value 0},fredholmInfimum s.val Λ.mass (Λ.fredholm s.val))
      (⨆p:{p:ℝ×ℝ // 0<p.1 ∧ -(34/5:ℝ)≤p.2},
        ENNReal.ofReal (rootCalibrationValue Λ p.val.1 p.val.2 p.property.1 p.property.2)))

/-- The complete printed lower constant bounds the actual finite-fibre
lower limiting optimal energy for every genuine limiting edge spectrum.
Use: Bessel specialization and the actual persymmetric energy limit
give all of the two-sided inequality of Theorem 4.1.
Article: jacobi, Theorem 4.1.
Proof: general Transfer bounds the original root and root-free moment
relaxations and every original Fredholm relaxation. The proved actual
root calibration bounds each quadrature value by the root-constrained
second-moment infimum. Taking both full suprema and the printed maximum
therefore preserves the same actual finite-fibre lower bound. -/
theorem lowerConstant_transfer (N:ℕ→ℕ) (S:∀n,jacobi.Finite.Nodes (N n)) (hN:∀n,0<N n)
    (hNlim:Tendsto N atTop atTop) (Λ:EdgeSpectrum)
    (hd:Tendsto (fun n => distance (jacobi.Packing.fibreSpectrum (S n)) Λ.value) atTop (𝓝 0)) :
    lowerConstant Λ≤liminf (fun n => fibreEnergyInfimum (S n)) atTop := by
  -- All four bounds concern the same original fibres and the same limiting edge spectrum.
  obtain ⟨hm,hF⟩ := fibre_transfer N S hN hNlim Λ hd
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
      exact (jacobi.RootMass.root_calibration (a:=p.val.2/2) (by linarith [p.property.2])
        p.property.1 (threshold Λ) Λ.second_pos).trans (hm {Observation.second})

end
end jacobi.Variational
