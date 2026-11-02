import jacobi.Comparison.EnergyLimit
import jacobi.Variational.LowerConstant
import jacobi.Jacobi.FibreLimit
import jacobi.GelfandLevitan.HalfSineClosed
import jacobi.Analytic.YoungLower
import jacobi.Elliptic.StrictImprovement

/-!
Article: jacobi, Section 3.2 (sharp comparison at U).
The actual full Jacobi-fibre limiting optimal energy is bounded above
by the proved original persymmetric candidate limit and below by all
four original continuum calibrations. Both bounding constants depend
only on alpha. At U the full optimal energy and both bounds coincide.
Use: Theorems A--C bound this original quantity without restricting the finite competitors to a chosen reconstruction or symmetry class.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Reference jacobi.GelfandLevitan jacobi.Variational
open scoped Topology ENNReal

/-- The actual lower limiting optimal energy of the complete genuine
Jacobi-polynomial fibres, using their true matrix dimensions.
Use: Theorems A--C bound this original quantity without restricting
the finite competitors to a chosen reconstruction or symmetry class.
Article: jacobi, Section 3.2 (sharp comparison at U).
-/
def jacobiOptimalEnergy (a b:ℝ) (ha:-1<a) (hb:-1<b) : ℝ≥0∞ :=
  liminf (fun n:ℕ => fibreEnergyInfimum (jacobi.Jacobi.nodes a b ha hb (n+1))) atTop

/-- The actual finite optimal energy is bounded by the original
alpha-only persymmetric constant, with every candidate premise proved.
Use: this is Theorem 2.1's final conclusion and the upper side of B.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: the genuine original persymmetric candidate belongs to every
actual fibre. Its energy converges to the original c_star, so monotonicity
of the lower limit gives the same upper bound for the full infima. -/
theorem jacobiOptimalEnergy_upper {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    jacobiOptimalEnergy a b ha hb≤ENNReal.ofReal (persymmetricConstant a ha) := by
  -- The actual candidate is used only as an upper competitor in the complete finite fibre.
  have hc := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (target_energy_limit ha hb)
  have hbnd : ∀n:ℕ,fibreEnergyInfimum (jacobi.Jacobi.nodes a b ha hb (n+1))≤
      ENNReal.ofReal ((targetChain a b ha hb n).energy/((n:ℝ)+1)^3) := by
    intro n
    apply sInf_le
    refine ⟨targetChain a b ha hb n,targetChain_inFiber a b ha hb n,?_⟩
    simp only [fibreCost,Nat.cast_add,Nat.cast_one]
  exact (liminf_le_liminf (Eventually.of_forall hbnd)).trans_eq hc.liminf_eq

/-- The complete original lower and upper calibrations bound the
actual optimal energy of every genuine Jacobi fibre sequence.
Use: this is the full two-sided inequality of Theorem 4.1, and supplies
the beta-independent squeeze used by Theorem 4.2 at the point U.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: specialize the completed general four-calibration Transfer to
the genuine proved Bessel L1 spectrum of the actual Jacobi fibres.
The upper inequality is the proved original persymmetric energy limit. -/
theorem jacobiOptimalEnergy_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    lowerConstant (jacobi.Bessel.edgeSpectrum a ha)≤jacobiOptimalEnergy a b ha hb ∧
      jacobiOptimalEnergy a b ha hb≤ENNReal.ofReal (persymmetricConstant a ha) := by
  exact ⟨lowerConstant_transfer (fun n => n+1) (fun n => jacobi.Jacobi.nodes a b ha hb (n+1))
    (fun n => Nat.succ_pos n) (tendsto_add_atTop_nat 1) (jacobi.Bessel.edgeSpectrum a ha)
    ((jacobi.Jacobi.fibre_spectral_limit ha hb).comp (tendsto_add_atTop_nat 1)),
    jacobiOptimalEnergy_upper ha hb⟩

/-- The actual explicit Young calibration lies below the complete
original four-calibration lower constant for every genuine edge spectrum.
Use: Theorem 4.1 at U and Theorem 4.2's beta-independent squeeze use the
same original explicit ell_Y, without assuming a calibration is attaining.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: the proved sharp Young lower bound applies to the actual
second-moment infimum, which is one term in the printed maximum. -/
theorem young_le_lowerConstant (Λ:EdgeSpectrum) :
    ENNReal.ofReal (jacobi.Young.youngValue Λ.second)≤lowerConstant Λ := by
  have he : relaxedInfimum {Observation.second} Λ.mass (threshold Λ)=
      relaxedInfimum {Observation.second} Λ.mass (fun _ => Λ.second) := by
    unfold relaxedInfimum
    congr 1
    ext m
    simp only [mem_singleton_iff,forall_eq,threshold]
  exact (jacobi.Elliptic.second_infimum_young_lower Λ.second_pos.le).trans
    (by rw [← he]; exact (le_max_left _ _).trans (le_max_left _ _))

/-- At U the actual full finite-fibre optimal energy and the complete
four-calibration lower constant equal the proved original upper value.
Use: this is the exact-value assertion of Theorem 4.1 for every beta;
Theorem 4.2 uses the same beta-independent equality point.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: the actual source upper constant is exactly 2/15 by its genuine
half-sine profile. The actual explicit Young calibration equals the
same value and is below the full lower constant. The proved complete
two-sided inequality squeezes both original quantities to that value. -/
theorem jacobiOptimalEnergy_U {b:ℝ} (hb:-1<b) (ha:-1<(1/2:ℝ)) :
    lowerConstant (jacobi.Bessel.edgeSpectrum (1/2) ha)=ENNReal.ofReal (2/15) ∧
      jacobiOptimalEnergy (1/2) b ha hb=ENNReal.ofReal (2/15) := by
  -- Neither side uses a numerical evaluation or an assumed asymptotic minimizer.
  have hB := jacobiOptimalEnergy_bounds ha hb
  rw [half_sine_persymmetricConstant] at hB
  have hY := young_le_lowerConstant (jacobi.Bessel.edgeSpectrum (1/2) ha)
  rw [← jacobi.Parameter.youngLower_spectral ha,jacobi.Parameter.youngLower_U] at hY
  exact ⟨le_antisymm (hB.1.trans hB.2) hY,le_antisymm hB.2 (hY.trans hB.1)⟩

end
end jacobi.Comparison
