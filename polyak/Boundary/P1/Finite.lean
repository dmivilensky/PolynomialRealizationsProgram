import polyak.Boundary.P1.SmallLags
import polyak.Certificates.P1Slacks.Lag01Upper
import polyak.Certificates.P1Slacks.Lag02Lower
import polyak.Certificates.P1Slacks.Lag03Lower
import polyak.Certificates.P1Slacks.Lag04Lower
import polyak.Certificates.P1Slacks.Lag04Upper
import polyak.Certificates.P1Slacks.Lag05Lower
import polyak.Certificates.P1Slacks.Lag05Upper
import polyak.Certificates.P1Slacks.Lag06Lower
import polyak.Certificates.P1Slacks.Lag06Upper
import polyak.Certificates.P1Slacks.Lag07Lower
import polyak.Certificates.P1Slacks.Lag07Upper
import polyak.Certificates.P1Slacks.Lag08Lower
import polyak.Certificates.P1Slacks.Lag08Upper
import polyak.Certificates.P1Slacks.Lag09Lower
import polyak.Certificates.P1Slacks.Lag09Upper
import polyak.Certificates.P1Slacks.Lag10Lower
import polyak.Certificates.P1Slacks.Lag10Upper
import polyak.Certificates.P1Slacks.Lag11Lower
import polyak.Certificates.P1Slacks.Lag11Upper
import polyak.Certificates.P1Slacks.Lag12Lower
import polyak.Certificates.P1Slacks.Lag12Upper

/-! Article: all finite P1 lag signs, checked against the actual source formula. -/
noncomputable section
namespace polyak.Boundary.P1
open polyak.Certificates.P1Slacks

theorem scaledSlack_prefix_nonneg {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) (n : ℕ) (hn : 1≤n) (hN : n≤12)
    (σ : ℝ) (hs : σ= -1 ∨ σ=1) : 0≤scaledSlack n σ z a := by
  rcases hs with rfl | rfl
  · interval_cases n
    · rw [scaledSlack_one_lower]
    · exact (positive02Lower hz hz1 ha).le
    · exact (positive03Lower hz hz1 ha).le
    · exact (positive04Lower hz hz1 ha).le
    · exact (positive05Lower hz hz1 ha).le
    · exact (positive06Lower hz hz1 ha).le
    · exact (positive07Lower hz hz1 ha).le
    · exact (positive08Lower hz hz1 ha).le
    · exact (positive09Lower hz hz1 ha).le
    · exact (positive10Lower hz hz1 ha).le
    · exact (positive11Lower hz hz1 ha).le
    · exact (positive12Lower hz hz1 ha).le
  · interval_cases n
    · exact (positive01Upper hz hz1 ha).le
    · exact scaledSlack_two_upper_nonneg hz ha
    · rw [scaledSlack_three_upper]
    · exact (positive04Upper hz hz1 ha).le
    · exact (positive05Upper hz hz1 ha).le
    · exact (positive06Upper hz hz1 ha).le
    · exact (positive07Upper hz hz1 ha).le
    · exact (positive08Upper hz hz1 ha).le
    · exact (positive09Upper hz hz1 ha).le
    · exact (positive10Upper hz hz1 ha).le
    · exact (positive11Upper hz hz1 ha).le
    · exact (positive12Upper hz hz1 ha).le

theorem rawSlack_prefix_nonneg {z u a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) (hu : 0≤u) (h0 : quartic z u a=0)
    (n : ℕ) (hn : 1≤n) (hN : n≤12) (σ : ℝ) (hs : σ= -1 ∨ σ=1) :
    0≤rawSlack u (1/z) (chargeNumerator z u a) n σ a := by
  have hg := geometry_bounds hz hz1 ha
  exact rawSlack_nonneg_of_scaled hz hg.1 hu hg.2.2.2.le h0 n hn σ
    (scaledSlack_prefix_nonneg hz hz1 ha n hn hN σ hs)

/-- Full infinite feasibility: the finite signs and every n≥13 are discharged. -/
theorem feasibleU {z u t : ℝ} (a : Spectral.Frequency) (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤(a : ℝ) ∧ (a : ℝ)≤0) (hu : 0≤u) (hu1 : u≤1)
    (hgz : z/2≤1-(a : ℝ)^2-u^2) (h0 : quartic z u a=0)
    (ht : Real.cosh t=1/z) :
    Spectral.FeasibleU u t (spectrum a) (chargeNumerator z u a/Real.sinh t) :=
  feasibleU_of_raw_prefix a hz hz1 ha hu hu1 hgz h0 ht
    (rawSlack_prefix_nonneg hz hz1 ha hu h0)

/-- Exact boundary from the actual one-atom spectrum and actual quartic dual. -/
theorem optimal {z u t : ℝ} (a : Spectral.Frequency) (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤(a : ℝ) ∧ (a : ℝ)≤0) (hu : 0≤u) (hu1 : u≤1)
    (hgz : z/2≤1-(a : ℝ)^2-u^2) (h0 : quartic z u a=0)
    (h1 : quarticDerivative z u a=0)
    (hq : |residualLinear z u a|<residualConstant z u a)
    (ht : Real.cosh t=1/z) : Spectral.V t=Real.arsinh u :=
  optimal_of_raw_prefix a hz hz1 ha hu hu1 hgz h0 h1 hq ht
    (rawSlack_prefix_nonneg hz hz1 ha hu h0)

end polyak.Boundary.P1
