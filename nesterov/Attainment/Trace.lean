import nesterov.Attainment.CompactDual
import polyak.Spectral.NormalizedCertificate

/-! Exact physical traces of the compactified two-amplitude dual generators. -/
noncomputable section
open scoped Topology OnePoint
namespace nesterov.Attainment
open Spectral

def polynomialPair (u p : Polynomial ℝ) (t : ℝ) : SymbolPair :=
  ⟨StationaryMethod.circlePolynomial u t, StationaryMethod.circlePolynomial p t⟩

abbrev physicalAngle := polyak.Spectral.dualAngle

@[simp] theorem compactifiedKernels_coe (lo hi : ℝ) (hlo : 0 < lo) (n : ℕ) :
    compactifiedKernels lo hi hlo (n : OnePoint ℕ) =
      (cosineKernelMap lo hi hlo n, sineKernelMap lo hi hlo n) := rfl

@[simp] theorem compactifiedKernels_infty (lo hi : ℝ) (hlo : 0 < lo) :
    compactifiedKernels lo hi hlo ∞ = (1,0) := rfl

@[simp] theorem dualFamily_charge (lo hi : ℝ) (hlo : 0 < lo)
    (G S : C(LagDomain lo hi,ℂ)) (δ : ℝ) (l : OnePoint ℕ) :
    (dualFamily lo hi hlo G S δ l).1 = δ := rfl

theorem dualFamily_infty (lo hi : ℝ) (hlo : 0 < lo)
    (G S : C(LagDomain lo hi,ℂ)) (δ : ℝ) :
    dualFamily lo hi hlo G S δ ∞ = (δ,G) := by
  apply Prod.ext
  · rfl
  · ext q
    simp [dualFamily]

theorem gapEntireMap_physical (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) (c : Frequency) :
    gapEntireMap u p lo hi σ (s,physicalAngle lo hlo c) =
      (g (polynomialPair u p (σ*s)) c : ℂ) :=
  gapEntire_real u p (σ*s) (Real.arccos c)

theorem skewEntireMap_physical (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) (c : Frequency) :
    skewEntireMap u p lo hi σ (s,physicalAngle lo hlo c) =
      (skew (polynomialPair u p (σ*s)) c : ℂ) :=
  skewEntire_real u p (σ*s) (Real.arccos c)

theorem dualFamily_physical_infty (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (δ : ℝ) (s : LagParameter lo hi) (c : Frequency) :
    (dualFamily lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ) δ ∞).2
      (s,physicalAngle lo hlo c) = (g (polynomialPair u p (σ*s)) c : ℂ) := by
  rw [dualFamily_infty]
  exact gapEntireMap_physical u p lo hi σ hlo s c

theorem dualFamily_physical_coe (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (δ : ℝ) (s : LagParameter lo hi) (n : ℕ) (c : Frequency) :
    (dualFamily lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ)
      δ (n : OnePoint ℕ)).2 (s,physicalAngle lo hlo c) =
      (((lagA (polynomialPair u p (σ*s)) s (n+1) c -
        δ*lagB (polynomialPair u p (σ*s)) (n+1) c) /
          Real.sinh ((n+1 : ℕ)*s) : ℝ) : ℂ) := by
  change gapEntireMap u p lo hi σ (s,physicalAngle lo hlo c) * cosineKernel s n (Real.arccos c) -
    (2*δ) • (skewEntireMap u p lo hi σ (s,physicalAngle lo hlo c) *
      sineKernel s n (Real.arccos c)) = _
  rw [gapEntireMap_physical, skewEntireMap_physical,
    (kernels_eq_hyperbolic (hlo.trans_le s.property.1) n _).1,
    (kernels_eq_hyperbolic (hlo.trans_le s.property.1) n _).2]
  simp only [Complex.real_smul, lagA, lagB]
  push_cast
  ring

end nesterov.Attainment
