import krylov.OneGradient.SpectralPrior
import krylov.OneGradient.HeavyBallFibreDictionary
import krylov.OneGradient.JacobiCouplingNorm
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), actual sharp irreducible spectral family.
Use: construct true full-atom references in every fixed dimension at least
two, with genuine positive beta tending to zero and actual ratio tending to
the global spectral condition ratio.
Source: existing finite heavy-ball matrices, their proved original physical
fibre dictionary and real Schur endpoint limits; no abstract fibre is assumed.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix chebyshev1 krylov.Reference krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator

/-- A genuine member of the original spectral prior from the actual positive
irreducible heavy-ball family, with all physical support domains derived.
Use: the sharp construction remains in the original matrix/gradient class.
Article: main_krylov, s5:fibre(b).
Proof: reuse actual LDL positivity, first-site nonstagnation and full support. -/
def heavyBallSpectralReference (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (n : ℕ)
    (mu upper : ℝ) (hband : (heavyBallMatrix d q (n+2)-mu • 1).PosSemidef ∧
      (upper • 1-heavyBallMatrix d q (n+2)).PosSemidef) : SpectralPriorReference n mu upper where
  matrix := heavyBallMatrix d q (n+2)
  positive := heavyBallMatrix_posDef d q hd (n+2)
  gradient := WithLp.toLp 2 (JacobiData.site (n+2) 0)
  gradient_ne_zero := (heavyBall_information_domains d q hd hq (n+1)).1
  full_support := (heavyBall_information_domains d q hd hq (n+1)).2
  lower_band := hband.1
  upper_band := hband.2

/-- The actual original spectral-prior ratio on the real heavy-ball family
equals the genuine supplied-coordinate inverse Schur expression.
Use: transfer its proved scalar limit without substituting artificial data.
Article: main_krylov, s5:fibre(b).
Proof: apply the full physical endpoint and actual threshold dictionary. -/
theorem heavyBall_spectral_reference_ratio (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (n : ℕ)
    (mu upper : ℝ) (hband : (heavyBallMatrix d q (n+2)-mu • 1).PosSemidef ∧
      (upper • 1-heavyBallMatrix d q (n+2)).PosSemidef)
    (hlo : (heavyBallMatrix d q (n+1)-mu • 1).PosDef)
    (hhi : (upper • 1-heavyBallMatrix d q (n+1)).PosDef) :
    spectralPriorRatio (heavyBallSpectralReference d q hd hq n mu upper hband)=
      heavyBallFibreRatio d mu upper n q :=
  heavyBall_physical_fibre_ratio d q hd hq n
    (heavyBall_information_domains d q hd hq (n+1)).1
    (heavyBall_information_domains d q hd hq (n+1)).2 mu upper hlo hhi hband

/-- In every fixed physical dimension at least two, actual full-atom
spectral references have arbitrarily small positive genuine Lanczos coupling
and information ratio arbitrarily close to the global condition ratio.
Use: the sharp spectral supremum is approached by real irreducible references,
and the source's beta tends to zero, without a convergent-frame assumption.
Article: main_krylov, s5:fibre(b), sharpness as beta tends to zero.
Proof: choose the scalar pivot strictly between the prior endpoints. True
heavy-ball spectral windows remain inside the prior for small positive q.
Its original physical fibre ratio equals the proved inverse Schur ratio,
which tends to upper/mu. The actual positive physical coupling is bounded by
the original matrix's vanishing spectral distance from its scalar limit. -/
theorem spectral_fibre_sharp_references (mu upper : ℝ) (hmu : 0 < mu) (hmuL : mu < upper)
    (n : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ q : ℝ,0 < q ∧ q < epsilon ∧
      ∃ P : SpectralPriorReference n mu upper,
        P.matrix=heavyBallMatrix ((mu+upper)/2) q (n+2) ∧
        0 < spectralPriorCoupling P ∧ spectralPriorCoupling P < epsilon ∧
        upper/mu-epsilon < spectralPriorRatio P ∧ spectralPriorRatio P < upper/mu := by
  let d := (mu+upper)/2
  have hlow : mu < d := by dsimp only [d];linarith
  have hhigh : d < upper := by dsimp only [d];linarith
  have hd : 0 < d := hmu.trans hlow
  have hband := heavyBall_eventually_strict_band d mu upper hd hlow hhigh
  have hratio := (heavyBall_fibre_ratio_limit d mu upper hmu hlow hhigh n).eventually
    (Ioi_mem_nhds (show upper/mu-epsilon < upper/mu by linarith))
  have hM : ContinuousAt (fun q : ℝ => heavyBallMatrix d q (n+2)) 0 :=
    (heavyBall_matrix_contDiffAt d 0 (n+2) (r := 1)).continuousAt
  have hnorm := (hM.sub continuousAt_const).norm.eventually
    (Iio_mem_nhds (show ‖heavyBallMatrix d 0 (n+2)-d • 1‖ < epsilon by
      rw [heavyBall_matrix_zero,sub_self,norm_zero];exact hepsilon))
  have hevent : ∀ᶠ q : ℝ in nhds 0,0 < q →
      ∃ P : SpectralPriorReference n mu upper,
        P.matrix=heavyBallMatrix d q (n+2) ∧
        0 < spectralPriorCoupling P ∧ spectralPriorCoupling P < epsilon ∧
        upper/mu-epsilon < spectralPriorRatio P ∧ spectralPriorRatio P < upper/mu := by
    filter_upwards [hband,hratio,hnorm] with q hb hr hn
    intro hq
    let bands := hb hq
    let P := heavyBallSpectralReference d q hd hq n mu upper
      ⟨(bands (n+2)).1.posSemidef,(bands (n+2)).2.posSemidef⟩
    have hp := spectral_prior_ratio_bounds P hmu
    have he := heavyBall_spectral_reference_ratio d q hd hq n mu upper
      ⟨(bands (n+2)).1.posSemidef,(bands (n+2)).2.posSemidef⟩
      (bands (n+1)).1 (bands (n+1)).2
    have hc := physical_jacobi_last_coupling_le_scalar_distance P.matrix P.positive P.gradient
      P.gradient_ne_zero P.full_support d
    refine ⟨P,rfl,hp.1,hc.trans_lt hn,?_,hp.2.2⟩
    change upper/mu-epsilon < heavyBallFibreRatio d mu upper n q at hr
    change spectralPriorRatio P=heavyBallFibreRatio d mu upper n q at he
    rwa [he]
  obtain ⟨delta,hdelta,hall⟩ := Metric.eventually_nhds_iff.mp hevent
  obtain ⟨q,hq,hqsmall⟩ := exists_between (lt_min hdelta hepsilon)
  have hqdelta : dist q 0 < delta := by
    rw [dist_zero_right,Real.norm_eq_abs,abs_of_pos hq]
    exact hqsmall.trans_le (min_le_left _ _)
  exact ⟨q,hq,hqsmall.trans_le (min_le_right _ _),hall hqdelta hq⟩

end
end krylov.OneGradient
