import jacobi.Analytic.ShiftedSpectrum
import jacobi.GelfandLevitan.ProfileSeries

/-!
Article: jacobi, Corollary C.6.
The genuine shifted resolvent series converges absolutely and
uniformly on the full closed physical interval times every compact
subset of the actual slit domain. Its zero-shift value and reflection
are exactly those of the already constructed original profile.
Use: shiftedProfile is the source's actual series, with the same transformed normalized spectral profiles already proved in Proposition C.2.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Set Filter jacobi.GelfandLevitan jacobi.Reference
open scoped Topology

/-- One original genuine shifted-resolvent spectral profile term.
Use: shiftedProfile is the source's actual series, with the same transformed normalized spectral profiles already proved in Proposition C.2.
Article: jacobi, Theorem C.5.
-/
def shiftedProfileTerm (a:ℝ) (ha:-1<a) (k:ℕ) (t:Interval) (w:ℂ) : ℂ :=
  shiftedEdge a ha k w*(spectralProfile a ha k t:ℂ)

/-- The actual original shifted resolvent profile, on the full physical interval.
Use: the continuum part of Theorem C.5 and the later genuine finite resolvent limit use this same source series.
Article: jacobi, Theorem C.5.
-/
def shiftedProfile (a:ℝ) (ha:-1<a) (t:Interval) (w:ℂ) : ℂ :=
  ∑'k:ℕ,shiftedProfileTerm a ha k t w

/-- The original shifted profile terms have one genuine Rayleigh-summable majorant uniform in every physical point and every compact source parameter set.
Use: the original profile series is absolutely and uniformly convergent, and its holomorphic parameter limit has an actual locally uniform majorant.
Article: jacobi, Theorem C.5.
Proof: the proved original compact shifted eigenvalue bound and the proved common uniform norm bound of all actual Phi_k multiply to the same genuine positive summable Bessel edge sequence. -/
theorem shiftedProfile_majorant (a:ℝ) (ha:-1<a) {W:Set ℂ} (hW:IsCompact W)
    (hsub:W⊆edgeDomain a ha) :
    ∃C:ℝ,0<C ∧ ∀k:ℕ,∀t:Interval,∀w∈W,
      ‖shiftedProfileTerm a ha k t w‖≤C* jacobi.Bessel.edgeValue a ha k := by
  -- The two independently proved original norm bounds multiply to the same summable genuine Bessel edge value.
  obtain ⟨K,hK,hbound⟩ := shiftedEdge_compact_bound a ha hW hsub
  obtain ⟨D,hD,hPhi⟩ := spectralProfile_uniform_bound a ha
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro k t w hw
  have hp : ‖spectralProfile a ha k t‖≤D :=
    ((spectralProfile a ha k).norm_coe_le_norm t).trans (hPhi k)
  rw [shiftedProfileTerm,norm_mul,Complex.norm_real]
  exact (mul_le_mul (hbound k w hw) hp (norm_nonneg _)
    (mul_nonneg hK.le ((jacobi.Bessel.edgeValue_properties ha).1 k).le)).trans_eq (by ring)

/-- The original actual shifted profile series is absolutely convergent at every genuine physical point and every source-domain parameter.
Use: shiftedProfile_summable and the actual Theorem C.5 profile have genuine convergent series, rather than totalized unsummable values.
Article: jacobi, Theorem C.5.
Proof: the actual singleton parameter set is compact in the original domain. Its proved spectral majorant has the genuine summable Rayleigh mass. -/
theorem shiftedProfile_norm_summable (a:ℝ) (ha:-1<a) (t:Interval) {w:ℂ} (hw:w∈edgeDomain a ha) :
    Summable (fun k:ℕ => ‖shiftedProfileTerm a ha k t w‖) := by
  obtain ⟨C,hC,hbound⟩ := shiftedProfile_majorant a ha (W:={w}) isCompact_singleton (by simpa only [singleton_subset_iff] using hw)
  exact ((jacobi.Bessel.edgeValue_summable ha).mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => hbound k t w (mem_singleton w))

/-- The original actual shifted profile series genuinely sums at every point of the complete original source domain.
Use: holomorphic summation and the actual shifted-profile identities concern the convergent original series.
Article: jacobi, Theorem C.5.
Proof: the proved absolute norm summability implies convergence in the complete complex field. -/
theorem shiftedProfile_summable (a:ℝ) (ha:-1<a) (t:Interval) {w:ℂ} (hw:w∈edgeDomain a ha) :
    Summable (fun k:ℕ => shiftedProfileTerm a ha k t w) :=
  (shiftedProfile_norm_summable a ha t hw).of_norm

/-- The original actual partial sums converge uniformly on the whole physical interval times every genuine compact subset of the original slit domain.
Use: Theorem C.5's continuum profile has the required joint compact parameter uniformity, including both physical endpoints; its holomorphy follows from the same genuine locally uniform series.
Article: jacobi, Theorem C.5.
Source: the Weierstrass majorant theorem for uniformly convergent series.
Proof: the actual compact shifted-profile majorant is a constant multiple of the independently proved summable original Bessel edge spectrum. Apply the community uniform-series theorem to the genuine original terms. -/
theorem shiftedProfile_uniform_limit (a:ℝ) (ha:-1<a) {W:Set ℂ} (hW:IsCompact W)
    (hsub:W⊆edgeDomain a ha) :
    TendstoUniformly (fun N:ℕ => fun p:Interval×W =>
      ∑k∈Finset.range N,shiftedProfileTerm a ha k p.1 p.2)
      (fun p:Interval×W => shiftedProfile a ha p.1 p.2) atTop := by
  obtain ⟨C,hC,hbound⟩ := shiftedProfile_majorant a ha hW hsub
  exact tendstoUniformly_tsum_nat ((jacobi.Bessel.edgeValue_summable ha).mul_left C)
    (fun k p => hbound k p.1 p.2 p.2.property)

/-- The actual shifted resolvent profile at zero is exactly the already constructed original persymmetric profile.
Use: Theorem C.5's zero-shift assertion refers to the same original phi_alpha and the same original unshifted Green diagonal of Proposition C.2.
Article: jacobi, Theorem C.5.
Proof: the original shifted coefficient equals the original Bessel edge value at zero, and the continuous real-to-complex map commutes with the genuine original profile sum. -/
theorem shiftedProfile_zero (a:ℝ) (ha:-1<a) (t:Interval) :
    shiftedProfile a ha t 0=(persymmetricProfile a ha t:ℂ) := by
  rw [shiftedProfile,persymmetricProfile_apply,Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  simp only [shiftedProfileTerm,shiftedEdge_zero,Complex.ofReal_mul]

/-- The actual original shifted resolvent profile has exact physical midpoint symmetry at every complex parameter.
Use: Theorem C.5's half-interval definition extends to the same genuine full physical interval used by its squared-profile integrals.
Article: jacobi, Theorem C.5.
Proof: every genuine original transformed spectral profile is unchanged by the already proved physical reflection, so the actual original series agree term by term. -/
theorem shiftedProfile_reflection (a:ℝ) (ha:-1<a) (t:Interval) (w:ℂ) :
    shiftedProfile a ha (physicalReflection t) w=shiftedProfile a ha t w := by
  unfold shiftedProfile
  apply tsum_congr
  intro k
  simp only [shiftedProfileTerm,spectralProfile_reflection]

end
end jacobi.EdgeResolvent
