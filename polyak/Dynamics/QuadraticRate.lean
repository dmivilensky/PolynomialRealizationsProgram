import polyak.Dynamics.Quadratic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
Article: introduction, the quadratic factor ρq and eq:polyak.
Use: define the actual characteristic-root maximum and prove its exact Polyak value.
-/

namespace polyak.Dynamics
noncomputable section

/-- Article: ρq. Use: moduli of actual characteristic roots over the curvature interval. -/
def quadraticRootNorms (μ L α β : ℝ) : Set ℝ :=
  {r | ∃ lam ∈ Set.Icc μ L, ∃ z : ℂ,
    z^2-((1+β-α*lam : ℝ) : ℂ)*z+(β : ℂ)=0 ∧ r=‖z‖}

/-- Article: ρq. Use: the source quadratic spectral factor. -/
def quadraticRate (μ L α β : ℝ) : ℝ := sSup (quadraticRootNorms μ L α β)

/-- Article: ρq. Use: the characteristic equation always has an actual complex root. -/
theorem exists_complex_quadratic_root (a β : ℝ) :
    ∃ z : ℂ, z^2-(a : ℂ)*z+(β : ℂ)=0 := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq
    ((a : ℂ)^2-4*(β : ℂ)) (n := 2) (by norm_num)
  refine ⟨((a : ℂ)+d)/2, ?_⟩
  linear_combination hd/4

/-- Article: eq:quad. Use: the root-modulus supremum is attained uniformly in curvature. -/
theorem quadraticRate_isGreatest {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β < 1) (hquad : α*L < 2*(1+β)) :
    IsGreatest (quadraticRootNorms μ L α β) (quadraticRate μ L α β) := by
  let S : Set (ℝ × ℂ) := {p | p.1 ∈ Set.Icc μ L ∧
    p.2^2-((1+β-α*p.1 : ℝ) : ℂ)*p.2+(β : ℂ)=0}
  have hclosed : IsClosed S := by
    apply (isClosed_Icc.preimage continuous_fst).inter
    apply isClosed_eq _ continuous_const
    fun_prop
  have hcompact : IsCompact S := by
    apply (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) 1)).of_isClosed_subset hclosed
    intro p hp
    refine ⟨hp.1, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (heavyBall_root_norm_lt_one hμ hα hβ hβ1 hp.1.1 hp.1.2 hquad hp.2).le
  have himage : (fun p : ℝ × ℂ => ‖p.2‖) '' S = quadraticRootNorms μ L α β := by
    ext r
    constructor
    · rintro ⟨⟨lam,z⟩, hp, rfl⟩
      exact ⟨lam,hp.1,z,hp.2,rfl⟩
    · rintro ⟨lam,hlam,z,hz,rfl⟩
      exact ⟨(lam,z), ⟨hlam,hz⟩, rfl⟩
  have hrc : IsCompact (quadraticRootNorms μ L α β) := by
    rw [← himage]
    exact hcompact.image (continuous_norm.comp continuous_snd)
  obtain ⟨z,hz⟩ := exists_complex_quadratic_root (1+β-α*μ) β
  have hne : (quadraticRootNorms μ L α β).Nonempty :=
    ⟨‖z‖, μ, ⟨le_rfl,hL.le⟩, z, hz,rfl⟩
  obtain ⟨r,hr⟩ := hrc.exists_isGreatest hne
  simpa only [quadraticRate, hr.csSup_eq] using hr

/-- Article: eq:quad. Use: the uniform quadratic factor is strictly below one. -/
theorem quadraticRate_lt_one {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β < 1) (hquad : α*L < 2*(1+β)) :
    quadraticRate μ L α β < 1 := by
  obtain ⟨lam,hlam,z,hz,hr⟩ := (quadraticRate_isGreatest hμ hL hα hβ hβ1 hquad).1
  rw [hr]
  exact heavyBall_root_norm_lt_one hμ hα hβ hβ1 hlam.1 hlam.2 hquad hz

/-- Article: eq:polyak. Use: balanced tuning realizes the factor, rather than just bounding it. -/
theorem polyak_quadratic_isGreatest {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    IsGreatest (quadraticRootNorms μ L (polyakAlpha μ L) (polyakBeta μ L))
      (polyakQ μ L) := by
  have hq := polyakQ_pos hμ hL
  constructor
  · refine ⟨(L+μ)/2, ⟨by linarith, by linarith⟩,
      (polyakQ μ L : ℂ)*Complex.I, ?_, ?_⟩
    · have hA := polyak_normalizedA hμ hL
      dsimp [normalizedA] at hA
      have ha : 1+polyakBeta μ L-polyakAlpha μ L*((L+μ)/2)=0 := by nlinarith
      rw [ha]
      simp only [Complex.ofReal_zero, zero_mul, sub_zero, mul_pow, Complex.I_sq,
        polyakBeta, Complex.ofReal_pow]
      ring
    · simp [Real.norm_eq_abs, abs_of_pos hq]
  · rintro r ⟨lam, hlam, z, hz, rfl⟩
    exact (polyak_root_norm hμ hL hlam.1 hlam.2 hz).le

/-- Article: eq:polyak. Use: the quadratic factor is exactly q for every κ>1. -/
theorem polyak_quadraticRate {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    quadraticRate μ L (polyakAlpha μ L) (polyakBeta μ L) = polyakQ μ L :=
  (polyak_quadratic_isGreatest hμ hL).csSup_eq

end
end polyak.Dynamics
