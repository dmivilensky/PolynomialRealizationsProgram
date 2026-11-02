import jacobi.Variational.FredholmVariation
import jacobi.Variational.FredholmDilation
import jacobi.Variational.MultiplierRule
import jacobi.Variational.ConstraintActivity
import jacobi.Variational.FredholmExistence

/-!
Article: jacobi, Theorem D.7.
Every actual radial finite-energy minimizer below its stated spectral pole
has the active Fredholm constraint and the printed Green-diagonal normal
Euler equation. All quadratic variation, strict dilation and constraint
qualification premises are proved for the actual determinant. Its extended
infinite branch is retained in the original variational admissible set.
Source: the article's Fredholm corollary of the normal multiplier rule.
Use: every competitor satisfying the real constraint is admissible for the original extended Fredholm infimum.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The actual extended determinant dominates the ofReal of its real expression, including at poles.
Use: every competitor satisfying the real constraint is admissible for the original extended Fredholm infimum.
Article: jacobi, Theorem D.7.
Proof: below the actual top pole use the convergent spectral series; at a pole the extended value is infinity. -/
theorem Density.fredholmReal_le (q : Density) {s : ℝ} (hs : 0≤s) :
    ENNReal.ofReal (q.fredholmReal s)≤q.fredholm s := by
  by_cases hp : s*observe q .top<1
  · rw [q.fredholm_eq hs (sub_pos.mpr hp) (by linarith)]
  · have htop : q.fredholm s=∞ := fredholmSpectrum_eq_top (j := 0) (le_of_not_gt hp)
    rw [htop]
    exact le_top

/-- Every actual subcritical radial Fredholm minimizer has active constraint and genuine normal Green multipliers.
Use: supplies the Fredholm calibration with proved multipliers and the actual weak Green kernel.
Article: jacobi, Theorem D.7.
Proof: derive the expansion and local dilation constants from the actual
spectral margin. Real-constraint competitors remain feasible for the
extended infimum, so the common activity and normal multiplier theorems
apply without any assumed expansion, qualification or multiplier certificate. -/
theorem fredholm_minimizer_kkt_of_mass_pos {s M d : ℝ} (hs : 0<s)
    (m : Density) (hm : 0<m.mass) (hrad : SymmetricDecreasing m.value)
    (hp : s*observe m .top<1) (hmM : m.mass≤M)
    (hmd : ENNReal.ofReal d≤m.fredholm s)
    (hmin : m.cost=fredholmInfimum s M (ENNReal.ofReal d)) :
    m.fredholm s=ENNReal.ofReal d ∧
      ∃ μ l : ℝ,0<μ ∧ 0≤l ∧ l*(M-m.mass)=0 ∧
        (fun x => sqrt (m.value x))=ᵐ[volume]
          fun x => (2/3:ℝ)*max (μ*s*(2*m.fredholmGreen s hs.le hp x x-1)-l) 0 := by
  -- The single actual spectral margin supplies every analytic constant in the multiplier rule.
  let ε := 1-s*observe m .top
  have hε : 0<ε := sub_pos.mpr hp
  have hmargin : s*observe m .top≤1-ε := by dsimp only [ε]; linarith
  let γ := m.fredholmGradient s hs.le hp
  have hminE (q : Density) (hqM : q.mass≤M) (hqd : d≤q.fredholmReal s) : m.energy≤q.energy := by
    have hcost : m.cost≤q.cost := by
      rw [hmin]
      apply sInf_le
      exact ⟨q,⟨hqM,(ENNReal.ofReal_le_ofReal hqd).trans (q.fredholmReal_le hs.le)⟩,rfl⟩
    exact (ENNReal.ofReal_le_ofReal_iff q.energy_nonneg).mp hcost
  have hmnon : 0≤m.fredholmReal s := tsum_nonneg fun j =>
    fredholmLog_nonneg (by have hh := m.spectral_margin hs.le hmargin j; linarith)
  have hmdReal : d≤m.fredholmReal s := by
    rw [m.fredholm_eq hs.le hε hmargin] at hmd
    exact (ENNReal.ofReal_le_ofReal_iff hmnon).mp hmd
  have hvar (q : Density) (hsmall : (∫ x,|q.value x-m.value x|)≤ε/(2*s)) :
      |q.fredholmReal s-m.fredholmReal s-(∫ x,γ x*(q.value x-m.value x))|≤
        (2*s^2/ε^2)*(∫ x,|q.value x-m.value x|)^2 := by
    have hh := (fredholm_variation m hs hε hmargin q hsmall).2
    convert hh using 1
    ring
  obtain ⟨k,η,hk,hη,hgain⟩ := fredholm_strict_dilation m hm hrad hs hp
  have hγB (x : ℝ) : |γ x|≤s*(ε⁻¹-1) := by
    rw [abs_of_nonneg (m.fredholmGradient_bounds hs.le hp x).1]
    exact (m.fredholmGradient_bounds hs.le hp x).2
  obtain ⟨μ,l,hμ,hl,hcomp,heq⟩ := normal_multiplier_rule_local m hm hrad
    (fun q => q.fredholmReal s) γ (m.fredholmGradient_continuous hs.le hp).measurable hγB
    (C := 2*s^2/ε^2) (r := ε/(2*s)) (by positivity) (by positivity) hk hη
    hmM hmdReal hminE hvar (fun t ht hupper => (hgain t ht hupper).2)
  have hactive := spectral_constraint_active m hm (fun q => q.fredholmReal s) γ
    (C := 2*s^2/ε^2) (r := ε/(2*s)) (by positivity) (by positivity)
    hmM hmdReal hminE hvar
  refine ⟨by rw [m.fredholm_eq hs.le hε hmargin,hactive],μ,l,hμ,hl,hcomp,?_⟩
  convert heq using 1
  funext x
  dsimp only [γ,L1Source.fredholmGradient]
  congr 2
  ring


/-- The Fredholm optimality corollary with precisely the article's positive threshold and subcriticality assumptions.
Use: makes nonvanishing a proved consequence of feasibility rather than an additional optimizer premise.
Article: jacobi, Theorem D.7.
Proof: positive extended feasibility forces positive mass; apply the fully
proved actual Fredholm KKT theorem with that mass and the stated pole condition. -/
theorem fredholm_minimizer_kkt {s M d : ℝ} (hs : 0<s) (hd : 0<d)
    (m : Density) (hrad : SymmetricDecreasing m.value)
    (hp : s*observe m .top<1) (hmM : m.mass≤M)
    (hmd : ENNReal.ofReal d≤m.fredholm s)
    (hmin : m.cost=fredholmInfimum s M (ENNReal.ofReal d)) :
    m.fredholm s=ENNReal.ofReal d ∧
      ∃ μ l : ℝ,0<μ ∧ 0≤l ∧ l*(M-m.mass)=0 ∧
        (fun x => sqrt (m.value x))=ᵐ[volume]
          fun x => (2/3:ℝ)*max (μ*s*(2*m.fredholmGreen s hs.le hp x x-1)-l) 0 :=
  fredholm_minimizer_kkt_of_mass_pos hs m
    (mass_pos_of_fredholm_pos m ((ENNReal.ofReal_pos.mpr hd).trans_le hmd))
    hrad hp hmM hmd hmin

end
end jacobi.Variational
