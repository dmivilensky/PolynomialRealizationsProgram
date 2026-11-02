import jacobi.Variational.Problem
import Mathlib.Topology.Order.LiminfLimsup

/-!
Article: jacobi, Theorem D.4.
A finite lower limit of extended infima admits actual competitors along a
cofinal sequence whose costs converge to that same lower limit. The statement
allows index-dependent competitor spaces, so it serves both density infima
and finite polynomial fibres. Empty or infinite initial problems cause no
extra feasibility premise: finite limiting cost supplies eventual feasibility.
Source: elementary infimum approximation and sequential lower-limit selection.
Use: chooses genuine densities or finite fibre matrices rather than assuming minimizing witnesses.
-/
namespace jacobi.Variational
noncomputable section
open Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- A finite extended infimum has an actual competitor within every positive real error.
Use: chooses genuine densities or finite fibre matrices rather than assuming minimizing witnesses.
Article: jacobi, Theorem D.4.
Proof: otherwise every candidate would lie above infimum+epsilon, contradicting the defining lower bound. -/
theorem exists_cost_lt_infimum_add {X : Type*} (f : X → ℝ≥0∞) (A : Set X)
    (hfin : sInf (f '' A) ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ A, f x < sInf (f '' A)+ENNReal.ofReal ε := by
  -- Strict positivity of epsilon and finiteness of the infimum justify the strict comparison in ENNReal.
  have hs := ENNReal.lt_add_right hfin (show ENNReal.ofReal ε ≠ 0 by positivity)
  by_contra h
  have hl : sInf (f '' A)+ENNReal.ofReal ε ≤ sInf (f '' A) := by
    apply le_sInf
    rintro y ⟨x,hx,rfl⟩
    exact le_of_not_gt (fun hi => h ⟨x,hx,hi⟩)
  exact (not_lt_of_ge hl) hs

/-- A finite lower limit of arbitrary extended variational infima is approached by actual cofinal competitors.
Use: the common selection step for lower semicontinuity of root relaxations and for finite-fibre Transfer.
Article: jacobi, Theorem D.4.
Proof: select infima tending to their lower limit. Discard the finite prefix
before they become finite, choose actual competitors within 1/(n+1), and squeeze
their costs between the infima and the vanishing-error upper bound. -/
theorem exists_liminf_competitors {X : ℕ → Type*} (f : ∀ n, X n → ℝ≥0∞)
    (A : ∀ n, Set (X n))
    (hfin : liminf (fun n => sInf (f n '' A n)) atTop ≠ ∞) :
    ∃ α : ℕ → ℕ, Tendsto α atTop atTop ∧
      ∃ x : ∀ n, X (α n), (∀ n, x n ∈ A (α n)) ∧
        Tendsto (fun n => f (α n) (x n)) atTop
          (𝓝 (liminf (fun n => sInf (f n '' A n)) atTop)) := by
  -- Cofinality retains every original asymptotic hypothesis; the selector need not be strictly increasing.
  let c (n : ℕ) := sInf (f n '' A n)
  let L := liminf c atTop
  obtain ⟨β,hβc,hβ⟩ := exists_seq_tendsto_liminf (u := c) (f := atTop)
  have he : ∀ᶠ n in atTop, c (β n) < ∞ := hβc.eventually (Iio_mem_nhds (lt_top_iff_ne_top.mpr hfin))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let α (n : ℕ) := β (n+N)
  have hα : Tendsto α atTop atTop := hβ.comp (tendsto_add_atTop_nat N)
  have hαc : Tendsto (fun n => c (α n)) atTop (𝓝 L) :=
    hβc.comp (tendsto_add_atTop_nat N)
  have hcfin (n : ℕ) : c (α n) ≠ ∞ := (hN (n+N) (Nat.le_add_left N n)).ne
  choose x hx hcost using fun n => exists_cost_lt_infimum_add (f (α n)) (A (α n))
    (hcfin n) (ε := 1/((n : ℝ)+1)) (by positivity)
  refine ⟨α,hα,x,hx,?_⟩
  have hε := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hup := hαc.add hε
  simp only [ENNReal.ofReal_zero,add_zero] at hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hαc hup
  · exact fun n => sInf_le ⟨x n,hx n,rfl⟩
  · exact fun n => (hcost n).le

end
end jacobi.Variational
