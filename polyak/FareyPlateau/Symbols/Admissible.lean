import polyak.FareyPlateau.Symbols.Bezout

/-! Literal finite-support admissibility.  The index type enumerates the
positive support, so zero weights from a finitely supported sequence have
already been removed. No analytic phase-floor property is a field. -/
noncomputable section
namespace polyak.FareyPlateau.Symbols
open Set
open scoped BigOperators
variable {I : Type*} [Fintype I]

structure Admissible (k b : ℤ) (bar : ℝ) (n : I→ℤ) (w : I→ℝ) : Prop where
  injective : Function.Injective n
  nonzero : ∀i,n i≠0
  positive : ∀i,0<w i
  normalization : ∑i,w i=1
  positions : ∀i,n i%k=b%k ∨ n i%k=0
  two_one : ∃i j,n i≠n j ∧ n i%k=b%k ∧ n j%k=b%k
  support_gcd : Finset.univ.gcd n=1
  slope : (∑i∈Finset.univ.filter (fun i=>n i%k=b%k),w i*((n i:ℝ)-bar))=
    ∑i∈Finset.univ.filter (fun i=>n i%k=0),w i*(n i:ℝ)

theorem Admissible.bezout {k b : ℤ} {bar : ℝ} {n : I→ℤ} {w : I→ℝ}
    (h : Admissible k b bar n w) : SupportBezout n w := by
  apply supportBezout_of_gcd
  have hN : Finset.univ.filter (fun i=>w i≠0)=Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    exact (h.positive i).ne'
  rw [hN]
  exact h.support_gcd

theorem Admissible.denominator_pos {k b : ℤ} {bar : ℝ} {n : I→ℤ} {w : I→ℝ}
    (h : Admissible k b bar n w) {ω : ℝ} (hω : ω∈Ioc (0:ℝ) Real.pi) :
    0<denominator n w ω :=
  polyak.FareyPlateau.Symbols.denominator_pos n w (fun i=>(h.positive i).le) h.bezout hω

theorem Admissible.phaseFloor_analytic {k b : ℤ} {bar : ℝ} {n : I→ℤ} {w : I→ℝ}
    (h : Admissible k b bar n w) : AnalyticOnNhd ℝ (psi n w) (Icc (-1:ℝ) 1) :=
  fun _ hc=>analyticAt_psi n w h.nonzero (fun i=>(h.positive i).le)
    h.normalization h.bezout hc

end polyak.FareyPlateau.Symbols
