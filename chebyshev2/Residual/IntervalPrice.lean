import chebyshev2.Residual.Price

/-!
Article: chebyshev2, Theorem 3.6.
Extension of precisely the article's prices on [0,2].
Use: `chebyshev2.Residual.Price.ofInterval` feeds `chebyshev2.Residual.Price.ofInterval_eq`
(of Interval eq).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_analytic` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.Residual.Price
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Constructs `ofInterval` of type `chebyshev2.Residual.Price` by the displayed record fields.
Data fields specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.Residual.Price.ofInterval_eq` uses this definition to establish exact
identity `(ofInterval η D B hB hb hc).value q=η q`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def ofInterval (η : ℝ → ℝ) (D : Finset ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ q ∈ Icc (0:ℝ) 2, ‖η q‖ ≤ B)
    (hc : ∀ q ∈ Icc (0:ℝ) 2, q ∉ D → ContinuousWithinAt η (Icc (0:ℝ) 2) q) :
    chebyshev2.Residual.Price where
  value := (Icc (0:ℝ) 2).indicator η
  exceptional := insert 0 (insert 2 D)
  continuous := by
    intro q hq
    have h0 : q ≠ 0 := fun he => hq (by simp [he])
    have h2 : q ≠ 2 := fun he => hq (by simp [he])
    have hD : q ∉ D := fun he => hq (by simp [he])
    by_cases hqI : q ∈ Icc (0:ℝ) 2
    · have hi : q ∈ Ioo (0:ℝ) 2 := ⟨lt_of_le_of_ne hqI.1 (Ne.symm h0),lt_of_le_of_ne hqI.2 h2⟩
      apply ((hc q hqI hD).continuousAt (Icc_mem_nhds hi.1 hi.2)).congr
      filter_upwards [Ioo_mem_nhds hi.1 hi.2] with t ht
      exact (indicator_of_mem (s := Icc (0:ℝ) 2) ⟨ht.1.le,ht.2.le⟩ η).symm
    · apply continuousAt_const.congr
      have hn : (Icc (0:ℝ) 2)ᶜ ∈ 𝓝 q := isClosed_Icc.isOpen_compl.mem_nhds hqI
      filter_upwards [hn] with t ht
      exact (indicator_of_notMem ht η).symm
  B := B
  bound_nonneg := hB
  bound := by
    intro q
    by_cases hq : q ∈ Icc (0:ℝ) 2
    · rw [indicator_of_mem hq]
      exact hb q hq
    · rw [indicator_of_notMem hq,norm_zero]
      exact hB

/--
Exact identity `(ofInterval η D B hB hb hc).value q=η q`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.6.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem ofInterval_eq (η : ℝ → ℝ) (D : Finset ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ q ∈ Icc (0:ℝ) 2, ‖η q‖ ≤ B)
    (hc : ∀ q ∈ Icc (0:ℝ) 2, q ∉ D → ContinuousWithinAt η (Icc (0:ℝ) 2) q)
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    (ofInterval η D B hB hb hc).value q=η q := indicator_of_mem hq η

end
end chebyshev2.Residual.Price
