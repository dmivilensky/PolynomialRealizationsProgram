import polyak.FiniteHorizon.PriceCoefficients
import polyak.FiniteHorizon.PricesSeries

/-!
Article: Appendix C, Lemma exactprice and the closed invariant kernel.
Use: the actual finite-window cone and actual admissible segment transitions
retain nonnegativity and contraction when uniformly bounded prices converge.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

/-- The genuine consecutive-window relation, allowing every finite Euclidean dimension. -/
def windowTransitions (A B β : ℝ) (H : ℕ) : Set (WindowSpace H × WindowSpace H) :=
  {Y | ∃ d n : ℕ, ∃ s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n,
    ∃ k : ℕ, H≤k ∧ k+1≤n ∧ Y.1=segmentWindow s k ∧ Y.2=segmentWindow s (k+1)}

def PriceNonnegative (A B β : ℝ) (H : ℕ) (L : WindowPrice H) : Prop :=
  ∀ Y∈windowCone A B β H, 0≤L Y

def PriceContracts (A B β : ℝ) (H : ℕ) (T : ℝ) (L : WindowPrice H) : Prop :=
  ∀ Y∈windowTransitions A B β H, L Y.2≤Real.exp (2*T)*L Y.1

theorem windowTransitions_mem_cone {A B β : ℝ} {H : ℕ} (hB : B≠0)
    {Y : WindowSpace H × WindowSpace H} (hY : Y∈windowTransitions A B β H) :
    Y.1∈windowCone A B β H ∧ Y.2∈windowCone A B β H := by
  obtain ⟨d,n,s,k,hk,hkn,h0,h1⟩:=hY
  rw [h0,h1]
  exact ⟨segmentWindow_mem hB s k hk (by omega),
    segmentWindow_mem hB s (k+1) (by omega) hkn⟩

/-- Limits of the actual window inequalities preserve their exact exponent. -/
theorem price_conditions_of_limit {A B β T : ℝ} {H : ℕ}
    (L : ℕ → WindowPrice H) (t : ℕ → ℝ) (Lstar : WindowPrice H)
    (hL : ∀ Y, Tendsto (fun n => L n Y) atTop (𝓝 (Lstar Y)))
    (ht : Tendsto t atTop (𝓝 T))
    (hpos : ∀ n,PriceNonnegative A B β H (L n))
    (hstep : ∀ n,PriceContracts A B β H (t n) (L n)) :
    PriceNonnegative A B β H Lstar ∧ PriceContracts A B β H T Lstar := by
  constructor
  · intro Y hY
    exact ge_of_tendsto (hL Y) (Eventually.of_forall fun n => hpos n Y hY)
  · intro Y hY
    have he : Tendsto (fun n => Real.exp (2*t n)) atTop (𝓝 (Real.exp (2*T))):=
      Real.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds.mul ht)
    exact le_of_tendsto_of_tendsto (hL Y.2) (he.mul (hL Y.1))
      (Eventually.of_forall fun n => hstep n Y hY)

/-- The exactprice compactness step on the actual cone and all actual transitions.
The lower bound on any chosen stationary windows is retained pointwise. -/
theorem exists_exact_price_limit {A B β T M : ℝ} {H : ℕ}
    (L : ℕ → WindowPrice H) (t : ℕ → ℝ) (S : Set (WindowSpace H))
    (lower : WindowSpace H → ℝ) (hbound : ∀ n,priceSize (L n)≤M)
    (ht : Tendsto t atTop (𝓝 T))
    (hpos : ∀ n,PriceNonnegative A B β H (L n))
    (hstep : ∀ n,PriceContracts A B β H (t n) (L n))
    (hlower : ∀ n,∀ Y∈S, lower Y≤L n Y) :
    ∃ Lstar : WindowPrice H, PriceNonnegative A B β H Lstar ∧
      PriceContracts A B β H T Lstar ∧ ∀ Y∈S, lower Y≤Lstar Y := by
  obtain ⟨Lstar,φ,hφ,hconv⟩:=exists_price_subsequence L hbound
  have hh:=price_conditions_of_limit (fun n => L (φ n)) (fun n => t (φ n)) Lstar hconv
    (ht.comp hφ.tendsto_atTop) (fun n => hpos (φ n)) (fun n => hstep (φ n))
  refine ⟨Lstar,hh.1,hh.2,?_⟩
  intro Y hY
  exact ge_of_tendsto (hconv Y) (Eventually.of_forall fun n => hlower (φ n) Y hY)

/-- The concrete zero-price kernel inside the finite-window cone. -/
def priceKernel (A B β : ℝ) (H : ℕ) (L : WindowPrice H) : Set (WindowSpace H) :=
  {Y | Y∈windowCone A B β H ∧ L Y=0}

theorem priceKernel_isClosed (A B β : ℝ) (H : ℕ) (L : WindowPrice H) :
    IsClosed (priceKernel A B β H L) :=
  (windowCone_isClosed A B β H).inter (isClosed_eq L.continuous continuous_const)

theorem priceKernel_convex (A B β : ℝ) (H : ℕ) (L : WindowPrice H) :
    Convex ℝ (priceKernel A B β H L) := by
  intro Y hY Z hZ a b ha hb hab
  refine ⟨windowCone_convex A B β H hY.1 hZ.1 ha hb hab,?_⟩
  simp only [map_add,map_smul,hY.2,hZ.2,smul_zero,add_zero]

/-- Exact-rate nonnegativity and contraction make the actual kernel forward invariant. -/
theorem priceKernel_forward {A B β T : ℝ} {H : ℕ} (hB : B≠0) (L : WindowPrice H)
    (hpos : PriceNonnegative A B β H L) (hstep : PriceContracts A B β H T L)
    {Y Z : WindowSpace H} (hY : Y∈priceKernel A B β H L)
    (hYZ : (Y,Z)∈windowTransitions A B β H) : Z∈priceKernel A B β H L := by
  have hZ:=(windowTransitions_mem_cone hB hYZ).2
  refine ⟨hZ,?_⟩
  have hu:=hstep (Y,Z) hYZ
  have hl:=hpos Z hZ
  rw [hY.2,mul_zero] at hu
  exact le_antisymm hu hl

/-- Positive stationary lower bounds exclude every stationary window from the kernel. -/
theorem stationary_not_mem_priceKernel {A B β : ℝ} {H : ℕ} (L : WindowPrice H)
    {Y : WindowSpace H} {c : ℝ} (hc : 0<c) (hL : c≤L Y) :
    Y∉priceKernel A B β H L := by
  intro hY
  rw [hY.2] at hL
  linarith

end polyak.FiniteHorizon
