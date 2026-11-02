import jacobi.Packing.FibreLimit
import jacobi.Variational.InfimumSequence
import jacobi.Finite.WeightChart

/-!
Article: jacobi, Theorem 4.1.
The lower limiting infimum over each complete finite polynomial fibre bounds
the actual moment and Fredholm continuum relaxations. All finite matrices
are retained: near-minimizers are selected from the fibres, their actual
packings have exact root normalization and the prescribed spectral limit,
and the proved continuum root limit supplies the limiting competitors.
Dimensions may follow any positive cofinal sequence. The polynomial is the
monic product of its prescribed descending simple roots in (-1,1).
Source: the proved finite spectral reconstruction, packing and root-compactness theorems.
Use: a nonnegative extended cost gives the natural infinity convention for empty fibres.
-/
namespace jacobi.Variational
noncomputable section
open chebyshev1 chebyshev2 jacobi.Finite jacobi.Packing
open Set Real MeasureTheory Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The actual finite resolvent energy in the article's N-cubed normalization.
Use: a nonnegative extended cost gives the natural infinity convention for empty fibres.
Article: jacobi, Theorem 3.2.
-/
def fibreCost {N : ℕ} (J : Jacobi N) : ℝ≥0∞ := ENNReal.ofReal (J.energy/(N : ℝ)^3)

/-- The actual infimum of normalized energy over the entire prescribed polynomial fibre.
Use: the finite quantity on the left of the full Transfer theorem, without a chosen realization.
Article: jacobi, Theorem D.4.
-/
def fibreEnergyInfimum {N : ℕ} (S : Nodes N) : ℝ≥0∞ :=
  sInf (fibreCost '' {J : Jacobi N | InFiber J S.polynomial})

/-- Every nonempty-dimensional prescribed polynomial fibre contains an actual Jacobi matrix.
Use: the extended finite energy infimum has exactly the ordinary finite-fibre meaning in the article.
Article: jacobi, Theorem D.4.
Proof: reconstruct the chain from the prescribed distinct nodes with uniform positive probability weights. -/
theorem fibre_nonempty {N : ℕ} (S : Nodes N) (hN : 0 < N) :
    ∃ J : Jacobi N, InFiber J S.polynomial := by
  -- The constructive inverse spectral map supplies a concrete fibre member with all irreducibility conditions proved.
  let w : WeightSimplex N := ⟨fun _ => 1/(N : ℝ),fun _ => div_pos zero_lt_one (Nat.cast_pos.mpr hN),by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp⟩
  exact ⟨(reconstructFiber S w).val,(reconstructFiber S w).property⟩

/-- The actual finite-fibre energy infimum is finite before taking a dimension limit.
Use: the ENNReal formulation faithfully represents the article's finite nonnegative energy infima.
Article: jacobi, Theorem D.4.
Proof: the proved reconstructed fibre member has a finite real scaled energy. -/
theorem fibreEnergyInfimum_ne_top {N : ℕ} (S : Nodes N) (hN : 0 < N) : fibreEnergyInfimum S ≠ ∞ := by
  obtain ⟨J,hJ⟩ := fibre_nonempty S hN
  have h : fibreEnergyInfimum S ≤ fibreCost J := sInf_le ⟨J,hJ,rfl⟩
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

/-- The extended finite-fibre infimum recovers precisely the ordinary real infimum.
Use: identifies the Lean finite objective with the printed nonnegative real finite-fibre energy.
Article: jacobi, Theorem D.4.
Proof: every image cost is finite; toReal commutes with its infimum, and
nonnegativity of each squared-diagonal energy cancels ofReal on every candidate. -/
theorem fibreEnergyInfimum_toReal {N : ℕ} (S : Nodes N) :
    (fibreEnergyInfimum S).toReal=
      sInf ((fun J : Jacobi N => J.energy/(N : ℝ)^3) '' {J | InFiber J S.polynomial}) := by
  -- This identity concerns the actual full candidate image, without a separate numerical model.
  rw [fibreEnergyInfimum,ENNReal.toReal_sInf _ (by
    rintro y ⟨J,_,rfl⟩
    exact ENNReal.ofReal_ne_top),Set.image_image]
  congr 1
  apply Set.image_congr
  intro J _
  apply ENNReal.toReal_ofReal
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)

/-- Full Transfer to both actual root-normalized continuum relaxations for arbitrary l1-convergent edge spectra.
Use: common finite-to-continuum lower bound before the calibrations specialize its constraints.
Article: jacobi, Theorem D.4.
Proof: at finite lower limiting cost select genuine near-minimizers from the
complete finite fibres. Their actual packings have exactly the scaled finite
energy and root mass one; the proved uniform packing estimate gives the
assumed edge limit for their actual kernel spectra. The proved density
Transfer theorem then bounds both root-normalized infima by the same limiting cost. -/
theorem fibre_transfer (N : ℕ → ℕ) (S : ∀ n, Nodes (N n)) (hN : ∀ n, 0 < N n)
    (hNlim : Tendsto N atTop atTop) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (fibreSpectrum (S n)) Λ.value) atTop (𝓝 0)) :
    (∀ C : Set Observation, rootInfimum C Λ.mass (threshold Λ) ≤
      liminf (fun n => fibreEnergyInfimum (S n)) atTop) ∧
      ∀ s : ℝ, 0 ≤ s → rootFredholmInfimum s Λ.mass (Λ.fredholm s) ≤
        liminf (fun n => fibreEnergyInfimum (S n)) atTop := by
  -- Infinite lower limiting cost is immediate; the finite case constructs all needed witnesses from actual fibres.
  by_cases hL : liminf (fun n => fibreEnergyInfimum (S n)) atTop=∞
  · simp only [hL,le_top,implies_true,and_self]
  obtain ⟨α,hα,J,hJ,hcost⟩ := exists_liminf_competitors (X := fun n => Jacobi (N n))
    (fun _ => fibreCost) (fun n => {J | InFiber J (S n).polynomial}) hL
  let m (n : ℕ) := variationalDensity (J n) ((S (α n)).contractive (hJ n)) (hN (α n))
  have hroot (n : ℕ) : (m n).rootMass ≤ 1 :=
    (variationalDensity_integrals (J n) ((S (α n)).contractive (hJ n)) (hN (α n))).2.1.le
  have hspec : Tendsto (fun n => distance (m n).spectrum Λ.value) atTop (𝓝 0) :=
    packed_fibre_edge_limit (fun n => N (α n)) (fun n => S (α n)) (fun n => hN (α n))
      (hNlim.comp hα) Λ (hd.comp hα) J hJ
  have he (n : ℕ) : (m n).cost=fibreCost (J n) :=
    congrArg ENNReal.ofReal
      (variationalDensity_integrals (J n) ((S (α n)).contractive (hJ n)) (hN (α n))).2.2
  have ht := (hcost.congr (fun n => (he n).symm)).liminf_eq
  have hb := density_transfer m Λ hroot hspec
  rw [ht] at hb
  exact hb

/-- The article's complete Transfer lower bounds, including dropping the root constraint.
Use: specializes the stronger proved root-normalized Transfer to the printed moment and Fredholm relaxations.
Article: jacobi, Theorem D.4.
Proof: apply the proved full finite-fibre Transfer and the proved inclusions
between exact-mass/root-normalized and root-free admissible density sets. -/
theorem fibre_transfer_article (N : ℕ → ℕ) (S : ∀ n, Nodes (N n)) (hN : ∀ n, 0 < N n)
    (hNlim : Tendsto N atTop atTop) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (fibreSpectrum (S n)) Λ.value) atTop (𝓝 0)) :
    (∀ C : Set Observation,
      rootInfimum C Λ.mass (threshold Λ) ≤ liminf (fun n => fibreEnergyInfimum (S n)) atTop ∧
      relaxedInfimum C Λ.mass (threshold Λ) ≤ rootInfimum C Λ.mass (threshold Λ)) ∧
      ∀ s : ℝ, 0 ≤ s → fredholmInfimum s Λ.mass (Λ.fredholm s) ≤
        liminf (fun n => fibreEnergyInfimum (S n)) atTop := by
  obtain ⟨hm,hF⟩ := fibre_transfer N S hN hNlim Λ hd
  exact ⟨fun C => ⟨hm C,relaxed_le_root C Λ.mass (threshold Λ)⟩,
    fun s hs => (fredholm_le_root s Λ.mass (Λ.fredholm s)).trans (hF s hs)⟩

end
end jacobi.Variational
