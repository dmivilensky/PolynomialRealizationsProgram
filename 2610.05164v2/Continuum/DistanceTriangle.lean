import «2610.05164v2».Continuum.SpectralDistance

/-!
Article: 2610.05164v2, Theorem 2.3.
The l1 triangle inequality for genuine summable spectral sequences.
Use: `«2610.05164v2».Continuum.spectral_distance_triangle` feeds
`«2610.05164v2».Packing.packed_spectral_distance` (Theorem 2.3, equation (7), for the full fiber
including zero edges).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Continuum
open scoped BigOperators

/--
The l1 triangle inequality for genuine summable spectral sequences.

The stated quantitative bound `(∑' j, |a j-c j|) ≤ (∑' j, |a j-b j|)+(∑' j, |b j-c j|)`.

Use: `«2610.05164v2».Packing.packed_reference_distance` uses this bound to establish the stated
quantitative bound `(∑' j, |packedEigenvalue J hN ht j-referenceEigenvalue j|) ≤ transferError
N`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem spectral_distance_triangle {a b c : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (hc : Summable c) :
    (∑' j, |a j-c j|) ≤ (∑' j, |a j-b j|)+(∑' j, |b j-c j|) := by
  rw [← ((ha.sub hb).abs).tsum_add ((hb.sub hc).abs)]
  exact ((ha.sub hc).abs).tsum_le_tsum (fun j => abs_sub_le (a j) (b j) (c j))
    (((ha.sub hb).abs).add ((hb.sub hc).abs))

end «2610.05164v2».Continuum
