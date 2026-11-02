import jacobi.Finite.DiscreteDifference
import jacobi.Support.Volterra

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
The original complex support wave has an exact adjacent-difference
identity with its genuine top-node reference and actual coupling.
Use: naturalWave_firstDifference estimates both terms with the already proved actual growth, error and positive-coupling bounds.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference jacobi.Finite

/-- The genuine support wave's first-difference error is the sum of its reference difference times its relative error and the actual Wronskian source.
Use: naturalWave_firstDifference estimates both terms with the already proved actual growth, error and positive-coupling bounds.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: specialize the proved discrete Lagrange identity to the actual normalized original polynomials. Their exact recurrence, positive top-node value and irreducible actual coupling discharge every premise. -/
theorem naturalWave_difference_identity (a b : ℝ) (ha:-1<a) (hb:-1<b)
    (n m : ℕ) (hm:m<n) (y : ℂ) :
    (naturalWave a b ha hb n (m+1) y-naturalWave a b ha hb n m y)-
        ((topValue a b ha hb n (m+1):ℂ)-topValue a b ha hb n m)=
      ((naturalWave a b ha hb n m y-topValue a b ha hb n m)/topValue a b ha hb n m)*
        ((topValue a b ha hb n (m+1):ℂ)-topValue a b ha hb n m)+
      (y-(cos (gamma a*step a b (n+1)):ℝ))*
        (∑j∈Finset.range (m+1),(topValue a b ha hb n j:ℂ)*naturalWave a b ha hb n j y)/
        ((sqrt ((naturalChain a b ha hb (n+1)).data.aSq (m+1)):ℂ)*topValue a b ha hb n m) := by
  -- The reference and wave are the same original normalized polynomial evaluated at the two genuine spectral energies.
  let J := naturalChain a b ha hb (n+1)
  let y₀ : ℂ := (cos (gamma a*step a b (n+1)):ℝ)
  let ac : ℕ→ℂ := fun k => (sqrt (J.data.aSq k):ℂ)
  let bc : ℕ→ℂ := fun k => (J.data.b k:ℂ)
  let u := fun k => naturalWave a b ha hb n k y₀
  let v := fun k => naturalWave a b ha hb n k y
  have hrec (z : ℂ) (k : ℕ) (hk:k<n) :=
    normalizedLeading_recurrence J (naturalChain_irreducible a b ha hb (n+1)) z k (by omega)
  have h := discrete_difference_error ac bc u v y₀ y n
    (fun k hk => hrec y₀ k hk) (fun k hk => hrec y k hk) hm
    (Complex.ofReal_ne_zero.mpr (sqrt_pos.mpr
      (naturalChain_irreducible a b ha hb (n+1) (m+1) (by omega) (by omega))).ne')
    (by
      dsimp [u,y₀]
      rw [naturalWave_top]
      exact Complex.ofReal_ne_zero.mpr (naturalPolynomial_top_pos ha hb hm.le).ne')
  simpa only [u,v,ac,J,y₀,naturalWave_top] using h

end
end jacobi.Support
