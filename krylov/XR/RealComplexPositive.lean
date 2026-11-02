import krylov.XR.HermitianForms

/-!
Article: main_krylov, prop:cert and quadratic XR retention.
Use: transport actual real positive forms to their complexifications,
including the empty-window case. Source: splitting a complex quadratic
form into its real and imaginary coordinates.
-/
namespace krylov.XR
noncomputable section
open Matrix
open scoped ComplexOrder
variable {p : ℕ}

/-- Real symmetric matrices remain Hermitian after complexification.
Article: main_krylov, prop:cert. -/
theorem ofReal_isHermitian (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.IsSymm) :
    (A.map Complex.ofReal).IsHermitian := by
  have hs : A.IsHermitian := by
    simpa only [IsHermitian,conjTranspose_eq_transpose_of_trivial] using hA.eq
  apply hs.map
  intro x
  simp

/-- Real and imaginary coordinates reconstruct the original vector.
Article: main_krylov, prop:cert. -/
theorem complexVector_re_im (z : Fin p → ℂ) :
    complexVector (fun i=>(z i).re) (fun i=>(z i).im)=z := by
  ext i
  simpa only [complexVector,mul_comm Complex.I] using Complex.re_add_im (z i)

/-- A nonzero complex vector has a nonzero real or imaginary part.
Article: main_krylov, prop:cert. -/
theorem complexVector_ne_zero_iff (x y : Fin p → ℝ) :
    complexVector x y≠0 ↔ x≠0 ∨ y≠0 := by
  constructor
  · intro h
    by_contra! hz
    apply h
    ext i
    simp [complexVector,hz.1,hz.2]
  · intro h hz
    have hx : x=0 := by
      ext i
      have hi := congrArg Complex.re (congrFun hz i)
      simpa [complexVector] using hi
    have hy : y=0 := by
      ext i
      have hi := congrArg Complex.im (congrFun hz i)
      simpa [complexVector] using hi
    exact h.elim (fun h=>h hx) (fun h=>h hy)

/-- A true real positive form is positive on the entire complexified
space, rather than just on real vectors. Article: prop:cert. -/
theorem ofReal_posDef (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.PosDef) :
    (A.map Complex.ofReal).PosDef := by
  have hs := ofReal_isHermitian A hA.isHermitian.isSymm
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hs
  intro z hz
  let x : Fin p → ℝ := fun i=>(z i).re
  let y : Fin p → ℝ := fun i=>(z i).im
  have he : z=complexVector x y := (complexVector_re_im z).symm
  have hq : (star z ⬝ᵥ (A.map Complex.ofReal*ᵥ z)).re=
      x ⬝ᵥ (A*ᵥ x)+y ⬝ᵥ (A*ᵥ y) := by
    rw [he]
    have hm := hermitian_pair_quadratic_re A 0 x y
    simpa using hm
  have hx : 0≤x ⬝ᵥ (A*ᵥ x) := by
    simpa only [star_trivial] using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hy : 0≤y ⬝ᵥ (A*ᵥ y) := by
    simpa only [star_trivial] using hA.posSemidef.dotProduct_mulVec_nonneg y
  have hp : 0<(star z ⬝ᵥ (A.map Complex.ofReal*ᵥ z)).re := by
    rw [hq]
    have hne := complexVector_ne_zero_iff x y |>.mp (he ▸ hz)
    rcases hne with h|h
    · have hh : 0<x ⬝ᵥ (A*ᵥ x) := by
        simpa only [star_trivial] using hA.dotProduct_mulVec_pos h
      linarith
    · have hh : 0<y ⬝ᵥ (A*ᵥ y) := by
        simpa only [star_trivial] using hA.dotProduct_mulVec_pos h
      linarith
  exact Complex.lt_def.mpr ⟨hp,(hs.im_star_dotProduct_mulVec_self z).symm⟩

/-- Complex positivity restricts to the actual underlying real form.
Article: main_krylov, prop:cert. -/
theorem posDef_of_ofReal (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.IsSymm)
    (hC : (A.map Complex.ofReal).PosDef) : A.PosDef := by
  have hs : A.IsHermitian := by
    simpa only [IsHermitian,conjTranspose_eq_transpose_of_trivial] using hA.eq
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hs
  intro x hx
  have hne : (fun i=>(x i : ℂ))≠0 := by
    intro hz
    apply hx
    ext i
    have hi := congrArg Complex.re (congrFun hz i)
    simpa using hi
  have hh := hC.re_dotProduct_pos hne
  change 0<(star (fun i=>(x i : ℂ)) ⬝ᵥ (A.map Complex.ofReal*ᵥ
    (fun i=>(x i : ℂ)))).re at hh
  rw [ofReal_mulVec] at hh
  have he : star (fun i=>(x i : ℂ))=(fun i=>(x i : ℂ)) := by
    ext i
    simp
  rw [he,ofReal_dotProduct,Complex.ofReal_re] at hh
  simpa only [star_trivial] using hh

end
end krylov.XR
