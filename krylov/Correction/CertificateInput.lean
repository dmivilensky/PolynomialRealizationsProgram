import krylov.Correction.DeepSource
import krylov.Correction.CertificatePrefix

/-!
Article: main_krylov, prop:deep, exact four-dimensional source input layout.
Use: encode the real parameter, current gradient and actual newest-first
total-step and measured-secant arrays in the unchanged earlier certificate
input stack, with exact coordinate decoding and interpretation invariance.
Source: finite array indexing and elementary natural quotient/remainder
arithmetic; empty actual histories and outside indices are included.
-/

namespace krylov.Correction.Certificate
noncomputable section
open Matrix Finset chebyshev2.Numerics.IntegerCertificate

/-- The exact finite input-stack layout of a parameter, four-dimensional gradient and genuine newest-first stored step/secant families.
Use: Keep the checked source stack tied to its actual physical observations.
Article: main_krylov, prop:deep, exact genuine source input coordinates. -/
def encodeInput {α : Type*} (k : ℕ) (parameter : α) (g : Fin 4 → α)
    (s y : Fin k → Fin 4 → α) (zero : α) (j : ℕ) : α :=
  if j=0 then parameter
  else if h : j≤4 then g ⟨j-1,by omega⟩
  else if h : j<5+4*k then s ⟨(j-5)/4,by omega⟩ ⟨(j-5)%4,by omega⟩
  else if h : j<5+8*k then y ⟨(j-(5+4*k))/4,by omega⟩ ⟨(j-(5+4*k))%4,by omega⟩
  else zero

/-- The first encoded source input is precisely the actual family parameter.
Use: Preserve the genuine affine source parameter throughout all certificates.
Article: main_krylov, prop:deep, exact genuine source input coordinates.
Proof: Select the exact original first input branch. -/
theorem encodeInput_parameter {α : Type*} (k : ℕ) (parameter : α) (g : Fin 4 → α)
    (s y : Fin k → Fin 4 → α) (zero : α) : encodeInput k parameter g s y zero 0=parameter := by
  simp only [encodeInput,ite_true]

/-- The four encoded gradient slots recover exactly their original true coordinates.
Use: Connect the numerical prefix input to the genuine current observed gradient.
Article: main_krylov, prop:deep, exact genuine source input coordinates.
Proof: The gradient slots lie strictly after the parameter and within the first four-coordinate block; their decoded finite index is exactly the original one. -/
theorem encodeInput_gradient {α : Type*} (k : ℕ) (parameter : α) (g : Fin 4 → α)
    (s y : Fin k → Fin 4 → α) (zero : α) (j : Fin 4) :
    encodeInput k parameter g s y zero (1+j.val)=g j := by
  have hn : 1+j.val≠0 := by omega
  have hl : 1+j.val≤4 := by have := j.isLt; omega
  simp only [encodeInput,ite_eq_right hn,dite_eq_left hl]
  congr 1
  apply Fin.ext
  dsimp only
  omega

/-- Every encoded total-step coordinate recovers exactly its original finite age and physical coordinate.
Use: Preserve actual recorded total steps in the genuine newest-first storage order.
Article: main_krylov, prop:deep, exact genuine source input coordinates.
Proof: The step slots lie in their exact original block. Natural quotient and remainder by four recover the original finite record age and physical coordinate. -/
theorem encodeInput_step {α : Type*} (k : ℕ) (parameter : α) (g : Fin 4 → α)
    (s y : Fin k → Fin 4 → α) (zero : α) (i : Fin k) (j : Fin 4) :
    encodeInput k parameter g s y zero (5+4*i.val+j.val)=s i j := by
  -- Decode the true step block offset before recovering the finite record age and physical coordinate.
  have hn : 5+4*i.val+j.val≠0 := by omega
  have hl : ¬5+4*i.val+j.val≤4 := by omega
  have hu : 5+4*i.val+j.val<5+4*k := by have := i.isLt; have := j.isLt; omega
  simp only [encodeInput,ite_eq_right hn,dite_eq_right hl,dite_eq_left hu]
  congr 1 <;> apply Fin.ext <;> dsimp only <;> have := i.isLt <;> have := j.isLt <;> omega

/-- Every encoded measured-secant coordinate recovers precisely its true finite age and physical coordinate.
Use: Preserve the actual gradient-difference observations in the real source stack.
Article: main_krylov, prop:deep, exact genuine source input coordinates.
Proof: The image block starts after the actual step block. Subtract its exact original offset, then take quotient and remainder by four. -/
theorem encodeInput_image {α : Type*} (k : ℕ) (parameter : α) (g : Fin 4 → α)
    (s y : Fin k → Fin 4 → α) (zero : α) (i : Fin k) (j : Fin 4) :
    encodeInput k parameter g s y zero (5+4*k+4*i.val+j.val)=y i j := by
  -- Decode the true measured-secant block offset before recovering its actual finite indices.
  have hn : 5+4*k+4*i.val+j.val≠0 := by omega
  have hl : ¬5+4*k+4*i.val+j.val≤4 := by omega
  have hu : ¬5+4*k+4*i.val+j.val<5+4*k := by omega
  have hu' : 5+4*k+4*i.val+j.val<5+8*k := by have := i.isLt; have := j.isLt; omega
  simp only [encodeInput,ite_eq_right hn,dite_eq_right hl,dite_eq_right hu,dite_eq_left hu']
  congr 1 <;> apply Fin.ext <;> dsimp only <;> have := i.isLt <;> have := j.isLt <;> omega

/-- Every index outside the genuine finite source stack has its specified default value.
Use: Handle all totalized certificate input functions without exposing additional source data.
Article: main_krylov, prop:deep, exact genuine source input coordinates.
Proof: Outside the true finite block, every earlier original branch condition is false. -/
theorem encodeInput_outside {α : Type*} (k : ℕ) (parameter : α) (g : Fin 4 → α)
    (s y : Fin k → Fin 4 → α) (zero : α) {j : ℕ} (hj : 5+8*k≤j) :
    encodeInput k parameter g s y zero j=zero := by
  have hn : j≠0 := by omega
  have hl : ¬j≤4 := by omega
  have hs : ¬j<5+4*k := by omega
  have hy : ¬j<5+8*k := by omega
  simp only [encodeInput,ite_eq_right hn,dite_eq_right hl,dite_eq_right hs,dite_eq_right hy]

/-- Encoding the genuine finite source inputs commutes exactly with every value interpretation.
Use: Relate compiled expression inputs and actual physical source coordinates.
Article: main_krylov, prop:deep, exact genuine source input coordinates.
Proof: Each exact finite input branch selects the same original value before or after interpretation. -/
theorem encodeInput_map {α β : Type*} (f : α → β) (k : ℕ) (parameter : α) (g : Fin 4 → α)
    (s y : Fin k → Fin 4 → α) (zero : α) (j : ℕ) :
    f (encodeInput k parameter g s y zero j)=encodeInput k (f parameter) (f ∘ g)
      (fun i => f ∘ s i) (fun i => f ∘ y i) (f zero) j := by
  unfold encodeInput
  split_ifs <;> rfl

end
end krylov.Correction.Certificate
