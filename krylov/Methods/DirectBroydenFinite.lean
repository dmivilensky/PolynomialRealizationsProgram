import krylov.Methods.DirectBroydenBounds
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), actual chronological finite domains.
Use: apply the compact finite-array calculus to every prefix of the literal
native direct Broyden recursion with its arbitrary original schedule.
Source: exact chronological record and finite schedule dictionaries.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open Set Filter Topology Asymptotics
open scoped InnerProductSpace
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual chronological observed pairs stored newest first.
Use: every finite native prefix has the genuine interpolation index.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenRecords (D : ℕ → E × E) : ℕ → List (E × E)
  | 0 => []
  | k+1 => D k::directBroydenRecords D k

/-- The actual native chronological direct model with all original pairs
and interpolation parameters.
Use: perturbation comparisons concern this literal executed recursion.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenNative (B0 : E →L[ℝ] E) (phi : ℕ → ℝ) (D : ℕ → E × E) (k : ℕ) : E →L[ℝ] E :=
  directBroydenOperatorModel B0 phi (directBroydenRecords D k)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Every actual chronological record prefix has exactly its true length.
Use: retain the original native interpolation coordinate in every update.
Article: main_krylov, prop:classical(c).
Proof: chronological record induction. -/
theorem directBroydenRecords_length (D : ℕ → E × E) (k : ℕ) :
    (directBroydenRecords D k).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [directBroydenRecords,List.length_cons,ih]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The genuine chronological prefix is the finite newest-first pair array.
Use: compact actual pair charts represent the literal native recursion.
Article: main_krylov, prop:classical(c).
Proof: both sides prepend the actual newest pair; true natural index
arithmetic identifies every older coordinate. -/
theorem directBroydenRecords_ofFn (D : ℕ → E × E) (k : ℕ) :
    directBroydenRecords D k=List.ofFn (fun i : Fin k => D (k-1-i.val)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [directBroydenRecords,List.ofFn_succ,ih,Fin.val_zero,Nat.sub_zero,Nat.add_sub_cancel]
    congr 1
    congr 1
    funext i
    congr 1
    simp only [Fin.val_succ]
    omega

/-- Genuine native models use only their actual finite interpolation prefix.
Use: compactification changes no executed model or pair.
Article: main_krylov, prop:classical(c).
Proof: chronological induction preserves every literal update parameter. -/
theorem directBroydenOperatorModel_schedule_congr (B0 : E →L[ℝ] E)
    (phi psi : ℕ → ℝ) (W : List (E × E)) (h : ∀ j<W.length,phi j=psi j) :
    directBroydenOperatorModel B0 phi W=directBroydenOperatorModel B0 psi W := by
  induction W with
  | nil => rfl
  | cons p W ih =>
    simp only [directBroydenOperatorModel]
    rw [ih (fun j hj => h j (by simp only [List.length_cons];omega)),h W.length (by simp only [List.length_cons];omega)]

/-- The actual native chronological recursion equals its genuine finite
primitive-array chart with exactly its original finite parameters.
Use: derived compact model/pivot bounds apply to every real native prefix.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: real schedule truncation changes no chronological coordinate; the
proved newest-first record dictionary then identifies the literal models. -/
theorem directBroydenNative_finite (B0 : E →L[ℝ] E) (phi : ℕ → ℝ)
    (D : ℕ → E × E) (k : ℕ) : directBroydenNative B0 phi D k=
      directBroydenFiniteModel B0 (fun i : Fin k => phi i.val) (fun i => D (k-1-i.val)) := by
  unfold directBroydenNative directBroydenFiniteModel
  rw [directBroydenRecords_ofFn]
  apply directBroydenOperatorModel_schedule_congr
  intro j hj
  have hjk : j<k := by simpa only [List.length_ofFn] using hj
  simp only [directBroydenFiniteSchedule,dite_eq_left hjk]

/-- The native direct model executes the literal next direct update with
its actual chronological interpolation parameter.
Use: perform the source perturbation induction on actual executed models.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: expand the true chronological head and its proved exact length. -/
theorem directBroydenNative_succ (B0 : E →L[ℝ] E) (phi : ℕ → ℝ)
    (D : ℕ → E × E) (k : ℕ) : directBroydenNative B0 phi D (k+1)=
      directBroydenOperatorUpdate (directBroydenNative B0 phi D k) (D k).1 (D k).2 (phi k) := by
  simp only [directBroydenNative,directBroydenRecords,directBroydenOperatorModel,directBroydenRecords_length]

end
end krylov.Methods
