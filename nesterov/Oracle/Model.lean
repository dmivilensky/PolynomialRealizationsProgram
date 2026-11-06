import polyak.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Data.Fin.Tuple.Basic

/-! A deterministic first-order black-box model. Query and output maps may
be arbitrary, adaptive and discontinuous. Their only objective information is
the previous queried points, function values and gradient vectors. -/
namespace nesterov.Oracle
noncomputable section
open Set Filter
open scoped Topology

abbrev Reply (E : Type*) := ℝ×E
abbrev Transcript (E : Type*) (n : ℕ) := Fin n→E×Reply E

structure Policy (E : Type*) where
  query : (n : ℕ)→Transcript E n→E
  output : (n : ℕ)→Transcript E n→E

namespace Policy
variable {E : Type*} (A : Policy E)

def run (O : E→Reply E) : (n : ℕ)→Transcript E n
  | 0 => Fin.elim0
  | n+1 =>
    let t := run O n
    let x := A.query n t
    Fin.snoc t (x,O x)

def point (O : E→Reply E) (n : ℕ) : E := A.query n (A.run O n)
def result (O : E→Reply E) (n : ℕ) : E := A.output n (A.run O n)

@[simp] theorem run_castSucc (O : E→Reply E) (n : ℕ) (i : Fin n) :
    A.run O (n+1) i.castSucc=A.run O n i := by simp [run]

@[simp] theorem run_last (O : E→Reply E) (n : ℕ) :
    A.run O (n+1) (Fin.last n)=(A.point O n,O (A.point O n)) := by simp [run,point]

theorem run_eq_of_answers {O₁ O₂ : E→Reply E} {N : ℕ}
    (h : ∀ k<N,O₁ (A.point O₁ k)=O₂ (A.point O₁ k)) : A.run O₁ N=A.run O₂ N := by
  have hh (n : ℕ) (hn : n≤N) : A.run O₁ n=A.run O₂ n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hi := ih (by omega)
      have ho := h n (by omega)
      unfold point at ho
      change (Fin.snoc (A.run O₁ n) (A.query n (A.run O₁ n),O₁ (A.query n (A.run O₁ n))) : Transcript E (n+1))=
        (Fin.snoc (A.run O₂ n) (A.query n (A.run O₂ n),O₂ (A.query n (A.run O₂ n))) : Transcript E (n+1))
      rw [←hi,ho]
  exact hh N le_rfl

theorem result_eq_of_answers {O₁ O₂ : E→Reply E} {N : ℕ}
    (h : ∀ k<N,O₁ (A.point O₁ k)=O₂ (A.point O₁ k)) : A.result O₁ N=A.result O₂ N := by
  unfold result
  rw [A.run_eq_of_answers h]

end Policy

def firstOrderOracle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E→ℝ) : E→Reply E := fun x=>(f x,gradient f x)

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Horizon-dependent policies are included: a method may know its allowed
number of calls, and it may use completely different rules in each dimension. -/
abbrev Algorithm := (N d : ℕ)→Policy (Space d)

/-- Initial point is zero. Objective values may be shifted arbitrarily;
there is no access to the objective apart from its exact first-order oracle. -/
def Instance (q : ℝ) (d : ℕ) (f : Space d→ℝ) (xstar : Space d) : Prop :=
  polyak.SmoothStronglyConvex q 1 f ∧ gradient f xstar=0 ∧ ‖xstar‖≤1

def UniformGeometricRate (A : Algorithm) (q r : ℝ) : Prop :=
  ∃ C : ℝ,0<C ∧ ∀ N d : ℕ,∀ (f : Space d→ℝ) (xstar : Space d),
    Instance q d f xstar →
      ‖(A N d).result (firstOrderOracle f) N-xstar‖≤C*r^N

/-- The extended real value retains policies with no finite geometric
bound. Such policies have factor +∞, rather than an undefined real supremum. -/
def rate (A : Algorithm) (q : ℝ) : EReal :=
  sInf {R : EReal | ∃ r : ℝ,0≤r ∧ R=(r:EReal) ∧ UniformGeometricRate A q r}

theorem le_rate_of_uniform {A : Algorithm} {q b : ℝ}
    (h : ∀ r : ℝ,0≤r → UniformGeometricRate A q r → b≤r) : (b:EReal)≤rate A q := by
  apply le_sInf
  rintro R ⟨r,hr,rfl,hR⟩
  exact EReal.coe_le_coe_iff.mpr (h r hr hR)

end
end nesterov.Oracle
