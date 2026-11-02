import krylov.Information.PreQuadraticGram
import krylov.Information.ForwardForms

/-!
Article: main_krylov, s4:cor-Q, one true physical twin common to every method.
Use: reflection in the genuine original common CG flag, with zero
intermediate correction defects, preserves the actual complete prefix and
last probe for every globally CG-consistent nonanticipating source method.
Source: exact physical reflected-column preservation and the actual
pre-quadratic full-history shadow theorem; no method-dependent twin is chosen.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The concrete physical flag-reflected scenario formed in the original common CG direction basis, with genuine zero intermediate defects.
Use: the same actual twin is chosen before every competing source method.
Article: main_krylov, s4:cor-Q, actual method-independent pre-quadratic twin. -/
def Scenario.preQuadraticTwin (S : Scenario (N+1)) (Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) : Scenario (N+1) :=
  let D := fullBasisMatrix (referenceDirectionColumns Q g)
  (((S.inCoordinates D).reflect N).inPhysical D).withCorrections (fun _ => 0)

/-- The actual common physical twin preserves every original reference-CG-direction probe action through the last original source probe.
Use: derive all competing methods' genuine observation equality from original common probe data.
Article: main_krylov, s4:cor-Q, genuine common physical information twin.
Proof: actual full reference rank justifies the genuine common direction inverse. The exact physical reflected-column identity preserves each original chronological CG column; replacing intermediate defects by zero leaves every genuine probe unchanged. -/
theorem Scenario.preQuadraticTwin_probe (S : Scenario (N+1))
    (Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hQ : Q.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount Q hQ g=N+1)
    {k : ℕ} (hk : k≤N) :
    (S.preQuadraticTwin Q g).probeOracle k (CG.direction (cgOperator Q) g k)=
      S.probeOracle k (CG.direction (cgOperator Q) g k) := by
  -- The actual full common CG direction basis identifies each preserved physical probe column.
  let D := fullBasisMatrix (referenceDirectionColumns Q g)
  have hD : IsUnit D.det := fullBasisMatrix_unit _ (referenceDirectionColumns_independent Q hQ g hcount)
  let j : Fin (N+1) := ⟨k,by omega⟩
  have hd : euclideanColumn D j=CG.direction (cgOperator Q) g k := rfl
  unfold Scenario.preQuadraticTwin Scenario.probeOracle
  rw [Scenario.withCorrections_probe,← hd]
  ext i
  change ((((S.inCoordinates D).reflect N).inPhysical D).probe k*D) i j=(S.probe k*D) i j
  have he := (S.inCoordinates D).physical_reflect_probe_column D hD hk j rfl i
  rw [S.inCoordinates_inPhysical D hD] at he
  exact he

/-- The true common physical twin of a pre-quadratic source scenario remains in exactly the original pre-quadratic information class.
Use: all globally CG-consistent methods keep the same real reference prefix on the common twin.
Article: main_krylov, s4:cor-Q, genuine common physical information twin.
Proof: the exact common reflected probe identity preserves every primitive original pre-quadratic reference-direction action. -/
theorem Scenario.PreQuadratic.twin {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    (h : S.PreQuadratic (cgOperator Q) g N) :
    (S.preQuadraticTwin Q g).PreQuadratic (cgOperator Q) g N := by
  intro k hk
  rw [S.preQuadraticTwin_probe Q hQ g hcount hk.le]
  exact h k hk

/-- One actual common physical twin preserves the complete real preterminal history of every globally CG-consistent method.
Use: the same twin works simultaneously for the full competing source method class, including arbitrary finite adaptive correction trees.
Article: main_krylov, s4:cor-Q, genuine common physical information twin.
Proof: both actual source scenarios are genuinely pre-quadratic relative to the same true reference. Their complete histories therefore equal that method's original quadratic history at every genuine prefix. -/
theorem Scenario.PreQuadratic.twin_run {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    (h : S.PreQuadratic (cgOperator Q) g N)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m)
    {k : ℕ} (hk : k≤N) :
    methodRun m S.probeOracle (S.correctionOracle N) g k=
      methodRun m (S.preQuadraticTwin Q g).probeOracle ((S.preQuadraticTwin Q g).correctionOracle N) g k := by
  have hp := cgOperator_positive Q hQ
  exact (h.run hp.1 hp.2 m hm hk).trans ((h.twin hQ hcount).run hp.1 hp.2 m hm hk).symm

/-- The same genuine common physical twin also preserves every globally CG-consistent method's actual last probe.
Use: each true method must make the same real terminal correction decision on the original scenario and its common twin.
Article: main_krylov, s4:cor-Q, genuine common physical information twin.
Proof: the complete actual prefixes agree. The true chosen last direction is a positive multiple of the original common CG direction, whose actual source probe is exactly preserved by the common physical reflection. -/
theorem Scenario.PreQuadratic.twin_last_probe {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    (h : S.PreQuadratic (cgOperator Q) g N)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) :
    probedProbe m S.probeOracle (S.correctionOracle N) g N=
      probedProbe m (S.preQuadraticTwin Q g).probeOracle ((S.preQuadraticTwin Q g).correctionOracle N) g N := by
  -- Identical actual histories give the same chosen final direction before its true probe.
  have hp := cgOperator_positive Q hQ
  obtain ⟨c,_,hd⟩ := h.direction hp.1 hp.2 m hm (le_refl N)
  have hh := h.twin_run hQ hcount m hm (le_refl N)
  unfold probedProbe probedDirection
  rw [← hh]
  change S.probeOracle N (probedDirection m S.probeOracle (S.correctionOracle N) g N)=
    (S.preQuadraticTwin Q g).probeOracle N (probedDirection m S.probeOracle (S.correctionOracle N) g N)
  rw [hd,map_smul,map_smul,S.preQuadraticTwin_probe Q hQ g hcount le_rfl]

end
end krylov.Information
