import krylov.XR.XRFCFunction
import krylov.Stability.ContDiffSolve

/-!
Article: main_krylov, lem:xr-local, genuine endpoint-coordinate calculus.
Use: a fixed chronological endpoint chart supplies the actual observed
steps, secants, transported covectors and scalar defects. The virtual
XRFC/XRFC-F query is C^r at its actual inverse and secant-quotient domains.
Smoothness of an executed trajectory or of a computed inverse is not an
input. Source: finite C^r calculus and the proved analytic observed solves.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- All true endpoint coordinates of a chronological k-pair window.
Only actual points, values and gradients enter this chart. -/
abbrev EndpointChart (E : Type*) (k : ℕ) :=
  (Fin (k + 1) → E) × (Fin (k + 1) → ℝ) × (Fin (k + 1) → E)

def endpointStep {k : ℕ} (C : EndpointChart E k) (i : Fin k) : E :=
  C.1 i.succ - C.1 i.castSucc

def endpointImage {k : ℕ} (C : EndpointChart E k) (i : Fin k) : E :=
  C.2.2 i.succ - C.2.2 i.castSucc

def endpointDefect {k : ℕ} (C : EndpointChart E k) (i : Fin k) : ℝ :=
  C.2.1 i.succ - C.2.1 i.castSucc - inner ℝ (C.2.2 i.castSucc) (endpointStep C i) -
    inner ℝ (endpointStep C i) (endpointImage C i) / 2

def endpointSplit {k : ℕ} (C : EndpointChart E k) (i : Fin k) : ℝ :=
  inner ℝ (endpointImage C i) (C.1 (Fin.last k) - C.1 i.castSucc) /
    inner ℝ (endpointStep C i) (endpointImage C i) - 1 / 2

/-- The literal chronological latest model, with the exact F diagonal
when enabled. No scalar clipping or acceptance test is built into XRFC. -/
def endpointVirtualModel {k : ℕ} (values : Bool) (C : EndpointChart E k) :
    Matrix (Fin k) (Fin k) ℝ :=
  latest (crossGram (endpointStep C) (endpointImage C)) -
    diagonal (fun i => if values then 12 * endpointSplit C i * endpointDefect C i else 0)

/-- The next physical virtual-model query in endpoint coordinates. -/
def endpointVirtualQuery {k : ℕ} (values : Bool) (trial : EndpointChart E k → ℝ)
    (C : EndpointChart E k) : E :=
  C.1 (Fin.last k) +
    modelVirtualCorrection (endpointStep C) (endpointVirtualModel values C) (C.2.2 (Fin.last k)) +
    trial C • modelDirection (endpointStep C) (endpointImage C)
      (endpointVirtualModel values C) (C.2.2 (Fin.last k))

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [CompleteSpace E] in
/-- The true endpoint-value model entries inherit the smoothness of their
actual coordinates, on precisely the observed nonzero secant quotients. -/
theorem contDiff_endpointVirtualModel {k : ℕ} {r : WithTop ℕ∞}
    (values : Bool) (C : X → EndpointChart E k) (x : X)
    (hC : ContDiffAt ℝ r C x)
    (hq : ∀ i, inner ℝ (endpointStep (C x) i) (endpointImage (C x) i) ≠ 0) :
    ∀ i j, ContDiffAt ℝ r (fun z => endpointVirtualModel values (C z) i j) x := by
  have hp (i : Fin (k + 1)) : ContDiffAt ℝ r (fun z => (C z).1 i) x :=
    (contDiffAt_pi.mp hC.fst) i
  have hf (i : Fin (k + 1)) : ContDiffAt ℝ r (fun z => (C z).2.1 i) x :=
    (contDiffAt_pi.mp hC.snd.fst) i
  have hg (i : Fin (k + 1)) : ContDiffAt ℝ r (fun z => (C z).2.2 i) x :=
    (contDiffAt_pi.mp hC.snd.snd) i
  have hs (i : Fin k) : ContDiffAt ℝ r (fun z => endpointStep (C z) i) x :=
    (hp i.succ).sub (hp i.castSucc)
  have hy (i : Fin k) : ContDiffAt ℝ r (fun z => endpointImage (C z) i) x :=
    (hg i.succ).sub (hg i.castSucc)
  have hd (i : Fin k) : ContDiffAt ℝ r (fun z => endpointDefect (C z) i) x :=
    (((hf i.succ).sub (hf i.castSucc)).sub ((hg i.castSucc).inner ℝ (hs i))).sub
      (((hs i).inner ℝ (hy i)).div_const 2)
  have hl (i : Fin k) : ContDiffAt ℝ r (fun z => endpointSplit (C z) i) x :=
    (((hy i).inner ℝ ((hp (Fin.last k)).sub (hp i.castSucc))).div
      ((hs i).inner ℝ (hy i)) (hq i)).sub contDiffAt_const
  intro i j
  have hm : ContDiffAt ℝ r (fun z =>
      latest (crossGram (endpointStep (C z)) (endpointImage (C z))) i j) x :=
    (hs (min i j)).inner ℝ (hy (max i j))
  apply hm.sub
  by_cases hij : i = j
  · subst j
    simp only [diagonal_apply_eq]
    cases values
    · exact contDiffAt_const
    · exact (contDiffAt_const.mul (hl i)).mul (hd i)
  · simp only [diagonal_apply_ne _ hij]
    exact contDiffAt_const

/-- Genuine endpoint and trial smoothness imply genuine smoothness of the
whole computed virtual query, including its two actual finite inverse solves. -/
theorem contDiff_endpointVirtualQuery {k : ℕ} {r : WithTop ℕ∞}
    (values : Bool) (C : X → EndpointChart E k) (trial : EndpointChart E k → ℝ) (x : X)
    (hC : ContDiffAt ℝ r C x) (ht : ContDiffAt ℝ r trial (C x))
    (hq : ∀ i, inner ℝ (endpointStep (C x) i) (endpointImage (C x) i) ≠ 0)
    (hM : (endpointVirtualModel values (C x)).det ≠ 0)
    (hY : (crossGram (endpointImage (C x)) (endpointStep (C x))).det ≠ 0) :
    ContDiffAt ℝ r (fun z => endpointVirtualQuery values trial (C z)) x := by
  have hp (i : Fin (k + 1)) : ContDiffAt ℝ r (fun z => (C z).1 i) x :=
    (contDiffAt_pi.mp hC.fst) i
  have hg (i : Fin (k + 1)) : ContDiffAt ℝ r (fun z => (C z).2.2 i) x :=
    (contDiffAt_pi.mp hC.snd.snd) i
  have hs (i : Fin k) : ContDiffAt ℝ r (fun z => endpointStep (C z) i) x :=
    (hp i.succ).sub (hp i.castSucc)
  have hy (i : Fin k) : ContDiffAt ℝ r (fun z => endpointImage (C z) i) x :=
    (hg i.succ).sub (hg i.castSucc)
  have hmodel := contDiff_endpointVirtualModel values C x hC hq
  have hw := contDiff_modelCoefficients (fun z => endpointStep (C z))
    (fun z => endpointVirtualModel values (C z)) (fun z => (C z).2.2 (Fin.last k)) x
    hs hmodel (hg (Fin.last k)) hM
  have hc := contDiff_combine (fun z => endpointStep (C z)) _ x hs hw
  have hv := (hg (Fin.last k)).add (contDiff_combine (fun z => endpointImage (C z)) _ x hy hw)
  have hd := contDiff_conjugacyDirection (fun z => endpointStep (C z))
    (fun z => endpointImage (C z)) _ x hs hy hv hY
  exact ((hp (Fin.last k)).add hc).add ((ht.comp x hC).smul hd)

end
end krylov.XR
