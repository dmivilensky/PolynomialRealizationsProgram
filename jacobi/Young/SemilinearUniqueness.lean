import jacobi.Young.Hyperbolic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen

/-!
Article: jacobi, Theorem D.7.
The actual second-order polynomial ODE is rewritten as a first-order system
on R². Its smooth vector field is locally Lipschitz, so equal initial values
and slopes force global equality on the connected real line. This common
uniqueness lemma also supports the zero-multiplier elliptic endpoint.
Source: Picard--Lindelof uniqueness (mathlib), continued by connectedness.
Use: shares the same Picard--Lindelof continuation argument between Young, elliptic and Keller equality profiles.
-/
namespace jacobi.Young
noncomputable section
open Set Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Global uniqueness for any actual locally Lipschitz autonomous planar ODE.
Use: shares the same Picard--Lindelof continuation argument between Young,
elliptic and Keller equality profiles.
Article: jacobi, Section 3.2 (sharp Young inequality).
Source: Picard--Lindelof uniqueness and connectedness of the real line.
Proof: the coincidence set is closed by continuity and open by local
Lipschitz uniqueness. Its initial point makes it the whole connected line. -/
theorem autonomous_unique {V : ℝ × ℝ → ℝ × ℝ} (hV : LocallyLipschitz V)
    {F G : ℝ → ℝ × ℝ} (hF : ∀ x, HasDerivAt F (V (F x)) x)
    (hG : ∀ x, HasDerivAt G (V (G x)) x) {b : ℝ} (hb : F b=G b) : F=G := by
  -- Genuine local solution uniqueness propagates from every coincidence point.
  have hFc : Continuous F := continuous_iff_continuousAt.mpr (fun x => (hF x).continuousAt)
  have hGc : Continuous G := continuous_iff_continuousAt.mpr (fun x => (hG x).continuousAt)
  have hclosed : IsClosed {x | F x=G x} := isClosed_eq hFc hGc
  have hopen : IsOpen {x | F x=G x} := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨K,S,hS,hLip⟩ := hV (F x)
    have hFS : ∀ᶠ y in 𝓝 x, F y∈S := hFc.continuousAt.preimage_mem_nhds hS
    have hGS : ∀ᶠ y in 𝓝 x, G y∈S := by
      apply hGc.continuousAt.preimage_mem_nhds
      simpa only [show G x=F x from hx.symm] using hS
    exact ODE_solution_unique_of_eventually (v := fun _ => V)
      (s := fun _ => S) (Eventually.of_forall fun _ => hLip)
      (hFS.mono fun y hy => ⟨hF y,hy⟩) (hGS.mono fun y hy => ⟨hG y,hy⟩) hx
  have hall : {x | F x=G x}=univ := IsClopen.eq_univ ⟨hclosed,hopen⟩ ⟨b,hb⟩
  funext x
  have hx : x∈{y | F y=G y} := by rw [hall]; trivial
  exact hx

/-- The first-order vector field for the semilinear second-order Green equation.
Use: a single Picard--Lindelof argument classifies the Young profile and the free-mass elliptic endpoint.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def semilinearField (a : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (z.2,4*z.1-a*z.1^2)

/-- Global uniqueness for the actual semilinear second-order equation.
Use: identifies a positive decaying equality solution with its explicit sech-squared profile.
Article: jacobi, Section 3.2 (sharp Young inequality).
Source: Picard--Lindelof uniqueness and connectedness of the real line.
Proof: the polynomial vector field is locally Lipschitz. The set where the
two value/slope pairs agree is closed by continuity and open by local ODE
uniqueness. The initial equality makes this clopen set the whole line. -/
theorem semilinear_unique {f d g e : ℝ → ℝ} (a b : ℝ)
    (hf : ∀ x, HasDerivAt f (d x) x)
    (hd : ∀ x, HasDerivAt d (4*f x-a*f x^2) x)
    (hg : ∀ x, HasDerivAt g (e x) x)
    (he : ∀ x, HasDerivAt e (4*g x-a*g x^2) x)
    (h0 : f b=g b) (h1 : d b=e b) : f=g ∧ d=e := by
  -- The polynomial equation is an instance of the shared actual planar uniqueness theorem.
  have hV : ContDiff ℝ 1 (semilinearField a) := by unfold semilinearField; fun_prop
  have hFG := autonomous_unique hV.locallyLipschitz
    (fun x => (hf x).prodMk (hd x)) (fun x => (hg x).prodMk (he x)) (Prod.ext h0 h1)
  exact ⟨funext (fun x => congrArg Prod.fst (congrFun hFG x)),
    funext (fun x => congrArg Prod.snd (congrFun hFG x))⟩

end
end jacobi.Young
