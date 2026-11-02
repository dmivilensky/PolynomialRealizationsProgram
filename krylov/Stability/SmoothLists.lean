import krylov.Methods.ObservedRules
import Mathlib.Data.List.OfFn

/-!
Article: main_krylov, def:classes and lem:U(d), actual finite observation charts.
Use: handle genuine finite history and correction traces without giving
the raw variable-length lists an artificial vector-space structure.
Source: actual finite-vector local charts, exact list coordinate identities
and the standard finite-product C-r composition calculus.
-/

namespace krylov.Stability
noncomputable section
open Filter Topology
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A genuinely finite locally fixed observed list has a C-r finite-vector chart.
Use: A genuinely finite locally fixed observed list has a C-r finite-vector chart.
Article: main_krylov, def:classes and lem:U(d), actual finite observation charts.
Proof: The chart agrees locally with the actual list itself. -/
def SmoothListAt (r : WithTop ℕ∞) (v : X → List E) (x : X) : Prop :=
  ∃ n : ℕ, ∃ data : X → Fin n → E, ContDiffAt ℝ r data x ∧
    ∀ᶠ p in 𝓝 x, v p=List.ofFn (data p)

/-- The actual empty observed trace has a smooth finite chart.
Use: The actual empty observed trace has a smooth finite chart.
Article: main_krylov, def:classes and lem:U(d), actual finite observation charts.
Proof: Use the zero-dimensional genuine empty vector family. -/
theorem SmoothListAt.nil (r : WithTop ℕ∞) (x : X) : SmoothListAt r (fun _ : X => ([] : List E)) x := by
  refine ⟨0,fun _ _ => 0,contDiffAt_const,?_⟩
  exact Filter.Eventually.of_forall fun _ => rfl

/-- Prepending a real C-r observation preserves a genuine smooth finite trace chart.
Use: Prepending a real C-r observation preserves a genuine smooth finite trace chart.
Article: main_krylov, def:classes and lem:U(d), actual finite observation charts.
Proof: Use the true finite cons coordinates and exact actual list equality. -/
theorem SmoothListAt.cons {r : WithTop ℕ∞} {v : X → List E} {a : X → E} {x : X}
    (ha : ContDiffAt ℝ r a x) (hv : SmoothListAt r v x) : SmoothListAt r (fun p => a p::v p) x := by
  obtain ⟨n,data,hd,he⟩ := hv
  refine ⟨n+1,fun p => Fin.cons (a p) (data p),contDiffAt_pi.mpr ?_,?_⟩
  · exact Fin.cases ha (fun i => (contDiffAt_pi.mp hd) i)
  · filter_upwards [he] with p hp
    rw [hp,List.ofFn_cons]

/-- Concatenating actual smooth finite observed traces preserves their genuine C-r chart.
Use: Concatenating actual smooth finite observed traces preserves their genuine C-r chart.
Article: main_krylov, def:classes and lem:U(d), actual finite observation charts.
Proof: Append the two actual finite coordinate families and use the real list concatenation identity. -/
theorem SmoothListAt.append {r : WithTop ℕ∞} {v w : X → List E} {x : X}
    (hv : SmoothListAt r v x) (hw : SmoothListAt r w x) : SmoothListAt r (fun p => v p++w p) x := by
  -- Concatenation changes only the true finite coordinate indexing.
  obtain ⟨m,a,ha,he⟩ := hv
  obtain ⟨n,b,hb,hf⟩ := hw
  refine ⟨m+n,fun p => Fin.append (a p) (b p),contDiffAt_pi.mpr ?_,?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using (contDiffAt_pi.mp ha) i
    · simpa only [Fin.append_right] using (contDiffAt_pi.mp hb) j
  · filter_upwards [he,hf] with p hp hq
    rw [hp,hq,List.ofFn_fin_append]

/-- Every genuine observed finite trace coordinate is locally C-r, with zero outside its actual length.
Use: Every genuine observed finite trace coordinate is locally C-r, with zero outside its actual length.
Article: main_krylov, def:classes and lem:U(d), actual finite observation charts.
Proof: Read the corresponding true finite chart coordinate, or the constant zero outside the actual finite index range. -/
theorem SmoothListAt.getD {r : WithTop ℕ∞} {v : X → List E} {x : X}
    (hv : SmoothListAt r v x) (i : ℕ) : ContDiffAt ℝ r (fun p => (v p).getD i 0) x := by
  obtain ⟨n,data,hd,he⟩ := hv
  -- The local actual list length fixes whether this observation coordinate exists.
  by_cases hi : i<n
  · apply ((contDiffAt_pi.mp hd) ⟨i,hi⟩).congr_of_eventuallyEq
    filter_upwards [he] with p hp
    simp only [hp,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,dite_eq_left,Option.getD_some]
  · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
    filter_upwards [he] with p hp
    simp only [hp,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_right hi,Option.getD_none]

/-- Removing an actual finite observed prefix preserves its true C-r chart.
Use: Removing an actual finite observed prefix preserves its true C-r chart.
Article: main_krylov, def:classes and lem:U(d), actual finite observation charts.
Proof: Restrict the real coordinate family to the actual remaining index interval. -/
theorem SmoothListAt.drop {r : WithTop ℕ∞} {v : X → List E} {x : X}
    (hv : SmoothListAt r v x) (k : ℕ) : SmoothListAt r (fun p => (v p).drop k) x := by
  -- Restrict the actual finite chart to precisely the surviving observed indices.
  obtain ⟨n,data,hd,he⟩ := hv
  let f : X → Fin (n-k) → E := fun p i => data p ⟨k+i.val,by omega⟩
  refine ⟨n-k,f,contDiffAt_pi.mpr (fun i => (contDiffAt_pi.mp hd) _),?_⟩
  filter_upwards [he] with p hp
  rw [hp]
  apply List.ext_getElem
  · simp only [List.length_drop,List.length_ofFn]
  · intro i hi hj
    simp only [List.getElem_drop,List.getElem_ofFn,f]
end
end krylov.Stability
