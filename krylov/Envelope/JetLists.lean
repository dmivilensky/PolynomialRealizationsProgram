import krylov.Envelope.JetSubspace
import krylov.Stability.SmoothLists
import Mathlib.Data.List.GetD

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, actual finite observed first-jet lists.
Use: preserve genuine reference-value and derivative subspace membership
through actual complete-history list operations and finite smooth charts.
Source: actual C-two finite-list charts, local constancy of their true length
and standard locality of the derivative; no cycle expansion is assumed.
-/

namespace krylov.Envelope
noncomputable section
open Filter Topology krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A genuine locally C-two finite observed list whose actual coordinate first jets belong to the prescribed true linear subspace.
Use: A genuine locally C-two finite observed list whose actual coordinate first jets belong to the prescribed true linear subspace.
Article: main_krylov, apB:lem:filtration, actual finite observed first-jet lists.
Proof: Every coordinate is read from the actual list, including its genuine zero defaults. -/
def JetListAt (J : Submodule ℝ (E × E)) (v : ℝ → List E) : Prop :=
  SmoothListAt 2 v 0 ∧ ∀ i, ((v 0).getD i 0,deriv (fun t => (v t).getD i 0) 0)∈J

/-- A genuine finite smooth observation chart has its true reference length on an actual neighborhood.
Use: A genuine finite smooth observation chart has its true reference length on an actual neighborhood.
Article: main_krylov, apB:lem:filtration, actual finite observed first-jet lists.
Proof: Take lengths in the real local finite-array chart. -/
theorem smoothList_length_eventually {v : ℝ → List E} {r : WithTop ℕ∞}
    (hv : SmoothListAt r v 0) : ∀ᶠ t in 𝓝 (0 : ℝ), (v t).length=(v 0).length := by
  obtain ⟨n,data,_,he⟩ := hv
  have h0 := he.self_of_nhds
  filter_upwards [he] with t ht
  simp only [ht,h0,List.length_ofFn]

/-- The actual empty observed history has its true first jets in every real linear subspace.
Use: The actual empty observed history has its true first jets in every real linear subspace.
Article: main_krylov, apB:lem:filtration, actual finite observed first-jet lists.
Proof: Every actual coordinate is the constant zero vector. -/
theorem JetListAt.nil (J : Submodule ℝ (E × E)) : JetListAt J (fun _ => []) := by
  refine ⟨SmoothListAt.nil 2 0,?_⟩
  intro i
  simp only [List.getD_nil,deriv_const]
  exact J.zero_mem

/-- Prepending a genuine smooth observation preserves true first-jet membership.
Use: Prepending a genuine smooth observation preserves true first-jet membership.
Article: main_krylov, apB:lem:filtration, actual finite observed first-jet lists.
Proof: The actual head and successor coordinates are exactly the supplied true observations. -/
theorem JetListAt.cons {J : Submodule ℝ (E × E)} {v : ℝ → List E} {a : ℝ → E}
    (ha : ContDiffAt ℝ 2 a 0) (haj : (a 0,deriv a 0)∈J) (hv : JetListAt J v) :
    JetListAt J (fun t => a t::v t) := by
  refine ⟨hv.1.cons ha,?_⟩
  intro i
  cases i with
  | zero => simpa only [List.getD_cons_zero] using haj
  | succ i => simpa only [List.getD_cons_succ] using hv.2 i

/-- Actual observed-list jet membership transfers through any true subspace inclusion.
Use: Actual observed-list jet membership transfers through any true subspace inclusion.
Article: main_krylov, apB:lem:filtration, actual finite observed first-jet lists.
Proof: Transfer each genuine coordinate jet. -/
theorem JetListAt.mono {J J' : Submodule ℝ (E × E)} {v : ℝ → List E}
    (hv : JetListAt J v) (hJJ : J≤J') : JetListAt J' v :=
  ⟨hv.1,fun i => hJJ (hv.2 i)⟩

/-- Genuinely locally equal observed lists have identical actual coordinate first jets.
Use: Genuinely locally equal observed lists have identical actual coordinate first jets.
Article: main_krylov, apB:lem:filtration, actual finite observed first-jet lists.
Proof: Use the true local chart equality and derivative locality coordinate by coordinate. -/
theorem JetListAt.congr {J : Submodule ℝ (E × E)} {v w : ℝ → List E}
    (hv : JetListAt J v) (he : w=ᶠ[𝓝 (0 : ℝ)]v) : JetListAt J w := by
  obtain ⟨n,data,hd,hobs⟩ := hv.1
  refine ⟨⟨n,data,hd,he.trans hobs⟩,?_⟩
  intro i
  have hget : (fun t => (w t).getD i 0)=ᶠ[𝓝 (0 : ℝ)]fun t => (v t).getD i 0 :=
    he.mono fun t ht => congrArg (fun l : List E => l.getD i 0) ht
  rw [show (w 0).getD i 0=(v 0).getD i 0 from hget.self_of_nhds,hget.deriv_eq]
  exact hv.2 i

/-- Concatenating genuine finite observed lists preserves their actual first-jet subspace.
Use: Concatenating genuine finite observed lists preserves their actual first-jet subspace.
Article: main_krylov, apB:lem:filtration, actual finite observed first-jet lists.
Proof: The real chart length is locally fixed, so each actual append coordinate is locally one fixed coordinate of its true input list. -/
theorem JetListAt.append {J : Submodule ℝ (E × E)} {v w : ℝ → List E}
    (hv : JetListAt J v) (hw : JetListAt J w) : JetListAt J (fun t => v t++w t) := by
  refine ⟨hv.1.append hw.1,?_⟩
  intro i
  -- The actual local list length fixes which real input supplies each appended coordinate.
  have hlen := smoothList_length_eventually hv.1
  by_cases hi : i<(v 0).length
  · have he : (fun t => (v t++w t).getD i 0)=ᶠ[𝓝 (0 : ℝ)]fun t => (v t).getD i 0 := by
      filter_upwards [hlen] with t ht
      exact List.getD_append _ _ _ _ (by omega)
    rw [show (v 0++w 0).getD i 0=_ from he.self_of_nhds,he.deriv_eq]
    exact hv.2 i
  · have he : (fun t => (v t++w t).getD i 0)=ᶠ[𝓝 (0 : ℝ)]fun t => (w t).getD (i-(v 0).length) 0 := by
      filter_upwards [hlen] with t ht
      rw [List.getD_append_right _ _ _ _ (by omega),ht]
    rw [show (v 0++w 0).getD i 0=_ from he.self_of_nhds,he.deriv_eq]
    exact hw.2 _

/-- Removing any true finite observed prefix preserves actual coordinate first jets.
Use: Removing any true finite observed prefix preserves actual coordinate first jets.
Article: main_krylov, apB:lem:filtration, actual finite observed first-jet lists.
Proof: Each real remaining coordinate is the original actual coordinate at the shifted true index. -/
theorem JetListAt.drop {J : Submodule ℝ (E × E)} {v : ℝ → List E}
    (hv : JetListAt J v) (k : ℕ) : JetListAt J (fun t => (v t).drop k) := by
  refine ⟨hv.1.drop k,?_⟩
  intro i
  have he : (fun t => ((v t).drop k).getD i 0)=(fun t => (v t).getD (k+i) 0) := by
    funext t
    simp only [List.getD_eq_getElem?_getD,List.getElem?_drop]
  rw [show ((v 0).drop k).getD i 0=(v 0).getD (k+i) 0 from congrFun he 0,he]
  exact hv.2 _

/-- A genuine observed jet list admits a true C-two finite-array chart with the same actual first-jet membership in every coordinate.
Use: A genuine observed jet list admits a true C-two finite-array chart with the same actual first-jet membership in every coordinate.
Article: main_krylov, apB:lem:filtration, actual finite observed first-jet lists.
Proof: Read each actual finite coordinate through the real local list equality and transfer its derivative by locality. -/
theorem JetListAt.chart {J : Submodule ℝ (E × E)} {v : ℝ → List E} (hv : JetListAt J v) :
    ∃ n : ℕ, ∃ data : ℝ → Fin n → E, ContDiffAt ℝ 2 data 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), v t=List.ofFn (data t)) ∧
      ∀ i, (data 0 i,deriv (fun t => data t i) 0)∈J := by
  -- Recover the true finite chart and identify each actual coordinate on the same neighborhood.
  obtain ⟨n,data,hd,he⟩ := hv.1
  refine ⟨n,data,hd,he,?_⟩
  intro i
  have hget : (fun t => (v t).getD i.val 0)=ᶠ[𝓝 (0 : ℝ)]fun t => data t i := by
    filter_upwards [he] with t ht
    simp only [ht,List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_eq_left,Option.getD_some]
  have hj := hv.2 i.val
  rwa [show (v 0).getD i.val 0=data 0 i from hget.self_of_nhds,hget.deriv_eq] at hj
end
end krylov.Envelope
