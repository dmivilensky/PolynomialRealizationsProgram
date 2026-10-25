import polyak.FiniteHorizon.SourceFactories
import polyak.FiniteHorizon.PolyakSize
import polyak.Regularity.RightExtension

/-!
Article: Appendix C, construction of the uniform prefactor from actual source germs.
Use: the genuine linear source margins and the concrete branch factors produce
uniformly bounded interpolation data. All price, separation, energy and compact
closure inputs are then discharged by the preceding proved constructions.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Boundary Filter Set
open scoped Topology

def LinearSourceMargins7 (q T a b η : ℝ) : Prop := η≤1 ∧
  ∀ δ : ℝ,0<δ → δ≤η →
    0≤Real.sinh (V (T+δ)) ∧ Real.sinh (V (T+δ))≤Real.sinh (T+δ-Real.log q) ∧
    0≤b*δ/8 ∧ b*δ/8≤1 ∧
    4*(b*δ/8)≤Real.sinh (T+δ-Real.log q)^2-Real.sinh (V (T+δ))^2 ∧
    a*δ≤(Real.cosh (T+δ)-1)*(Real.sinh (T+δ-Real.log q)^2-Real.sinh (V (T+δ))^2)+
      2*(b*δ/8)*Real.sinh (T+δ-Real.log q)^2

theorem exists_banded_family_of_linear_source_germ {q T a b η : ℝ} {H : ℕ}
    (hq : 0<q) (ha : 0<a) (hη : 0<η) (hH : 7≤H)
    (hmargins : LinearSourceMargins7 q T a b η)
    (hfactory : ∀ᶠ t in 𝓝[≥] T,HasPhysicalFactors7 q t) :
    ∃ M δ₀ : ℝ,0<δ₀ ∧ ∀ δ : ℝ,0<δ → δ≤δ₀ →
      Nonempty (AboveRateData7 0 (2*q) (q^2) T a M H δ) := by
  obtain ⟨l,r,hT,hsub⟩:=mem_nhds_iff_exists_Ioo_subset.mp (eventually_nhdsWithin_iff.mp hfactory)
  let δ₀:=min η ((r-T)/2)
  have hδ₀ : 0<δ₀:=lt_min hη (by linarith [hT.2])
  let M:=normalizedSourceBound q (|T|+1)+a
  refine ⟨M,δ₀,hδ₀,?_⟩
  intro δ hδ hδbound
  have hδη : δ≤η:=hδbound.trans (min_le_left _ _)
  have hδr : δ≤(r-T)/2:=hδbound.trans (min_le_right _ _)
  have hδ1 : δ≤1:=hδη.trans hmargins.1
  obtain ⟨hu,huv,hγ,hγ1,hsmall,hε⟩:=hmargins.2 δ hδ hδη
  have hf:=hsub (show T+δ∈Ioo l r by constructor <;> linarith [hT.1,hT.2])
    (show T+δ∈Ici T by simp only [mem_Ici]; linarith)
  obtain ⟨W,hW,hfactor⟩:=hf
  obtain ⟨factors⟩:=hfactor (b*δ/8) (a*δ) hγ huv hsmall hε
  have ht : |T+δ|≤|T|+1:=by
    calc
      _≤|T|+|δ|:=abs_add_le _ _
      _=|T|+δ:=by rw [abs_of_pos hδ]
      _≤_:=by linarith
  refine ⟨{
    matrix:=normalizedMatrix7 W q (T+δ) (b*δ/8) hγ
    values:=normalizedValues7 W (T+δ) (b*δ/8) hγ
    factors:=factors
    source:=normalizedBanded7_source W hq (T+δ) (b*δ/8) hγ hW H hH
    bounded:=?_}⟩
  have hsize:=normalized_source_size_le W hq ht hγ hγ1 hW
  dsimp [M]
  nlinarith

theorem exists_prefactor_of_linear_source_germ {q T a b η : ℝ} {H : ℕ}
    (hq : 0<q) (ha : 0<a) (hη : 0<η) (hH : 7≤H)
    (hRate : growthRate 0 (2*q) (q^2) H≤Real.exp T)
    (hmargins : LinearSourceMargins7 q T a b η)
    (hfactory : ∀ᶠ t in 𝓝[≥] T,HasPhysicalFactors7 q t) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,envelope 0 (2*q) (q^2) H n≤C*Real.exp ((n : ℝ)*T) := by
  obtain ⟨M,δ₀,hδ₀,hfamily⟩:=exists_banded_family_of_linear_source_germ hq ha hη hH hmargins hfactory
  exact exists_prefactor_of_banded_family (by positivity) ha hδ₀ hH hRate hfamily

theorem exists_banded_family_of_right_source_germ {q T v' : ℝ} {H : ℕ}
    (hq : 0<q) (hV : HasDerivWithinAt V v' (Ici T) T) (hv' : v'<1) (hVT : 0<V T)
    (heq : T-Real.log q=V T) (hH : 7≤H)
    (hfactory : ∀ᶠ t in 𝓝[≥] T,HasPhysicalFactors7 q t) :
    ∃ a M δ₀ : ℝ,0<a ∧ 0<δ₀ ∧ ∀ δ : ℝ,0<δ → δ≤δ₀ →
      Nonempty (AboveRateData7 0 (2*q) (q^2) T a M H δ) := by
  let g:=Regularity.rightExtension V v' T
  have hg : HasDerivAt g v' T:=Regularity.rightExtension_hasDerivAt hV
  have hg0 : g T=V T:=Regularity.rightExtension_eq le_rfl
  have hgpos : 0<g T:=by rw [hg0]; exact hVT
  have hgeq : T-Real.log q=g T:=by rw [hg0]; exact heq
  obtain ⟨a,b,η,ha,_,hη,hη1,hmargins⟩:=exists_polyak_linear_margins hg hv' hgpos hgeq
  have hm : LinearSourceMargins7 q T a b η:=by
    refine ⟨hη1,?_⟩
    intro δ hδ hδη
    have hh:=hmargins δ hδ hδη
    have he : g (T+δ)=V (T+δ):=Regularity.rightExtension_eq (by linarith)
    rwa [he] at hh
  obtain ⟨M,δ₀,hδ₀,hfamily⟩:=exists_banded_family_of_linear_source_germ hq ha hη hH hm hfactory
  exact ⟨a,M,δ₀,ha,hδ₀,hfamily⟩

theorem exists_prefactor_of_source_germ {q T v' : ℝ} {H : ℕ}
    (hq : 0<q) (hV : HasDerivAt V v' T) (hv' : v'<1) (hVT : 0<V T)
    (heq : T-Real.log q=V T) (hH : 7≤H)
    (hRate : growthRate 0 (2*q) (q^2) H≤Real.exp T)
    (hfactory : ∀ᶠ t in 𝓝[≥] T,HasPhysicalFactors7 q t) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,envelope 0 (2*q) (q^2) H n≤C*Real.exp ((n : ℝ)*T) := by
  obtain ⟨a,b,η,ha,_,hη,hη1,hmargins⟩:=exists_polyak_linear_margins hV hv' hVT heq
  exact exists_prefactor_of_linear_source_germ hq ha hη hH hRate ⟨hη1,hmargins⟩ hfactory

theorem exists_prefactor_of_right_source_germ {q T v' : ℝ} {H : ℕ}
    (hq : 0<q) (hV : HasDerivWithinAt V v' (Ici T) T) (hv' : v'<1) (hVT : 0<V T)
    (heq : T-Real.log q=V T) (hH : 7≤H)
    (hRate : growthRate 0 (2*q) (q^2) H≤Real.exp T)
    (hfactory : ∀ᶠ t in 𝓝[≥] T,HasPhysicalFactors7 q t) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,envelope 0 (2*q) (q^2) H n≤C*Real.exp ((n : ℝ)*T) := by
  let g:=Regularity.rightExtension V v' T
  have hg : HasDerivAt g v' T:=Regularity.rightExtension_hasDerivAt hV
  have hg0 : g T=V T:=Regularity.rightExtension_eq le_rfl
  have hgpos : 0<g T:=by rw [hg0]; exact hVT
  have hgeq : T-Real.log q=g T:=by rw [hg0]; exact heq
  obtain ⟨a,b,η,ha,_,hη,hη1,hmargins⟩:=exists_polyak_linear_margins hg hv' hgpos hgeq
  apply exists_prefactor_of_linear_source_germ (b:=b) hq ha hη hH hRate _ hfactory
  refine ⟨hη1,?_⟩
  intro δ hδ hδη
  have hm:=hmargins δ hδ hδη
  have he : g (T+δ)=V (T+δ):=Regularity.rightExtension_eq (by linarith)
  rwa [he] at hm

end polyak.FiniteHorizon
