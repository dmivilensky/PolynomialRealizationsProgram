import polyak.FiniteHorizon.ClassCompact

/-!
Article: Appendix C, finite-section contraction for Lemma plateauclass.
Use: failure on arbitrarily long finite members produces a scalar limit
profile. Uniform contraction of that profile contradicts the failure. No
member or limiting profile is assumed to have a continuation in the class.
-/
noncomputable section
namespace polyak.FiniteHorizon.SegmentClass
open Growth Growth.FiniteHorizon Set Filter Finset
open scoped Topology
variable {A B β : ℝ} {H : ℕ} (G : SegmentClass A B β H)

theorem exists_long_prefix_contraction {r K : ℝ} {w : ℕ}
    (hpos : ∀ n,0<G.envelope n) (hr : 0<r)
    (hlim : Tendsto (fun n : ℕ => G.envelope n^((n : ℝ)⁻¹)) atTop (𝓝 r))
    (hK : 0<K) (he : G.EnergyBound (Real.log r) K w) :
    ∃ P N : ℕ,0<P ∧ P+1≤N ∧ ∀ d n : ℕ,
      ∀ s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n,N≤n → G.contains d n s →
        Real.exp (-2*(P : ℝ)*Real.log r)*stateNorm s.x P^2≤(1/2 : ℝ)*stateNorm s.x 0^2 := by
  let t:=Real.log r
  let g:=G.profileWeight t
  obtain ⟨P,hP,hcontract⟩:=exists_profile_contraction g (G.profileWeight_nonneg t) t hK w
  suffices hgood : ∃ N : ℕ,∀ d n : ℕ,
      ∀ s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n,N≤n → G.contains d n s →
        Real.exp (-2*(P : ℝ)*t)*stateNorm s.x P^2≤(1/2 : ℝ)*stateNorm s.x 0^2 by
    obtain ⟨N,hN⟩:=hgood
    exact ⟨P,max N (P+1),hP,le_max_right _ _,fun d n s hn hs =>
      hN d n s ((le_max_left _ _).trans hn) hs⟩
  by_contra hfail
  push Not at hfail
  have hwitness (q : ℕ) : ∃ d n : ℕ,
      ∃ s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n,
        G.contains d n s ∧ q+P+1≤n ∧
          (1/2 : ℝ)*stateNorm s.x 0^2<Real.exp (-2*(P : ℝ)*t)*stateNorm s.x P^2 := by
    obtain ⟨d,n,s,hn,hs,hbad⟩:=hfail (q+P+1)
    exact ⟨d,n,s,hs,hn,hbad⟩
  choose d n s hs hlong hbad using hwitness
  let profiles : ℕ → ℕ → ℝ:=fun q => G.energyProfile (s q) t
  have hcompact : IsCompact {b : ℕ → ℝ | ∀ k,b k∈Icc (0 : ℝ) (g k)}:=
    isCompact_pi_infinite fun _ => isCompact_Icc
  obtain ⟨b,hb,φ,hφ,hconv⟩:=hcompact.tendsto_subseq (x:=profiles) (fun q k =>
    ⟨G.energyProfile_nonneg (s q) t k,G.energyProfile_le (s q) (hs q) t k⟩)
  have hlarge (L : ℕ) : ∀ᶠ q : ℕ in atTop,L≤n (φ q):=by
    filter_upwards [eventually_ge_atTop L] with q hq
    have hφq:=hφ.id_le q
    change q≤φ q at hφq
    have hn:=hlong (φ q)
    omega
  have hnonneg : ∀ k,0≤b k:=fun k => (hb k).1
  have hupper : ∀ k,b k≤g k:=fun k => (hb k).2
  have hsub : Subexponential b:=by
    intro δ hδ
    obtain ⟨C,hC,hbound⟩:=G.profileWeight_subexponential hpos hr hlim δ hδ
    exact ⟨C,hC,fun k => (hupper k).trans (hbound k)⟩
  have henergy : ProfileEnergy b K w:=by
    intro i j hi hij
    have hc₁ : Continuous (fun b : ℕ → ℝ => mass b i (j+1)):=by unfold mass; fun_prop
    have hc₂ : Continuous (fun b : ℕ → ℝ => K*(energyWindow b w i+energyWindow b w j)):=by
      unfold energyWindow mass
      fun_prop
    apply (isClosed_le hc₁ hc₂).mem_of_tendsto hconv
    filter_upwards [hlarge (j+w)] with q hq
    exact G.energyProfile_energy he (s (φ q)) (hs (φ q)) i j hi hij hq
  have hforward : ProfileForward g b t:=by
    intro i k
    have hc₁ : Continuous (fun b : ℕ → ℝ => b (i+k)):=by fun_prop
    have hc₂ : Continuous (fun b : ℕ → ℝ => g k*(b i+Real.exp (2*t)*b (i+1))):=by fun_prop
    apply (isClosed_le hc₁ hc₂).mem_of_tendsto hconv
    filter_upwards [hlarge (max (i+k) (i+1))] with q hq
    exact G.energyProfile_forward (s (φ q)) (hs (φ q)) t i k
      ((le_max_left _ _).trans hq) ((le_max_right _ _).trans hq)
  have hsmall:=hcontract b hnonneg hupper hsub henergy hforward
  have hbig (q : ℕ) : (1/2 : ℝ)<profiles q P+Real.exp (2*t)*profiles q (P+1):=by
    have hlen : P+1≤n q:=by have := hlong q; omega
    have hz : 0<stateNorm (s q).x 0^2:=by
      by_contra hh
      have hz : stateNorm (s q).x 0=0:=by nlinarith [sq_nonneg (stateNorm (s q).x 0)]
      have hzero:=(s q).stateNorm_eq_zero_of_zero hz P (by omega)
      have hf:=hbad q
      rw [hz,hzero] at hf
      norm_num at hf
    change (1/2 : ℝ)<G.energyProfile (s q) t P+Real.exp (2*t)*G.energyProfile (s q) t (P+1)
    rw [G.energyProfile_state (s q) t P hlen]
    exact (lt_div_iff₀ hz).mpr (hbad q)
  have hlow : (1/2 : ℝ)≤b P+Real.exp (2*t)*b (P+1):=by
    have hc : Continuous (fun b : ℕ → ℝ => b P+Real.exp (2*t)*b (P+1)):=by fun_prop
    exact ge_of_tendsto (hc.tendsto b |>.comp hconv) (Eventually.of_forall fun q => (hbig (φ q)).le)
  linarith

end polyak.FiniteHorizon.SegmentClass
