import polyak.FareyPlateau.FanAnalysis.CompactGeometry
import polyak.FareyPlateau.FanAnalysis.AmbientUniform
import polyak.FareyPlateau.FanAnalysis.NeighborLimits

/-! Genuine compact-uniform finite Taylor tests. Their analyticity comes from
the source coefficient extension, and their coefficients are the exact
previously computed fan jets. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.Parameters
open General Levels

def testDifference (j k : ℕ) (n : ℤ) (e : Point→ℝ) (τ y₁ y₂ : ℝ) : Point×ℝ→ℝ :=
  test j k n e τ y₁-test j k n e τ y₂

theorem analytic_testDifference {j k : ℕ} {n : ℤ} {e : Point→ℝ}
    (he : ∀p,AnalyticAt ℝ e p) (τ y₁ y₂ : ℝ) (z : Point×ℝ)
    (ha : Real.sin (omega j k+z.2)≠0)
    (hc : Real.sin (omega j k-((k:ℝ)-1)*z.2)≠0) :
    AnalyticAt ℝ (testDifference j k n e τ y₁ y₂) z :=
  (analytic_test (j:=j) (k:=k) (n:=n) (e:=e) he τ y₁ z ha hc).sub
    (analytic_test (j:=j) (k:=k) (n:=n) (e:=e) he τ y₂ z ha hc)

end polyak.FareyPlateau.FanAnalysis.Parameters

namespace polyak.FareyPlateau.FanAnalysis.CompactFamily.Data
open General Levels Set Filter
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
variable {j k : ℕ} (B : CompactFamily.Data X j k)

theorem uniform_positive_test (ε τ y : ℝ)
    (hlim : ∀x : X, ∃c : ℝ, 0<c ∧ Tendsto (fun δ => B.phi ε x δ (τ+y*δ)/δ^2) (𝓝[≠] 0) (𝓝 c)) :
    ∀ᶠ δ in 𝓝[≠] 0, ∀x : X, 0<B.phi ε x δ (τ+y*δ) := by
  obtain ⟨r,hr,hstrip⟩ := B.phase_strip
  have hF (x : X) (δ : ℝ) (hδ : |δ|<r) :
      AnalyticAt ℝ (Parameters.test j k B.lower (B.shiftError ε) τ y) (B.coordinates x,δ) :=
    Parameters.analytic_test (j := j) (k := k) (n := B.lower) (B.analytic_shiftError ε)
      τ y (B.coordinates x,δ) (hstrip δ hδ).1 (hstrip δ hδ).2
  have hh := AmbientUniform.uniform_positive_of_pointwise
    (Parameters.test j k B.lower (B.shiftError ε) τ y) B.coordinates B.continuous_coordinates hr hF
    (by simpa only [B.phi_ambient] using hlim)
  simpa only [B.phi_ambient] using hh

theorem uniform_core_tests {η : ℝ} (hη : 0<η) :
    ∀ᶠ δ in 𝓝[≠] 0, ∀x : X,
      0<B.phi (-η) x δ (2*Real.pi/k+(B.lower : ℝ)*δ) ∧
      0<B.phi (-η) x δ (2*Real.pi/k+((B.lower : ℝ)+k)*δ) := by
  have htest (m : ℤ) (hm : m=0 ∨ m=1) := B.uniform_positive_test (-η) (2*Real.pi/k) ((B.lower : ℝ)+(m : ℝ)*k)
    (show ∀x : X, ∃c : ℝ, 0<c ∧ Tendsto _ _ (𝓝 c) from by
      intro x
      let A := B.adjacent x
      let e := Actual.critical A-η
      have hp := Actual.minimum_positive A (show e<Actual.critical A by dsimp [e]; linarith)
      refine ⟨2*Actual.minimum A e,by positivity,?_⟩
      have hh := (Actual.site_limit A e m).mul_const 2
      have hfun : (fun δ => B.phi (-η) x δ (2*Real.pi/k+((B.lower : ℝ)+(m : ℝ)*k)*δ)/δ^2)=
          (fun δ => Actual.site A e m δ/(2*δ^2)*2) := by
        funext δ
        rw [B.phi_actual]
        change Actual.phi A (Actual.critical A+-η) δ _/δ^2=Actual.site A e m δ/(2*δ^2)*2
        unfold Actual.site e
        rw [B.lower_eq x]
        ring
      rw [hfun]
      convert hh using 1
      rcases hm with rfl|rfl
      all_goals
        simp only [Int.cast_zero,Int.cast_one,zero_mul,mul_zero,sub_self,add_zero]
        congr 1
        ring)
  have h₀ := htest 0 (Or.inl rfl)
  have h₁ := htest 1 (Or.inr rfl)
  simp only [Int.cast_zero,zero_mul,add_zero,Int.cast_one,one_mul] at h₀ h₁
  filter_upwards [h₀,h₁] with δ hδ0 hδ1 x
  exact ⟨hδ0 x,hδ1 x⟩

omit [CompactSpace X] [Nonempty X] in
theorem site_difference_limit (ε : ℝ) (m n : ℤ) (x : X) :
    Tendsto (fun δ =>
      (B.phi ε x δ (2*Real.pi/k+((B.lower : ℝ)+(m : ℝ)*k)*δ)-
        B.phi ε x δ (2*Real.pi/k+((B.lower : ℝ)+(n : ℝ)*k)*δ))/δ^2)
      (𝓝[≠] 0) (𝓝 (2*Actual.u (B.adjacent x)*(k : ℝ)^2*
        ((m : ℝ)*((m : ℝ)-1)-(n : ℝ)*((n : ℝ)-1)))) := by
  let A := B.adjacent x
  let e := Actual.critical A+ε
  let S : ℤ→ℝ→ℝ := fun l δ => B.phi ε x δ (2*Real.pi/k+((B.lower : ℝ)+(l : ℝ)*k)*δ)
  have hsite (l : ℤ) : S l=Actual.site A e l := by
    funext δ
    change B.phi ε x δ (2*Real.pi/k+((B.lower : ℝ)+(l : ℝ)*k)*δ)=
      Actual.phi (B.adjacent x) (Actual.critical (B.adjacent x)+ε) δ
        (2*Real.pi/k+(((B.adjacent x).lower : ℝ)+(l : ℝ)*k)*δ)
    rw [B.lower_eq x]
    exact B.phi_actual ε x δ _
  have hh := ((Actual.site_limit A e m).sub (Actual.site_limit A e n)).mul_const 2
  change Tendsto (fun δ => (S m δ-S n δ)/δ^2) _ _
  rw [hsite,hsite]
  convert hh using 1
  · funext δ
    ring
  · congr 1
    ring

theorem uniform_positive_difference_test (ε τ y₁ y₂ : ℝ)
    (hlim : ∀x : X,∃c : ℝ,0<c ∧ Tendsto
      (fun δ => (B.phi ε x δ (τ+y₁*δ)-B.phi ε x δ (τ+y₂*δ))/δ^2)
      (𝓝[≠] 0) (𝓝 c)) :
    ∀ᶠ δ in 𝓝[≠] 0,∀x : X,
      B.phi ε x δ (τ+y₂*δ)<B.phi ε x δ (τ+y₁*δ) := by
  obtain ⟨r,hr,hstrip⟩ := B.phase_strip
  let F : Parameters.Point×ℝ→ℝ :=
    Parameters.testDifference j k B.lower (B.shiftError ε) τ y₁ y₂
  let G : X→ℝ→ℝ := fun x δ => B.phi ε x δ (τ+y₁*δ)-B.phi ε x δ (τ+y₂*δ)
  have hbridge (x : X) (δ : ℝ) : F (B.coordinates x,δ)=G x δ := by
    dsimp only [F,G,Parameters.testDifference,Pi.sub_apply]
    rw [B.phi_ambient,B.phi_ambient]
  have hF (x : X) (δ : ℝ) (hδ : |δ|<r) : AnalyticAt ℝ F (B.coordinates x,δ) :=
    Parameters.analytic_testDifference (j:=j) (k:=k) (n:=B.lower) (e:=B.shiftError ε)
      (B.analytic_shiftError ε) τ y₁ y₂ _ (hstrip δ hδ).1 (hstrip δ hδ).2
  have hlimF (x : X) : ∃c : ℝ,0<c ∧
      Tendsto (fun δ => F (B.coordinates x,δ)/δ^2) (𝓝[≠] 0) (𝓝 c) := by
    obtain ⟨c,hc,ht⟩ := hlim x
    refine ⟨c,hc,?_⟩
    have hfun : (fun δ => F (B.coordinates x,δ)/δ^2)=(fun δ => G x δ/δ^2) :=
      funext (fun δ => congrArg (fun z : ℝ=>z/δ^2) (hbridge x δ))
    rw [hfun]
    exact ht
  have hh := AmbientUniform.uniform_positive_of_pointwise F B.coordinates B.continuous_coordinates hr hF hlimF
  filter_upwards [hh] with δ hδ x
  have hx := hδ x
  rw [hbridge] at hx
  exact sub_pos.mp hx

theorem uniform_site_difference (ε : ℝ) (m n : ℤ)
    (hpos : ∀x : X,0<2*Actual.u (B.adjacent x)*(k : ℝ)^2*
      ((m : ℝ)*((m : ℝ)-1)-(n : ℝ)*((n : ℝ)-1))) :
    ∀ᶠ δ in 𝓝[≠] 0,∀x : X,
      B.phi ε x δ (2*Real.pi/k+((B.lower : ℝ)+(n : ℝ)*k)*δ)<
        B.phi ε x δ (2*Real.pi/k+((B.lower : ℝ)+(m : ℝ)*k)*δ) := by
  apply B.uniform_positive_difference_test ε (2*Real.pi/k) ((B.lower : ℝ)+(m : ℝ)*k)
    ((B.lower : ℝ)+(n : ℝ)*k)
  intro x
  exact ⟨_,hpos x,B.site_difference_limit ε m n x⟩

theorem uniform_outer_tests (ε : ℝ) :
    ∀ᶠ δ in 𝓝[≠] 0, ∀x : X,
      B.phi ε x δ (2*Real.pi/k+(B.lower : ℝ)*δ)≤B.phi ε x δ (2*Real.pi/k+((B.lower : ℝ)-k)*δ) ∧
      B.phi ε x δ (2*Real.pi/k+((B.lower : ℝ)+k)*δ)≤B.phi ε x δ (2*Real.pi/k+((B.lower : ℝ)+2*k)*δ) := by
  have hp (x : X) : 0<4*Actual.u (B.adjacent x)*(k : ℝ)^2 := by
    have hu := Actual.u_positive (B.adjacent x)
    have hkR : (0 : ℝ)<k := by exact_mod_cast (show 0<k by have := (B.adjacent x).period_ge; omega)
    positivity
  have hleft := B.uniform_site_difference ε (-1) 0 (by intro x; norm_num; nlinarith [hp x])
  have hright := B.uniform_site_difference ε 2 1 (by intro x; norm_num; nlinarith [hp x])
  simp only [Int.cast_neg,Int.cast_one,Int.cast_zero,Int.cast_ofNat,neg_one_mul,zero_mul,add_zero,one_mul,←sub_eq_add_neg] at hleft hright
  filter_upwards [hleft,hright] with δ hl hr x
  exact ⟨(hl x).le,(hr x).le⟩

theorem uniform_zero_neighbors (ε : ℝ) :
    ∀ᶠ δ in 𝓝[≠] 0, ∀x : X,
      0<B.phi ε x δ ((k : ℝ)*δ) ∧ 0<B.phi ε x δ (-((k : ℝ)*δ)) := by
  have hp := B.uniform_positive_test ε 0 (k : ℝ) (by
    intro x
    let A := B.adjacent x
    refine ⟨4*Actual.u A*(k : ℝ)^2*(1-A.mix),?_,?_⟩
    · have hu := Actual.u_positive A
      have hm := sub_pos.mpr A.mix_lt
      have hkR : (0 : ℝ)<k := by exact_mod_cast (show 0<k by have := A.period_ge; omega)
      positivity
    · simpa only [zero_add,B.phi_actual] using (Actual.zero_neighbor_limits A (Actual.critical A+ε)).1)
  have hm := B.uniform_positive_test ε 0 (-(k : ℝ)) (by
    intro x
    let A := B.adjacent x
    refine ⟨4*Actual.u A*(k : ℝ)^2*A.mix,?_,?_⟩
    · have hu := Actual.u_positive A
      have hm := A.mix_pos
      have hkR : (0 : ℝ)<k := by exact_mod_cast (show 0<k by have := A.period_ge; omega)
      positivity
    · simpa only [zero_add,B.phi_actual] using (Actual.zero_neighbor_limits A (Actual.critical A+ε)).2)
  simp only [zero_add,neg_mul] at hp hm
  filter_upwards [hp,hm] with δ hδp hδm x
  exact ⟨hδp x,hδm x⟩

end polyak.FareyPlateau.FanAnalysis.CompactFamily.Data
