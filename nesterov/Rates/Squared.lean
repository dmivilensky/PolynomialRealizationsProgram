import nesterov.Rates.Rest

/-!
Article: Remark `rem:uniform-smoothness`, distance and squared-distance factors.
Use: literal squared-distance suprema equal the squares of the original
finite-horizon suprema. Their asymptotic factors are squared, so the leading
acceleration constant doubles.
-/
namespace nesterov.Rates
noncomputable section
open Set Filter
open scoped Topology

private theorem sSup_squared_image {A : Set ℝ}
    (hA : ∀ x ∈ A, 0≤x) (hb : BddAbove (insert 0 A)) :
    sSup (insert 0 ((fun x : ℝ => x^2) '' A))=(sSup (insert 0 A))^2 := by
  let a := sSup (insert 0 A)
  have ha : 0≤a := le_csSup hb (mem_insert _ _)
  have hx (x : ℝ) (hx : x∈A) : x≤a := le_csSup hb (mem_insert_of_mem _ hx)
  have hb' : BddAbove (insert 0 ((fun x : ℝ => x^2) '' A)) := by
    refine ⟨a^2,?_⟩
    intro x hx'
    rcases hx' with rfl | ⟨y,hy,rfl⟩
    · exact sq_nonneg a
    · exact (sq_le_sq₀ (hA y hy) ha).mpr (hx y hy)
  let b := sSup (insert 0 ((fun x : ℝ => x^2) '' A))
  have hb0 : 0≤b := le_csSup hb' (mem_insert _ _)
  apply le_antisymm
  · apply csSup_le (insert_nonempty _ _)
    intro x hx'
    rcases hx' with rfl | ⟨y,hy,rfl⟩
    · exact sq_nonneg a
    · exact (sq_le_sq₀ (hA y hy) ha).mpr (hx y hy)
  · have hroot : a≤Real.sqrt b := by
      apply csSup_le (insert_nonempty _ _)
      intro x hx'
      rcases hx' with rfl | hx'
      · exact Real.sqrt_nonneg _
      · apply Real.le_sqrt_of_sq_le
        exact le_csSup hb' (mem_insert_of_mem _ ⟨x,hx',rfl⟩)
    have hs := Real.sq_sqrt hb0
    nlinarith [Real.sqrt_nonneg b]

/-- Actual squared state-distance ratios, with the supremum still taken before
any horizon limit and with arbitrary real Hilbert objectives. -/
def squaredRatios (M : StationaryMethod) (μ L : ℝ) (n : ℕ) : Set ℝ :=
  {x | ∃ r : HilbertRun M μ L, r.stateNorm 0≠0 ∧
    x=(r.stateNorm n)^2/(r.stateNorm 0)^2}

/-- The literal squared-state finite-horizon supremum. -/
def squaredEnvelope (M : StationaryMethod) (μ L : ℝ) (n : ℕ) : ℝ :=
  sSup (insert 0 (squaredRatios M μ L n))

theorem squaredRatios_eq_image (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    squaredRatios M μ L n=(fun x : ℝ => x^2) '' ratios M μ L n := by
  ext x
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact ⟨r.stateNorm n/r.stateNorm 0,⟨r,hr,rfl⟩,by exact div_pow _ _ 2⟩
  · rintro ⟨x,⟨r,hr,rfl⟩,rfl⟩
    exact ⟨r,hr,by exact div_pow _ _ 2⟩

/-- Squared-distance risk is exactly the square of the original literal envelope. -/
theorem squaredEnvelope_eq (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    squaredEnvelope M μ L n=(envelope M μ L n)^2 := by
  unfold squaredEnvelope envelope
  rw [squaredRatios_eq_image]
  apply sSup_squared_image _ (ratios_bddAbove M μ L n)
  rintro x ⟨r,_,rfl⟩
  exact div_nonneg (M.stateNorm_nonneg _ _) (M.stateNorm_nonneg _ _)

/-- The squared-distance uniform root factor exists and is ρ_F². -/
theorem tendsto_squaredEnvelope_root (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) :
    Tendsto (fun n : ℕ => squaredEnvelope M μ L n^((n:ℝ)⁻¹)) atTop
      (𝓝 ((rate M μ L)^2)) := by
  have he (n : ℕ) : squaredEnvelope M μ L n^((n:ℝ)⁻¹)=
      (envelope M μ L n^((n:ℝ)⁻¹))^2 := by
    rw [squaredEnvelope_eq]
    exact (Real.rpow_pow_comm (envelope_nonneg M μ L n) _ 2).symm
  simpa only [he] using (tendsto_envelope_root M hμ hμL).pow 2

/-- Genuine finite-dimensional squared-distance ratios from the unchanged rest start. -/
def restSquaredRatios (M : StationaryMethod) (μ L : ℝ) (n : ℕ) : Set ℝ :=
  {x | ∃ r : HilbertRun M μ L, ∃ _ : FiniteDimensional ℝ r.Carrier,
    r.FromRest ∧ r.w 0≠0 ∧ x=‖r.w (n+M.memory-1)‖^2/‖r.w 0‖^2}

/-- The literal finite-horizon from-rest squared-distance supremum. -/
def restSquaredEnvelope (M : StationaryMethod) (μ L : ℝ) (n : ℕ) : ℝ :=
  sSup (insert 0 (restSquaredRatios M μ L n))

theorem restSquaredRatios_eq_image (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    restSquaredRatios M μ L n=(fun x : ℝ => x^2) '' restRatios M μ L n := by
  ext x
  constructor
  · rintro ⟨r,hfd,hr,hz,rfl⟩
    exact ⟨‖r.w (n+M.memory-1)‖/‖r.w 0‖,⟨r,hfd,hr,hz,rfl⟩,by exact div_pow _ _ 2⟩
  · rintro ⟨x,⟨r,hfd,hr,hz,rfl⟩,rfl⟩
    exact ⟨r,hfd,hr,hz,by exact div_pow _ _ 2⟩

/-- The exact finite-horizon from-rest squared envelope is the original square. -/
theorem restSquaredEnvelope_eq (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    restSquaredEnvelope M μ L n=(restEnvelope M μ L n)^2 := by
  unfold restSquaredEnvelope restEnvelope
  rw [restSquaredRatios_eq_image]
  apply sSup_squared_image _ (restRatios_bddAbove M μ L n)
  rintro x ⟨r,_,_,_,rfl⟩
  positivity

/-- Bounded nonnegative root sequences commute with squaring under limsup. -/
theorem limsup_sq_of_nonneg {a : ℕ → ℝ} (ha : ∀ n,0≤a n)
    (hb : IsBoundedUnder (·≤·) atTop a) :
    limsup (fun n => (a n)^2) atTop=(limsup a atTop)^2 := by
  have hc := isCoboundedUnder_le_of_le atTop ha
  have hl : 0≤limsup a atTop := by
    apply le_limsup_of_le hb
    intro b h
    obtain ⟨n,hn⟩ := h.exists
    exact (ha n).trans hn
  have hm : Monotone (fun x : ℝ => (max x 0)^2) := by
    intro x y hxy
    exact (sq_le_sq₀ (le_max_right _ _) (le_max_right _ _)).mpr (max_le_max hxy le_rfl)
  have h := hm.map_limsup_of_continuousAt a (by fun_prop) hb hc
  simpa only [Function.comp_def,max_eq_left (ha _),max_eq_left hl] using h.symm

/-- The literal from-rest squared-distance root limsup is exactly (ρ_F⁰)². -/
theorem restSquared_root_limsup (M : StationaryMethod) (μ L : ℝ) :
    limsup (fun n : ℕ => restSquaredEnvelope M μ L n^((n:ℝ)⁻¹)) atTop=
      (restRate M μ L)^2 := by
  have he (n : ℕ) : restSquaredEnvelope M μ L n^((n:ℝ)⁻¹)=
      (restEnvelope M μ L n^((n:ℝ)⁻¹))^2 := by
    rw [restSquaredEnvelope_eq]
    exact (Real.rpow_pow_comm (restEnvelope_nonneg M μ L n) _ 2).symm
  simp only [he]
  exact limsup_sq_of_nonneg (fun n => Real.rpow_nonneg (restEnvelope_nonneg M μ L n) _)
    (rest_roots_bounded M μ L)

/-- Squaring a distance factor doubles its first-order acceleration constant.
This uses only the actual factor and normalized-error limits; no additional
regularity of the tuning family is required. -/
theorem squared_first_order_constant {ι : Type*} {l : Filter ι}
    {ρ ε : ι → ℝ} {c : ℝ} (hρ : Tendsto ρ l (𝓝 1))
    (hc : Tendsto (fun i => (1-ρ i)/ε i) l (𝓝 c)) :
    Tendsto (fun i => (1-(ρ i)^2)/ε i) l (𝓝 (2*c)) := by
  have h := hc.mul ((tendsto_const_nhds (x := (1:ℝ)) (f := l)).add hρ)
  convert h using 1
  · funext i
    ring
  · congr 1
    ring

end
end nesterov.Rates
