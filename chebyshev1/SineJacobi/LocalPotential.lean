import chebyshev1.SineJacobi.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Article: chebyshev1, Theorem E.1.
A single remainder constant works for every site in a compact interior set.
Result: `chebyshev1.SineJacobi.coupling_expansion_uniform` supplies the stated article
conclusion.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Filter Topology

/--
Exact identity `sin (x-y)*sin (x+y) = sin x ^ 2 - sin y ^ 2`.

Use: `chebyshev1.SineJacobi.coupling_den_eq` uses this identity to establish the identity
`sin (((s:ℝ)-1/2)*h N)*sin (((s:ℝ)+1/2)*h N) = sin ((s:ℝ)*h N)^2-sin (h N/2)^2`.

Article: chebyshev1, Theorem E.1 via
`chebyshev1.SineJacobi.coupling_fourth_order_error_le`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem sin_shift_product (x y : ℝ) :
    sin (x-y)*sin (x+y) = sin x ^ 2 - sin y ^ 2 := by
  rw [sin_sub, sin_add]
  nlinarith [sin_sq_add_cos_sq x, sin_sq_add_cos_sq y]

/--
Exact identity `sin (((s:ℝ)-1/2)*h N)*sin (((s:ℝ)+1/2)*h N) = sin ((s:ℝ)*h N)^2-sin (h N/2)^2`.

Use: `chebyshev1.SineJacobi.couplingSq_sub_quarter` rewrites with this identity to
establish exact identity `couplingSq N s - 1/4 = sin (h N/2)^2 / (4*(sin ((s:ℝ)*h N)^2-sin (h
N/2)^2))`.

Article: chebyshev1, Theorem E.1 via
`chebyshev1.SineJacobi.coupling_fourth_order_error_le`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sin_shift_product` with the
arguments shown in the proof.
-/
theorem coupling_den_eq (N s : ℕ) :
    sin (((s:ℝ)-1/2)*h N)*sin (((s:ℝ)+1/2)*h N) =
      sin ((s:ℝ)*h N)^2-sin (h N/2)^2 := by convert sin_shift_product ((s:ℝ)*h N) (h N/2) using 1 ; congr 2 <;> ring

/--
Exact identity `couplingSq N s - 1/4 = sin (h N/2)^2 / (4*(sin ((s:ℝ)*h N)^2-sin (h N/2)^2))`.

Use: `chebyshev1.SineJacobi.coupling_scaled_eq` rewrites with this identity to establish
exact identity `(N:ℝ)^2 * (couplingSq N s-1/4) = scaledCorrection ((s:ℝ)/N) (1/N)`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.endpoint_second_difference`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem couplingSq_sub_quarter (N s : ℕ) (hs : 0 < s) (hsN : s < N) :
    couplingSq N s - 1/4 =
      sin (h N/2)^2 / (4*(sin ((s:ℝ)*h N)^2-sin (h N/2)^2)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hn : sin ((s:ℝ)*h N)^2-sin (h N/2)^2 ≠ 0 := by
    rw [← coupling_den_eq]
    exact ne_of_gt (coupling_den_pos N s hs hsN)
  unfold couplingSq
  rw [coupling_den_eq]
  field_simp
  ring

/--
Defines `localPotential` of type `ℝ` by `Real.pi^2/(16*sin (Real.pi*t)^2)`.

Use: `chebyshev1.SineJacobi.coupling_fourth_order_error_le` uses this definition to
establish the stated quantitative bound `|couplingSq N s-1/4-localPotential ((s:ℝ)/N)/(N:ℝ)^2|
≤ Real.pi^4/(24*m^2*(N:ℝ)^4)`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.coupling_expansion_uniform`.
-/
def localPotential (t : ℝ) : ℝ := Real.pi^2/(16*sin (Real.pi*t)^2)

/--
A continuous extension of the scaled coupling correction to mesh size zero.

Use: `chebyshev1.SineJacobi.coupling_scaled_eq` rewrites with this definition to establish
exact identity `(N:ℝ)^2 * (couplingSq N s-1/4) = scaledCorrection ((s:ℝ)/N) (1/N)`.

Article: chebyshev1, Theorem E.1 via
`chebyshev1.SineJacobi.coupling_fourth_order_error_le`.
-/
def scaledCorrection (t mesh : ℝ) : ℝ :=
  (Real.pi^2/16)*sinc (Real.pi*mesh/2)^2 / (sin (Real.pi*t)^2-sin (Real.pi*mesh/2)^2)

/--
Exact identity `scaledCorrection t 0 = localPotential t`.

Use: `chebyshev1.SineJacobi.scaledCorrection_uniform` uses this identity to establish the
stated quantitative bound `TendstoUniformlyOn (fun mesh t => scaledCorrection t mesh)
localPotential (𝓝 0) K`.

Article: chebyshev1, Theorem E.1 via
`chebyshev1.SineJacobi.scaledCorrection_mesh_uniform`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem scaledCorrection_zero (t : ℝ) : scaledCorrection t 0 = localPotential t := by
  simp [scaledCorrection, localPotential]
  ring

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun a =>
scaledCorrection (t a) (mesh a)) l (𝓝 (localPotential u))`.

Use: `chebyshev1.SineJacobi.coupling_local_limit` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
(N:ℝ)^2*(couplingSq N (sites N)-1/4)) atTop (𝓝 (localPotential t))`.

Article: chebyshev1, Theorem E.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem scaledCorrection_tendsto {α : Type*} {l : Filter α} {t mesh : α → ℝ} {u : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) (ht : Tendsto t l (𝓝 u)) (hm : Tendsto mesh l (𝓝 0)) :
    Tendsto (fun a => scaledCorrection (t a) (mesh a)) l (𝓝 (localPotential u)) := by
  -- Record the convergence hx with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hx : Tendsto (fun a => Real.pi*mesh a/2) l (𝓝 (Real.pi*0/2)) :=
    ((tendsto_const_nhds (x := Real.pi)).mul hm).div_const 2
  have hn := (Real.continuous_sinc.tendsto 0).comp (by simpa using hx)
  have hs := (Real.continuous_sin.tendsto (Real.pi*u)).comp
    ((tendsto_const_nhds (x := Real.pi)).mul ht)
  have hs0 := (Real.continuous_sin.tendsto (Real.pi*0/2)).comp hx
  have hd := (hs.pow 2).sub (hs0.pow 2)
  have hp : sin (Real.pi*u) ≠ 0 := ne_of_gt (sin_pos_of_mem_Ioo
    ⟨mul_pos pi_pos hu.1, by nlinarith [pi_pos, hu.2]⟩)
  have hb := ((tendsto_const_nhds (x := Real.pi^2/16)).mul (hn.pow 2)).div hd
    (show sin (Real.pi*u)^2-sin (Real.pi*0/2)^2 ≠ 0 by simpa using pow_ne_zero 2 hp)
  convert hb using 1
  · funext a
    rfl
  · simp [localPotential, div_div]

/--
Exact identity `(N:ℝ)^2 * (couplingSq N s-1/4) = scaledCorrection ((s:ℝ)/N) (1/N)`.

Use: `chebyshev1.SineJacobi.coupling_fourth_order_error_le` rewrites with this identity to
establish the stated quantitative bound `|couplingSq N s-1/4-localPotential ((s:ℝ)/N)/(N:ℝ)^2|
≤ Real.pi^4/(24*m^2*(N:ℝ)^4)`.

Article: chebyshev1, Theorem E.1 via
`chebyshev1.SineJacobi.coupling_fourth_order_error_le`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem coupling_scaled_eq (N s : ℕ) (hs : 0 < s) (hsN : s < N) :
    (N:ℝ)^2 * (couplingSq N s-1/4) = scaledCorrection ((s:ℝ)/N) (1/N) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hx : Real.pi * (1/(N:ℝ))/2 = h N/2 := by unfold h; ring
  have ht : Real.pi * ((s:ℝ)/N) = (s:ℝ)*h N := by unfold h; ring
  have hb : h N/2 ≠ 0 := by unfold h; positivity
  rw [couplingSq_sub_quarter N s hs hsN, scaledCorrection, hx, ht, sinc_of_ne_zero hb]
  have hd : sin ((s:ℝ)*h N)^2-sin (h N/2)^2 ≠ 0 := by
    rw [← coupling_den_eq]
    exact ne_of_gt (coupling_den_pos N s hs hsN)
  generalize sin ((s:ℝ)*h N) = a at hd ⊢
  generalize sin (h N/2) = b at hd ⊢
  unfold h
  field_simp
  ring

/--
The local potential limit, allowing the site to vary with the mesh.

Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
(N:ℝ)^2*(couplingSq N (sites N)-1/4)) atTop (𝓝 (localPotential t))`.

Use: a standalone supporting limit for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev1, Theorem E.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem coupling_local_limit (sites : ℕ → ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1)
    (hsites : ∀ᶠ N in atTop, 0 < sites N ∧ sites N < N)
    (hgrid : Tendsto (fun N => (sites N:ℝ)/(N:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun N : ℕ => (N:ℝ)^2*(couplingSq N (sites N)-1/4)) atTop
      (𝓝 (localPotential t)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hb := scaledCorrection_tendsto ht hgrid
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply hb.congr'
  filter_upwards [hsites] with N hN
  exact (coupling_scaled_eq N (sites N) hN.1 hN.2).symm

/--
The potential limit is uniform on every compact interior set, as in E.1(iii).

The stated quantitative bound `TendstoUniformlyOn (fun mesh t => scaledCorrection t mesh)
localPotential (𝓝 0) K`.

Use: `chebyshev1.SineJacobi.scaledCorrection_mesh_uniform` uses this limit to establish the
stated quantitative bound `TendstoUniformlyOn (fun N : ℕ => fun t => scaledCorrection t
(1/(N:ℝ))) localPotential atTop K`.

Article: chebyshev1, Theorem E.1 via
`chebyshev1.SineJacobi.scaledCorrection_mesh_uniform`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.scaledCorrection_zero` with the
arguments shown in the proof.
-/
theorem scaledCorrection_uniform (K : Set ℝ) (hK : IsCompact K)
    (hsub : K ⊆ Set.Ioo (0:ℝ) 1) :
    TendstoUniformlyOn (fun mesh t => scaledCorrection t mesh) localPotential (𝓝 0) K := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.scaledCorrection_zero` with the
  -- arguments shown in the proof.
  obtain ⟨m, hm, hmin⟩ := hK.exists_forall_le'
    (f := fun t : ℝ => sin (Real.pi*t)^2)
    (by fun_prop)
    (a := 0) (by
      intro t ht
      have ht' := hsub ht
      exact sq_pos_of_pos (sin_pos_of_mem_Ioo
        ⟨mul_pos pi_pos ht'.1, by nlinarith [pi_pos, ht'.2]⟩))
  let U : Set ℝ := {mesh | sin (Real.pi*mesh/2)^2 < m}
  have hU : U ∈ 𝓝 (0:ℝ) := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (by fun_prop) continuous_const
    · simpa [U] using hm
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : ContinuousOn (fun p : ℝ × K => scaledCorrection p.2 p.1)
      (U ×ˢ Set.univ) := by
    unfold scaledCorrection
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp
    have hb := hmin p.2 p.2.property
    have hs : sin (Real.pi*p.1/2)^2 < m := hp.1
    exact ne_of_gt (by linarith)
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have hb := ContinuousOn.tendstoUniformly
    (f := fun mesh (t : K) => scaledCorrection t mesh) hU hc
  simpa only [Function.comp_def, scaledCorrection_zero] using hb

/--
The stated quantitative bound `TendstoUniformlyOn (fun N : ℕ => fun t => scaledCorrection t
(1/(N:ℝ))) localPotential atTop K`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem E.1.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.scaledCorrection_uniform` with
the arguments shown in the proof.
-/
theorem scaledCorrection_mesh_uniform (K : Set ℝ) (hK : IsCompact K)
    (hsub : K ⊆ Set.Ioo (0:ℝ) 1) :
    TendstoUniformlyOn (fun N : ℕ => fun t => scaledCorrection t (1/(N:ℝ)))
      localPotential atTop K := by
  have hb := scaledCorrection_uniform K hK hsub
  intro u hu
  exact (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (hb u hu)

/--
The stated quantitative bound `|sinc x-1| ≤ x^2/6`.

Use: `chebyshev1.SineJacobi.sinc_sq_sub_one_bound` uses this bound to establish the stated
quantitative bound `|sinc x^2-1| ≤ x^2/3`.

Article: chebyshev1, Theorem E.1 via
`chebyshev1.SineJacobi.coupling_fourth_order_error_le`.

Proof: Separate `x = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem sinc_sub_one_bound (x : ℝ) : |sinc x-1| ≤ x^2/6 := by
  -- Separate `x = 0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hx : x = 0
  · simp [hx]
  rw [sinc_of_ne_zero hx, div_sub_one hx, abs_div]
  apply (div_le_iff₀ (abs_pos.mpr hx)).mpr
  have hb := abs_sub_sin_le x
  rw [abs_sub_comm] at hb
  convert hb using 1
  rw [← sq_abs]
  ring

/--
The stated quantitative bound `|sinc x^2-1| ≤ x^2/3`.

Use: `chebyshev1.SineJacobi.scaledCorrection_error_le` uses this bound to establish the
stated quantitative bound `|scaledCorrection t mesh-localPotential t| ≤
Real.pi^4*mesh^2/(24*m^2)`.

Article: chebyshev1, Theorem E.1 via
`chebyshev1.SineJacobi.coupling_fourth_order_error_le`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sinc_sub_one_bound` with the
arguments shown in the proof.
-/
theorem sinc_sq_sub_one_bound (x : ℝ) : |sinc x^2-1| ≤ x^2/3 := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.sinc_sub_one_bound` with the
  -- arguments shown in the proof.
  have hb := sinc_sub_one_bound x
  have hc := abs_sinc_le_one x
  have he : sinc x^2-1 = (sinc x-1)*(sinc x+1) := by ring
  rw [he, abs_mul]
  have hs : |sinc x+1| ≤ 2 := by
    have := abs_add_le (sinc x) 1
    norm_num at this
    linarith
  have hm := mul_le_mul hb hs (abs_nonneg _) (by positivity)
  nlinarith

/--
Explicit uniform remainder before specializing to the integer mesh.

The stated quantitative bound `|scaledCorrection t mesh-localPotential t| ≤
Real.pi^4*mesh^2/(24*m^2)`.

Use: `chebyshev1.SineJacobi.coupling_fourth_order_error_le` uses this bound to establish
the stated quantitative bound `|couplingSq N s-1/4-localPotential ((s:ℝ)/N)/(N:ℝ)^2| ≤
Real.pi^4/(24*m^2*(N:ℝ)^4)`.

Article: chebyshev1, Theorem E.1 via
`chebyshev1.SineJacobi.coupling_fourth_order_error_le`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem scaledCorrection_error_le (t mesh m : ℝ) (hm : 0 < m)
    (ht : m ≤ sin (Real.pi*t)^2) (hmesh : (Real.pi*mesh/2)^2 ≤ m/2) :
    |scaledCorrection t mesh-localPotential t| ≤ Real.pi^4*mesh^2/(24*m^2) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let a := sin (Real.pi*t)^2
  let b := sin (Real.pi*mesh/2)^2
  let c := sinc (Real.pi*mesh/2)^2
  have ha : 0 < a := lt_of_lt_of_le hm ht
  have hab : m/2 ≤ a-b := by
    have hb := sin_sq_le_sq (x := Real.pi*mesh/2)
    dsimp [a, b]
    linarith
  have hd : 0 < a-b := lt_of_lt_of_le (by positivity) hab
  have ha1 : a ≤ 1 := by
    dsimp [a]
    nlinarith [abs_le.mp (abs_sin_le_one (Real.pi*t))]
  have hb0 : 0 ≤ b := sq_nonneg _
  have hb1 : b ≤ (Real.pi*mesh/2)^2 := sin_sq_le_sq
  have hc : |c-1| ≤ (Real.pi*mesh/2)^2/3 := sinc_sq_sub_one_bound _
  have he : scaledCorrection t mesh-localPotential t =
      (Real.pi^2/16)*((c-1)*a+b)/(a*(a-b)) := by
    change (Real.pi^2/16)*c/(a-b)-Real.pi^2/(16*a) = _
    rw [← div_div]
    field_simp [ha.ne', hd.ne']
    ring
  rw [he, abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.pi^2/16),
    abs_of_pos (mul_pos ha hd)]
  apply (div_le_iff₀ (mul_pos ha hd)).mpr
  have hnum : |(c-1)*a+b| ≤ 4/3*(Real.pi*mesh/2)^2 := by
    calc
      _ ≤ |(c-1)*a| + |b| := abs_add_le _ _
      _ = |c-1| * a+b := by rw [abs_mul, abs_of_pos ha, abs_of_nonneg hb0]
      _ ≤ ((Real.pi*mesh/2)^2/3)*1+(Real.pi*mesh/2)^2 :=
        add_le_add (mul_le_mul hc ha1 ha.le (by positivity)) hb1
      _ = _ := by ring
  have hden : m^2/2 ≤ a*(a-b) := by
    have hb := mul_le_mul ht hab (by positivity : 0 ≤ m/2) ha.le
    dsimp [a] at *
    nlinarith
  have hupper := mul_le_mul_of_nonneg_left hnum
    (show 0 ≤ Real.pi^2/16 by positivity)
  have hlower := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ Real.pi^4*mesh^2/(24*m^2) by positivity)
  have hid : Real.pi^4*mesh^2/(24*m^2)*(m^2/2) =
      (Real.pi^2/16)*(4/3*(Real.pi*mesh/2)^2) := by field_simp; ring
  rw [hid] at hlower
  exact hupper.trans hlower

/--
The explicit O(N⁻⁴) expansion of E.1(iii).

The stated quantitative bound `|couplingSq N s-1/4-localPotential ((s:ℝ)/N)/(N:ℝ)^2| ≤
Real.pi^4/(24*m^2*(N:ℝ)^4)`.

Use: `chebyshev1.SineJacobi.coupling_expansion_uniform` uses this bound to establish
constructs witnesses with the exact properties `∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s, 0 < s
→ s < N → (s:ℝ)/(N:ℝ) ∈ K → |couplingSq N s-1/4-localPotential ((s:ℝ)/N)/(N:ℝ)^2| ≤ C/(N:ℝ)^4`.

Article: chebyshev1, Theorem E.1.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem coupling_fourth_order_error_le (N s : ℕ) (hs : 0 < s) (hsN : s < N)
    (m : ℝ) (hm : 0 < m) (ht : m ≤ sin (Real.pi*((s:ℝ)/N))^2)
    (hmesh : (Real.pi*(1/(N:ℝ))/2)^2 ≤ m/2) :
    |couplingSq N s-1/4-localPotential ((s:ℝ)/N)/(N:ℝ)^2| ≤
      Real.pi^4/(24*m^2*(N:ℝ)^4) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hN : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hb := scaledCorrection_error_le ((s:ℝ)/N) (1/(N:ℝ)) m hm ht hmesh
  rw [← coupling_scaled_eq N s hs hsN] at hb
  have he : couplingSq N s-1/4-localPotential ((s:ℝ)/N)/(N:ℝ)^2 =
      ((N:ℝ)^2*(couplingSq N s-1/4)-localPotential ((s:ℝ)/N))/(N:ℝ)^2 := by
    field_simp
  rw [he, abs_div, abs_of_pos (sq_pos_of_pos hN)]
  have hb' := div_le_div_of_nonneg_right hb (sq_nonneg (N:ℝ))
  convert hb' using 1
  field_simp

/--
A single remainder constant works for every site in a compact interior set.

Constructs witnesses with the exact properties `∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s, 0 < s
→ s < N → (s:ℝ)/(N:ℝ) ∈ K → |couplingSq N s-1/4-localPotential ((s:ℝ)/N)/(N:ℝ)^2| ≤ C/(N:ℝ)^4`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem E.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem coupling_expansion_uniform (K : Set ℝ) (hK : IsCompact K)
    (hsub : K ⊆ Set.Ioo (0:ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ s, 0 < s → s < N → (s:ℝ)/(N:ℝ) ∈ K →
        |couplingSq N s-1/4-localPotential ((s:ℝ)/N)/(N:ℝ)^2| ≤ C/(N:ℝ)^4 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  obtain ⟨m, hm, hmin⟩ := hK.exists_forall_le'
    (f := fun t : ℝ => sin (Real.pi*t)^2) (by fun_prop)
    (a := 0) (by
      intro t ht
      have ht' := hsub ht
      exact sq_pos_of_pos (sin_pos_of_mem_Ioo
        ⟨mul_pos pi_pos ht'.1, by nlinarith [pi_pos, ht'.2]⟩))
  refine ⟨Real.pi^4/(24*m^2), by positivity, ?_⟩
  -- Record the convergence hmesh with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hmesh : Tendsto (fun N : ℕ => (Real.pi*(1/(N:ℝ))/2)^2) atTop (𝓝 0) := by
    simpa using (((tendsto_const_nhds (x := Real.pi)).mul
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const 2).pow 2
  filter_upwards [hmesh.eventually_le_const (by positivity : (0:ℝ) < m/2)] with N hn
  intro s hs hsN ht
  have hb := coupling_fourth_order_error_le N s hs hsN m hm (hmin _ ht) hn
  simpa only [div_div, mul_assoc] using hb

end
end chebyshev1.SineJacobi
