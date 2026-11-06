import nesterov.Corner.Model
import nesterov.Corner.Coefficients
import nesterov.Layer.SymbolLimits

/-! Fixed-corner expansions are uniform on compact test-constant and frequency sets. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ : ℝ} (F : Scaling A l θ 2 (1/2))

def cornerParametersAt (c : ℝ) (p : A) : Corner.Parameters :=
  ![c,F.thetaAt p,F.cornerA p,F.cornerB p]

theorem corner_coefficient_exact : ∀ᶠ p in l,∀ c : ℝ,∀ k : Fin 6,
    scaledCoefficient (F.epsilon p) (F.parametersAt c p) k=
      F.epsilon p*Corner.first (F.cornerParametersAt c p) k+
        F.epsilon p^2*Corner.remainder (F.epsilon p) (F.cornerParametersAt c p) k := by
  filter_upwards [F.corner_coordinates_exact] with p hp c k
  have he : F.parametersAt c p=Corner.physicalParameters (F.epsilon p) (F.cornerParametersAt c p) := by
    ext j
    fin_cases j <;> simp [parametersAt,Corner.physicalParameters,cornerParametersAt,hp.1,hp.2]
  rw [he]
  exact Corner.coefficient_exact _ _ _

theorem corner_parameters_tendsto {a b c₀ : ℝ} {c : A→ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hc : Tendsto c l (𝓝 c₀)) :
    Tendsto (fun p=>F.cornerParametersAt (c p) p) l (𝓝 ![c₀,θ,a,b]) := by
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases j
  · exact hc
  · exact F.theta_tendsto
  · exact ha
  · exact hb

theorem corner_coefficient_tendsto {a b c₀ : ℝ} {c : A→ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hc : Tendsto c l (𝓝 c₀)) (k : Fin 6) :
    Tendsto (fun p=>scaledCoefficient (F.epsilon p) (F.parametersAt (c p) p) k/F.epsilon p) l
      (𝓝 (Corner.first ![c₀,θ,a,b] k)) := by
  have hp := F.corner_parameters_tendsto ha hb hc
  have hfirst : Continuous (fun p : Corner.Parameters=>Corner.first p k) := by
    fin_cases k <;> dsimp [Corner.first] <;> fun_prop
  have hf := (hfirst.tendsto _).comp hp
  have hr := ((Corner.continuous_remainder k).tendsto _).comp (F.epsilon_zero.prodMk_nhds hp)
  have h := hf.add (F.epsilon_zero.mul hr)
  simp only [zero_mul,add_zero] at h
  apply h.congr'
  filter_upwards [F.epsilon_pos,F.corner_coefficient_exact] with p he hx
  rw [hx]
  dsimp only [Function.comp_def]
  field_simp

theorem corner_coefficient_uniform {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (k : Fin 6) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun p c=>scaledCoefficient (F.epsilon p) (F.parametersAt c p) k/F.epsilon p)
      (fun c=>Corner.first ![c,θ,a,b] k) l K := by
  apply Slow.uniform_on_compact_of_joint_limit (by fin_cases k <;> dsimp [Corner.first] <;> fun_prop) _ hK
  intro c
  exact (F.reindex Prod.fst tendsto_fst).corner_coefficient_tendsto
    (ha.comp tendsto_fst) (hb.comp tendsto_fst) tendsto_snd k

theorem corner_tail_tendsto {a b ξ₀ : ℝ} {ξ : A→ℝ} (c : ℝ)
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hξ : Tendsto ξ l (𝓝 ξ₀)) :
    Tendsto (fun p=>scaledTail (F.epsilon p) c (F.thetaAt p) (F.tuning p).stepSize
      (F.tuning p).tau (ξ p)/F.epsilon p) l
      (𝓝 (Corner.N θ a b ξ₀-4*c*(3-ξ₀))) := by
  have h1 := F.corner_coefficient_tendsto ha hb (c:=fun _=>c) tendsto_const_nhds 0
  have h2 := F.corner_coefficient_tendsto ha hb (c:=fun _=>c) tendsto_const_nhds 1
  have h3 := F.corner_coefficient_tendsto ha hb (c:=fun _=>c) tendsto_const_nhds 2
  have h := (h1.add (h2.mul hξ)).add (h3.mul (hξ.pow 2))
  have he : Corner.first ![c,θ,a,b] 0+Corner.first ![c,θ,a,b] 1*ξ₀+
      Corner.first ![c,θ,a,b] 2*ξ₀^2=Corner.N θ a b ξ₀-4*c*(3-ξ₀) := by
    dsimp [Corner.first,Corner.N]
    ring
  rw [he] at h
  convert h using 1
  ext p
  dsimp [scaledCoefficient,parametersAt,scaledTail]
  ring

theorem corner_mixed_tendsto {a b ξ₀ : ℝ} {ξ : A→ℝ} (c : ℝ)
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hξ : Tendsto ξ l (𝓝 ξ₀)) :
    Tendsto (fun p=>F.layerMixed c p (ξ p)/F.epsilon p) l
      (𝓝 (Corner.N θ a b ξ₀-2*c*(4-ξ₀))) := by
  have h1 := F.corner_coefficient_tendsto ha hb (c:=fun _=>c) tendsto_const_nhds 3
  have h2 := F.corner_coefficient_tendsto ha hb (c:=fun _=>c) tendsto_const_nhds 4
  have h3 := F.corner_coefficient_tendsto ha hb (c:=fun _=>c) tendsto_const_nhds 5
  have h := (h1.add (h2.mul hξ)).add (h3.mul (hξ.pow 2))
  have he : Corner.first ![c,θ,a,b] 3+Corner.first ![c,θ,a,b] 4*ξ₀+
      Corner.first ![c,θ,a,b] 5*ξ₀^2=Corner.N θ a b ξ₀-2*c*(4-ξ₀) := by
    dsimp [Corner.first,Corner.N]
    ring
  rw [he] at h
  convert h using 1
  ext p
  dsimp [scaledCoefficient,parametersAt,layerMixed]
  ring

theorem corner_tail_uniform {a b : ℝ} (c : ℝ)
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun p ξ=>scaledTail (F.epsilon p) c (F.thetaAt p)
      (F.tuning p).stepSize (F.tuning p).tau ξ/F.epsilon p)
      (fun ξ=>Corner.N θ a b ξ-4*c*(3-ξ)) l K := by
  apply Slow.uniform_on_compact_of_joint_limit (by unfold Corner.N;fun_prop) _ hK
  intro ξ
  exact (F.reindex Prod.fst tendsto_fst).corner_tail_tendsto c
    (ha.comp tendsto_fst) (hb.comp tendsto_fst) tendsto_snd

theorem corner_mixed_uniform {a b : ℝ} (c : ℝ)
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun p ξ=>F.layerMixed c p ξ/F.epsilon p)
      (fun ξ=>Corner.N θ a b ξ-2*c*(4-ξ)) l K := by
  apply Slow.uniform_on_compact_of_joint_limit (by unfold Corner.N;fun_prop) _ hK
  intro ξ
  exact (F.reindex Prod.fst tendsto_fst).corner_mixed_tendsto c
    (ha.comp tendsto_fst) (hb.comp tendsto_fst) tendsto_snd

theorem P0_corner_tendsto (c : ℝ) :
    Tendsto (fun p=>scaledP0 (F.epsilon p) c (F.thetaAt p) (F.tuning p).stepSize
      (F.tuning p).tau/F.epsilon p) l (𝓝 0) := by
  have h := (((F.epsilon_zero.pow 2).const_mul c).mul (F.slow_test_tendsto c)).mul
    (F.characteristic_at_radius_tendsto c 1)
  simp only [zero_pow (by omega : 2≠0),mul_zero,zero_mul] at h
  apply h.congr'
  filter_upwards [F.epsilon_pos,F.beta_eq] with p hp hb
  rw [hb,scaledP0_exact,realCharacteristic_slow]
  field_simp

theorem corner_cubic_tendsto {a b ξ₀ : ℝ} {ξ : A→ℝ} (c : ℝ)
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hξ : Tendsto ξ l (𝓝 ξ₀)) :
    Tendsto (fun p=>F.layerCubic c p (ξ p)/F.epsilon p) l
      (𝓝 (ξ₀*(Corner.N θ a b ξ₀-4*c*(3-ξ₀)))) := by
  have h := (F.P0_corner_tendsto c).add (hξ.mul (F.corner_tail_tendsto c ha hb hξ))
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [F.epsilon_pos] with p hp
  unfold layerCubic
  field_simp

theorem corner_cubic_uniform {a b : ℝ} (c : ℝ)
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun p ξ=>F.layerCubic c p ξ/F.epsilon p)
      (fun ξ=>ξ*(Corner.N θ a b ξ-4*c*(3-ξ))) l K := by
  apply Slow.uniform_on_compact_of_joint_limit (by unfold Corner.N;fun_prop) _ hK
  intro ξ
  exact (F.reindex Prod.fst tendsto_fst).corner_cubic_tendsto c
    (ha.comp tendsto_fst) (hb.comp tendsto_fst) tendsto_snd

end
end nesterov.TwoStep.Scaling
