import nesterov.Corner.Expansion

/-! Joint compact uniformity in the source's test constant and frequency coordinate. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ : ℝ} (F : Scaling A l θ 2 (1/2))

theorem corner_tail_joint_tendsto {a b c₀ ξ₀ : ℝ} {c ξ : A→ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hc : Tendsto c l (𝓝 c₀)) (hξ : Tendsto ξ l (𝓝 ξ₀)) :
    Tendsto (fun p=>scaledTail (F.epsilon p) (c p) (F.thetaAt p) (F.tuning p).stepSize
      (F.tuning p).tau (ξ p)/F.epsilon p) l
      (𝓝 (Corner.N θ a b ξ₀-4*c₀*(3-ξ₀))) := by
  have h1 := F.corner_coefficient_tendsto ha hb hc 0
  have h2 := F.corner_coefficient_tendsto ha hb hc 1
  have h3 := F.corner_coefficient_tendsto ha hb hc 2
  have h := (h1.add (h2.mul hξ)).add (h3.mul (hξ.pow 2))
  have he : Corner.first ![c₀,θ,a,b] 0+Corner.first ![c₀,θ,a,b] 1*ξ₀+
      Corner.first ![c₀,θ,a,b] 2*ξ₀^2=Corner.N θ a b ξ₀-4*c₀*(3-ξ₀) := by
    dsimp [Corner.first,Corner.N]
    ring
  rw [he] at h
  convert h using 1
  ext p
  dsimp [scaledCoefficient,parametersAt,scaledTail]
  ring

theorem corner_mixed_joint_tendsto {a b c₀ ξ₀ : ℝ} {c ξ : A→ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hc : Tendsto c l (𝓝 c₀)) (hξ : Tendsto ξ l (𝓝 ξ₀)) :
    Tendsto (fun p=>F.layerMixed (c p) p (ξ p)/F.epsilon p) l
      (𝓝 (Corner.N θ a b ξ₀-2*c₀*(4-ξ₀))) := by
  have h1 := F.corner_coefficient_tendsto ha hb hc 3
  have h2 := F.corner_coefficient_tendsto ha hb hc 4
  have h3 := F.corner_coefficient_tendsto ha hb hc 5
  have h := (h1.add (h2.mul hξ)).add (h3.mul (hξ.pow 2))
  have he : Corner.first ![c₀,θ,a,b] 3+Corner.first ![c₀,θ,a,b] 4*ξ₀+
      Corner.first ![c₀,θ,a,b] 5*ξ₀^2=Corner.N θ a b ξ₀-2*c₀*(4-ξ₀) := by
    dsimp [Corner.first,Corner.N]
    ring
  rw [he] at h
  convert h using 1
  ext p
  dsimp [scaledCoefficient,parametersAt,layerMixed]
  ring


theorem corner_tail_uniform_joint {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    {K : Set (ℝ×ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun p x=>scaledTail (F.epsilon p) x.1 (F.thetaAt p)
      (F.tuning p).stepSize (F.tuning p).tau x.2/F.epsilon p)
      (fun x=>Corner.N θ a b x.2-4*x.1*(3-x.2)) l K := by
  apply Slow.uniform_on_compact_of_joint_limit (by unfold Corner.N;fun_prop) _ hK
  intro x
  have hc : Tendsto (fun p : A×(ℝ×ℝ)=>p.2.1) (l×ˢ𝓝 x) (𝓝 x.1) :=
    (continuous_fst.tendsto x).comp tendsto_snd
  have hξ : Tendsto (fun p : A×(ℝ×ℝ)=>p.2.2) (l×ˢ𝓝 x) (𝓝 x.2) :=
    (continuous_snd.tendsto x).comp tendsto_snd
  exact (F.reindex Prod.fst tendsto_fst).corner_tail_joint_tendsto
    (ha.comp tendsto_fst) (hb.comp tendsto_fst) hc hξ

theorem corner_mixed_uniform_joint {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    {K : Set (ℝ×ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun p x=>F.layerMixed x.1 p x.2/F.epsilon p)
      (fun x=>Corner.N θ a b x.2-2*x.1*(4-x.2)) l K := by
  apply Slow.uniform_on_compact_of_joint_limit (by unfold Corner.N;fun_prop) _ hK
  intro x
  have hc : Tendsto (fun p : A×(ℝ×ℝ)=>p.2.1) (l×ˢ𝓝 x) (𝓝 x.1) :=
    (continuous_fst.tendsto x).comp tendsto_snd
  have hξ : Tendsto (fun p : A×(ℝ×ℝ)=>p.2.2) (l×ˢ𝓝 x) (𝓝 x.2) :=
    (continuous_snd.tendsto x).comp tendsto_snd
  exact (F.reindex Prod.fst tendsto_fst).corner_mixed_joint_tendsto
    (ha.comp tendsto_fst) (hb.comp tendsto_fst) hc hξ

end
end nesterov.TwoStep.Scaling
