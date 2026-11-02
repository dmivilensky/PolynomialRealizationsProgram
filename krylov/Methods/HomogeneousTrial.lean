import krylov.Methods.OneGradientCoordinates

/-!
Article: main_krylov, lem:U(c,d), genuine observed-data trial homogeneity.
Use: impose degree zero on primitive finite observed trial coefficients and
transfer it to the actual trial chosen by a real one-gradient prefix.
Source: exact actual one-gradient history coordinates; no trajectory scaling is assumed as a definition.
-/

namespace krylov.Methods
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The primitive observed trial coefficient is unchanged by positive scaling of all available vector data.
Use: this is the source's degree-zero trial-rule hypothesis, on actual finite observation charts.
Article: main_krylov, lem:U(c,d), homogeneous XRFC trials. -/
def ObservedTrialHomogeneous (trial : History E → ℝ) : Prop :=
  ∀ (k : ℕ) (data : E × (Fin k → E) × (Fin k → E)) (c : ℝ), 0<c →
    trial (oneGradientHistoryChart (c • data.1,(fun i => c • data.2.1 i),
      (fun i => c • data.2.2 i)))=trial (oneGradientHistoryChart data)

/-- A degree-zero primitive observed trial rule chooses the same actual trial on corresponding scaled real one-gradient prefixes.
Use: real XRFC execution homogeneity derives its trial equality from the source coefficient condition.
Article: main_krylov, lem:U(c,d).
Proof: the exact true history charts consist of the real initial gradient,
real queried steps and real returned gradients. Their actual prefix scaling
hypotheses identify the two genuine observed tuples, so primitive degree zero applies. -/
theorem oneGradient_trial_scalar (trial : History E → ℝ) (ht : ObservedTrialHomogeneous trial)
    (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (c : ℝ) (hc : 0<c)
    (hs : ∀ i<k, oneGradientStep m A (c • g) i=c • oneGradientStep m A g i)
    (hG : ∀ i≤k, oneGradientGradient m A (c • g) i=c • oneGradientGradient m A g i) :
    trial (oneGradientRun m A (c • g) k)=trial (oneGradientRun m A g k) := by
  -- Only already observed scaled data enter the genuine primitive trial chart.
  have hS : (fun i : Fin k => oneGradientStep m A (c • g) (k-1-i.val))=
      fun i => c • oneGradientStep m A g (k-1-i.val) := funext fun i => hs _ (by omega)
  have hGs : (fun i : Fin k => oneGradientGradient m A (c • g) (k-i.val))=
      fun i => c • oneGradientGradient m A g (k-i.val) := funext fun i => hG _ (by omega)
  rw [oneGradientRun_chart m A (c • g) k,oneGradientRun_chart m A g k,hS,hGs]
  exact ht k (g,(fun i : Fin k => oneGradientStep m A g (k-1-i.val)),
    (fun i : Fin k => oneGradientGradient m A g (k-i.val))) c hc

end
end krylov.Methods
