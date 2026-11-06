import nesterov.Oracle.EmbeddingData
import nesterov.Oracle.Model

/-! Partial-frame oracle replies are defined for arbitrary frames. On an
orthonormal full frame they agree with a genuine first-order oracle. -/
namespace nesterov.Oracle
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace
variable {J E : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def prefixCoordinates {N k : ℕ} (u : Fin k→E) (x : E) : EuclideanSpace ℝ (Fin (N+1)) :=
  WithLp.toLp 2 (fun j=>if h : j.val<k then inner ℝ (u ⟨j.val,h⟩) x else 0)

def prefixLift {N k : ℕ} (u : Fin k→E) (z : EuclideanSpace ℝ (Fin (N+1))) : E :=
  ∑ j : Fin (N+1),if h : j.val<k then z j • u ⟨j.val,h⟩ else 0

def fakeOraclePrefix {N k : ℕ} (D : ExtensionData J (EuclideanSpace ℝ (Fin (N+1))))
    (u : Fin k→E) (x : E) : Reply E :=
  let z := prefixCoordinates (N:=N) u x
  (D.q/2*‖x‖^2+D.raw z (D.optimizer z),D.q • x+prefixLift u (D.support z))

omit [Fintype J] [DecidableEq J] [Nonempty J] in
theorem prefixCoordinates_full {N : ℕ} (v : Fin (N+1)→E) (x : E) :
    prefixCoordinates (N:=N) v x=frameCoordinates v x := by
  ext j
  simp only [prefixCoordinates,frameCoordinates,WithLp.ofLp_toLp,dite_eq_left j.isLt]

omit [Fintype J] [DecidableEq J] [Nonempty J] in
theorem prefixLift_full {N : ℕ} (v : Fin (N+1)→E) (z : EuclideanSpace ℝ (Fin (N+1))) :
    prefixLift v z=frameLift v z := by
  unfold prefixLift
  change _=∑ j,z j • v j
  apply Finset.sum_congr rfl
  intro j _
  simp only [dite_eq_left j.isLt]

omit [Fintype J] [DecidableEq J] [Nonempty J] in
theorem prefixCoordinates_eq_full {N k : ℕ} (v : Fin (N+1)→E) (hk : k≤N+1) (x : E)
    (hz : ∀ j : Fin (N+1),k≤j.val → inner ℝ (v j) x=0) :
    prefixCoordinates (N:=N) (framePrefix v k hk) x=frameCoordinates v x := by
  ext j
  by_cases hj : j.val<k
  · simp only [prefixCoordinates,frameCoordinates,WithLp.ofLp_toLp,dite_eq_left hj,framePrefix]
  · simp only [prefixCoordinates,frameCoordinates,WithLp.ofLp_toLp,dite_eq_right hj]
    exact (hz j (by omega)).symm

omit [Fintype J] [DecidableEq J] [Nonempty J] in
theorem prefixLift_eq_full {N k : ℕ} (v : Fin (N+1)→E) (hk : k≤N+1)
    (z : EuclideanSpace ℝ (Fin (N+1))) (hz : ∀ j : Fin (N+1),k≤j.val → z j=0) :
    prefixLift (framePrefix v k hk) z=frameLift v z := by
  unfold prefixLift
  change _=∑ j,z j • v j
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val<k
  · simp only [dite_eq_left hj,framePrefix]
  · simp only [dite_eq_right hj,hz j (by omega),zero_smul]

variable {N : ℕ} (D : ExtensionData J (EuclideanSpace ℝ (Fin (N+1))))

theorem fakeOraclePrefix_agrees_full {v : Fin (N+1)→E} {i k : ℕ}
    (hk : k≤N+1) (hik : i<k) {x : E}
    (hx : ∀ j : Fin (N+1),i≤j.val → inner ℝ (v j) x=0)
    (hsupport : ∀ j : Fin (N+1),i<j.val → D.support (frameCoordinates v x) j=0) :
    fakeOraclePrefix D (framePrefix v k hk) x=fakeOraclePrefix D v x := by
  have hc := prefixCoordinates_eq_full v hk x (fun j hj=>hx j (by omega))
  have hl := prefixLift_eq_full v hk (D.support (frameCoordinates v x)) (fun j hj=>hsupport j (by omega))
  unfold fakeOraclePrefix
  rw [hc,prefixCoordinates_full]
  dsimp only
  rw [hl,prefixLift_full]

variable [CompleteSpace E]

theorem fakeOraclePrefix_is_oracle {v : Fin (N+1)→E} (hv : Orthonormal ℝ v) :
    fakeOraclePrefix D v=firstOrderOracle (D.embed v).potential := by
  funext x
  apply Prod.ext
  · change D.q/2*‖x‖^2+D.raw (prefixCoordinates v x) (D.optimizer (prefixCoordinates v x))=
      (D.embed v).potential x
    rw [prefixCoordinates_full]
    exact (D.embed_potential hv x).symm
  · change D.q • x+prefixLift v (D.support (prefixCoordinates v x))=gradient (D.embed v).potential x
    rw [(D.embed v).gradient_eq,D.embed_field hv,prefixCoordinates_full,prefixLift_full]

end
end nesterov.Oracle
