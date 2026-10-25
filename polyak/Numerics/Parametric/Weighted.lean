import polyak.Numerics.Parametric.Scale

/-!
Article: Appendix B, weighted parametric continuation certificate.
Use: positive rational radii conjugate the Newton map to the unit cube. The
Boolean check implies existence and uniqueness for all real slab parameters.
-/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def unitBox (n : ℕ) : Fin n → IntervalRat := fun _ => ⟨-1,1,by norm_num⟩

def coordinateBox {n : ℕ} (c r : Fin n → ℚ) : Fin n → IntervalRat :=
  fun i => IntervalRat.add (IntervalRat.singleton (c i)) (symmetricInterval (r i))

structure WeightedCertificate (n : ℕ) where
  center : Fin n → ℚ
  radius : Fin n → ℚ
  preconditioner : Matrix (Fin n) (Fin n) ℚ

def normalized {n : ℕ} (cert : WeightedCertificate n) : Certificate n where
  center := fun _ => 0
  preconditioner := fun i j => cert.preconditioner i j/cert.radius i

def checkWeighted {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (cert : WeightedCertificate n) (cfg : EvalConfig := {}) : Bool :=
  decide (∀ i, 0<cert.radius i) &&
    check (scaledSystem F cert.center cert.radius) I (unitBox n) (normalized cert) cfg

noncomputable section

def normalizePoint {n : ℕ} (c r : Fin n → ℚ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (x i-(c i : ℝ))/(r i : ℝ)

theorem chart_mem {n : ℕ} (c r : Fin n → ℚ) (hr : ∀ i, 0<r i)
    {x : Fin n → ℝ} (hx : FinBoxMem x (unitBox n)) :
    FinBoxMem (chart c r x) (coordinateBox c r) := by
  intro i
  apply IntervalRat.mem_add (IntervalRat.mem_singleton (c i))
  have hp : (0 : ℝ)<r i := by exact_mod_cast hr i
  have hy : (-1 : ℝ)≤x i ∧ x i≤1 := by
    simpa [unitBox,IntervalRat.mem_def] using hx i
  simp only [symmetricInterval,IntervalRat.mem_def,abs_of_pos (hr i),Rat.cast_neg]
  constructor <;> nlinarith

theorem normalizePoint_mem {n : ℕ} (c r : Fin n → ℚ) (hr : ∀ i, 0<r i)
    {x : Fin n → ℝ} (hx : FinBoxMem x (coordinateBox c r)) :
    FinBoxMem (normalizePoint c r x) (unitBox n) := by
  intro i
  have hp : (0 : ℝ)<r i := by exact_mod_cast hr i
  have hy := hx i
  simp only [coordinateBox,IntervalRat.mem_def,IntervalRat.add,IntervalRat.singleton,
    symmetricInterval,abs_of_pos (hr i),Rat.cast_add,Rat.cast_neg] at hy
  simp only [unitBox,IntervalRat.mem_def,normalizePoint,Rat.cast_neg,Rat.cast_one]
  constructor
  · rw [le_div_iff₀ hp]
    linarith [hy.1]
  · rw [div_le_iff₀ hp]
    linarith [hy.2]

theorem chart_normalizePoint {n : ℕ} (c r : Fin n → ℚ) (hr : ∀ i, 0<r i)
    (x : Fin n → ℝ) : chart c r (normalizePoint c r x)=x := by
  ext i
  have hp : (r i : ℝ)≠0 := by exact_mod_cast (hr i).ne'
  dsimp [chart,normalizePoint]
  field_simp
  ring

theorem checkWeighted_sound {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (cert : WeightedCertificate n) (cfg : EvalConfig)
    (hc : checkWeighted F I cert cfg=true) :
    ∀ s∈I, ∃! x, FinBoxMem x (coordinateBox cert.center cert.radius) ∧ system F s x=0 := by
  simp only [checkWeighted,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨hr,hcheck⟩ := hc
  intro s hs
  obtain ⟨y,hy,huniq⟩ := check_sound _ I (unitBox n) (normalized cert) cfg hcheck s hs
  have hzero : system F s (chart cert.center cert.radius y)=0 := by
    rw [← scaledSystem_eval]
    exact hy.2
  refine ⟨chart cert.center cert.radius y,⟨chart_mem _ _ hr hy.1,hzero⟩,?_⟩
  intro x hx
  have he := chart_normalizePoint cert.center cert.radius hr x
  have hz : system (scaledSystem F cert.center cert.radius) s
      (normalizePoint cert.center cert.radius x)=0 := by
    rw [scaledSystem_eval,he]
    exact hx.2
  have hn := huniq _ ⟨normalizePoint_mem _ _ hr hx.1,hz⟩
  rw [← he,hn]

end
end polyak.Numerics.Parametric
