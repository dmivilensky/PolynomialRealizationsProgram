import jacobi.Analytic.ProfileTerms
import jacobi.GelfandLevitan.ProfileSeries

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The original Lambda-weighted reflected profile series converges normally
in the genuine continuous-function Banach space, uniformly in complex
order on one common disk. Its holomorphic sum has exactly the original
real profile as its real restriction.
Use: its true squared integral defines the holomorphic continuation of the original persymmetric energy.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual original persymmetric profile, summed in the continuous-function norm on the full reflected physical interval.
Use: its true squared integral defines the holomorphic continuation of the original persymmetric energy.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def OrderDisk.profileMap {a0 : ℝ} (D : OrderDisk a0) (a : ℂ) : C(Interval,ℂ) :=
  ∑' k,D.profileTerm k a

/-- The genuine continued profile series is norm summable at every order of its closed inverse disk.
Use: justifies its continuous-function sum, scalar pointwise formula and exact original real identification.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: compare the actual profile-term norms with the proved uniform coefficient times the shifted inverse-square p-series. -/
theorem OrderDisk.profileMap_summable {a0 r B : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hB : 0<B) (hbound : ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ‖D.GLsolution a‖≤B)
    {a : ℂ} (ha : ‖a-(a0:ℂ)‖≤r) : Summable (fun k => D.profileTerm k a) := by
  obtain ⟨C,_,hterm⟩ := D.profileTerm_bounds hrD hB hbound
  have hM : Summable (fun k : ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  exact hM.of_norm_bounded (fun k => hterm a ha k)

/-- The genuine analytic profile has precisely the article's actual pointwise spectral series.
Use: preserves the original profile normalization, physical reflection and source term order in subsequent integration.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the proved genuine norm summability allows the bounded complex-linear point evaluation to commute with the original sum. -/
theorem OrderDisk.profileMap_apply {a0 r B : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hB : 0<B) (hbound : ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ‖D.GLsolution a‖≤B)
    {a : ℂ} (ha : ‖a-(a0:ℂ)‖≤r) (t : Interval) :
    D.profileMap a t=∑' k,D.profileTerm k a t :=
  (ContinuousMap.evalCLM ℂ t).map_tsum (D.profileMap_summable hrD hB hbound ha)

/-- The original profile partial sums converge uniformly in order in the actual continuous-function norm.
Use: supplies uniform convergence simultaneously in order and physical position, with every original spectral index included.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: use the proved actual summable inverse-square term majorant in the community uniform-series theorem, now in the original continuous-function Banach space itself. -/
theorem OrderDisk.profileMap_uniform {a0 r B : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hB : 0<B) (hbound : ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ‖D.GLsolution a‖≤B) :
    TendstoUniformlyOn (fun N : ℕ => fun a : ℂ => ∑ k∈Finset.range N,D.profileTerm k a)
      D.profileMap atTop (closedBall (a0:ℂ) r) := by
  obtain ⟨C,_,hterm⟩ := D.profileTerm_bounds hrD hB hbound
  have hM : Summable (fun k : ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  exact tendstoUniformlyOn_tsum_nat hM (fun k a ha => hterm a
    (by simpa only [mem_closedBall,dist_eq_norm] using ha) k)

/-- The original continued persymmetric profile is holomorphic in its genuine continuous-function norm.
Use: the true profile square and its bounded linear integral are holomorphic, giving the original c_star continuation.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual full-index profile majorant is summable uniformly on the order disk, and every original term is Banach holomorphic there. Apply the community Banach-valued Weierstrass theorem to their genuine sum. -/
theorem OrderDisk.profileMap_holomorphic {a0 r B : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hB : 0<B) (hbound : ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ‖D.GLsolution a‖≤B)
    (hunit : ∀ a∈ball (a0:ℂ) r,IsUnit (D.GLoperator a)) :
    DifferentiableOn ℂ D.profileMap (ball (a0:ℂ) r) := by
  obtain ⟨C,_,hterm⟩ := D.profileTerm_bounds hrD hB hbound
  have hM : Summable (fun k : ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  exact _root_.Complex.differentiableOn_tsum_of_summable_norm
    (E := C(Interval,ℂ)) hM (D.profileTerm_holomorphic hrD hunit) isOpen_ball
    (fun k a ha => hterm a (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using ha)) k)

/-- The actual analytic profile has one finite positive uniform bound on the entire closed inverse disk and reflected physical interval.
Use: proves the boundedness assertion for phi and ensures its original squared integral is a genuine finite analytic quantity.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual norm of the sum is at most the sum of the original term norms, and those are bounded by the same genuine summable inverse-square majorant. Enlarge its finite sum by one. -/
theorem OrderDisk.profileMap_bound {a0 r B : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hB : 0<B) (hbound : ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ‖D.GLsolution a‖≤B) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ‖D.profileMap a‖≤C := by
  -- The constant bounds the actual complete infinite profile series, rather than a numerical truncation.
  obtain ⟨A,hA,hterm⟩ := D.profileTerm_bounds hrD hB hbound
  let M := fun k : ℕ => A/(k+1:ℝ)^2
  have hM : Summable M := by
    simpa only [M,one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left A
  have hM0 : 0≤∑' k,M k := tsum_nonneg (fun k => by dsimp [M]; positivity)
  refine ⟨(∑' k,M k)+1,by linarith,fun a ha => ?_⟩
  have hn := hM.of_nonneg_of_le (fun k => norm_nonneg (D.profileTerm k a)) (hterm a ha)
  exact (norm_tsum_le_tsum_norm hn).trans
    ((hn.tsum_le_tsum (hterm a ha) hM).trans (by linarith))

/-- At every real order of the genuine inverse disk the complete analytic profile equals the original real persymmetric profile.
Use: identifies the holomorphic squared-profile integral with the article's actual original energy c_star.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: continuous evaluation commutes with the genuinely norm-summable analytic series. Every actual continued term has its exact original real value; real inclusion commutes with the original scalar sum. -/
theorem OrderDisk.profileMap_real {a0 r B b : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hB : 0<B) (hbound : ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ‖D.GLsolution a‖≤B)
    (hb : -1<b) (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤r) :
    D.profileMap (b:ℂ)=continuousOfReal (persymmetricProfile b hb) := by
  apply ContinuousMap.ext
  intro t
  rw [D.profileMap_apply hrD hB hbound hbd t]
  change (∑' k,D.profileTerm k (b:ℂ) t)=(persymmetricProfile b hb t:ℂ)
  rw [persymmetricProfile_apply,_root_.Complex.ofReal_tsum]
  exact tsum_congr (fun k => by
    simpa only [_root_.Complex.ofReal_mul] using D.profileTerm_real hb (hbd.trans hrD) k t)

end
end jacobi.Analytic
