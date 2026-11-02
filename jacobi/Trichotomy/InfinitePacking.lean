import jacobi.Trichotomy.PackedDensity

/-!
Article: jacobi, Proposition C.4.
For the actual centered coordinate, divergence at the left endpoint
forces its entire image to be the real line. The genuine inverse then
tends to zero at minus infinity. These common topological facts are
used by both infinite-support endpoint regimes.
Use: the supercritical and critical endpoint theorems discharge the divergence premise from their actual profile asymptotics, obtaining full source support.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- A proved infinite left endpoint of the actual centered coordinate forces the genuine packing image to be the entire real line.
Use: the supercritical and critical endpoint theorems discharge the divergence premise from their actual profile asymptotics, obtaining full source support.
Article: jacobi, Proposition C.4.
Proof: actual coordinate values become smaller than both y and -y near zero. The exact physical reflection supplies their negatives in the same interval image, whose order-connectedness fills y. -/
theorem packingImage_eq_univ_of_atBot (a : ℝ) (ha : -1<a)
    (hleft : Tendsto (packingCoordinate a ha) (𝓝[>] (0:ℝ)) atBot) :
    packingImage a ha=univ := by
  -- Every real target is bracketed by two genuine physical preimages, without assuming an inverse on a larger domain.
  apply eq_univ_of_forall
  intro y
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),t∈Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨t,ht,hsmall⟩ := (hnear.and
    (hleft.eventually (eventually_lt_atBot (min y (-y)-1)))).exists
  have hmem : packingCoordinate a ha t∈packingImage a ha := ⟨t,ht,rfl⟩
  apply (packingImage_ordConnected a ha).out hmem (packingImage_neg a ha hmem)
  constructor <;> linarith [min_le_left y (-y),min_le_right y (-y)]

/-- When the actual coordinate has full image, its genuine inverse tends to the physical left endpoint from inside as x tends to minus infinity.
Use: actual density tail limits, first proved in the original physical coordinate, transfer through this same inverse to ordinary spatial infinity.
Article: jacobi, Proposition C.4.
Proof: each fixed positive physical point provides a finite coordinate threshold. Strict increase forces the actual inverse below that point beyond the threshold, while its original interior membership keeps it positive. -/
theorem packingInverse_atBot (a : ℝ) (ha : -1<a) (hfull : packingImage a ha=univ) :
    Tendsto (packingInverse a ha) atBot (𝓝[>] (0:ℝ)) := by
  -- The bounds concern the actual inverse on the proved whole image, not an independently chosen parametrization.
  have hmem (x : ℝ) : x∈packingImage a ha := by rw [hfull]; trivial
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_order.mpr ⟨?_,?_⟩,Filter.Eventually.of_forall (fun x => (packingInverse_mem a ha (hmem x)).1)⟩
  · intro b hb
    exact Filter.Eventually.of_forall (fun x => hb.trans (packingInverse_mem a ha (hmem x)).1)
  · intro b hb
    let t := min b (1/2)/2
    have ht : t∈Ioo (0:ℝ) 1 := by
      have hmin : 0<min b (1/2) := lt_min hb (by norm_num)
      dsimp only [t]
      constructor <;> linarith [min_le_right b (1/2)]
    have htb : t<b := by dsimp only [t]; linarith [min_le_left b (1/2)]
    filter_upwards [eventually_lt_atBot (packingCoordinate a ha t)] with x hx
    apply lt_trans _ htb
    apply ((packingCoordinate_strictMono a ha).lt_iff_lt (packingInverse_mem a ha (hmem x)) ht).mp
    rwa [packingCoordinate_inverse a ha (hmem x)]

end
end jacobi.Trichotomy
