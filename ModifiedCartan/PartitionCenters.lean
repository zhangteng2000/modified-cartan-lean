import ModifiedCartan.PartitionTheorem

noncomputable section
set_option autoImplicit false
open Filter Topology Set Metric
namespace ModifiedCartan

theorem locallyBounded_comp {g : ℕ → ℂ → ℂ} {ψ : ℂ → ℂ} {U V : Set ℂ}
    (hg : LocallyBounded g U) (hψ : ContinuousOn ψ V) (hmap : MapsTo ψ V U) :
    LocallyBounded (fun n z => g n (ψ z)) V := by
  intro K hKV hK
  have him : ψ '' K ⊆ U := by rintro _ ⟨z, hz, rfl⟩; exact hmap (hKV hz)
  obtain ⟨C, hC⟩ := hg (ψ '' K) him (hK.image_of_continuousOn (hψ.mono hKV))
  exact ⟨C, fun n z hz => hC n (ψ z) (mem_image_of_mem ψ hz)⟩

theorem cclass_comp {p : ℕ} {f : Family p} {I : Finset (Fin p)} {ψ : ℂ → ℂ} {U V : Set ℂ}
    (hc : IsCClass f I U) (hψ : ContinuousOn ψ V) (hmap : MapsTo ψ V U) :
    IsCClass (fun i n z => f i n (ψ z)) I V := by
  obtain ⟨k, hk, hb, hlim⟩ := hc
  exact ⟨k, hk, fun j hj => locallyBounded_comp (hb j hj) hψ hmap,
    compactConvergence_comp hlim hψ hmap⟩

theorem cclass_congr {p : ℕ} {f g : Family p} {I : Finset (Fin p)} {U : Set ℂ}
    (hc : IsCClass f I U) (heq : ∀ i n z, z ∈ U → f i n z = g i n z) :
    IsCClass g I U := by
  obtain ⟨k, hk, hb, hlim⟩ := hc
  refine ⟨k, hk, ?_, ?_⟩
  · intro j hj
    exact locallyBounded_congr (hb j hj) (fun n z hz => by rw [heq j n z hz, heq k n z hz])
  · exact compactConvergence_congr hlim (fun n z hz => by
      apply Finset.sum_congr rfl
      intro j _
      rw [heq j n z hz, heq k n z hz])

/-- Pull the genuine partition property back by a unit-disk automorphism. -/
theorem partitionProperty_center {p : ℕ} {r : ℝ}
    (hpart : PartitionProperty p (disk r)) {a : ℂ} (ha : a ∈ disk 1) :
    PartitionProperty p {z ∈ disk 1 | ‖diskAutomorphism a z‖ < r} := by
  have han : ‖a‖ < 1 := by simpa [disk] using ha
  have hauto : DifferentiableOn ℂ (diskAutomorphism a) (disk 1) :=
    (diskAutomorphism_analytic han).differentiableOn.mono ball_subset_closedBall
  have hmap : MapsTo (diskAutomorphism a) (disk 1) (disk 1) :=
    fun z hz => diskAutomorphism_mem_disk han hz
  intro f hf hs
  let g : Family p := fun i n z => f i n (diskAutomorphism a z)
  have hg : UnitFamily g := fun i n =>
    ⟨(hf i n).1.comp hauto hmap, fun z hz => (hf i n).2 _ (hmap hz)⟩
  have hgs : ZeroSum g := fun n z hz => hs n _ (hmap hz)
  obtain ⟨φ, hφ, ⟨P⟩⟩ := hpart g hg hgs
  let V := {z ∈ disk 1 | ‖diskAutomorphism a z‖ < r}
  have hV : V ⊆ disk 1 := fun _ hz => hz.1
  have hVmap : MapsTo (diskAutomorphism a) V (disk r) := by
    intro z hz
    simpa [disk] using hz.2
  refine ⟨φ, hφ, ⟨{ parts := P.parts, cover := P.cover, disjoint := P.disjoint, classes := ?_ }⟩⟩
  intro I hI
  have hc := cclass_comp (P.classes I hI) (hauto.continuousOn.mono hV) hVmap
  apply cclass_congr hc
  intro i n z hz
  simp only [subsequence, g, diskAutomorphism_involutive han hz.1]

/-- Corollary `cor:centers`, with the same explicit radius as the main theorem. -/
theorem partition_at_center {p : ℕ} (hp : 3 ≤ p) {K : ℕ → ℝ}
    (hK : WronskianExponents K) (hKm : ∀ m : ℕ, (m : ℝ) ≤ K m)
    {a : ℂ} (ha : a ∈ disk 1) :
    PartitionProperty p {z ∈ disk 1 |
      ‖(z - a) / (1 - star a * z)‖ < absorptionRadius K (p - 1) ^ (p - 1)} := by
  have h := partitionProperty_center (partition_at_recursive_radius hp hK hKm) ha
  convert h using 1
  ext z
  simp only [mem_ofPred_eq, diskAutomorphism, norm_div]
  rw [norm_sub_rev a z]
  rfl

end ModifiedCartan
