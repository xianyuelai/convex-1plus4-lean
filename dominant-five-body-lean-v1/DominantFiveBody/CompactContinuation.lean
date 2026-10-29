import DominantFiveBody.LocalContinuation
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Compact product continuation for the actual seven equations

The compact input is a set of genuine parameter/root pairs. In the
manuscript it is the graph `(0, β, y⁰(β))`; no lower bound on satellite
masses or relation between independent parameters is added here.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

abbrev RootGraphPoint := ContinuationParameter × SliceCoordinates

/-- A compact set lying in an actual neighborhood has a common metric
tube. This is the metric Lebesgue number lemma, not an assumed radius. -/
theorem compact_uniform_neighborhood {X : Type*} [PseudoMetricSpace X]
    (K U : Set X) (hK : IsCompact K) (hU : ∀ x ∈ K, U ∈ 𝓝 x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ z, dist z x < δ → z ∈ U := by
  have hcover : K ⊆ ⋃ _ : Unit, interior U := by
    intro x hx
    exact mem_iUnion.mpr ⟨(), mem_interior_iff_mem_nhds.mpr (hU x hx)⟩
  obtain ⟨δ, hδ, hballs⟩ := lebesgue_number_lemma_of_metric hK
    (fun _ : Unit => isOpen_interior) hcover
  refine ⟨δ, hδ, ?_⟩
  intro x hx z hz
  obtain ⟨_, hb⟩ := hballs x hx
  exact interior_subset (hb hz)

theorem sliceRegular_joint_eventually (p : ContinuationParameter) (y : SliceCoordinates)
    (hreg : SliceRegular p y) :
    ∀ᶠ z : RootGraphPoint in 𝓝 (p, y), SliceRegular z.1 z.2 := by
  have hy : ∀ᶠ z : RootGraphPoint in 𝓝 (p, y), SliceRegular p z.2 :=
    continuousAt_snd.tendsto.eventually ((isOpen_sliceRegular p).mem_nhds hreg)
  have hp : ∀ᶠ z : RootGraphPoint in 𝓝 (p, y), -1 < z.1.1 :=
    (isOpen_lt continuous_const (continuous_fst.fst)).mem_nhds hreg.1
  filter_upwards [hy, hp] with z hy hp
  exact ⟨hp, hy.2⟩

theorem reducedJacobian_inverse_joint_continuousAt (p : ContinuationParameter)
    (y : SliceCoordinates) (hreg : SliceRegular p y)
    (hJ : (reducedJacobian p y).IsInvertible) :
    ContinuousAt (fun z : RootGraphPoint => (reducedJacobian z.1 z.2).inverse) (p, y) := by
  exact ContinuousAt.comp (f := fun z : RootGraphPoint => reducedJacobian z.1 z.2)
    (x := (p, y))
    (hJ.contDiffAt_map_inverse (𝕜 := ℝ) (n := 0)).continuousAt
    (reducedJacobian_joint_continuousAt p y hreg)

/-- Actual common inverse bound in a full tube around a compact set of
regular invertible points; the bound also covers nearby actual roots. -/
theorem reducedJacobian_compact_inverse_tube (K : Set RootGraphPoint)
    (hK : IsCompact K)
    (hdata : ∀ a ∈ K, SliceRegular a.1 a.2 ∧ (reducedJacobian a.1 a.2).IsInvertible) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ a ∈ K, ∀ z : RootGraphPoint,
      dist z a < δ → SliceRegular z.1 z.2 ∧ (reducedJacobian z.1 z.2).IsInvertible ∧
        ‖(reducedJacobian z.1 z.2).inverse‖ ≤ C := by
  have hcont : ContinuousOn (fun a : RootGraphPoint =>
      (reducedJacobian a.1 a.2).inverse) K := by
    intro a ha
    exact (reducedJacobian_inverse_joint_continuousAt a.1 a.2
      (hdata a ha).1 (hdata a ha).2).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcont.norm
  let C : ℝ := max B 1 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right B 1]
  let U : Set RootGraphPoint := {z | SliceRegular z.1 z.2 ∧
    (reducedJacobian z.1 z.2).IsInvertible ∧ ‖(reducedJacobian z.1 z.2).inverse‖ ≤ C}
  have hU : ∀ a ∈ K, U ∈ 𝓝 a := by
    intro a ha
    obtain ⟨hreg, hJ⟩ := hdata a ha
    have hbase : ‖(reducedJacobian a.1 a.2).inverse‖ < C := by
      have hb := hB (Set.mem_image_of_mem _ ha)
      dsimp [C]
      linarith [le_max_left B 1]
    have hnorm : ∀ᶠ z : RootGraphPoint in 𝓝 a,
        ‖(reducedJacobian z.1 z.2).inverse‖ < C :=
      ((reducedJacobian_inverse_joint_continuousAt a.1 a.2 hreg hJ).norm).tendsto.eventually
        ((isOpen_lt continuous_id continuous_const).mem_nhds hbase)
    filter_upwards [sliceRegular_joint_eventually a.1 a.2 hreg,
      reducedJacobian_eventually_isInvertible a.1 a.2 hreg hJ, hnorm] with z hr hj hn
    exact ⟨hr, hj, hn.le⟩
  obtain ⟨δ, hδ, htube⟩ := compact_uniform_neighborhood K U hK hU
  exact ⟨δ, C, hδ, hC, htube⟩

/-- A common root radius and parameter radius for uniqueness follows by
covering the actual compact graph with genuine IFT rectangles. -/
theorem reducedResidual_compact_uniform_uniqueness (K : Set RootGraphPoint)
    (hK : IsCompact K)
    (hdata : ∀ a ∈ K, SliceRegular a.1 a.2 ∧ reducedResidual a.1 a.2 = 0 ∧
      (reducedJacobian a.1 a.2).IsInvertible) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ K, ∀ q v w,
      dist q a.1 < r → dist v a.2 < r → dist w a.2 < r →
      reducedResidual q v = 0 → reducedResidual q w = 0 → v = w := by
  classical
  have hlocal (a : K) := reducedResidual_local_product a.1.1 a.1.2
    (hdata a.1 a.2).1 (hdata a.1 a.2).2.1 (hdata a.1 a.2).2.2
  choose ψ η ζ hη hζ hbase hsmooth hrows using hlocal
  let U (a : K) : Set RootGraphPoint :=
    {z | dist z.1 a.1.1 < η a ∧ dist z.2 a.1.2 < ζ a}
  have hopen (a : K) : IsOpen (U a) := by
    exact (isOpen_lt (continuous_fst.dist continuous_const) continuous_const).inter
      (isOpen_lt (continuous_snd.dist continuous_const) continuous_const)
  have hcover : K ⊆ ⋃ a : K, U a := by
    intro a ha
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, by simpa [U] using And.intro (hη ⟨a, ha⟩) (hζ ⟨a, ha⟩)⟩
  obtain ⟨r, hr, hballs⟩ := lebesgue_number_lemma_of_metric hK hopen hcover
  refine ⟨r, hr, ?_⟩
  intro a ha q v w hq hv hw hrv hrw
  obtain ⟨b, hb⟩ := hballs a ha
  have hvb : (q, v) ∈ U b := hb (by simpa only [Metric.mem_ball, Prod.dist_eq] using max_lt hq hv)
  have hwb : (q, w) ∈ U b := hb (by simpa only [Metric.mem_ball, Prod.dist_eq] using max_lt hq hw)
  have hqp : dist q.1 b.1.1.1 < η b :=
    lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_left _ _) hvb.1
  have hqm : dist q.2 b.1.1.2 < η b :=
    lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _) hvb.1
  have hvroot := (hrows b q.1 q.2 hqp hqm).2.2 v hvb.2
  have hwroot := (hrows b q.1 q.2 hqp hqm).2.2 w hwb.2
  exact (hvroot.mp hrv).symm.trans (hwroot.mp hrw)

/-- Existence near one actual base root, with an arbitrary prescribed
root tolerance. The target root center can vary independently as well. -/
theorem reducedResidual_eventually_exists_near (p : ContinuationParameter)
    (y : SliceCoordinates) (hreg : SliceRegular p y) (hroot : reducedResidual p y = 0)
    (hJ : (reducedJacobian p y).IsInvertible) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ a : RootGraphPoint in 𝓝 (p, y),
      ∃ x, dist x a.2 < r ∧ reducedResidual a.1 x = 0 := by
  obtain ⟨ψ, hbase, hsmooth, hroots, _⟩ :=
    reducedResidual_local_implicitFunction p y hreg hroot hJ
  have hψ : ∀ᶠ a : RootGraphPoint in 𝓝 (p, y), dist (ψ a.1) y < r / 2 := by
    have hc : ContinuousAt (fun a : RootGraphPoint => ψ a.1) (p, y) :=
      ContinuousAt.comp (f := Prod.fst) (x := (p, y)) hsmooth.continuousAt continuousAt_fst
    have h := hc.tendsto.eventually
      (Metric.ball_mem_nhds (ψ p) (by linarith : 0 < r / 2))
    simpa only [Metric.mem_ball, hbase] using h
  have hy : ∀ᶠ a : RootGraphPoint in 𝓝 (p, y), dist a.2 y < r / 2 :=
    (continuous_snd.continuousAt (x := (p, y))).tendsto.eventually
      (Metric.ball_mem_nhds y (by linarith : 0 < r / 2))
  have hz : ∀ᶠ a : RootGraphPoint in 𝓝 (p, y), reducedResidual a.1 (ψ a.1) = 0 :=
    (continuous_fst.continuousAt (x := (p, y))).tendsto.eventually hroots
  filter_upwards [hψ, hy, hz] with a hψ hy hz
  refine ⟨ψ a.1, ?_, hz⟩
  have ht := dist_triangle (ψ a.1) y a.2
  rw [dist_comm y a.2] at ht
  linarith

/-- The full compact-graph product IFT for the actual residual. Both
parameter radii, the root radius and the true inverse bound are common.
The returned functions are smooth throughout their open parameter balls;
zero masses in the compact base are permitted by the actual hypotheses. -/
theorem reducedResidual_compact_product_bounded (K : Set RootGraphPoint) (hK : IsCompact K)
    (hdata : ∀ a ∈ K, SliceRegular a.1 a.2 ∧ reducedResidual a.1 a.2 = 0 ∧
      (reducedJacobian a.1 a.2).IsInvertible) (τ : ℝ) (hτ : 0 < τ) :
    ∃ η r C : ℝ, 0 < η ∧ 0 < r ∧ 0 < C ∧ r ≤ τ ∧ η ≤ r ∧
      ∀ a ∈ K, ∃ ψ : ContinuationParameter → SliceCoordinates,
        ψ a.1 = a.2 ∧ ContDiffOn ℝ ∞ ψ (Metric.ball a.1 η) ∧
        ∀ q, dist q a.1 < η → dist (ψ q) a.2 < r / 2 ∧
          SliceRegular q (ψ q) ∧ (reducedJacobian q (ψ q)).IsInvertible ∧
          ‖(reducedJacobian q (ψ q)).inverse‖ ≤ C ∧ reducedResidual q (ψ q) = 0 ∧
          (∀ z, dist z a.2 < r → (reducedResidual q z = 0 ↔ ψ q = z)) := by
  classical
  obtain ⟨u, hu, huniq⟩ := reducedResidual_compact_uniform_uniqueness K hK hdata
  obtain ⟨d, C, hd, hC, hinverse⟩ := reducedJacobian_compact_inverse_tube K hK
    (fun a ha => ⟨(hdata a ha).1, (hdata a ha).2.2⟩)
  let r : ℝ := min (min u d) τ
  have hr : 0 < r := lt_min (lt_min hu hd) hτ
  have hru : r ≤ u := (min_le_left (min u d) τ).trans (min_le_left u d)
  have hrd : r ≤ d := (min_le_left (min u d) τ).trans (min_le_right u d)
  let U : Set RootGraphPoint := {b | ∃ x, dist x b.2 < r / 2 ∧ reducedResidual b.1 x = 0}
  have hU : ∀ a ∈ K, U ∈ 𝓝 a := by
    intro a ha
    exact reducedResidual_eventually_exists_near a.1 a.2 (hdata a ha).1
      (hdata a ha).2.1 (hdata a ha).2.2 (r / 2) (by linarith)
  obtain ⟨b, hb, hexists⟩ := compact_uniform_neighborhood K U hK hU
  let η : ℝ := min b r
  have hη : 0 < η := lt_min hb hr
  refine ⟨η, r, C, hη, hr, hC, min_le_right _ _, min_le_right _ _, ?_⟩
  intro a ha
  let ψ : ContinuationParameter → SliceCoordinates := fun q =>
    if h : ∃ x, dist x a.2 < r / 2 ∧ reducedResidual q x = 0 then Classical.choose h else a.2
  have hψ (q : ContinuationParameter) (hq : dist q a.1 < η) :
      dist (ψ q) a.2 < r / 2 ∧ reducedResidual q (ψ q) = 0 := by
    have hdist : dist (q, a.2) a < b := by
      rw [Prod.dist_eq, dist_self]
      exact max_lt (lt_of_lt_of_le hq (min_le_left b r)) hb
    have he : ∃ x, dist x a.2 < r / 2 ∧ reducedResidual q x = 0 := hexists a ha (q, a.2) hdist
    simpa only [ψ, dif_pos he] using Classical.choose_spec he
  have hq_u (q : ContinuationParameter) (hq : dist q a.1 < η) : dist q a.1 < u :=
    lt_of_lt_of_le hq ((min_le_right b r).trans hru)
  have hnear (q : ContinuationParameter) (hq : dist q a.1 < η) :
      SliceRegular q (ψ q) ∧ (reducedJacobian q (ψ q)).IsInvertible ∧
        ‖(reducedJacobian q (ψ q)).inverse‖ ≤ C := by
    apply hinverse a ha (q, ψ q)
    rw [Prod.dist_eq]
    refine max_lt (lt_of_lt_of_le hq ((min_le_right b r).trans hrd)) ?_
    exact lt_of_lt_of_le (lt_trans (hψ q hq).1 (by linarith : r / 2 < r)) hrd
  have hψunique (q : ContinuationParameter) (hq : dist q a.1 < η)
      (z : SliceCoordinates) (hz : dist z a.2 < r) (hrootz : reducedResidual q z = 0) : ψ q = z := by
    exact huniq a ha q (ψ q) z (hq_u q hq)
      (lt_of_lt_of_le (lt_trans (hψ q hq).1 (by linarith : r / 2 < r)) hru)
      (lt_of_lt_of_le hz hru) (hψ q hq).2 hrootz
  refine ⟨ψ, hψunique a.1 (by simpa using hη) a.2 (by simpa using hr) (hdata a ha).2.1,
    ?_, ?_⟩
  · intro q hq
    obtain ⟨φ, hφbase, hφsmooth, hφroot, _⟩ := reducedResidual_local_implicitFunction q (ψ q)
      (hnear q hq).1 (hψ q hq).2 (hnear q hq).2.1
    have hparam : ∀ᶠ t in 𝓝 q, dist t a.1 < η :=
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const).mem_nhds hq
    have hφnear : ∀ᶠ t in 𝓝 q, dist (φ t) a.2 < r := by
      have hdist : dist (φ q) a.2 < r := by
        rw [hφbase]
        linarith [(hψ q hq).1]
      exact hφsmooth.continuousAt.tendsto.eventually
        ((isOpen_lt (continuous_id.dist continuous_const) continuous_const).mem_nhds hdist)
    have heq : ψ =ᶠ[𝓝 q] φ := by
      filter_upwards [hparam, hφnear, hφroot] with t ht hd hr
      exact hψunique t ht (φ t) hd hr
    exact (hφsmooth.congr_of_eventuallyEq heq).contDiffWithinAt
  · intro q hq
    refine ⟨(hψ q hq).1, (hnear q hq).1, (hnear q hq).2.1,
      (hnear q hq).2.2, (hψ q hq).2, ?_⟩
    intro z hz
    exact ⟨hψunique q hq z hz, fun he => he ▸ (hψ q hq).2⟩

theorem reducedResidual_compact_product (K : Set RootGraphPoint) (hK : IsCompact K)
    (hdata : ∀ a ∈ K, SliceRegular a.1 a.2 ∧ reducedResidual a.1 a.2 = 0 ∧
      (reducedJacobian a.1 a.2).IsInvertible) :
    ∃ η r C : ℝ, 0 < η ∧ 0 < r ∧ 0 < C ∧
      ∀ a ∈ K, ∃ ψ : ContinuationParameter → SliceCoordinates,
        ψ a.1 = a.2 ∧ ContDiffOn ℝ ∞ ψ (Metric.ball a.1 η) ∧
        ∀ q, dist q a.1 < η → dist (ψ q) a.2 < r / 2 ∧
          SliceRegular q (ψ q) ∧ (reducedJacobian q (ψ q)).IsInvertible ∧
          ‖(reducedJacobian q (ψ q)).inverse‖ ≤ C ∧ reducedResidual q (ψ q) = 0 ∧
          (∀ z, dist z a.2 < r → (reducedResidual q z = 0 ↔ ψ q = z)) := by
  obtain ⟨η, r, C, hη, hr, hC, _, _, hlocal⟩ :=
    reducedResidual_compact_product_bounded K hK hdata 1 (by norm_num)
  exact ⟨η, r, C, hη, hr, hC, hlocal⟩

/-- Any actual geometric open condition at the compact base graph is
preserved on the same uniform independent continuation products. -/
theorem reducedResidual_compact_product_preserving (K V : Set RootGraphPoint) (hK : IsCompact K)
    (hdata : ∀ a ∈ K, SliceRegular a.1 a.2 ∧ reducedResidual a.1 a.2 = 0 ∧
      (reducedJacobian a.1 a.2).IsInvertible) (hV : ∀ a ∈ K, V ∈ 𝓝 a) :
    ∃ η r C : ℝ, 0 < η ∧ 0 < r ∧ 0 < C ∧
      ∀ a ∈ K, ∃ ψ : ContinuationParameter → SliceCoordinates,
        ψ a.1 = a.2 ∧ ContDiffOn ℝ ∞ ψ (Metric.ball a.1 η) ∧
        ∀ q, dist q a.1 < η → (q, ψ q) ∈ V ∧ dist (ψ q) a.2 < r / 2 ∧
          SliceRegular q (ψ q) ∧ (reducedJacobian q (ψ q)).IsInvertible ∧
          ‖(reducedJacobian q (ψ q)).inverse‖ ≤ C ∧ reducedResidual q (ψ q) = 0 ∧
          (∀ z, dist z a.2 < r → (reducedResidual q z = 0 ↔ ψ q = z)) := by
  obtain ⟨d, hd, hVtube⟩ := compact_uniform_neighborhood K V hK hV
  obtain ⟨η, r, C, hη, hr, hC, hrd, hηr, hlocal⟩ :=
    reducedResidual_compact_product_bounded K hK hdata d hd
  refine ⟨η, r, C, hη, hr, hC, ?_⟩
  intro a ha
  obtain ⟨ψ, hbase, hsmooth, hbranch⟩ := hlocal a ha
  refine ⟨ψ, hbase, hsmooth, ?_⟩
  intro q hq
  have h := hbranch q hq
  refine ⟨hVtube a ha (q, ψ q) ?_, h⟩
  rw [Prod.dist_eq]
  exact max_lt (lt_of_lt_of_le hq (hηr.trans hrd))
    (lt_of_lt_of_le (lt_trans h.1 (by linarith : r / 2 < r)) hrd)

end DominantFiveBody
