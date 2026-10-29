import DominantFiveBody.TripleAreaPositivity
import DominantFiveBody.PairConvexity

/-! # Both actual directed regular-triple convex orders

Source §6.2. All ten cyclic triangle signs, including the primary vertex,
are verified from the exact internal and exterior area factors.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

def tripleRightOrder : HullOrder where
  labels :=
    { toFun := ![0, 4, 1, 2, 3]
      invFun := ![0, 2, 3, 4, 1]
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by intro i; fin_cases i <;> rfl }
  primary_first := rfl

def tripleBoundaryHullOrder (tau : ℝ) : HullOrder :=
  if 0 < tau then tripleRightOrder else standardHullOrder

def tripleMacroArea (tau : ℝ) (x : Configuration) (i : TripleLabel) : ℝ :=
  if 0 < tau then orientedArea x 0 4 i.castSucc.succ
  else orientedArea x 0 i.castSucc.succ 4

theorem tripleMacroArea_unit_boundary (alpha : TripleVector) (g : TripleGaps)
    (tau : ℝ) (htau : tau = 1 ∨ tau = -1) (i : TripleLabel) :
    tripleMacroArea tau (liftRelative (tripleChartPoints 0 alpha (tripleUnitPoint (tau * h) g))) i =
      Real.sin h := by
  have hq := tripleChartPoints_zero_cluster alpha (tripleUnitPoint (tau * h) g) i
  have hp := tripleChartPoints_zero_exterior alpha (tripleUnitPoint (tau * h) g)
  rcases htau with rfl | rfl
  · rw [tripleMacroArea, if_pos (by norm_num)]
    change det2 (tripleChartPoints 0 alpha (tripleUnitPoint (1 * h) g) 3 - 0)
      (tripleChartPoints 0 alpha (tripleUnitPoint (1 * h) g) i.castSucc - 0) = _
    rw [sub_zero, sub_zero, hp, hq]
    simp [tripleUnitPoint, unit_polar_det]
  · rw [tripleMacroArea, if_neg (by norm_num)]
    change det2 (tripleChartPoints 0 alpha (tripleUnitPoint (-1 * h) g) i.castSucc - 0)
      (tripleChartPoints 0 alpha (tripleUnitPoint (-1 * h) g) 3 - 0) = _
    rw [sub_zero, sub_zero, hp, hq]
    simp [tripleUnitPoint, unit_polar_det]

theorem tripleCentered_positions_ordered (alpha : TripleVector) (g : TripleGaps)
    (ha : ∑ i, alpha i = 1) (hg0 : 0 < g 0) (hg1 : 0 < g 1) :
    TripleOrdered (tripleCenteringMatrix alpha *ᵥ g) := by
  have hgap : tripleGapMatrix *ᵥ (tripleCenteringMatrix alpha *ᵥ g) = g := by
    rw [Matrix.mulVec_mulVec, tripleGapMatrix_centeringMatrix alpha ha, Matrix.one_mulVec]
  have h0 := congrFun hgap 0
  have h1 := congrFun hgap 1
  rw [tripleGapMatrix_mulVec_entry] at h0 h1
  apply tripleOrdered_of_positive_gaps
  · exact sub_pos.mp (h0.symm ▸ hg0)
  · exact sub_pos.mp (h1.symm ▸ hg1)

theorem tripleExternalAreaQuotient_unit_boundary_positive (alpha : TripleVector) (g : TripleGaps)
    (ha : ∑ i, alpha i = 1) (hg0 : 0 < g 0) (hg1 : 0 < g 1)
    (tau : ℝ) (htau : tau = 1 ∨ tau = -1) (i j : TripleLabel) (hij : i < j)
    (k : Label) (hk : k ∈ ({0, 4} : Finset Label)) :
    0 < tripleExternalAreaQuotient 0 alpha (tripleUnitPoint (tau * h) g) i j k := by
  have ho := tripleCentered_positions_ordered alpha g ha hg0 hg1
  have hg := sub_pos.mpr (ho i j hij)
  have hh : 0 < h := by unfold h; positivity
  have hangle : |tau * h| = h := by
    rcases htau with rfl | rfl <;> simp [abs_of_pos hh]
  obtain ⟨hne, hpi, _, _⟩ := tripleBoundaryAngle_facts (tau * h) hangle
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · simpa only [tripleExternalAreaQuotient_primary_boundary] using hg
  · rw [tripleExternalAreaQuotient_exterior_boundary]
    exact mul_pos hg (one_sub_cos_pos_of_ne_zero (tau * h) hne hpi)

theorem tripleChartArea_joint_continuous (i j k : Label) :
    Continuous (fun v : TripleJointVariables =>
      orientedArea (liftRelative (tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2)) i j k) :=
  (orientedArea_continuous i j k).comp (liftRelative_continuous.comp
    (continuous_pi (fun l => (tripleChartPoints_joint_contDiff 0 l).continuous)))

theorem tripleMacroArea_joint_continuous (tau : ℝ) (i : TripleLabel) :
    Continuous (fun v : TripleJointVariables =>
      tripleMacroArea tau (liftRelative (tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2)) i) := by
  unfold tripleMacroArea
  split_ifs
  · exact tripleChartArea_joint_continuous 0 4 i.castSucc.succ
  · exact tripleChartArea_joint_continuous 0 i.castSucc.succ 4

theorem tripleExteriorAreas_positive_neighborhood (alpha : TripleVector) (g : TripleGaps)
    (ha : ∑ i, alpha i = 1) (hg0 : 0 < g 0) (hg1 : 0 < g 1)
    (tau : ℝ) (htau : tau = 1 ∨ tau = -1) :
    ∀ᶠ v : TripleJointVariables in 𝓝 (tripleBoundaryParameter alpha, tripleUnitPoint (tau * h) g),
      (∀ i j : TripleLabel, i < j → ∀ k ∈ ({0, 4} : Finset Label),
        0 < tripleExternalAreaQuotient (v.1 1) (tripleJointAlpha v.1) v.2 i j k) ∧
      ∀ i : TripleLabel,
        0 < tripleMacroArea tau (liftRelative (tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2)) i := by
  have he : ∀ᶠ v : TripleJointVariables in 𝓝 (tripleBoundaryParameter alpha, tripleUnitPoint (tau * h) g),
      ∀ i j : TripleLabel, i < j → ∀ k ∈ ({0, 4} : Finset Label),
        0 < tripleExternalAreaQuotient (v.1 1) (tripleJointAlpha v.1) v.2 i j k := by
    have he' : ∀ᶠ v : TripleJointVariables in 𝓝 (tripleBoundaryParameter alpha, tripleUnitPoint (tau * h) g),
        ∀ (i j : TripleLabel) (k : Label), i < j → k ∈ ({0, 4} : Finset Label) →
          0 < tripleExternalAreaQuotient (v.1 1) (tripleJointAlpha v.1) v.2 i j k := by
      apply Filter.eventually_all.mpr
      intro i
      apply Filter.eventually_all.mpr
      intro j
      apply Filter.eventually_all.mpr
      intro k
      by_cases hij : i < j
      · by_cases hk : k ∈ ({0, 4} : Finset Label)
        · have hpos := tripleExternalAreaQuotient_unit_boundary_positive alpha g ha hg0 hg1 tau htau i j hij k hk
          have hc := (tripleExternalAreaQuotient_joint_contDiff 0 i j k).continuous.continuousAt
            (x := (tripleBoundaryParameter alpha, tripleUnitPoint (tau * h) g))
          have hp := hc.eventually (Ioi_mem_nhds hpos)
          filter_upwards [hp] with v hv
          exact fun _ _ => hv
        · exact Filter.Eventually.of_forall (fun _ _ h => (hk h).elim)
      · exact Filter.Eventually.of_forall (fun _ h _ => (hij h).elim)
    filter_upwards [he'] with v hv
    exact fun i j hij k hk => hv i j k hij hk
  have hm : ∀ᶠ v : TripleJointVariables in 𝓝 (tripleBoundaryParameter alpha, tripleUnitPoint (tau * h) g),
      ∀ i : TripleLabel,
        0 < tripleMacroArea tau (liftRelative (tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2)) i := by
    apply Filter.eventually_all.mpr
    intro i
    have hh : 0 < h := by unfold h; positivity
    have hpi : h < Real.pi := by unfold h; linarith [Real.pi_pos]
    have hpos : 0 < tripleMacroArea tau (liftRelative (tripleChartPoints 0 alpha (tripleUnitPoint (tau * h) g))) i := by
      rw [tripleMacroArea_unit_boundary alpha g tau htau i]
      exact Real.sin_pos_of_pos_of_lt_pi hh hpi
    exact (tripleMacroArea_joint_continuous tau i).continuousAt.eventually (Ioi_mem_nhds hpos)
  exact he.and hm

theorem tripleStrictConvex_of_positive_areas (tau : ℝ) (htau : tau = 1 ∨ tau = -1)
    (x : Configuration)
    (he : ∀ i j : TripleLabel, i < j → ∀ k ∈ ({0, 4} : Finset Label),
      0 < orientedArea x i.castSucc.succ j.castSucc.succ k)
    (hm : ∀ i : TripleLabel, 0 < tripleMacroArea tau x i)
    (hint : 0 < orientedArea x 1 2 3) : StrictConvexInOrder (tripleBoundaryHullOrder tau) x := by
  have hp (i j : TripleLabel) (hij : i < j) :
      0 < orientedArea x 0 i.castSucc.succ j.castSucc.succ := by
    have h := he i j hij 0 (by simp)
    rwa [orientedArea_cyclic, orientedArea_cyclic] at h
  have hpe (i j : TripleLabel) (hij : i < j) :
      0 < orientedArea x 4 i.castSucc.succ j.castSucc.succ := by
    have h := he i j hij 4 (by simp)
    rwa [orientedArea_cyclic, orientedArea_cyclic] at h
  have hp01 := hp 0 1 (by decide)
  have hp02 := hp 0 2 (by decide)
  have hp12 := hp 1 2 (by decide)
  have he01 := he 0 1 (by decide) 4 (by simp)
  have he02 := he 0 2 (by decide) 4 (by simp)
  have he12 := he 1 2 (by decide) 4 (by simp)
  have hpe01 := hpe 0 1 (by decide)
  have hpe02 := hpe 0 2 (by decide)
  have hpe12 := hpe 1 2 (by decide)
  rcases htau with rfl | rfl
  · have hm0 : 0 < orientedArea x 0 4 1 := by simpa [tripleMacroArea] using hm 0
    have hm1 : 0 < orientedArea x 0 4 2 := by simpa [tripleMacroArea] using hm 1
    have hm2 : 0 < orientedArea x 0 4 3 := by simpa [tripleMacroArea] using hm 2
    simp only [tripleBoundaryHullOrder, if_pos (by norm_num : (0 : ℝ) < 1)]
    apply strictConvex_of_ordered_triple_areas
    intro i j k hij hjk
    rcases increasingTriple_fin_five i j k hij hjk with h | h | h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals dsimp [tripleRightOrder]
    all_goals first
      | exact hm0
      | exact hm1
      | exact hm2
      | exact hp01
      | exact hp02
      | exact hp12
      | exact hpe01
      | exact hpe02
      | exact hpe12
      | exact hint
  · have hm0 : 0 < orientedArea x 0 1 4 := by
      have he := hm 0
      rw [tripleMacroArea, if_neg (by norm_num : ¬ (0 : ℝ) < -1)] at he
      simpa using he
    have hm1 : 0 < orientedArea x 0 2 4 := by
      have he := hm 1
      rw [tripleMacroArea, if_neg (by norm_num : ¬ (0 : ℝ) < -1)] at he
      simpa using he
    have hm2 : 0 < orientedArea x 0 3 4 := by
      have he := hm 2
      rw [tripleMacroArea, if_neg (by norm_num : ¬ (0 : ℝ) < -1)] at he
      simpa using he
    simp only [tripleBoundaryHullOrder, if_neg (by norm_num : ¬ (0 : ℝ) < -1)]
    apply standardStrictConvex_of_increasing_triples
    intro i j k hij hjk
    rcases increasingTriple_fin_five i j k hij hjk with h | h | h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals first
      | exact hm0
      | exact hm1
      | exact hm2
      | exact hp01
      | exact hp02
      | exact hp12
      | exact he01
      | exact he02
      | exact he12
      | exact hint

/-- All ten area signs on a smaller product about an actual scalar seed.
Both directed triple orders include the primary as a hull vertex. -/
theorem tripleChart_strictConvex_neighborhood
    (alpha0 z0 : TripleVector) (ha : TripleWeights alpha0) (hz : TripleOrdered z0)
    (hscalar : ∀ i, tripleScalarResidual alpha0 z0 i = 0)
    (tau : ℝ) (htau : tau = 1 ∨ tau = -1)
    (eta r : ℝ) (heta : 0 < eta) (hr : 0 < r)
    (branch : TripleChartParameters → TripleChartVariables)
    (hbase : branch (tripleBoundaryParameter alpha0) =
      tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z0))
    (hsmooth : ContDiffOn ℝ ∞ branch (Metric.ball (tripleBoundaryParameter alpha0) eta))
    (hroots : ∀ q, dist q (tripleBoundaryParameter alpha0) < eta →
      tripleChartParameterRows q (branch q) = 0)
    (hradii : ∀ q, dist q (tripleBoundaryParameter alpha0) < eta →
      ∀ i, 0 < tripleChartRadii (q 1) (tripleJointAlpha q) (branch q) i)
    (huniq : ∀ q, dist q (tripleBoundaryParameter alpha0) < eta →
      ∀ y, dist y (tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z0)) < r →
        (tripleChartParameterRows q y = 0 ↔ branch q = y)) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ eta ∧
      ∀ eps t alpha, dist (tripleParameter eps t alpha) (tripleBoundaryParameter alpha0) < delta →
        (∑ i, alpha i = 1) → 0 < t →
        StrictConvexInOrder (tripleBoundaryHullOrder tau)
          (liftRelative (tripleChartPoints t alpha (branch (tripleParameter eps t alpha)))) := by
  let q0 := tripleBoundaryParameter alpha0
  have hg0 : 0 < (tripleGapMatrix *ᵥ z0) 0 := by
    rw [tripleGapMatrix_mulVec_entry]
    exact sub_pos.mpr (hz 0 1 (by decide))
  have hg1 : 0 < (tripleGapMatrix *ᵥ z0) 1 := by
    rw [tripleGapMatrix_mulVec_entry]
    exact sub_pos.mpr (hz 1 2 (by decide))
  have hambient := tripleExteriorAreas_positive_neighborhood alpha0 (tripleGapMatrix *ᵥ z0)
    ha.2 hg0 hg1 tau htau
  have hbAt : ContinuousAt branch q0 :=
    hsmooth.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self heta))
  have hgraph : ContinuousAt (fun q : TripleChartParameters => (q, branch q)) q0 :=
    continuousAt_id.prodMk hbAt
  rw [← hbase] at hambient
  have hext := hgraph.eventually hambient
  obtain ⟨dE, hdE, hE⟩ := Metric.eventually_nhds_iff.mp hext
  obtain ⟨dI, hdI, hdIeta, hI⟩ := tripleChart_internal_area_positive_neighborhood
    alpha0 z0 ha hz hscalar tau htau eta r heta hr branch hbase hsmooth hroots hradii huniq
  refine ⟨min dI dE, lt_min hdI hdE, (min_le_left _ _).trans hdIeta, ?_⟩
  intro eps t alpha hq hasum ht
  have hqi := lt_of_lt_of_le hq (min_le_left dI dE)
  have hqe := lt_of_lt_of_le hq (min_le_right dI dE)
  obtain ⟨hfactor, hcoeff⟩ := hI eps t alpha hqi hasum
  have harea : 0 < orientedArea
      (liftRelative (tripleChartPoints t alpha (branch (tripleParameter eps t alpha)))) 1 2 3 := by
    rw [hfactor]
    exact mul_pos (pow_pos ht 3) hcoeff
  obtain ⟨he, hm⟩ := hE hqe
  apply tripleStrictConvex_of_positive_areas tau htau _ _ _ harea
  · intro i j hij k hk
    rw [tripleExternalArea_factor]
    apply mul_pos ht
    simpa only [tripleParameter_alpha,
      show tripleParameter eps t alpha 1 = t from rfl] using he i j hij k hk
  · intro i
    simpa only [tripleParameter_alpha,
      show tripleParameter eps t alpha 1 = t from rfl] using hm i

end DominantFiveBody
