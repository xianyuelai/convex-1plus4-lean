import DominantFiveBody.NestedConvexContinuation

/-! The original common-product area assertion over the entire closed
alpha interval. Six divided exterior areas, three macro areas, and the
internal triple area are retained as ten separate actual signs. -/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1000000

def NestedTenAreasPositive (tau omega : ℝ) (x : Configuration) : Prop :=
  (∀ k : NestedEdge, ∀ j ∈ ({0, 4} : Finset Label),
    0 < nestedEdgeOrientation omega k *
      orientedArea x (nestedEdgeSource k).succ (nestedEdgeTarget k).succ j) ∧
  (∀ i : TripleLabel, 0 < tripleMacroArea tau x i) ∧
    0 < orientedArea x 1 2 3

theorem nestedChart_ten_areas_positive_neighborhood_of_zero_face
    (alpha0 tau omega radius : ℝ) (htau : tau = 1 ∨ tau = -1)
    (hw : omega = 1 ∨ omega = -1) (hrad : 0 < radius)
    (branch : NestedChartParameters → NestedChartVariables)
    (hbase : branch (nestedParameter 0 0 0 alpha0) = nestedBasePoint (tau * h) omega)
    (hsmooth : ContDiffOn ℝ ∞ branch (Metric.ball (nestedParameter 0 0 0 alpha0) radius))
    (hroots : ∀ q, dist q (nestedParameter 0 0 0 alpha0) < radius →
      nestedChartParameterRows q (branch q) = 0)
    (hradii : ∀ q, dist q (nestedParameter 0 0 0 alpha0) < radius →
      ∀ i, 0 < nestedChartRadii (q 1) (q 2) (q 3) (branch q) i)
    (hzero : ∀ eps eta alpha, dist (nestedParameter eps 0 eta alpha)
        (nestedParameter 0 0 0 alpha0) < radius → 0 < eta → alpha ∈ Icc (0 : ℝ) 1 →
      nestedAreaAlongRoot branch eps eta alpha 0 = 0) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ radius ∧
      ∀ eps t eta alpha, dist (nestedParameter eps t eta alpha)
        (nestedParameter 0 0 0 alpha0) < delta →
        0 < t → 0 < eta → alpha ∈ Icc (0 : ℝ) 1 →
        NestedTenAreasPositive tau omega (liftRelative (nestedChartPoints t eta alpha
          (branch (nestedParameter eps t eta alpha)))) := by
  let q0 := nestedParameter 0 0 0 alpha0
  have hambient := nestedExteriorAreas_positive_neighborhood alpha0 tau omega htau hw
  have hbAt : ContinuousAt branch q0 := hsmooth.continuousOn.continuousAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrad))
  have hgraph : ContinuousAt (fun q : NestedChartParameters => (q, branch q)) q0 :=
    continuousAt_id.prodMk hbAt
  rw [← hbase] at hambient
  obtain ⟨dE, hdE, hE⟩ := Metric.eventually_nhds_iff.mp (hgraph.eventually hambient)
  have hwabs : |omega| = 1 := by rcases hw with rfl | rfl <;> norm_num
  obtain ⟨dI, hdI, hdIrad, hI⟩ := nestedChart_internal_area_positive_neighborhood_of_zero_face
    alpha0 tau omega radius hwabs hrad branch hbase hsmooth hroots hradii hzero
  refine ⟨min dI dE, lt_min hdI hdE, (min_le_left _ _).trans hdIrad, ?_⟩
  intro eps t eta alpha hq ht heta halpha
  obtain ⟨hfactor, hcoeff⟩ := hI eps t eta alpha
    (lt_of_lt_of_le hq (min_le_left dI dE)) heta halpha
  obtain ⟨he, hm⟩ := hE (lt_of_lt_of_le hq (min_le_right dI dE))
  refine ⟨?_, hm, ?_⟩
  · intro k j hj
    rw [nestedExternalArea_factor, mul_left_comm]
    have hscale : 0 < nestedEdgeScale t eta k := by
      fin_cases k <;> simp [nestedEdgeScale] <;> positivity
    exact mul_pos hscale (he k j hj)
  · rw [hfactor]
    exact mul_pos (mul_pos (pow_pos ht 3) heta) hcoeff

def NestedActualRootTenAreas (tau omega : ℝ) (v : NestedJointVariables) : Prop :=
  nestedChartParameterRows v.1 v.2 = 0 → 0 < v.1 1 → 0 < v.1 2 →
    v.1 3 ∈ Icc (0 : ℝ) 1 →
    NestedTenAreasPositive tau omega (liftRelative (nestedChartPoints
      (v.1 1) (v.1 2) (v.1 3) v.2)) ∧
    StrictConvexInOrder (nestedBoundaryHullOrder tau omega) (liftRelative (nestedChartPoints
      (v.1 1) (v.1 2) (v.1 3) v.2))

theorem nestedActualRootTenAreas_eventually (alpha0 tau omega : ℝ)
    (ha : alpha0 ∈ Icc (0 : ℝ) 1) (htau : tau = 1 ∨ tau = -1)
    (hw : omega = 1 ∨ omega = -1) :
    ∀ᶠ v : NestedJointVariables in
      𝓝 (nestedParameter 0 0 0 alpha0, nestedBasePoint (tau * h) omega),
      NestedActualRootTenAreas tau omega v := by
  have hh : 0 < h := by unfold h; positivity
  have hangle : |tau * h| = h := by rcases htau with rfl | rfl <;> simp [abs_of_pos hh]
  have hwabs : |omega| = 1 := by rcases hw with rfl | rfl <;> norm_num
  obtain ⟨d, r, C, hd, hr, _, _, _, hbranches⟩ :=
    nestedChart_compact_boundary_continuation (tau * h) omega hangle hwabs 1 (by norm_num)
  obtain ⟨branch, hbase, hsmooth, hdata⟩ := hbranches alpha0 ha
  obtain ⟨dZ, hdZ, hdZd, hzero⟩ := nestedChart_zero_face_area_zero_of_local_uniqueness
    alpha0 tau omega htau d r hd hr branch hbase hsmooth
    (fun q hq => (hdata q hq).2.1)
    (fun q hq => (hdata q hq).2.2.2.2.1)
    (fun q hq => (hdata q hq).2.2.2.2.2)
  obtain ⟨delta, hdelta, hdeltaZ, hareas⟩ :=
    nestedChart_ten_areas_positive_neighborhood_of_zero_face
      alpha0 tau omega dZ htau hw hdZ branch hbase
      (hsmooth.mono (Metric.ball_subset_ball hdZd))
      (fun q hq => (hdata q (lt_of_lt_of_le hq hdZd)).2.2.2.2.1)
      (fun q hq => (hdata q (lt_of_lt_of_le hq hdZd)).2.1.2.1) hzero
  have hqd : ∀ᶠ v : NestedJointVariables in
      𝓝 (nestedParameter 0 0 0 alpha0, nestedBasePoint (tau * h) omega),
      dist v.1 (nestedParameter 0 0 0 alpha0) < delta := by
    have hc : ContinuousAt (fun v : NestedJointVariables => v.1)
        (nestedParameter 0 0 0 alpha0, nestedBasePoint (tau * h) omega) := continuousAt_fst
    exact hc.eventually (show ∀ᶠ q in 𝓝 (nestedParameter 0 0 0 alpha0),
      dist q (nestedParameter 0 0 0 alpha0) < delta from Metric.ball_mem_nhds _ hdelta)
  have hyr : ∀ᶠ v : NestedJointVariables in
      𝓝 (nestedParameter 0 0 0 alpha0, nestedBasePoint (tau * h) omega),
      dist v.2 (nestedBasePoint (tau * h) omega) < r := by
    have hc : ContinuousAt (fun v : NestedJointVariables => v.2)
        (nestedParameter 0 0 0 alpha0, nestedBasePoint (tau * h) omega) := continuousAt_snd
    exact hc.eventually (show ∀ᶠ y in 𝓝 (nestedBasePoint (tau * h) omega),
      dist y (nestedBasePoint (tau * h) omega) < r from Metric.ball_mem_nhds _ hr)
  filter_upwards [hqd, hyr] with v hq hy
  intro hroot ht heta halpha
  have hqin : dist v.1 (nestedParameter 0 0 0 alpha0) < d :=
    lt_of_lt_of_le hq (hdeltaZ.trans hdZd)
  have heq : branch v.1 = v.2 := (hdata v.1 hqin).2.2.2.2.2 v.2 hy |>.mp hroot
  have hp : nestedParameter (v.1 0) (v.1 1) (v.1 2) (v.1 3) = v.1 := by
    ext i
    fin_cases i <;> rfl
  have hten : NestedTenAreasPositive tau omega (liftRelative
      (nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2)) := by
    have ha' := hareas (v.1 0) (v.1 1) (v.1 2) (v.1 3)
      (by simpa only [hp] using hq) ht heta halpha
    simpa only [hp, heq] using ha'
  exact ⟨hten, nestedStrictConvex_of_positive_areas tau omega htau hw _
    hten.1 hten.2.1 hten.2.2⟩

/-- One radius precedes the universal quantifier over alpha in [0,1].
It is a product in the four independent parameters and the seven actual
root variables. No alpha limit or positive lower mass bound is assumed. -/
theorem nestedChart_all_ten_areas_uniform_product (tau omega : ℝ)
    (htau : tau = 1 ∨ tau = -1) (hw : omega = 1 ∨ omega = -1) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ alpha0 ∈ Icc (0 : ℝ) 1,
      ∀ q : NestedChartParameters, ∀ y : NestedChartVariables,
        dist q (nestedParameter 0 0 0 alpha0) < delta →
        dist y (nestedBasePoint (tau * h) omega) < delta →
        nestedChartParameterRows q y = 0 → 0 < q 1 → 0 < q 2 → q 3 ∈ Icc (0 : ℝ) 1 →
        NestedTenAreasPositive tau omega (liftRelative (nestedChartPoints (q 1) (q 2) (q 3) y)) ∧
        StrictConvexInOrder (nestedBoundaryHullOrder tau omega)
          (liftRelative (nestedChartPoints (q 1) (q 2) (q 3) y)) := by
  let K : Set NestedJointVariables := (fun a : ℝ =>
    (nestedParameter 0 0 0 a, nestedBasePoint (tau * h) omega)) '' Icc 0 1
  let U : Set NestedJointVariables := {v | NestedActualRootTenAreas tau omega v}
  have hK : IsCompact K := isCompact_Icc.image (by unfold nestedParameter; fun_prop)
  have hU : ∀ a ∈ K, U ∈ 𝓝 a := by
    rintro a ⟨alpha, halpha, rfl⟩
    exact nestedActualRootTenAreas_eventually alpha tau omega halpha htau hw
  obtain ⟨delta, hd, hcommon⟩ := compact_uniform_neighborhood K U hK hU
  refine ⟨delta, hd, ?_⟩
  intro alpha halpha q y hq hy
  exact hcommon _ ⟨alpha, halpha, rfl⟩ (q, y)
    (by simpa only [Prod.dist_eq] using max_lt hq hy)

end DominantFiveBody
