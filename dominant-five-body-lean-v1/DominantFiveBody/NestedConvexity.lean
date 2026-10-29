import DominantFiveBody.NestedAreaPositivity
import DominantFiveBody.NestedInternalAreaPositivity

/-! # All four nested convex orders from the ten actual triangle signs -/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

def nestedClusterPermutation (omega : ℝ) : Equiv.Perm Label :=
  if 0<omega then Equiv.refl Label else pairMiddleOrder.labels

@[simp] theorem nestedClusterPermutation_one : nestedClusterPermutation 1=Equiv.refl Label := by
  unfold nestedClusterPermutation
  rw [if_pos (by norm_num)]

@[simp] theorem nestedClusterPermutation_neg_one : nestedClusterPermutation (-1)=pairMiddleOrder.labels := by
  unfold nestedClusterPermutation
  rw [if_neg (by norm_num)]

theorem nestedIncreasingPair_fin_three (i j : TripleLabel) (hij : i<j) :
    (i=0 ∧ j=1) ∨ (i=0 ∧ j=2) ∨ (i=1 ∧ j=2) := by
  revert i j
  decide

theorem nestedArea_swap_first_two (x : Configuration) (i j k : Label) :
    orientedArea x i j k= -orientedArea x j i k := by
  simp [orientedArea,det2]
  ring

theorem nestedClusterPermutation_primary (omega : ℝ) : nestedClusterPermutation omega 0=0 := by
  unfold nestedClusterPermutation
  split_ifs <;> rfl

def nestedBoundaryHullOrder (tau omega : ℝ) : HullOrder where
  labels := (tripleBoundaryHullOrder tau).labels.trans (nestedClusterPermutation omega)
  primary_first := by
    rw [Equiv.trans_apply,(tripleBoundaryHullOrder tau).primary_first]
    exact nestedClusterPermutation_primary omega

theorem nestedStrictConvex_of_positive_areas (tau omega : ℝ)
    (htau : tau=1 ∨ tau=-1) (hw : omega=1 ∨ omega=-1) (x : Configuration)
    (he : ∀ k : NestedEdge,∀ j∈({0,4} : Finset Label),
      0<nestedEdgeOrientation omega k*orientedArea x
        (nestedEdgeSource k).succ (nestedEdgeTarget k).succ j)
    (hm : ∀ i : TripleLabel,0<tripleMacroArea tau x i)
    (hint : 0<orientedArea x 1 2 3) :
    StrictConvexInOrder (nestedBoundaryHullOrder tau omega) x := by
  have he' : ∀ i j : TripleLabel,i<j → ∀ k∈({0,4} : Finset Label),
      0<orientedArea (x ∘ nestedClusterPermutation omega) i.castSucc.succ j.castSucc.succ k := by
    intro i j hij k hk
    have he0 := he 0 k hk
    have he1 := he 1 k hk
    have he2 := he 2 k hk
    have hke : nestedClusterPermutation omega k=k := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact nestedClusterPermutation_primary omega
      · unfold nestedClusterPermutation
        split_ifs <;> rfl
    change 0<orientedArea x (nestedClusterPermutation omega i.castSucc.succ)
      (nestedClusterPermutation omega j.castSucc.succ) (nestedClusterPermutation omega k)
    rw [hke]
    have hp := nestedIncreasingPair_fin_three i j hij
    rcases hw with rfl | rfl
    · rcases hp with hp | hp | hp
      all_goals rcases hp with ⟨rfl,rfl⟩
      all_goals simp only [nestedClusterPermutation_one,Equiv.refl_apply]
      all_goals first
        | simpa [nestedEdgeOrientation,nestedEdgeSource,nestedEdgeTarget] using he0
        | simpa [nestedEdgeOrientation,nestedEdgeSource,nestedEdgeTarget] using he1
        | simpa [nestedEdgeOrientation,nestedEdgeSource,nestedEdgeTarget] using he2
    · rcases hp with hp | hp | hp
      all_goals rcases hp with ⟨rfl,rfl⟩
      all_goals simp only [nestedClusterPermutation_neg_one]
      all_goals dsimp [pairMiddleOrder]
      all_goals first
        | simpa [nestedEdgeOrientation,nestedEdgeSource,nestedEdgeTarget] using he2
        | rw [nestedArea_swap_first_two]; simpa [nestedEdgeOrientation,nestedEdgeSource,nestedEdgeTarget] using he0
        | rw [nestedArea_swap_first_two]; simpa [nestedEdgeOrientation,nestedEdgeSource,nestedEdgeTarget] using he1
  have hm' : ∀ i : TripleLabel,0<tripleMacroArea tau (x ∘ nestedClusterPermutation omega) i := by
    intro i
    rcases hw with rfl | rfl
    · simpa only [nestedClusterPermutation_one,Equiv.coe_refl,Function.comp_id] using hm i
    · simp only [nestedClusterPermutation_neg_one]
      fin_cases i
      all_goals first
        | simpa [tripleMacroArea,pairMiddleOrder,orientedArea,Function.comp_apply] using hm 0
        | simpa [tripleMacroArea,pairMiddleOrder,orientedArea,Function.comp_apply] using hm 1
        | simpa [tripleMacroArea,pairMiddleOrder,orientedArea,Function.comp_apply] using hm 2
  have hi' : 0<orientedArea (x ∘ nestedClusterPermutation omega) 1 2 3 := by
    rcases hw with rfl | rfl
    · simpa only [nestedClusterPermutation_one,Equiv.coe_refl,Function.comp_id] using hint
    · change 0<orientedArea x (nestedClusterPermutation (-1) 1)
        (nestedClusterPermutation (-1) 2) (nestedClusterPermutation (-1) 3)
      simp only [nestedClusterPermutation_neg_one]
      change 0<orientedArea x 3 1 2
      rwa [orientedArea_cyclic]
  have hconv := tripleStrictConvex_of_positive_areas tau htau
    (x ∘ nestedClusterPermutation omega) he' hm' hi'
  simpa only [StrictConvexInOrder,nestedBoundaryHullOrder,Equiv.trans_apply,
    orientedArea,Function.comp_apply] using hconv

theorem nestedChart_strictConvex_neighborhood_of_zero_face
    (alpha0 tau omega radius : ℝ) (htau : tau=1 ∨ tau=-1) (hw : omega=1 ∨ omega=-1)
    (hrad : 0<radius) (branch : NestedChartParameters → NestedChartVariables)
    (hbase : branch (nestedParameter 0 0 0 alpha0)=nestedBasePoint (tau*h) omega)
    (hsmooth : ContDiffOn ℝ ∞ branch (Metric.ball (nestedParameter 0 0 0 alpha0) radius))
    (hroots : ∀ q,dist q (nestedParameter 0 0 0 alpha0)<radius →
      nestedChartParameterRows q (branch q)=0)
    (hradii : ∀ q,dist q (nestedParameter 0 0 0 alpha0)<radius →
      ∀ i,0<nestedChartRadii (q 1) (q 2) (q 3) (branch q) i)
    (hzero : ∀ eps eta alpha,dist (nestedParameter eps 0 eta alpha)
        (nestedParameter 0 0 0 alpha0)<radius → 0<eta → alpha∈Icc (0 : ℝ) 1 →
      nestedAreaAlongRoot branch eps eta alpha 0=0) :
    ∃ delta : ℝ,0<delta ∧ delta≤radius ∧
      ∀ eps t eta alpha,dist (nestedParameter eps t eta alpha)
        (nestedParameter 0 0 0 alpha0)<delta → 0<t → 0<eta → alpha∈Icc (0 : ℝ) 1 →
        StrictConvexInOrder (nestedBoundaryHullOrder tau omega)
          (liftRelative (nestedChartPoints t eta alpha (branch (nestedParameter eps t eta alpha)))) := by
  let q0 := nestedParameter 0 0 0 alpha0
  have hambient := nestedExteriorAreas_positive_neighborhood alpha0 tau omega htau hw
  have hbAt : ContinuousAt branch q0 :=
    hsmooth.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrad))
  have hgraph : ContinuousAt (fun q : NestedChartParameters => (q,branch q)) q0 :=
    continuousAt_id.prodMk hbAt
  rw [← hbase] at hambient
  have hext := hgraph.eventually hambient
  obtain ⟨dE,hdE,hE⟩ := Metric.eventually_nhds_iff.mp hext
  have hwabs : |omega|=1 := by rcases hw with rfl | rfl <;> norm_num
  obtain ⟨dI,hdI,hdIrad,hI⟩ := nestedChart_internal_area_positive_neighborhood_of_zero_face
    alpha0 tau omega radius hwabs hrad branch hbase hsmooth hroots hradii hzero
  refine ⟨min dI dE,lt_min hdI hdE,(min_le_left _ _).trans hdIrad,?_⟩
  intro eps t eta alpha hq ht heta halpha
  have hqi := lt_of_lt_of_le hq (min_le_left dI dE)
  have hqe := lt_of_lt_of_le hq (min_le_right dI dE)
  obtain ⟨hfactor,hcoeff⟩ := hI eps t eta alpha hqi heta halpha
  have harea : 0<orientedArea (liftRelative (nestedChartPoints t eta alpha
      (branch (nestedParameter eps t eta alpha)))) 1 2 3 := by
    rw [hfactor]
    exact mul_pos (mul_pos (pow_pos ht 3) heta) hcoeff
  obtain ⟨he,hm⟩ := hE hqe
  apply nestedStrictConvex_of_positive_areas tau omega htau hw _ _ _ harea
  · intro k j hj
    rw [nestedExternalArea_factor,mul_left_comm]
    have hscale : 0<nestedEdgeScale t eta k := by
      fin_cases k <;> simp [nestedEdgeScale] <;> positivity
    apply mul_pos hscale
    exact he k j hj
  · intro i
    exact hm i

end DominantFiveBody
