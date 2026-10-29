import DominantFiveBody.CollisionExteriorDerivativeBounds
import DominantFiveBody.CollisionNestedRectangleControls

/-! Actual exterior derivatives are O(current exterior mass), on a joint
source/target neighborhood. There is no lower bound on any mass fraction. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1200000

abbrev PairExteriorBoundsData := ((Satellite → ℝ) × (Satellite → ℝ)) × (ℝ × ℝ)

def pairSourceDerivativeSize (z : PairExteriorBoundsData) (j : Satellite) : ℝ :=
  4/‖polarPoint (z.1.1 j) (z.1.2 j)-polarPoint z.2.1 z.2.2‖^3+
    |physicalSourceAngularRadialDerivative (z.1.1 j) (z.1.2 j) z.2.1 z.2.2|+
    |physicalSourceAngularAngularDerivative (z.1.1 j) (z.1.2 j) z.2.1 z.2.2|

theorem pairSourceDerivativeSize_nonneg (z : PairExteriorBoundsData) (j : Satellite) :
    0≤pairSourceDerivativeSize z j := by unfold pairSourceDerivativeSize; positivity

theorem pairSourceDerivativeSize_continuousAt (z : PairExteriorBoundsData) (j : Satellite)
    (hr : z.1.1 j≠0)
    (hsep : polarPoint (z.1.1 j) (z.1.2 j)≠polarPoint z.2.1 z.2.2) :
    ContinuousAt (fun w => pairSourceDerivativeSize w j) z := by
  have hp : ContinuousAt (fun w : PairExteriorBoundsData =>
      ((w.1.1 j,w.1.2 j),w.2)) z := by fun_prop
  have hR := (physicalSourceAngularRadialDerivative_joint_contDiffAt
    ((z.1.1 j,z.1.2 j),z.2) hsep).continuousAt.comp
      (f := fun w : PairExteriorBoundsData => ((w.1.1 j,w.1.2 j),w.2)) hp
  have hV := (physicalSourceAngularAngularDerivative_joint_contDiffAt
    ((z.1.1 j,z.1.2 j),z.2) hr hsep).continuousAt.comp
      (f := fun w : PairExteriorBoundsData => ((w.1.1 j,w.1.2 j),w.2)) hp
  have hdist : ContinuousAt (fun w : PairExteriorBoundsData =>
      ‖polarPoint (w.1.1 j) (w.1.2 j)-polarPoint w.2.1 w.2.2‖) z := by
    apply ContinuousAt.norm
    exact ((polarPoint_contDiff ∞).continuous.continuousAt.comp
      (f := fun w : PairExteriorBoundsData => (w.1.1 j,w.1.2 j)) (by fun_prop)).sub
      ((polarPoint_contDiff ∞).continuous.continuousAt.comp
        (f := fun w : PairExteriorBoundsData => w.2) (by fun_prop))
  exact ((continuousAt_const.div (hdist.pow 3)
    (pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsep)))).add hR.abs).add hV.abs

def pairExteriorDerivativeSize (a b : Satellite) (z : PairExteriorBoundsData) : ℝ :=
  1+∑ j∈pairExteriorLabels a b,pairSourceDerivativeSize z j

theorem pairSourceDerivativeSize_le_total (a b : Satellite) (z : PairExteriorBoundsData)
    (j : Satellite) (hj : j∈pairExteriorLabels a b) :
    pairSourceDerivativeSize z j≤pairExteriorDerivativeSize a b z := by
  have h := Finset.single_le_sum (fun i _ => pairSourceDerivativeSize_nonneg z i) hj
  unfold pairExteriorDerivativeSize
  linarith

theorem pairExterior_joint_neighborhood_derivative_bounds
    (a b : Satellite) (z0 : PairExteriorBoundsData)
    (hr : ∀ j,0<z0.1.1 j)
    (hsep : ∀ j∈pairExteriorLabels a b,
      polarPoint (z0.1.1 j) (z0.1.2 j)≠polarPoint z0.2.1 z0.2.2) :
    ∃ C : ℝ,0<C ∧ ∃ U∈nhds z0,∀ z∈U,∀ mu : MassRatio,(∀ j,0≤mu j) →
      ‖fderiv ℝ (pairExteriorField mu (polarSatellites z.1.1 z.1.2) a b)
        (polarPoint z.2.1 z.2.2)‖≤C*(∑ j∈pairExteriorLabels a b,mu j) ∧
      |deriv (fun rho => physicalPairExteriorAngularField mu z.1.1 z.1.2 a b rho z.2.2) z.2.1|
        ≤C*(∑ j∈pairExteriorLabels a b,mu j) ∧
      |deriv (fun v => physicalPairExteriorAngularField mu z.1.1 z.1.2 a b z.2.1 v) z.2.2|
        ≤C*(∑ j∈pairExteriorLabels a b,mu j) := by
  let C := pairExteriorDerivativeSize a b z0+1
  have hC : 0<C := by
    have hsum := Finset.sum_nonneg (fun j (_ : j∈pairExteriorLabels a b) =>
      pairSourceDerivativeSize_nonneg z0 j)
    dsimp [C,pairExteriorDerivativeSize]
    linarith
  have hG : ContinuousAt (pairExteriorDerivativeSize a b) z0 := by
    apply ContinuousAt.add continuousAt_const
    exact tendsto_finsetSum _ (fun j hj =>
      pairSourceDerivativeSize_continuousAt z0 j (hr j).ne' (hsep j hj))
  have hbound : ∀ᶠ z in nhds z0,pairExteriorDerivativeSize a b z<C :=
    hG.eventually (gt_mem_nhds (by dsimp [C]; linarith))
  have hrad : ∀ᶠ z : PairExteriorBoundsData in nhds z0,∀ j,0<z.1.1 j := by
    apply Filter.eventually_all.mpr
    intro j
    exact (by fun_prop : ContinuousAt (fun z : PairExteriorBoundsData => z.1.1 j) z0).eventually
      (lt_mem_nhds (hr j))
  have hdist : ∀ᶠ z : PairExteriorBoundsData in nhds z0,∀ j∈pairExteriorLabels a b,
      polarPoint (z.1.1 j) (z.1.2 j)≠polarPoint z.2.1 z.2.2 := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j∈pairExteriorLabels a b
    · have hc : ContinuousAt (fun z : PairExteriorBoundsData =>
          polarPoint (z.1.1 j) (z.1.2 j)-polarPoint z.2.1 z.2.2) z0 :=
        ((polarPoint_contDiff ∞).continuous.continuousAt.comp
          (f := fun z : PairExteriorBoundsData => (z.1.1 j,z.1.2 j)) (by fun_prop)).sub
          ((polarPoint_contDiff ∞).continuous.continuousAt.comp
            (f := fun z : PairExteriorBoundsData => z.2) (by fun_prop))
      have hn := hc.eventually (isClosed_singleton.isOpen_compl.mem_nhds
        (sub_ne_zero.mpr (hsep j hj)))
      filter_upwards [hn] with z hz
      exact fun _ => sub_ne_zero.mp hz
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hj h))
  let U : Set PairExteriorBoundsData := {z | pairExteriorDerivativeSize a b z<C ∧
    (∀ j,0<z.1.1 j) ∧ ∀ j∈pairExteriorLabels a b,
      polarPoint (z.1.1 j) (z.1.2 j)≠polarPoint z.2.1 z.2.2}
  refine ⟨C,hC,U,hbound.and (hrad.and hdist),?_⟩
  intro z hz mu hm
  have hsmall (j : Satellite) (hj : j∈pairExteriorLabels a b) :
      pairSourceDerivativeSize z j≤C := (pairSourceDerivativeSize_le_total a b z j hj).trans hz.1.le
  have hP (j : Satellite) (hj : j∈pairExteriorLabels a b) :
      4/‖polarPoint (z.1.1 j) (z.1.2 j)-polarPoint z.2.1 z.2.2‖^3≤C := by
    have h := hsmall j hj
    unfold pairSourceDerivativeSize at h
    linarith [abs_nonneg (physicalSourceAngularRadialDerivative (z.1.1 j) (z.1.2 j) z.2.1 z.2.2),
      abs_nonneg (physicalSourceAngularAngularDerivative (z.1.1 j) (z.1.2 j) z.2.1 z.2.2)]
  have hRV (j : Satellite) (hj : j∈pairExteriorLabels a b) :
      |physicalSourceAngularRadialDerivative (z.1.1 j) (z.1.2 j) z.2.1 z.2.2|≤C ∧
      |physicalSourceAngularAngularDerivative (z.1.1 j) (z.1.2 j) z.2.1 z.2.2|≤C := by
    have h := hsmall j hj
    have hnon : 0≤4/‖polarPoint (z.1.1 j) (z.1.2 j)-polarPoint z.2.1 z.2.2‖^3 := by positivity
    unfold pairSourceDerivativeSize at h
    constructor <;> linarith [abs_nonneg (physicalSourceAngularRadialDerivative (z.1.1 j) (z.1.2 j) z.2.1 z.2.2),
      abs_nonneg (physicalSourceAngularAngularDerivative (z.1.1 j) (z.1.2 j) z.2.1 z.2.2)]
  have hweighted (f : Satellite → ℝ) (hf : ∀ j∈pairExteriorLabels a b,|f j|≤C) :
      |∑ j∈pairExteriorLabels a b,mu j*f j|≤C*(∑ j∈pairExteriorLabels a b,mu j) := by
    calc
      _≤∑ j∈pairExteriorLabels a b,|mu j*f j| := Finset.abs_sum_le_sum_abs _ _
      _≤∑ j∈pairExteriorLabels a b,mu j*C := Finset.sum_le_sum (fun j hj => by
        rw [abs_mul,abs_of_nonneg (hm j)]
        exact mul_le_mul_of_nonneg_left (hf j hj) (hm j))
      _=_ := by rw [← Finset.sum_mul]; ring
  refine ⟨?_,?_,?_⟩
  · apply (pairExteriorField_fderiv_norm_bound mu (polarSatellites z.1.1 z.1.2) a b
      (polarPoint z.2.1 z.2.2) (fun j _ => hm j) hz.2.2).trans
    calc
      _≤∑ j∈pairExteriorLabels a b,mu j*C := Finset.sum_le_sum
        (fun j hj => mul_le_mul_of_nonneg_left (hP j hj) (hm j))
      _=_ := by rw [← Finset.sum_mul]; ring
  · rw [(physicalPairExteriorAngularField_named_derivatives mu z.1.1 z.1.2 a b
      z.2.1 z.2.2 hz.2.1 hz.2.2).1.deriv]
    exact hweighted _ (fun j hj => (hRV j hj).1)
  · rw [(physicalPairExteriorAngularField_named_derivatives mu z.1.1 z.1.2 a b
      z.2.1 z.2.2 hz.2.1 hz.2.2).2.deriv]
    exact hweighted _ (fun j hj => (hRV j hj).2)

theorem pairExterior_moving_neighborhood_derivative_bounds
    (a b : Satellite) (r theta : ℕ → Satellite → ℝ) (r0 theta0 : Satellite → ℝ)
    (hrt : Tendsto r atTop (nhds r0)) (htt : Tendsto theta atTop (nhds theta0))
    (rho0 v0 : ℝ) (hr : ∀ j,0<r0 j)
    (hsep : ∀ j∈pairExteriorLabels a b,polarPoint (r0 j) (theta0 j)≠polarPoint rho0 v0) :
    ∃ C : ℝ,0<C ∧ ∃ U∈nhds (rho0,v0),∀ᶠ n in atTop,∀ q∈U,
      ∀ mu : MassRatio,(∀ j,0≤mu j) →
      ‖fderiv ℝ (pairExteriorField mu (polarSatellites (r n) (theta n)) a b)
        (polarPoint q.1 q.2)‖≤C*(∑ j∈pairExteriorLabels a b,mu j) ∧
      |deriv (fun rho => physicalPairExteriorAngularField mu (r n) (theta n) a b rho q.2) q.1|
        ≤C*(∑ j∈pairExteriorLabels a b,mu j) ∧
      |deriv (fun v => physicalPairExteriorAngularField mu (r n) (theta n) a b q.1 v) q.2|
        ≤C*(∑ j∈pairExteriorLabels a b,mu j) := by
  obtain ⟨C,hC,W,hW,hbound⟩ := pairExterior_joint_neighborhood_derivative_bounds
    a b ((r0,theta0),(rho0,v0)) hr hsep
  obtain ⟨V,hV,U,hU,hsub⟩ := mem_nhds_prod_iff.mp hW
  refine ⟨C,hC,U,hU,?_⟩
  have hs := (hrt.prodMk_nhds htt).eventually hV
  filter_upwards [hs] with n hn
  intro q hq mu hm
  exact hbound ((r n,theta n),q) (hsub ⟨hn,hq⟩) mu hm

end DominantFiveBody
