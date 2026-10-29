import DominantFiveBody.CollisionGeometry
import DominantFiveBody.ConvexContinuation

/-! The open-semicircle characterization stated before Lemma 2.1.
Both implications refer to all five vertices, with their original labels. -/
noncomputable section
namespace DominantFiveBody

theorem unit_satellites_strictConvex_iff_open_semicircle (x : Configuration)
    (hx : CollisionFree x) (hu : ∀ i : Satellite,‖x i.succ-x 0‖=1) :
    StrictConvexInOrder standardHullOrder x ↔
      ∃ theta : Satellite → ℝ, OrderedSemicircle theta ∧
        ∀ i : Satellite,x i.succ-x 0=polarPoint 1 (theta i) := by
  constructor
  · intro hc
    obtain ⟨r,theta,phi,hr,_,ha,hrep⟩ :=
      strictConvexInOrder_exists_ordered_polar standardHullOrder x hc hx
    have hr1 (i : Satellite) : r i=1 := by
      have hh := congrArg norm (hrep i)
      simpa only [standardHullOrder,Equiv.refl_apply,hu i,polarPoint_norm,
        abs_of_pos (hr i)] using hh.symm
    refine ⟨fun i => theta i+phi,?_,?_⟩
    · intro i j hij
      simpa only [add_sub_add_right_eq_sub] using ha i j hij
    · intro i
      simpa only [standardHullOrder,Equiv.refl_apply,hr1 i] using hrep i
  · rintro ⟨theta,ha,hrep⟩
    have hc := unit_polar_strictConvex theta ha
    have heq : x=fun i => liftRelative (polarSatellites (fun _ => 1) theta) i+x 0 := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [liftRelative]
      · simpa only [liftRelative,Fin.cases_succ,polarSatellites] using
          (sub_eq_iff_eq_add.mp (hrep j))
    rw [heq]
    intro k j hj hj'
    simpa only [orientedArea,add_sub_add_right_eq_sub] using hc k j hj hj'

end DominantFiveBody
