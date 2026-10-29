import DominantFiveBody.PhysicalHullRelabeling
import DominantFiveBody.NoCollisionContinuation
import DominantFiveBody.TripleAreas

/-! # Exact coorbital endpoint in any original-label angle gauge

The hull order determines the sorting permutation. It only reindexes
the equations; the returned endpoint retains the original labels.
-/

noncomputable section
open scoped BigOperators
namespace DominantFiveBody
open Coorbital

theorem unitStrictConvex_orderedSemicircle (sigma : HullOrder) (theta : Satellite → ℝ)
    (hwidth : ∀ i j,|theta j-theta i|<Real.pi)
    (hconv : StrictConvexInOrder sigma (liftRelative (polarSatellites (fun _ => 1) theta))) :
    OrderedSemicircle (theta ∘ hullSatellitePermutation sigma) := by
  let e := hullSatellitePermutation sigma
  have hadj (i : Fin 3) : theta (e i.castSucc)<theta (e i.succ) := by
    let k : Label := i.castSucc.succ
    have hk0 : (0 : Label)≠k := by fin_cases i <;> decide
    have hk1 : (0 : Label)≠k+1 := by fin_cases i <;> decide
    have harea := hconv k 0 hk0 hk1
    have hkplus : k+1=i.succ.succ := by fin_cases i <;> rfl
    rw [hkplus,orientedArea_cyclic,orientedArea_cyclic,sigma.primary_first,
      hullOrder_label_succ sigma i.castSucc,hullOrder_label_succ sigma i.succ] at harea
    change 0<det2 (polarPoint 1 (theta (e i.castSucc))-0)
      (polarPoint 1 (theta (e i.succ))-0) at harea
    rw [sub_zero,sub_zero,unit_polar_det] at harea
    apply sub_pos.mp
    by_contra hn
    have hsle := Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt hn)
      (abs_lt.mp (hwidth (e i.castSucc) (e i.succ))).1.le
    exact (not_lt_of_ge hsle) harea
  have hmono : StrictMono (theta ∘ e) := Fin.strictMono_iff_lt_succ.mpr hadj
  intro i j hij
  exact ⟨sub_pos.mpr (hmono hij),lt_of_le_of_lt (le_abs_self _) (hwidth (e i) (e j))⟩

def fixedLabelCoorbitalEndpointAngles (mu : MassRatio) (sigma : HullOrder) (p : Satellite) : Satellite → ℝ :=
  let e := hullSatellitePermutation sigma
  fun i => coorbitalRootAngles (mu ∘ e) (e.symm i)-coorbitalRootAngles (mu ∘ e) (e.symm p)

def fixedLabelCoorbitalEndpoint (mu : MassRatio) (sigma : HullOrder) (p : Satellite) : Configuration :=
  liftRelative (polarSatellites (fun _ => 1) (fixedLabelCoorbitalEndpointAngles mu sigma p))

theorem actualCoorbitalAngles_eq_fixedLabelEndpoint (mu : MassRatio) (sigma : HullOrder)
    (p : Satellite) (theta : Satellite → ℝ) (hm : PositiveRatio mu) (hfixed : theta p=0)
    (hwidth : ∀ i j,|theta j-theta i|<Real.pi)
    (hconv : StrictConvexInOrder sigma (liftRelative (polarSatellites (fun _ => 1) theta)))
    (hroot : ∀ i,coorbitalResidual mu theta i=0) :
    theta=fixedLabelCoorbitalEndpointAngles mu sigma p := by
  let e := hullSatellitePermutation sigma
  have hsorted := unitStrictConvex_orderedSemicircle sigma theta hwidth hconv
  have heq := coorbitalRootAngles_eq_sorted_shift mu theta hm e hsorted hroot
  funext i
  have hi := congrFun heq (e.symm i)
  have hp := congrFun heq (e.symm p)
  simp only [Equiv.apply_symm_apply,hfixed] at hi hp
  change theta i=coorbitalRootAngles (mu ∘ e) (e.symm i)-coorbitalRootAngles (mu ∘ e) (e.symm p)
  linarith

end DominantFiveBody
