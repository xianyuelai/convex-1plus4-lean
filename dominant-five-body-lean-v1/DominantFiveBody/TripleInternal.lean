import DominantFiveBody.TripleChart
import DominantFiveBody.TripleDirections

/-! # Actual regular-triple internal interactions

These are source `regular-int` with all three divided probe rows.
The signed extension is smooth at t=0 wherever the rescaled distances
are positive, and equality with the physical interactions is proved at t>0.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
set_option maxHeartbeats 800000

def tripleChartWSq (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) : ℝ :=
  singleScaleWSq (y 1) t (tripleChartRadialPositions alpha y i)
    (tripleChartRadialPositions alpha y j) (tripleChartAngularPositions alpha y i)
    (tripleChartAngularPositions alpha y j)

def tripleChartW (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) : ℝ := Real.sqrt (tripleChartWSq t alpha y i j)

theorem tripleChartRadii_cluster (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) : tripleChartRadii t alpha y i.castSucc =
      singleScaleRadius (y 1) t (tripleChartRadialPositions alpha y i) := by
  fin_cases i <;> rfl

theorem tripleChartAngles_cluster (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) : tripleChartAngles t alpha y i.castSucc =
      singleScaleAngle (y 4) t (tripleChartAngularPositions alpha y i) := by
  fin_cases i <;> rfl

theorem tripleChart_cluster_distance (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) (ht : 0 < t) (hW : 0 < tripleChartWSq t alpha y i j) :
    satelliteDistance (tripleChartPoints t alpha y) i.castSucc j.castSucc =
      t * tripleChartW t alpha y i j := by
  unfold satelliteDistance tripleChartPoints polarSatellites
  rw [tripleChartRadii_cluster, tripleChartRadii_cluster,
    tripleChartAngles_cluster, tripleChartAngles_cluster]
  exact singleScale_distance (y 1) (y 4) t _ _ _ _ ht hW

def tripleInternalRadialReduced (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) : ℝ :=
  -eps * ∑ j ∈ Finset.univ.erase i, alpha j *
    (tripleChartRadialPositions alpha y i - tripleChartRadialPositions alpha y j +
      tripleChartRadii t alpha y j.castSucc * singleScaleChi t
        (tripleChartAngularPositions alpha y i - tripleChartAngularPositions alpha y j)) *
    (tripleChartW t alpha y i j ^ 3)⁻¹

def tripleInternalAngularReduced (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) : ℝ :=
  -∑ j ∈ Finset.univ.erase i, alpha j * tripleChartRadii t alpha y i.castSucc *
    tripleChartRadii t alpha y j.castSucc *
    (tripleChartAngularPositions alpha y i - tripleChartAngularPositions alpha y j) *
    Real.sinc (t * (tripleChartAngularPositions alpha y i - tripleChartAngularPositions alpha y j)) *
    ((tripleChartW t alpha y i j ^ 3)⁻¹ - t ^ 3 / (1 + eps))

def tripleInternalRadial (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) : ℝ := t * tripleInternalRadialReduced eps t alpha y i

def tripleInternalAngular (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) : ℝ := t * tripleInternalAngularReduced eps t alpha y i

theorem tripleInternalRadial_eq_physical (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel) (ht : 0 < t)
    (hW : ∀ j, j ≠ i → 0 < tripleChartWSq t alpha y i j) :
    tripleInternalRadial eps t alpha y i =
      ∑ j ∈ Finset.univ.erase i,
        -eps * tripleChartMass t alpha j.castSucc *
          (tripleChartRadii t alpha y i.castSucc - tripleChartRadii t alpha y j.castSucc *
            Real.cos (tripleChartAngles t alpha y i.castSucc - tripleChartAngles t alpha y j.castSucc)) /
          satelliteDistance (tripleChartPoints t alpha y) i.castSucc j.castSucc ^ 3 := by
  unfold tripleInternalRadial tripleInternalRadialReduced
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  let p : SingleScaleVariables := ![y 1, t, tripleChartRadialPositions alpha y i,
    tripleChartRadialPositions alpha y j, tripleChartAngularPositions alpha y i,
    tripleChartAngularPositions alpha y j, eps, alpha j]
  have hp := singleScaleRadialTerm_eq_physical p (y 4) ht
    (hW j (Finset.mem_erase.mp hj).1)
  simp [p] at hp
  have hmass : tripleChartMass t alpha j.castSucc = t ^ 3 * alpha j := by fin_cases j <;> rfl
  rw [hmass, tripleChartRadii_cluster, tripleChartRadii_cluster,
    tripleChartAngles_cluster, tripleChartAngles_cluster]
  simp only [satelliteDistance, tripleChartPoints, polarSatellites,
    tripleChartRadii_cluster, tripleChartAngles_cluster]
  change _ = -eps * (t ^ 3 * alpha j) *
    (singleScaleRadius (y 1) t (tripleChartRadialPositions alpha y i) -
      singleScaleRadius (y 1) t (tripleChartRadialPositions alpha y j) *
        Real.cos (singleScaleAngle (y 4) t (tripleChartAngularPositions alpha y i) -
          singleScaleAngle (y 4) t (tripleChartAngularPositions alpha y j))) /
      ‖polarPoint (singleScaleRadius (y 1) t (tripleChartRadialPositions alpha y i))
        (singleScaleAngle (y 4) t (tripleChartAngularPositions alpha y i)) -
       polarPoint (singleScaleRadius (y 1) t (tripleChartRadialPositions alpha y j))
        (singleScaleAngle (y 4) t (tripleChartAngularPositions alpha y j))‖ ^ 3
  calc
    _ = singleScaleRadialTerm p := by
      simp [p, singleScaleRadialTerm, tripleChartW, tripleChartWSq, singleScaleW]
      ring
    _ = _ := by simpa [p] using hp

theorem tripleInternalAngular_eq_physical (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel) (ht : 0 < t)
    (hW : ∀ j, j ≠ i → 0 < tripleChartWSq t alpha y i j) (heps : 1 + eps ≠ 0) :
    tripleInternalAngular eps t alpha y i =
      ∑ j ∈ Finset.univ.erase i,
        tripleChartMass t alpha j.castSucc * tripleChartRadii t alpha y i.castSucc *
          tripleChartRadii t alpha y j.castSucc *
          Real.sin (tripleChartAngles t alpha y j.castSucc -
            tripleChartAngles t alpha y i.castSucc) *
          ((satelliteDistance (tripleChartPoints t alpha y) i.castSucc j.castSucc ^ 3)⁻¹ -
            (1 + eps)⁻¹) := by
  unfold tripleInternalAngular tripleInternalAngularReduced
  rw [mul_neg, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  let p : SingleScaleVariables := ![y 1, t, tripleChartRadialPositions alpha y i,
    tripleChartRadialPositions alpha y j, tripleChartAngularPositions alpha y i,
    tripleChartAngularPositions alpha y j, eps, alpha j]
  have hp := singleScaleAngularTerm_eq_physical p (y 4) ht
    (hW j (Finset.mem_erase.mp hj).1) heps
  simp [p] at hp
  have hmass : tripleChartMass t alpha j.castSucc = t ^ 3 * alpha j := by fin_cases j <;> rfl
  rw [hmass]
  simp only [satelliteDistance, tripleChartPoints, polarSatellites,
    tripleChartRadii_cluster, tripleChartAngles_cluster]
  calc
    _ = singleScaleAngularTerm p := by
      simp [p, singleScaleAngularTerm, tripleChartW, tripleChartWSq, singleScaleW]
      ring
    _ = _ := by simpa [p] using hp

@[fun_prop] theorem tripleChartWSq_joint_contDiff (n : ℕ∞ω) (i j : TripleLabel) :
    ContDiff ℝ n (fun v : TripleJointVariables =>
      tripleChartWSq (v.1 1) (tripleJointAlpha v.1) v.2 i j) := by
  unfold tripleChartWSq singleScaleWSq singleScaleRadius
  fun_prop

theorem tripleChartW_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (i j : TripleLabel) (hW : 0 < tripleChartWSq (v.1 1) (tripleJointAlpha v.1) v.2 i j) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleChartW (w.1 1) (tripleJointAlpha w.1) w.2 i j) v :=
  (tripleChartWSq_joint_contDiff n i j).contDiffAt.sqrt (ne_of_gt hW)

theorem tripleInternalRadialReduced_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (i : TripleLabel)
    (hW : ∀ j, j ≠ i → 0 < tripleChartWSq (v.1 1) (tripleJointAlpha v.1) v.2 i j) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleInternalRadialReduced (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2 i) v := by
  unfold tripleInternalRadialReduced
  apply ContDiffAt.mul (by fun_prop)
  apply ContDiffAt.sum
  intro j hj
  have hn : tripleChartW (v.1 1) (tripleJointAlpha v.1) v.2 i j ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (hW j (Finset.mem_erase.mp hj).1))
  have hpre : ContDiff ℝ n (fun w : TripleJointVariables =>
      tripleJointAlpha w.1 j *
        (tripleChartRadialPositions (tripleJointAlpha w.1) w.2 i -
          tripleChartRadialPositions (tripleJointAlpha w.1) w.2 j +
          tripleChartRadii (w.1 1) (tripleJointAlpha w.1) w.2 j.castSucc *
            singleScaleChi (w.1 1) (tripleChartAngularPositions (tripleJointAlpha w.1) w.2 i -
              tripleChartAngularPositions (tripleJointAlpha w.1) w.2 j))) := by
    unfold singleScaleChi
    fun_prop
  exact hpre.contDiffAt.mul
    (((tripleChartW_joint_contDiffAt n v i j (hW j (Finset.mem_erase.mp hj).1)).pow 3).inv
      (pow_ne_zero 3 hn))

theorem tripleInternalAngularReduced_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (i : TripleLabel) (heps : 1 + v.1 0 ≠ 0)
    (hW : ∀ j, j ≠ i → 0 < tripleChartWSq (v.1 1) (tripleJointAlpha v.1) v.2 i j) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleInternalAngularReduced (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2 i) v := by
  unfold tripleInternalAngularReduced
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro j hj
  have hn : tripleChartW (v.1 1) (tripleJointAlpha v.1) v.2 i j ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (hW j (Finset.mem_erase.mp hj).1))
  have hpre : ContDiff ℝ n (fun w : TripleJointVariables =>
      tripleJointAlpha w.1 j * tripleChartRadii (w.1 1) (tripleJointAlpha w.1) w.2 i.castSucc *
        tripleChartRadii (w.1 1) (tripleJointAlpha w.1) w.2 j.castSucc *
        (tripleChartAngularPositions (tripleJointAlpha w.1) w.2 i -
          tripleChartAngularPositions (tripleJointAlpha w.1) w.2 j) *
        Real.sinc (w.1 1 * (tripleChartAngularPositions (tripleJointAlpha w.1) w.2 i -
          tripleChartAngularPositions (tripleJointAlpha w.1) w.2 j))) := by fun_prop
  have hback : ContDiffAt ℝ n (fun w : TripleJointVariables => (w.1 1)^3 / (1 + w.1 0)) v := by
    fun_prop
  exact hpre.contDiffAt.mul
    ((((tripleChartW_joint_contDiffAt n v i j (hW j (Finset.mem_erase.mp hj).1)).pow 3).inv
      (pow_ne_zero 3 hn)).sub hback)

theorem tripleInternalRadial_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (i : TripleLabel)
    (hW : ∀ j, j ≠ i → 0 < tripleChartWSq (v.1 1) (tripleJointAlpha v.1) v.2 i j) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleInternalRadial (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2 i) v :=
  (by fun_prop : ContDiffAt ℝ n (fun w : TripleJointVariables => w.1 1) v).mul
    (tripleInternalRadialReduced_joint_contDiffAt n v i hW)

theorem tripleInternalAngular_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (i : TripleLabel) (heps : 1 + v.1 0 ≠ 0)
    (hW : ∀ j, j ≠ i → 0 < tripleChartWSq (v.1 1) (tripleJointAlpha v.1) v.2 i j) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleInternalAngular (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2 i) v :=
  (by fun_prop : ContDiffAt ℝ n (fun w : TripleJointVariables => w.1 1) v).mul
    (tripleInternalAngularReduced_joint_contDiffAt n v i heps hW)

def tripleInternalRadialMean (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) : ℝ :=
  ∑ i, alpha i * tripleInternalRadial eps t alpha y i

def tripleInternalAngularMean (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) : ℝ :=
  ∑ i, alpha i * tripleInternalAngular eps t alpha y i

def tripleInternalRadialDifference (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) :
    TripleGaps := tripleGapMatrix *ᵥ tripleInternalRadialReduced eps t alpha y

def tripleInternalAngularDifference (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) :
    TripleGaps := tripleGapMatrix *ᵥ tripleInternalAngularReduced eps t alpha y

theorem tripleInternalRadial_difference_identity (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) :
    tripleGapMatrix *ᵥ tripleInternalRadial eps t alpha y =
      t • tripleInternalRadialDifference eps t alpha y := by
  ext k
  simp only [tripleInternalRadialDifference, Matrix.mulVec, dotProduct,
    tripleInternalRadial, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem tripleInternalAngular_difference_identity (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) :
    tripleGapMatrix *ᵥ tripleInternalAngular eps t alpha y =
      t • tripleInternalAngularDifference eps t alpha y := by
  ext k
  simp only [tripleInternalAngularDifference, Matrix.mulVec, dotProduct,
    tripleInternalAngular, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end DominantFiveBody
