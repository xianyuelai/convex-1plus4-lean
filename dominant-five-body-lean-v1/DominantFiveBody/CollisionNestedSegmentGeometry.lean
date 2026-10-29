import DominantFiveBody.CollisionNestedRectangleGeometry

/-! # Uniform actual smaller-pair segment geometry -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1500000

def physicalPairSegmentPoint (qa qb : Plane) (t : ℝ) : Plane := (1-t) • qa+t • qb

theorem physicalPairSegmentPoint_eq (qa qb : Plane) (t : ℝ) :
    physicalPairSegmentPoint qa qb t=qa+t • (qb-qa) := by unfold physicalPairSegmentPoint;module

theorem bounded_segment_coefficient_small_smul
    (t : ℕ → ℝ) (B : ℕ → Plane) (ht : ∀ n,t n∈Icc (0 : ℝ) 1)
    (hB : Tendsto B atTop (𝓝 0)) : Tendsto (fun n => t n • B n) atTop (𝓝 0) := by
  apply squeeze_zero_norm _ (by simpa only [norm_zero] using hB.norm)
  intro n
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (ht n).1]
  exact (mul_le_mul_of_nonneg_right (ht n).2 (norm_nonneg _)).trans_eq (one_mul _)

theorem physical_pair_segment_near_distance_uniform
    (qa qb qc : ℕ → Plane) (d : ℕ → ℝ) (u : Plane) (hd : ∀ n,0<d n) (hu : ‖u‖=1)
    (hnear : Tendsto (fun n => (d n)⁻¹ • (qc n-qa n)) atTop (𝓝 u))
    (hsmall : Tendsto (fun n => ‖qb n-qa n‖/d n) atTop (𝓝 0)) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,∀ t∈Icc (0 : ℝ) 1,
      |‖qc n-physicalPairSegmentPoint (qa n) (qb n) t‖/d n-1|<eta := by
  have hB : Tendsto (fun n => (d n)⁻¹ • (qb n-qa n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert! hsmall using 1
    funext n
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd n)]
    ring
  let F : ℕ → ℝ → ℝ := fun n t => ‖qc n-physicalPairSegmentPoint (qa n) (qb n) t‖/d n
  have hseq : ∀ t : ℕ → ℝ,(∀ n,t n∈Icc (0 : ℝ) 1) → Tendsto (fun n => F n (t n)) atTop (𝓝 1) := by
    intro t ht
    have hsm := bounded_segment_coefficient_small_smul t _ ht hB
    have hv : Tendsto (fun n => (d n)⁻¹ • (qc n-physicalPairSegmentPoint (qa n) (qb n) (t n)))
        atTop (𝓝 u) := by
      convert! hnear.sub hsm using 1
      · funext n;rw [physicalPairSegmentPoint_eq];module
      · simp
    convert! hv.norm using 1
    · funext n
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd n)]
      ring
    · rw [hu]
  have hU := limit_on_moving_sets_of_all_selections (fun _ => Icc (0 : ℝ) 1) (fun _ => (0 : ℝ))
    (fun _ => by norm_num) F 1 hseq
  simpa only [Real.dist_eq] using hU

theorem physical_pair_segment_far_distance_uniform
    (qa qb qp : ℕ → Plane) (c p : Plane)
    (ha : Tendsto qa atTop (𝓝 c)) (hb : Tendsto qb atTop (𝓝 c)) (hp : Tendsto qp atTop (𝓝 p)) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,∀ t∈Icc (0 : ℝ) 1,
      |‖qp n-physicalPairSegmentPoint (qa n) (qb n) t‖-‖p-c‖|<eta := by
  have hB : Tendsto (fun n => qb n-qa n) atTop (𝓝 0) := by simpa only [sub_self] using hb.sub ha
  let F : ℕ → ℝ → ℝ := fun n t => ‖qp n-physicalPairSegmentPoint (qa n) (qb n) t‖
  have hseq : ∀ t : ℕ → ℝ,(∀ n,t n∈Icc (0 : ℝ) 1) → Tendsto (fun n => F n (t n)) atTop (𝓝 ‖p-c‖) := by
    intro t ht
    have hs := bounded_segment_coefficient_small_smul t _ ht hB
    have hy : Tendsto (fun n => physicalPairSegmentPoint (qa n) (qb n) (t n)) atTop (𝓝 c) := by
      simpa only [physicalPairSegmentPoint_eq,add_zero] using ha.add hs
    exact (hp.sub hy).norm
  have hU := limit_on_moving_sets_of_all_selections (fun _ => Icc (0 : ℝ) 1) (fun _ => (0 : ℝ))
    (fun _ => by norm_num) F ‖p-c‖ hseq
  simpa only [Real.dist_eq] using hU

end DominantFiveBody
