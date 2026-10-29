import DominantFiveBody.SectionFourSourceEstimates

/-! The source radial subsequence supplies its two scalar limits and the
actual determinant remainder, rather than assuming those limits. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Topology Asymptotics
namespace DominantFiveBody

theorem physical_pair_radial_subsequence_source_package
    (r theta : ℕ → Satellite → ℝ) (a b j : Satellite) (psi : ℝ)
    (hr : ∀ n, 0 < r n b)
    (hrt : ∀ i, Tendsto (fun n => r n i) atTop (nhds 1))
    (hd : ∀ n, 0 < satelliteDistance (polarSatellites (r n) (theta n)) a b)
    (hat : Tendsto (fun n => theta n a) atTop (nhds psi))
    (hbt : Tendsto (fun n => theta n b) atTop (nhds psi))
    (v : Plane) (hv : v = polarPoint 1 psi ∨ v = -polarPoint 1 psi)
    (hvt : Tendsto (fun n => physicalPairDirection (polarSatellites (r n) (theta n)) a b)
      atTop (nhds v)) :
    (fun n => theta n b - theta n a) =o[atTop]
        (fun n => satelliteDistance (polarSatellites (r n) (theta n)) a b) ∧
      Tendsto (fun n => |r n b - r n a| /
        satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds 1) ∧
      (fun n => det2 (polarSatellites (r n) (theta n) b - polarSatellites (r n) (theta n) a)
        (polarSatellites (r n) (theta n) j - polarSatellites (r n) (theta n) a) -
        (r n b - r n a) * r n j * Real.sin (theta n j - theta n a)) =o[atTop]
          (fun n => satelliteDistance (polarSatellites (r n) (theta n)) a b) := by
  obtain ⟨hang, hrad⟩ := physical_pair_direction_polar_ratio_limits r theta a b psi hr hd
    (hrt b) hat hbt v hvt
  have horth : inner ℝ v (quarterTurn (polarPoint 1 psi)) = 0 := by
    rcases hv with h | h
    · rw [h, polarPoint_inner_rotation, sub_self, Real.sin_zero]
      ring
    · rw [h, inner_neg_left, polarPoint_inner_rotation, sub_self, Real.sin_zero]
      ring
  have habs : |inner ℝ v (polarPoint 1 psi)| = 1 := by
    rcases hv with h | h
    · rw [h, polarPoint_inner_radial, sub_self, Real.cos_zero]
      norm_num
    · rw [h, inner_neg_left, polarPoint_inner_radial, sub_self, Real.cos_zero]
      norm_num
  rw [horth] at hang
  have hsmall : (fun n => theta n b - theta n a) =o[atTop]
      (fun n => satelliteDistance (polarSatellites (r n) (theta n)) a b) :=
    (isLittleO_iff_tendsto (fun n h => (ne_of_gt (hd n) h).elim)).mpr hang
  refine ⟨hsmall, ?_, complete_pair_support_radial_expansion_littleO r theta a b j hrt hd hang⟩
  have hh := hrad.abs
  rw [habs] at hh
  convert! hh using 1
  ext n
  rw [abs_div, abs_of_pos (hd n)]

end DominantFiveBody
