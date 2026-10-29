import DominantFiveBody.CollisionPairScales
import DominantFiveBody.CollisionTripleBounds
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Original Section 4 estimates before the radial pair alternative is excluded.
The cluster center and all exterior masses are their current values. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Topology Asymptotics
namespace DominantFiveBody

theorem complete_cluster_current_center_exterior_bound
    (m : ℕ → MassVector) (x : ℕ → Configuration)
    (hm : ∀ n, PositiveMasses (m n))
    (mLimit : MassVector) (xLimit : Configuration)
    (hmt : Tendsto m atTop (nhds mLimit)) (hxt : Tendsto x atTop (nhds xLimit))
    (S : Finset Label) (hS : S.Nonempty) (c : Plane)
    (hC : CompleteLimitingCluster xLimit S c) :
    ∃ L : ℝ, 0 < L ∧ ∃ V : Set ExteriorData,
      IsOpen V ∧ V ∈ nhds ((mLimit, xLimit), c) ∧
      (∀ d ∈ V, DifferentiableAt ℝ (exteriorField S) d ∧
        ‖fderiv ℝ (exteriorField S) d‖ ≤ L) ∧
      ∀ᶠ n in atTop,
        ((m n, x n), clusterCenter (m n) (x n) S) ∈ V ∧
        ∀ i ∈ S, ((m n, x n), x n i) ∈ V ∧
          ‖exteriorAcceleration (m n) (x n) S i -
            exteriorField S ((m n, x n), clusterCenter (m n) (x n) S)‖ ≤
              L * ‖x n i - clusterCenter (m n) (x n) S‖ := by
  obtain ⟨K, U, hU, hLip⟩ := complete_cluster_exterior_lipschitz xLimit S c hC mLimit
  have hsep : ∀ j ∈ Sᶜ, c ≠ xLimit j := by
    intro j hj he
    exact (Finset.mem_compl.mp hj) ((hC j).mpr he.symm)
  have hregular : ∀ᶠ d in nhds ((mLimit, xLimit), c), ContDiffAt ℝ 1 (exteriorField S) d :=
    ((exteriorField_contDiffAt S ((mLimit, xLimit), c) hsep).of_le (by norm_num)).eventually (by norm_num)
  obtain ⟨V, hVW, hVopen, hVmem⟩ := mem_nhds_iff.mp (inter_mem hU hregular)
  have hVU : V ⊆ U := fun _ hd => (hVW hd).1
  have hVnear : V ∈ nhds ((mLimit, xLimit), c) := hVopen.mem_nhds hVmem
  have hLipV := hLip.mono hVU
  have hder (d : ExteriorData) (hd : d ∈ V) :
      DifferentiableAt ℝ (exteriorField S) d ∧
        ‖fderiv ℝ (exteriorField S) d‖ ≤ (K : ℝ) + 1 :=
    ⟨(show ContDiffAt ℝ 1 (exteriorField S) d from (hVW hd).2).differentiableAt (by norm_num),
      (norm_fderiv_le_of_lipschitzOn ℝ (hVopen.mem_nhds hd) hLipV).trans (by linarith)⟩
  have hcluster (i : Label) (hi : i ∈ S) : Tendsto (fun n => x n i) atTop (nhds c) := by
    simpa only [Function.comp_def, (hC i).mp hi] using
      (continuous_apply i).tendsto xLimit |>.comp hxt
  have hbt := clusterCenter_tendsto_current_weights m hm x S hS c hcluster
  have hbV := (hmt.prodMk_nhds hxt |>.prodMk_nhds hbt).eventually hVnear
  have hiV : ∀ᶠ n in atTop, ∀ i ∈ S, ((m n, x n), x n i) ∈ V := by
    apply (Finset.eventually_all S).mpr
    intro i hi
    exact (hmt.prodMk_nhds hxt |>.prodMk_nhds (hcluster i hi)).eventually hVnear
  refine ⟨(K : ℝ) + 1, by positivity, V, hVopen, hVnear, hder, ?_⟩
  filter_upwards [hbV, hiV] with n hnb hni
  refine ⟨hnb, fun i hi => ⟨hni i hi, ?_⟩⟩
  exact (exteriorField_target_lipschitz S K V hLipV (m n) (x n) _ _ (hni i hi) hnb).trans
    (mul_le_mul_of_nonneg_right (by linarith : (K : ℝ) ≤ (K : ℝ) + 1) (norm_nonneg _))

theorem physical_pair_angular_gap_le_four_distance (r theta : Satellite → ℝ) (a b : Satellite)
    (hrb : (1 / 2 : ℝ) ≤ r b)
    (hd : 0 < satelliteDistance (polarSatellites r theta) a b)
    (hgap : 0 ≤ theta b - theta a)
    (hsinc : (1 / 2 : ℝ) ≤ Real.sinc (theta b - theta a)) :
    theta b - theta a ≤ 4 * satelliteDistance (polarSatellites r theta) a b := by
  have hs : (theta b - theta a) / 2 ≤ Real.sin (theta b - theta a) := by
    rw [← sinc_mul_argument (theta b - theta a)]
    have h := mul_le_mul_of_nonneg_left hsinc hgap
    nlinarith
  have hqne : polarSatellites r theta a ≠ polarSatellites r theta b := by
    intro he
    simp only [satelliteDistance, he, sub_self, norm_zero] at hd
    exact (lt_irrefl 0 hd)
  have hJ : ‖quarterTurn (polarPoint 1 (theta a))‖ = 1 := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    rw [← real_inner_self_eq_norm_sq, quarterTurn_inner_quarterTurn,
      real_inner_self_eq_norm_sq, polarPoint_norm, abs_one]
    norm_num
  have hi := real_inner_le_norm (physicalPairDirection (polarSatellites r theta) a b)
    (quarterTurn (polarPoint 1 (theta a)))
  rw [physicalPairDirection_norm _ a b hqne, hJ, one_mul,
    (physical_pair_direction_polar_components r theta a b).1] at hi
  have hsinupper := (div_le_iff₀ hd).mp hi
  have hsinpos : 0 ≤ Real.sin (theta b - theta a) := by linarith
  have hprod := mul_le_mul_of_nonneg_right hrb hsinpos
  nlinarith

theorem physical_pair_radius_difference_le_distance (r theta : Satellite → ℝ)
    (a b : Satellite) (hra : 0 < r a) (hrb : 0 < r b) :
    |r b - r a| ≤ satelliteDistance (polarSatellites r theta) a b := by
  have h := abs_norm_sub_norm_le (polarPoint (r b) (theta b)) (polarPoint (r a) (theta a))
  simpa only [polarPoint_norm, abs_of_pos hra, abs_of_pos hrb, satelliteDistance,
    polarSatellites, norm_sub_rev] using h

theorem physical_pair_angular_prebound
    (C : ℝ) (mu r theta : Satellite → ℝ) (a b : Satellite)
    (hm : ∀ i, 0 < mu i) (hra : (1 / 2 : ℝ) ≤ r a) (hrb : (1 / 2 : ℝ) ≤ r b)
    (hd : 0 < satelliteDistance (polarSatellites r theta) a b)
    (hsmall : satelliteDistance (polarSatellites r theta) a b ≤ 1 / 4)
    (hgap : 0 ≤ theta b - theta a) (hsinc : (1 / 2 : ℝ) ≤ Real.sinc (theta b - theta a))
    (heq : physicalPairExteriorAngularField mu r theta a b (r b) (theta b) -
      physicalPairExteriorAngularField mu r theta a b (r a) (theta a) =
      Real.sin (theta b - theta a) *
        ((mu a * r a + mu b * r b) / satelliteDistance (polarSatellites r theta) a b ^ 3 -
          mu a / (r a) ^ 2 - mu b / (r b) ^ 2))
    (hupper : physicalPairExteriorAngularField mu r theta a b (r b) (theta b) -
      physicalPairExteriorAngularField mu r theta a b (r a) (theta a) ≤
      C * (1 - (mu a + mu b)) * satelliteDistance (polarSatellites r theta) a b) :
    (theta b - theta a) * (mu a + mu b) /
      satelliteDistance (polarSatellites r theta) a b ^ 3 ≤
        8 * C * (1 - (mu a + mu b)) * satelliteDistance (polarSatellites r theta) a b := by
  have hs : (theta b - theta a) / 2 ≤ Real.sin (theta b - theta a) := by
    rw [← sinc_mul_argument (theta b - theta a)]
    have h := mul_le_mul_of_nonneg_left hsinc hgap
    nlinarith
  have hco := pair_tangential_coefficient_lower mu r theta a b hm hra hrb hd hsmall
  have hcpos : 0 ≤ (mu a + mu b) / (4 * satelliteDistance (polarSatellites r theta) a b ^ 3) :=
    div_nonneg (add_pos (hm a) (hm b)).le (by positivity)
  have hprod := mul_le_mul hs hco hcpos (show 0 ≤ Real.sin (theta b - theta a) by linarith)
  rw [← heq] at hprod
  have h := mul_le_mul_of_nonneg_left (hprod.trans hupper) (show (0 : ℝ) ≤ 8 by norm_num)
  convert! h using 1 <;> ring

theorem complete_pair_angular_prebound_before_radial_exclusion
    (mu : ℕ → MassRatio) (hm : ∀ n, PositiveRatio (mu n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i, 0 < r n i)
    (hrt : ∀ i, Tendsto (fun n => r n i) atTop (nhds 1))
    (theta0 : Satellite → ℝ) (htt : Tendsto theta atTop (nhds theta0))
    (a b : Satellite) (hab : a ≠ b) (hab0 : theta0 b = theta0 a)
    (horder : ∀ n, theta n a < theta n b)
    (hsep : ∀ j ∈ pairExteriorLabels a b, polarPoint 1 (theta0 j) ≠ polarPoint 1 (theta0 a))
    (hd : ∀ n, 0 < satelliteDistance (polarSatellites (r n) (theta n)) a b)
    (hroot : ∀ n i, tangentialResidual (mu n) (r n) (theta n) i = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      theta n b - theta n a ≤ 4 * satelliteDistance (polarSatellites (r n) (theta n)) a b ∧
      (1 / 2 : ℝ) ≤ Real.sinc (theta n b - theta n a) ∧
      (theta n b - theta n a) * (mu n a + mu n b) /
        satelliteDistance (polarSatellites (r n) (theta n)) a b ^ 3 ≤
          C * (1 - (mu n a + mu n b)) * satelliteDistance (polarSatellites (r n) (theta n)) a b := by
  have hat := (continuous_apply a).tendsto theta0 |>.comp htt
  have hbt := (continuous_apply b).tendsto theta0 |>.comp htt
  have hgap : Tendsto (fun n => theta n b - theta n a) atTop (nhds 0) := by
    simpa only [Function.comp_def, hab0, sub_self] using hbt.sub hat
  have hsinct : Tendsto (fun n => Real.sinc (theta n b - theta n a)) atTop (nhds 1) := by
    simpa only [Function.comp_def, Real.sinc_zero] using Real.continuous_sinc.continuousAt.tendsto.comp hgap
  have hsinc := hsinct.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hra := (hrt a).eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hrb := (hrt b).eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hqa : Tendsto (fun n => polarPoint (r n a) (theta n a)) atTop
      (nhds (polarPoint 1 (theta0 a))) :=
    ((polarPoint_contDiff ∞).continuous.tendsto _).comp ((hrt a).prodMk_nhds hat)
  have hqb : Tendsto (fun n => polarPoint (r n b) (theta n b)) atTop
      (nhds (polarPoint 1 (theta0 b))) :=
    ((polarPoint_contDiff ∞).continuous.tendsto _).comp ((hrt b).prodMk_nhds hbt)
  have hdt : Tendsto (fun n => satelliteDistance (polarSatellites (r n) (theta n)) a b)
      atTop (nhds 0) := by
    simpa only [satelliteDistance, polarSatellites, hab0, sub_self, norm_zero] using (hqa.sub hqb).norm
  have hsmall := hdt.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨K, hK, hangular⟩ := complete_pair_exterior_angular_error_bound mu hm r theta hrt theta0 htt a b hab hab0 hsep
  refine ⟨32 * K, by positivity, ?_⟩
  filter_upwards [hsinc, hra, hrb, hsmall, hangular] with n hsn han hbn hdn hn
  have hdelta := physical_pair_angular_gap_le_four_distance (r n) (theta n) a b hbn.le (hd n)
    (sub_nonneg.mpr (horder n).le) hsn.le
  have hdiff := physical_pair_radius_difference_le_distance (r n) (theta n) a b (hr n a) (hr n b)
  have hmax : max |r n b - r n a| |theta n b - theta n a| ≤
      4 * satelliteDistance (polarSatellites (r n) (theta n)) a b := by
    apply max_le
    · nlinarith [hd n]
    · simpa only [abs_of_pos (sub_pos.mpr (horder n))] using hdelta
  have hupper : physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b) -
      physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a) ≤
        (4 * K) * (1 - (mu n a + mu n b)) * satelliteDistance (polarSatellites (r n) (theta n)) a b := by
    have h := (le_abs_self _).trans hn
    have hweight : 0 ≤ K * (1 - (mu n a + mu n b)) :=
      mul_nonneg hK.le (pairExteriorMass_pos (mu n) (hm n) a b hab).le
    have hh := mul_le_mul_of_nonneg_left hmax hweight
    exact h.trans (by convert! hh using 1; ring)
  refine ⟨hdelta, hsn.le, ?_⟩
  simpa only [show 8 * (4 * K) = 32 * K by ring] using
    physical_pair_angular_prebound (4 * K) (mu n) (r n) (theta n) a b (hm n).1 han.le hbn.le
      (hd n) hdn.le (sub_nonneg.mpr (horder n).le) hsn.le
      (physical_pair_tangential_difference (mu n) (r n) (theta n) a b hab (fun i => hr n i) (hroot n)) hupper

theorem polar_support_radial_expansion_exact (ra rb rj va vb vj : ℝ) :
    det2 (polarPoint rb vb - polarPoint ra va) (polarPoint rj vj - polarPoint ra va) -
        (rb - ra) * rj * Real.sin (vj - va) =
      rb * rj * (Real.sin (vj - vb) - Real.sin (vj - va)) + ra * rb * Real.sin (vb - va) := by
  rw [polar_support_triangle_formula]
  ring

theorem polar_support_radial_expansion_remainder_bound (ra rb rj va vb vj : ℝ) :
    |det2 (polarPoint rb vb - polarPoint ra va) (polarPoint rj vj - polarPoint ra va) -
        (rb - ra) * rj * Real.sin (vj - va)| ≤
      (|rb * rj| + |ra * rb|) * |vb - va| := by
  rw [polar_support_radial_expansion_exact]
  have hs := Real.abs_sin_sub_sin_le (vj - vb) (vj - va)
  have he : |vj - vb - (vj - va)| = |vb - va| := by
    rw [show vj - vb - (vj - va) = -(vb - va) by ring, abs_neg]
  rw [he] at hs
  calc
    _ ≤ |rb * rj * (Real.sin (vj - vb) - Real.sin (vj - va))| + |ra * rb * Real.sin (vb - va)| := abs_add_le _ _
    _ ≤ |rb * rj| * |vb - va| + |ra * rb| * |vb - va| := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hs (by positivity))
        (mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by positivity))
    _ = _ := by ring

theorem complete_pair_support_radial_expansion_littleO
    (r theta : ℕ → Satellite → ℝ) (a b j : Satellite)
    (hrt : ∀ i, Tendsto (fun n => r n i) atTop (nhds 1))
    (hd : ∀ n, 0 < satelliteDistance (polarSatellites (r n) (theta n)) a b)
    (hgap : Tendsto (fun n => (theta n b - theta n a) /
      satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds 0)) :
    (fun n => det2 (polarSatellites (r n) (theta n) b - polarSatellites (r n) (theta n) a)
        (polarSatellites (r n) (theta n) j - polarSatellites (r n) (theta n) a) -
      (r n b - r n a) * r n j * Real.sin (theta n j - theta n a)) =o[atTop]
        (fun n => satelliteDistance (polarSatellites (r n) (theta n)) a b) := by
  have hcoeff : Tendsto (fun n => |r n b * r n j| + |r n a * r n b|) atTop (nhds 2) := by
    convert! ((hrt b).mul (hrt j)).abs.add ((hrt a).mul (hrt b)).abs using 1
    norm_num
  have hcoeffbound := hcoeff.eventually (Iio_mem_nhds (by norm_num : (2 : ℝ) < 3))
  have hO : (fun n => det2 (polarSatellites (r n) (theta n) b - polarSatellites (r n) (theta n) a)
      (polarSatellites (r n) (theta n) j - polarSatellites (r n) (theta n) a) -
      (r n b - r n a) * r n j * Real.sin (theta n j - theta n a)) =O[atTop]
      (fun n => theta n b - theta n a) := by
    apply IsBigO.of_bound 3
    filter_upwards [hcoeffbound] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (polar_support_radial_expansion_remainder_bound (r n a) (r n b) (r n j)
      (theta n a) (theta n b) (theta n j)).trans
        (mul_le_mul_of_nonneg_right hn.le (abs_nonneg _))
  have hsmall : (fun n => theta n b - theta n a) =o[atTop]
      (fun n => satelliteDistance (polarSatellites (r n) (theta n)) a b) :=
    (isLittleO_iff_tendsto (fun n h => (ne_of_gt (hd n) h).elim)).mpr hgap
  exact hO.trans_isLittleO hsmall

end DominantFiveBody
