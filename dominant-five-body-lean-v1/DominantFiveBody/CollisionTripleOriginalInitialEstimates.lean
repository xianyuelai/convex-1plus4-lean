import DominantFiveBody.CollisionTripleInitialScale

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1800000

theorem physical_triple_extreme_source_signs (eps : ℝ) (mu r theta : Satellite → ℝ)
    (hm : PositiveRatio mu)
    (hgap01 : 0 < theta 1-theta 0) (hgap12 : 0 < theta 2-theta 1)
    (hco01 : 0 < tripleAngularCoefficient eps r theta 0 1)
    (hco02 : 0 < tripleAngularCoefficient eps r theta 0 2)
    (hco12 : 0 < tripleAngularCoefficient eps r theta 1 2)
    (hroot : ∀ i,angularResidual eps mu r theta i=0) :
    physicalSourceFullAngularField eps (r 3) (theta 3) (r 0) (theta 0)<0 ∧
      0<physicalSourceFullAngularField eps (r 3) (theta 3) (r 2) (theta 2) := by
  have h0 := hroot 0
  have h2 := hroot 2
  rw [angularResidual_eq_full_matrix_sum,Fin.sum_univ_four] at h0 h2
  simp only [fullAngularMatrix_self,mul_zero,zero_add,add_zero] at h0 h2
  rw [fullAngularMatrix_reverse eps r theta 0 2,fullAngularMatrix_reverse eps r theta 1 2] at h2
  simp only [fullAngularMatrix_eq_physicalSourceFullAngularField] at h0 h2
  have h01 := fullAngularMatrix_eq_gap_coefficient eps r theta 0 1
  have h02 := fullAngularMatrix_eq_gap_coefficient eps r theta 0 2
  have h12 := fullAngularMatrix_eq_gap_coefficient eps r theta 1 2
  simp only [fullAngularMatrix_eq_physicalSourceFullAngularField] at h01 h02 h12
  rw [h01,h02] at h0
  rw [h02,h12] at h2
  have hw : 0<theta 2-theta 0 := by linarith
  have hp0 : 0<mu 1*((theta 1-theta 0)*tripleAngularCoefficient eps r theta 0 1)+
      mu 2*((theta 2-theta 0)*tripleAngularCoefficient eps r theta 0 2) :=
    add_pos (mul_pos (hm.1 1) (mul_pos hgap01 hco01)) (mul_pos (hm.1 2) (mul_pos hw hco02))
  have hp2 : 0<mu 0*((theta 2-theta 0)*tripleAngularCoefficient eps r theta 0 2)+
      mu 1*((theta 2-theta 1)*tripleAngularCoefficient eps r theta 1 2) :=
    add_pos (mul_pos (hm.1 0) (mul_pos hw hco02)) (mul_pos (hm.1 1) (mul_pos hgap12 hco12))
  constructor <;> nlinarith [hm.1 3]

theorem physical_triple_extreme_mass_width_bound (eps d : ℝ) (mu r theta : Satellite → ℝ)
    (hm : PositiveRatio mu) (hgap01 : 0<theta 1-theta 0) (hgap12 : 0<theta 2-theta 1)
    (hco01 : 1/(16*d^3)≤tripleAngularCoefficient eps r theta 0 1)
    (hco02 : 1/(16*d^3)≤tripleAngularCoefficient eps r theta 0 2)
    (hco12 : 1/(16*d^3)≤tripleAngularCoefficient eps r theta 1 2)
    (hroot : ∀ i,angularResidual eps mu r theta i=0) :
    (mu 0+mu 1+mu 2)*(theta 2-theta 0)/d^3≤
      16*mu 3*(physicalSourceFullAngularField eps (r 3) (theta 3) (r 2) (theta 2)-
        physicalSourceFullAngularField eps (r 3) (theta 3) (r 0) (theta 0)) := by
  have hwidth : 0<theta 2-theta 0 := by linarith
  have hlow01 := mul_le_mul_of_nonneg_left hco01 hgap01.le
  have hlow02 := mul_le_mul_of_nonneg_left hco02 hwidth.le
  have hlow12 := mul_le_mul_of_nonneg_left hco12 hgap12.le
  have hlow0 := mul_le_mul_of_nonneg_left hlow02 (add_pos (hm.1 0) (hm.1 2)).le
  have hlow1 := mul_le_mul_of_nonneg_left (add_le_add hlow01 hlow12) (hm.1 1).le
  have hlow : (mu 0+mu 1+mu 2)*(theta 2-theta 0)/(16*d^3)≤
      mu 3*(physicalSourceFullAngularField eps (r 3) (theta 3) (r 2) (theta 2)-
        physicalSourceFullAngularField eps (r 3) (theta 3) (r 0) (theta 0)) := by
    rw [physical_triple_extreme_angular_identity eps mu r theta hroot]
    convert! add_le_add hlow0 hlow1 using 1 <;> ring
  have hscaled := mul_le_mul_of_nonneg_left hlow (show (0:ℝ)≤16 by norm_num)
  convert! hscaled using 1 <;> ring

theorem normalized_complete_lower_triple_original_initial_estimates
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n, PositiveRatio (mu n))
    (hx : ∀ n, NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n, StrictConvexInOrder ⟨Equiv.refl Label, rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i, 0 < r n i)
    (hpolar : ∀ n, satellitesRelative (x n) = polarSatellites (r n) (theta n))
    (horder : ∀ n i j, i < j → 0 < theta n j - theta n i ∧ theta n j - theta n i < Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htheta : Tendsto theta atTop (𝓝 theta0))
    (c : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 c) :
    ∃ k A C : ℝ,0<k ∧ 0<A ∧ 0<C ∧ ∀ᶠ n in atTop,
      physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0)<0 ∧
      0<physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2) ∧
      (r n 0≤r n 2 →
        0<physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2)-
            physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0) ∧
        physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2)-
            physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0)≤
          -k*(r n 2-r n 0)+A*(theta n 2-theta n 0)) ∧
      (mu n 0+mu n 1+mu n 2)*(theta n 2-theta n 0)/
          tripleLowDiameter (satellitesRelative (x n))^3≤
        16*mu n 3*(physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2)-
          physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0)) ∧
      16*mu n 3*(physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2)-
          physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0))≤
        C*mu n 3*(theta n 2-theta n 0) := by
  classical
  obtain ⟨hrt, hunit, hmono, _, hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x
    heps hepst hm hx r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (𝓝 1) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto (fun _ : Satellite => (1 : ℝ)) |>.comp hrt
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (𝓝 (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp htheta
  have hbound (i j : Satellite) : |theta0 i - theta0 j| < Real.pi := by
    have hiLo := hmono (Fin.zero_le i)
    have hjLo := hmono (Fin.zero_le j)
    have hiHi := hmono (Fin.le_last i)
    have hjHi := hmono (Fin.le_last j)
    change theta0 i ≤ theta0 3 at hiHi
    change theta0 j ≤ theta0 3 at hjHi
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hca : qLimit 0 = c := (htriple 0).mpr (by decide)
  have hcluster (i : Satellite) (hi : i ≠ 3) : theta0 i = theta0 0 := by
    by_contra hne
    apply polarUnit_ne_of_angle_ne (theta0 i) (theta0 0) hne (by simpa only [abs_sub_comm] using hbound i 0)
    rw [← hunit i, ← hunit 0, (htriple i).mpr hi, hca]
  have h1 := hcluster 1 (by decide)
  have h2 := hcluster 2 (by decide)
  have hgapAbs := (normalized_complete_triple_limiting_exterior eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta 3 c htriple).2 0 (by decide)
  have hgap : theta0 3 - theta0 0 = h := by
    have hnonneg := sub_nonneg.mpr (hmono (by decide : (0 : Satellite) ≤ 3))
    rwa [abs_of_nonneg hnonneg] at hgapAbs
  obtain ⟨eta, k, A, heta, hk, hA, hcontrol⟩ :=
    physicalSourceFullAngularField_left_difference_control (theta0 3) (theta0 0) hgap
  have hsep := polarUnit_ne_of_angle_ne (theta0 3) (theta0 0)
    (sub_ne_zero.mp (hgap ▸ (show (0 : ℝ) < h by unfold h; positivity).ne'))
    (by rw [abs_sub_comm, hgap, abs_of_pos (show (0 : ℝ) < h by unfold h; positivity)]; unfold h; linarith [Real.pi_pos])
  obtain ⟨etaL, B, hetaL, hB, hLip⟩ := physicalSourceFullAngularField_lipschitz_rectangle (theta0 3) (theta0 0) hsep
  let eta0 := min eta etaL
  have he0 : 0 < eta0 := lt_min heta hetaL
  have heeta : eta0 ≤ eta := min_le_left _ _
  have heLip : eta0 ≤ etaL := min_le_right _ _
  have hepsNear : ∀ᶠ n in atTop, |eps n| < eta0 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hepst.eventually (Metric.ball_mem_nhds (0 : ℝ) he0)
  have hsourceNear : ∀ᶠ n in atTop, dist (r n 3, theta n 3) (1, theta0 3) < eta0 :=
    ((hrat 3).prodMk_nhds (htat 3)).eventually (Metric.ball_mem_nhds _ he0)
  have htargetNear (i j : Satellite) (hj : j ≠ 3) :
      ∀ᶠ n in atTop, dist (r n i, theta n j) (1, theta0 0) < eta0 := by
    have hjt : Tendsto (fun n => theta n j) atTop (𝓝 (theta0 0)) := by
      simpa only [hcluster j hj] using htat j
    exact ((hrat i).prodMk_nhds hjt).eventually (Metric.ball_mem_nhds _ he0)
  have hradNear : ∀ᶠ n in atTop, ∀ i : Satellite, (1 / 2 : ℝ) ≤ r n i ∧ r n i ≤ 2 := by
    apply (eventually_all).mpr
    intro i
    exact ((hrat i).eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).and
      ((hrat i).eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))) |>.mono (fun _ h => ⟨h.1.le, h.2.le⟩)
  have hsinNear (i : Satellite) (hi : i ≠ 3) :
      ∀ᶠ n in atTop, (1 / 2 : ℝ) ≤ Real.sin (theta n 3 - theta n i) := by
    have hs := Real.continuous_sin.continuousAt.tendsto.comp ((htat 3).sub (htat i))
    have hlim : Real.sin (theta0 3 - theta0 i) = Real.sqrt 3 / 2 := by
      rw [hcluster i hi, hgap]
      exact Real.sin_pi_div_three
    rw [hlim] at hs
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hsqrt := Real.sqrt_nonneg (3 : ℝ)
    exact (hs.eventually (Ioi_mem_nhds (by nlinarith : (1 / 2 : ℝ) < Real.sqrt 3 / 2))).mono (fun _ h => h.le)
  have hsincNear (i j : Satellite) (hi : i ≠ 3) (hj : j ≠ 3) :
      ∀ᶠ n in atTop, (1 / 2 : ℝ) ≤ Real.sinc (theta n j - theta n i) := by
    have hs := Real.continuous_sinc.continuousAt.tendsto.comp ((htat j).sub (htat i))
    simp only [hcluster i hi, hcluster j hj, sub_self, Real.sinc_zero] at hs
    exact (hs.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).mono (fun _ h => h.le)
  let d := fun n => tripleLowDiameter (satellitesRelative (x n))
  have hcf (n : ℕ) := satellitesRelative_collisionFree (x n) (hx n).1
  have hd (n : ℕ) : 0 < d n := tripleLowDiameter_pos _ (hcf n)
  have hdt : Tendsto d atTop (𝓝 0) := tripleLowDiameter_tendsto_zero _ qLimit hqt
    (((htriple 1).mpr (by decide)).trans hca.symm) (((htriple 2).mpr (by decide)).trans hca.symm)
  have hdsmall : ∀ᶠ n in atTop, d n ≤ 1 / 4 :=
    (hdt.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono (fun _ h => h.le)
  have hroots (n : ℕ) := (polarResiduals_zero_of_normalized (eps n) (mu n) (x n) (hx n)
    (hm n) (heps n) (r n) (theta n) (hr n) (hpolar n)).2
  let K := A / k + 64
  have hK : 0 < K := by dsimp [K]; positivity
  have hK1 : 1 ≤ K := by dsimp [K]; have h := div_pos hA hk; linarith
  refine ⟨k, A, 16 * B * K, hk, hA, by positivity, ?_⟩
  filter_upwards [hepsNear, hsourceNear, htargetNear 0 0 (by decide), htargetNear 2 0 (by decide),
    htargetNear 2 2 (by decide), hradNear, hsinNear 1 (by decide), hsinNear 2 (by decide),
    hsincNear 0 1 (by decide) (by decide), hsincNear 0 2 (by decide) (by decide),
    hsincNear 1 2 (by decide) (by decide), hdsmall] with n hepsN hsourceN h00 h20 h22 hradN hsin1 hsin2 hsinc01 hsinc02 hsinc12 hdsmallN
  have hq (i j : Satellite) : satelliteDistance (polarSatellites (r n) (theta n)) i j =
      ‖satellitesRelative (x n) j - satellitesRelative (x n) i‖ := by rw [hpolar n]; exact norm_sub_rev _ _
  have hdb := tripleLowDiameter_bounds (satellitesRelative (x n))
  have hsep01 : 0 < satelliteDistance (polarSatellites (r n) (theta n)) 0 1 := by rw [hq]; exact norm_pos_iff.mpr (sub_ne_zero.mpr ((hcf n).2 1 0 (by decide)))
  have hsep02 : 0 < satelliteDistance (polarSatellites (r n) (theta n)) 0 2 := by rw [hq]; exact norm_pos_iff.mpr (sub_ne_zero.mpr ((hcf n).2 2 0 (by decide)))
  have hsep12 : 0 < satelliteDistance (polarSatellites (r n) (theta n)) 1 2 := by rw [hq]; exact norm_pos_iff.mpr (sub_ne_zero.mpr ((hcf n).2 2 1 (by decide)))
  have hco01 := tripleAngularCoefficient_lower (eps n) (d n) (r n) (theta n) 0 1 (heps n).le (hd n) hdsmallN
    (hradN 0).1 (hradN 1).1 hsinc01 hsep01 (by rw [hq]; exact hdb.1)
  have hco02 := tripleAngularCoefficient_lower (eps n) (d n) (r n) (theta n) 0 2 (heps n).le (hd n) hdsmallN
    (hradN 0).1 (hradN 2).1 hsinc02 hsep02 (by rw [hq]; exact hdb.2.1)
  have hco12 := tripleAngularCoefficient_lower (eps n) (d n) (r n) (theta n) 1 2 (heps n).le (hd n) hdsmallN
    (hradN 1).1 (hradN 2).1 hsinc12 hsep12 (by rw [hq]; exact hdb.2.2)
  have h01 := (horder n 0 1 (by decide)).1
  have h12 := (horder n 1 2 (by decide)).1
  have hW : 0 < theta n 2 - theta n 0 := by linarith
  have hdn := hd n
  have hm0 := (hm n).1 0
  have hm1 := (hm n).1 1
  have hm2 := (hm n).1 2
  have hidentity := physical_triple_extreme_angular_identity (eps n) (mu n) (r n) (theta n) (hroots n)
  have hJpos : 0 < physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2) -
      physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0) := by
    have hc01 : 0 < tripleAngularCoefficient (eps n) (r n) (theta n) 0 1 := (by positivity : 0 < 1 / (16 * d n ^ 3)).trans_le hco01
    have hc02 : 0 < tripleAngularCoefficient (eps n) (r n) (theta n) 0 2 := (by positivity : 0 < 1 / (16 * d n ^ 3)).trans_le hco02
    have hc12 : 0 < tripleAngularCoefficient (eps n) (r n) (theta n) 1 2 := (by positivity : 0 < 1 / (16 * d n ^ 3)).trans_le hco12
    have hprod : 0 < mu n 3 * (physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2) -
        physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0)) := by rw [hidentity]; positivity
    exact (mul_pos_iff_of_pos_left ((hm n).1 3)).mp hprod
  have hsupport01 := strictConvex_adjacent_pair_support (x n) (hconv n) 0 1 (by decide) 3 (by decide)
  have hsupport12 := strictConvex_adjacent_pair_support (x n) (hconv n) 1 2 (by decide) 3 (by decide)
  rw [hpolar n] at hsupport01 hsupport12
  have hdrop01 := polar_support_radial_drop_le (r n 0) (r n 1) (r n 3) (theta n 0) (theta n 1) (theta n 3)
    (hradN 0).1 (hradN 1).1 (hradN 3).1 (hradN 0).2 (hradN 1).2 (hradN 3).2 h01 hsin1 hsupport01
  have hdrop12 := polar_support_radial_drop_le (r n 1) (r n 2) (r n 3) (theta n 1) (theta n 2) (theta n 3)
    (hradN 1).1 (hradN 2).1 (hradN 3).1 (hradN 1).2 (hradN 2).2 (hradN 3).2 h12 hsin2 hsupport12
  have hup02 (hup : r n 0 ≤ r n 2) : r n 2 - r n 0 ≤ (A / k) * (theta n 2 - theta n 0) := by
    have h := hcontrol (eps n) (r n 3) (theta n 3) (r n 0) (r n 2) (theta n 0) (theta n 2)
      (hepsN.trans_le heeta) (hsourceN.trans_le heeta) hup (h00.trans_le heeta) (h20.trans_le heeta) (h22.trans_le heeta)
    rw [abs_of_pos hW] at h
    have he : A / k * (theta n 2 - theta n 0) = A * (theta n 2 - theta n 0) / k := by ring
    rw [he]
    exact (le_div_iff₀ hk).mpr (by nlinarith)
  have hspread := three_radii_spread_le_width (r n 0) (r n 1) (r n 2) (theta n 0) (theta n 1) (theta n 2)
    32 (A / k) (by norm_num) (div_pos hA hk).le (by linarith) (by linarith) hdrop01 hdrop12 hup02
  have hs01 : |r n 1 - r n 0| ≤ K * (theta n 2 - theta n 0) := by simpa only [K, show (2 : ℝ) * 32 = 64 by norm_num] using hspread.1
  have hs02 : |r n 2 - r n 0| ≤ K * (theta n 2 - theta n 0) := by simpa only [K, show (2 : ℝ) * 32 = 64 by norm_num] using hspread.2.1
  have hs12 : |r n 2 - r n 1| ≤ K * (theta n 2 - theta n 0) := by simpa only [K, show (2 : ℝ) * 32 = 64 by norm_num] using hspread.2.2

  have hc01 : 0<tripleAngularCoefficient (eps n) (r n) (theta n) 0 1 :=
    (by positivity : 0<1/(16*d n^3)).trans_le hco01
  have hc02 : 0<tripleAngularCoefficient (eps n) (r n) (theta n) 0 2 :=
    (by positivity : 0<1/(16*d n^3)).trans_le hco02
  have hc12 : 0<tripleAngularCoefficient (eps n) (r n) (theta n) 1 2 :=
    (by positivity : 0<1/(16*d n^3)).trans_le hco12
  have hsign := physical_triple_extreme_source_signs (eps n) (mu n) (r n) (theta n)
    (hm n) h01 h12 hc01 hc02 hc12 (hroots n)
  refine ⟨hsign.1,hsign.2,?_,?_,?_⟩
  · intro hup
    refine ⟨hJpos,?_⟩
    have h := hcontrol (eps n) (r n 3) (theta n 3) (r n 0) (r n 2) (theta n 0) (theta n 2)
      (hepsN.trans_le heeta) (hsourceN.trans_le heeta) hup
      (h00.trans_le heeta) (h20.trans_le heeta) (h22.trans_le heeta)
    simpa only [abs_of_pos hW] using h
  · exact physical_triple_extreme_mass_width_bound (eps n) (d n) (mu n) (r n) (theta n)
      (hm n) h01 h12 hco01 hco02 hco12 (hroots n)
  · have hJ := (le_abs_self _).trans (hLip (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0) (r n 2) (theta n 2)
      (hepsN.trans_le heLip) (hsourceN.trans_le heLip) (h00.trans_le heLip) (h22.trans_le heLip))
    rw [abs_of_pos hW] at hJ
    have hmax : max |r n 2-r n 0| (theta n 2-theta n 0)≤K*(theta n 2-theta n 0) :=
      max_le hs02 (by nlinarith)
    have hJbound := hJ.trans (mul_le_mul_of_nonneg_left hmax hB.le)
    have hm3 := (hm n).1 3
    have h := mul_le_mul_of_nonneg_left hJbound (by positivity : 0≤16*mu n 3)
    convert! h using 1
    ring

end DominantFiveBody
