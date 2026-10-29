import DominantFiveBody.CollisionTripleWidth
import DominantFiveBody.CollisionNestedScales

/-! # A positive actual cubic mass scale for comparable lower triples

The separated source secant tends to the positive unit-source derivative.
The exact extreme angular rows bound it above using all current cluster
masses together. No individual cluster mass share has a lower bound here.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1200000

theorem tripleAngularCoefficient_upper_comparable (eps d eta : ℝ)
    (r theta : Satellite → ℝ) (i j : Satellite)
    (heps : 0≤eps) (hd : 0<d) (heta : 0<eta)
    (hra : 0<r i) (hrb : 0<r j) (hra2 : r i≤2) (hrb2 : r j≤2)
    (hsinc : 0≤Real.sinc (theta j-theta i))
    (hsep : eta*d≤satelliteDistance (polarSatellites r theta) i j) :
    tripleAngularCoefficient eps r theta i j≤4/(eta^3*d^3) := by
  have hdist : 0<satelliteDistance (polarSatellites r theta) i j := (mul_pos heta hd).trans_le hsep
  have hpow := pow_le_pow_left₀ (mul_pos heta hd).le hsep 3
  have hinv : (satelliteDistance (polarSatellites r theta) i j^3)⁻¹≤((eta*d)^3)⁻¹ :=
    inv_anti₀ (pow_pos (mul_pos heta hd) 3) hpow
  have herr : 0≤(1+eps)⁻¹ := inv_nonneg.mpr (by linarith)
  have hmain : (satelliteDistance (polarSatellites r theta) i j^3)⁻¹-(1+eps)⁻¹≤((eta*d)^3)⁻¹ := by linarith
  have hprod : r i*r j≤4 := by
    have hp := mul_le_mul hra2 hrb2 hrb.le (by norm_num : (0 : ℝ)≤2)
    norm_num at hp
    exact hp
  have hpre : r i*r j*Real.sinc (theta j-theta i)≤4 := by
    exact (mul_le_mul_of_nonneg_left (Real.sinc_le_one _) (mul_pos hra hrb).le).trans
      (by simpa only [mul_one] using hprod)
  have hpre0 : 0≤r i*r j*Real.sinc (theta j-theta i) := mul_nonneg (mul_pos hra hrb).le hsinc
  unfold tripleAngularCoefficient
  calc
    _≤r i*r j*Real.sinc (theta j-theta i)*((eta*d)^3)⁻¹ := mul_le_mul_of_nonneg_left hmain hpre0
    _≤4*((eta*d)^3)⁻¹ := mul_le_mul_of_nonneg_right hpre (inv_pos.mpr (pow_pos (mul_pos heta hd) 3)).le
    _=4/(eta^3*d^3) := by rw [mul_pow]; rfl

theorem triple_mass_cube_lower_of_extreme_rows (eps d eta A : ℝ)
    (mu r theta : Satellite → ℝ) (hm : PositiveRatio mu)
    (hd : 0<d) (heta : 0<eta)
    (hgap01 : 0<theta 1-theta 0) (hgap12 : 0<theta 2-theta 1)
    (hco01 : tripleAngularCoefficient eps r theta 0 1≤4/(eta^3*d^3))
    (hco02 : tripleAngularCoefficient eps r theta 0 2≤4/(eta^3*d^3))
    (hco12 : tripleAngularCoefficient eps r theta 1 2≤4/(eta^3*d^3))
    (hroot : ∀ i,angularResidual eps mu r theta i=0)
    (hJ : A*(theta 2-theta 0)≤
      physicalSourceFullAngularField eps (r 3) (theta 3) (r 2) (theta 2)-
        physicalSourceFullAngularField eps (r 3) (theta 3) (r 0) (theta 0)) :
    (A*eta^3/4)*mu 3≤(mu 0+mu 1+mu 2)/d^3 := by
  have hwidth : 0<theta 2-theta 0 := by linarith
  have h01 := mul_le_mul_of_nonneg_left hco01 hgap01.le
  have h02 := mul_le_mul_of_nonneg_left hco02 hwidth.le
  have h12 := mul_le_mul_of_nonneg_left hco12 hgap12.le
  have h0 := mul_le_mul_of_nonneg_left h02 (add_pos (hm.1 0) (hm.1 2)).le
  have h1 := mul_le_mul_of_nonneg_left (add_le_add h01 h12) (hm.1 1).le
  have hidentity := physical_triple_extreme_angular_identity eps mu r theta hroot
  have hupper : mu 3*(physicalSourceFullAngularField eps (r 3) (theta 3) (r 2) (theta 2)-
      physicalSourceFullAngularField eps (r 3) (theta 3) (r 0) (theta 0))≤
      (mu 0+mu 1+mu 2)*(theta 2-theta 0)*(4/(eta^3*d^3)) := by
    rw [hidentity]
    convert! add_le_add h0 h1 using 1 <;> ring
  have hsource := mul_le_mul_of_nonneg_left hJ (hm.1 3).le
  have hcancel : mu 3*A≤(mu 0+mu 1+mu 2)*(4/(eta^3*d^3)) := by
    apply (mul_le_mul_iff_right₀ hwidth).mp
    convert! hsource.trans hupper using 1 <;> ring
  have hscaled := mul_le_mul_of_nonneg_left hcancel (div_pos (pow_pos heta 3) (by norm_num : (0 : ℝ)<4)).le
  convert! hscaled using 1 <;> field_simp [heta.ne',hd.ne']

/-- An actual comparable complete triple has a uniform positive lower
bound for its total current cluster mass divided by the actual diameter
cubed. The only case input is distance comparability. -/
theorem normalized_complete_lower_triple_regular_mass_lower
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htheta : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (eta : ℝ) (heta : 0<eta)
    (hcomparable : ∀ᶠ n in atTop,∀ i j : TripleLabel,i≠j →
      eta*tripleLowDiameter (satellitesRelative (x n))≤
        satelliteDistance (satellitesRelative (x n)) i.castSucc j.castSucc) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n in atTop,
      c≤(mu n 0+mu n 1+mu n 2)/tripleLowDiameter (satellitesRelative (x n))^3 := by
  classical
  let d := fun n => tripleLowDiameter (satellitesRelative (x n))
  have hd (n : ℕ) : 0<d n := tripleLowDiameter_pos _ (satellitesRelative_collisionFree (x n) (hx n).1)
  obtain ⟨_,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x
    heps hepst hm hx r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (𝓝 1) := by
    convert! dominant_satellite_radius_tendsto eps mu x heps hepst hm hx i using 1
    funext n
    rw [hpolar n]
    simp only [polarSatellites,polarPoint_norm,abs_of_pos (hr n i)]
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (𝓝 (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp htheta
  have hbound (i j : Satellite) : |theta0 i-theta0 j|<Real.pi := by
    have hiLo := hmono (Fin.zero_le i)
    have hjLo := hmono (Fin.zero_le j)
    have hiHi := hmono (Fin.le_last i)
    have hjHi := hmono (Fin.le_last j)
    change theta0 i≤theta0 3 at hiHi
    change theta0 j≤theta0 3 at hjHi
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  have hthetaEq (i j : TripleLabel) : theta0 i.castSucc=theta0 j.castSucc := by
    have hip : i.castSucc≠(3 : Satellite) := by fin_cases i <;> decide
    have hjp : j.castSucc≠(3 : Satellite) := by fin_cases j <;> decide
    by_contra hne
    apply polarUnit_ne_of_angle_ne (theta0 i.castSucc) (theta0 j.castSucc) hne
      (by simpa only [abs_sub_comm] using hbound i.castSucc j.castSucc)
    rw [← hunit i.castSucc,← hunit j.castSucc,(htriple i.castSucc).mpr hip,(htriple j.castSucc).mpr hjp]
  have hgap (i j : TripleLabel) : Tendsto (fun n => theta n j.castSucc-theta n i.castSucc) atTop (𝓝 0) := by
    simpa only [hthetaEq i j,sub_self] using (htat j.castSucc).sub (htat i.castSucc)
  have hradial := normalized_complete_lower_triple_regular_radial_limits eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple eta heta hcomparable
  have hwidth : Tendsto (fun n => (theta n 2-theta n 0)/d n) atTop (𝓝 1) := by
    have hradialP (i j : TripleLabel) : Tendsto (fun n => (r n j.castSucc-r n i.castSucc)/
        tripleLowDiameter (polarSatellites (r n) (theta n))) atTop (𝓝 0) := by
      simpa only [hpolar] using hradial i j
    have hdp (n : ℕ) : 0<tripleLowDiameter (polarSatellites (r n) (theta n)) := by
      rw [← hpolar n]
      exact hd n
    have hh := triple_width_distance_ratio_tendsto_one r theta hrat hdp
      (fun n => ⟨sub_nonneg.mp (horder n 0 1 (by decide)).1.le,
        sub_nonneg.mp (horder n 1 2 (by decide)).1.le⟩) (hgap 0 1) (hgap 1 2) hradialP
    simpa only [d,hpolar] using hh
  have hgapAbs := (normalized_complete_triple_limiting_exterior eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta 3 center htriple).2 0 (by decide)
  have hne : theta0 3≠theta0 0 := by
    intro he
    rw [he,sub_self,abs_zero] at hgapAbs
    have hh : 0<h := by unfold h; positivity
    linarith
  have hr02 : Tendsto (fun n => (r n 2-r n 0)/d n) atTop (𝓝 0) := hradial 0 2
  have ht2 : Tendsto (fun n => theta n 2) atTop (𝓝 (theta0 0)) := by
    have h20 : theta0 2=theta0 0 := hthetaEq 2 0
    simpa only [h20] using htat 2
  have hJ := physicalSourceFullAngularField_moving_secant_limit eps (fun n => r n 3)
    (fun n => theta n 3) (fun n => r n 0) (fun n => theta n 0) (fun n => r n 2) (fun n => theta n 2)
    d (theta0 3) (theta0 0) 1 hepst (hrat 3) (htat 3) (hrat 0) (hrat 2) (htat 0) ht2
    hd hr02 hwidth hne (hbound 3 0)
  have habs : |theta0 0-theta0 3|=h := by rw [abs_sub_comm]; exact hgapAbs
  have hJt : Tendsto (fun n =>
      (physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2)-
        physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0))/d n)
      atTop (𝓝 (9/4 : ℝ)) := by simpa only [one_mul,habs,kappa_h] using hJ
  have hmass3 := (normalized_complete_lower_triple_mass_vanishes eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple).2
  have hradNear : ∀ᶠ n in atTop,∀ i : Satellite,r n i≤2 := by
    apply (eventually_all).mpr
    intro i
    exact (hrat i).eventually (Iio_mem_nhds (by norm_num : (1 : ℝ)<2)) |>.mono (fun _ hi => hi.le)
  have hsincNear (i j : TripleLabel) : ∀ᶠ n in atTop,0≤Real.sinc (theta n j.castSucc-theta n i.castSucc) := by
    have ht : Tendsto (fun n => Real.sinc (theta n j.castSucc-theta n i.castSucc)) atTop (𝓝 1) := by
      simpa only [Function.comp_def,Real.sinc_zero] using Real.continuous_sinc.continuousAt.tendsto.comp (hgap i j)
    exact (ht.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ)<1))).mono (fun _ hi => hi.le)
  refine ⟨(9/128)*eta^3,by positivity,?_⟩
  filter_upwards [hcomparable,hradNear,hsincNear 0 1,hsincNear 0 2,hsincNear 1 2,
    hJt.eventually (Ioi_mem_nhds (by norm_num : (9/8 : ℝ)<9/4)),
    hwidth.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ)<2)),
    hmass3.eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1))]
      with n hcomp hrad hs01 hs02 hs12 hJN hWN hm3
  have hco (i j : TripleLabel) (hij : i≠j)
      (hs : 0≤Real.sinc (theta n j.castSucc-theta n i.castSucc)) :
      tripleAngularCoefficient (eps n) (r n) (theta n) i.castSucc j.castSucc≤4/(eta^3*d n^3) := by
    apply tripleAngularCoefficient_upper_comparable _ _ _ _ _ _ _ (heps n).le (hd n) heta
      (hr n _) (hr n _) (hrad _) (hrad _) hs
    simpa only [d,hpolar n] using hcomp i j hij
  have hW : 0<theta n 2-theta n 0 := (horder n 0 2 (by decide)).1
  have hJlower : (9/16 : ℝ)*(theta n 2-theta n 0)≤
      physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2)-
        physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0) := by
    have h1 := (le_div_iff₀ (hd n)).mp hJN.le
    have h2 := (div_le_iff₀ (hd n)).mp hWN.le
    linarith
  have hroots := (polarResiduals_zero_of_normalized (eps n) (mu n) (x n) (hx n)
    (hm n) (heps n) (r n) (theta n) (hr n) (hpolar n)).2
  have hlow := triple_mass_cube_lower_of_extreme_rows (eps n) (d n) eta (9/16) (mu n) (r n) (theta n)
    (hm n) (hd n) heta (horder n 0 1 (by decide)).1 (horder n 1 2 (by decide)).1
    (hco 0 1 (by decide) hs01) (hco 0 2 (by decide) hs02) (hco 1 2 (by decide) hs12) hroots hJlower
  have hc : (9/128)*eta^3≤((9/16)*eta^3/4)*mu n 3 := by
    have hh := mul_le_mul_of_nonneg_left hm3.le (by positivity : 0≤(9/16 : ℝ)*eta^3/4)
    convert! hh using 1
    ring
  exact hc.trans hlow

end DominantFiveBody
