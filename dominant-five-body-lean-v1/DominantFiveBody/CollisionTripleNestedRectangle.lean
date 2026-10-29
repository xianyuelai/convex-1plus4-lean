import DominantFiveBody.CollisionNestedRectangle

/-! # Actual uniform polar-rectangle limits for the nested lower triple -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1500000

theorem physicalSourceAngularRadialDerivative_unit_h (angle psi : ℝ) (hgap : angle-psi=h) :
    physicalSourceAngularRadialDerivative 1 angle 1 psi= -3*Real.sqrt 3/4 := by
  have hh : (psi-angle)/2= -(Real.pi/6) := by unfold h at hgap; linarith
  have hnormsq := polar_distance_sq 1 1 angle psi
  rw [hh,Real.sin_neg,Real.sin_pi_div_six] at hnormsq
  norm_num at hnormsq
  have hnorm : ‖polarPoint 1 psi-polarPoint 1 angle‖=1 := by
    rcases hnormsq with he|he
    · exact he
    · nlinarith [norm_nonneg (polarPoint 1 psi-polarPoint 1 angle)]
  unfold physicalSourceAngularRadialDerivative
  rw [hgap,hnorm]
  simp only [h,Real.sin_pi_div_three,Real.cos_pi_div_three,one_pow,inv_one,mul_one,one_mul]
  ring

theorem normalized_complete_lower_triple_nested_rectangle_uniform_limits
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder standardHullOrder (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,OrderedSemicircle (theta n))
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htt : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (a b c : TripleLabel) (hab : a<b) (hca : c≠a) (hcb : c≠b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc/
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,
      ∀ rho∈uIcc (r n a.castSucc) (r n b.castSucc),∀ v∈uIcc (theta n a.castSucc) (theta n b.castSucc),
      |mu n c.castSucc*physicalSourceAngularRadialDerivative (r n c.castSucc) (theta n c.castSucc) rho v+
        mu n 3*physicalSourceAngularRadialDerivative (r n 3) (theta n 3) rho v+3*Real.sqrt 3/4|<eta ∧
      |mu n c.castSucc*physicalSourceAngularAngularDerivative (r n c.castSucc) (theta n c.castSucc) rho v+
        mu n 3*physicalSourceAngularAngularDerivative (r n 3) (theta n 3) rho v-(27/4 : ℝ)|<eta := by
  have hfull := normalized_complete_lower_triple_nested_precise_scales eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  have hdir := normalized_complete_lower_triple_nested_directions eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  have hrad := normalized_complete_lower_triple_nested_radial_limits eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab.ne hca hcb hpair
  obtain ⟨hrt,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (𝓝 1) :=
    (continuous_apply i).continuousAt.tendsto.comp hrt
  have htat (i : TripleLabel) : Tendsto (fun n => theta n i.castSucc) atTop (𝓝 (theta0 0)) := by
    have he := complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple i 0
    simpa only [Function.comp_def,he,show (0 : TripleLabel).castSucc=(0 : Satellite) from rfl] using
      (continuous_apply i.castSucc).continuousAt.tendsto.comp htt
  have htp : Tendsto (fun n => theta n 3) atTop (𝓝 (theta0 3)) :=
    (continuous_apply (3 : Satellite)).continuousAt.tendsto.comp htt
  have hgapAbs := (normalized_complete_triple_limiting_exterior eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt 3 center htriple).2 0 (by decide)
  have hgapEq : theta0 3-theta0 0=h := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hmono (by decide : (0 : Satellite)≤3)))] at hgapAbs
    exact hgapAbs
  have hne : theta0 3≠theta0 0 := by
    intro he
    rw [he,sub_self] at hgapEq
    have hh : 0<h := by unfold h; positivity
    linarith
  have hpi : |theta0 3-theta0 0|<Real.pi := by rw [hgapAbs]; unfold h; linarith [Real.pi_pos]
  have hmp := (normalized_complete_lower_triple_mass_vanishes eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple).2
  have hq0 : qLimit 0=center := (htriple 0).mpr (by decide)
  have hdt := tripleLowDiameter_tendsto_zero _ qLimit hqt
    (((htriple 1).mpr (by decide)).trans hq0.symm)
    (((htriple 2).mpr (by decide)).trans hq0.symm)
  have homega : (lowNestedOrientation a c)^2=1 := by
    unfold lowNestedOrientation
    split_ifs <;> norm_num
  have ht := physical_nested_polar_rectangle_derivatives_uniform
    (fun n => mu n c.castSucc) (fun n => mu n 3)
    (fun n => r n c.castSucc) (fun n => theta n c.castSucc) (fun n => r n 3) (fun n => theta n 3)
    (fun n => r n a.castSucc) (fun n => theta n a.castSucc) (fun n => r n b.castSucc) (fun n => theta n b.castSucc)
    (fun n => tripleLowDiameter (satellitesRelative (x n))) (theta0 0) (theta0 3) (lowNestedOrientation a c)
    (9/4) 1 (hrat c.castSucc) (hrat 3) (hrat a.castSucc) (hrat b.castSucc) (htat c) htp (htat a) (htat b)
    (fun n => tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1)) hdt homega
    (hrad a b) hdir.2.1 (hrad a c) (hdir.2.2.1 a (by simp)) hfull.2.2.2.2.2.1 hmp hne hpi
  have habs : |theta0 0-theta0 3|=h := by rw [abs_sub_comm]; exact hgapAbs
  simpa only [physicalSourceAngularRadialDerivative_unit_h _ _ hgapEq,habs,kappa_h,one_mul,
    show -3*Real.sqrt 3/4= -(3*Real.sqrt 3/4) by ring,
    sub_neg_eq_add,show (2 : ℝ)*(9/4)+9/4=27/4 by norm_num] using ht

end DominantFiveBody
