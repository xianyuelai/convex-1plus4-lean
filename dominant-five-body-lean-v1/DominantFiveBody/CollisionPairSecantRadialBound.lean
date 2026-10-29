import DominantFiveBody.CollisionNestedPairSecant

/-! # A real pair radial bound from a bounded exterior Newton secant -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody

theorem physical_pair_radial_bound_of_exterior_secant_limit
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (r theta : ℕ → Satellite → ℝ)
    (a b : Satellite) (hab : a≠b) (heps : ∀ n,0≤eps n) (hm : ∀ n,PositiveRatio (mu n))
    (hr : ∀ n i,0<r n i) (hcf : ∀ n,RelativeCollisionFree (polarSatellites (r n) (theta n)))
    (hroot : ∀ n i,vectorResidual (eps n) (mu n) (polarSatellites (r n) (theta n)) i=0)
    (hlambda : Tendsto (fun n => eps n*(mu n a+mu n b)/
      satelliteDistance (polarSatellites (r n) (theta n)) a b^3) atTop (nhds 0))
    (hgap : Tendsto (fun n => theta n b-theta n a) atTop (nhds 0))
    (M : Plane)
    (hsec : Tendsto (fun n => pairSecantExteriorField (mu n) (polarSatellites (r n) (theta n)) a b
      (physicalPairDirection (polarSatellites (r n) (theta n)) a b)) atTop (nhds M)) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,|r n b-r n a|≤
      C*eps n*satelliteDistance (polarSatellites (r n) (theta n)) a b := by
  let B : ℝ := ‖M‖+1
  have hB : 0<B := by dsimp only [B]; linarith [norm_nonneg M]
  refine ⟨4*B,mul_pos (by norm_num) hB,?_⟩
  have hcost : Tendsto (fun n => Real.cos ((theta n b-theta n a)/2)) atTop (nhds 1) := by
    simpa only [Function.comp_def,zero_div,Real.cos_zero] using
      Real.continuous_cos.continuousAt.tendsto.comp (hgap.div_const 2)
  filter_upwards [hlambda.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2)),
    hcost.eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1)),
    hsec.norm.eventually (Iio_mem_nhds (by linarith : ‖M‖<B))] with n hnLambda hnCos hnSec
  let q : SatelliteConfiguration := polarSatellites (r n) (theta n)
  let s : ℝ := satelliteDistance q a b
  let sigma : ℝ := 1-(mu n a+mu n b)
  have hs : 0<s := norm_pos_iff.mpr (sub_ne_zero.mpr ((hcf n).2 a b hab))
  have hsigma : 0<sigma := pairExteriorMass_pos (mu n) (hm n) a b hab
  have hdiff : pairExteriorField (mu n) q a b (q b)-pairExteriorField (mu n) q a b (q a)=
      s • pairSecantExteriorField (mu n) q a b (physicalPairDirection q a b) := by
    have ht := congrArg (fun z : Plane => s • z) (physical_pair_exterior_secant (mu n) q a b (hcf n) hab)
    simpa only [show satelliteDistance q a b=s from rfl,smul_smul,mul_inv_cancel₀ (ne_of_gt hs),one_smul] using ht
  have hP : ‖pairExteriorField (mu n) q a b (q b)-pairExteriorField (mu n) q a b (q a)‖≤
      (B/sigma)*sigma*s := by
    rw [hdiff,norm_smul,Real.norm_eq_abs,abs_of_pos hs,div_mul_cancel₀ B (ne_of_gt hsigma)]
    exact (mul_le_mul_of_nonneg_left hnSec.le hs.le).trans_eq (mul_comm s B)
  have hbound := physical_pair_radial_bound (eps n) (B/sigma) (mu n) (r n) (theta n) a b hab (hr n)
    (heps n) (hroot n) hnLambda.le hnCos.le hP
  calc
    |r n b-r n a|≤4*(B/sigma)*eps n*sigma*s := hbound
    _=(4*B)*eps n*s := by field_simp [ne_of_gt hsigma]

end DominantFiveBody
