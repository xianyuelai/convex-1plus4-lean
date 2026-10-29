import DominantFiveBody.NestedAreas
import DominantFiveBody.NestedZeroFaces

/-! # Nested circle factor and the derivative along an actual root

The coefficient at eta=0 is z Z^2 / 2, positive for either sign of Z.
The epsilon-zero equations force unit radii even on signed scale faces;
all remaining coordinates are permitted to vary along the implicit root.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 800000

def nestedCircleAreaCoefficient (t eta alpha Z z : ℝ) : ℝ :=
  (z*(Z+(1-alpha)*eta*z)*(Z-alpha*eta*z)/2)*Real.sinc (t*eta*z/2)*
    Real.sinc (t*(Z+(1-alpha)*eta*z)/2)*Real.sinc (t*(Z-alpha*eta*z)/2)

theorem nestedCircleAreaCoefficient_zero (eta alpha Z z : ℝ) :
    nestedCircleAreaCoefficient 0 eta alpha Z z=z*(Z+(1-alpha)*eta*z)*(Z-alpha*eta*z)/2 := by
  simp [nestedCircleAreaCoefficient]

theorem nestedCircleAreaCoefficient_base (alpha Z z : ℝ) :
    nestedCircleAreaCoefficient 0 0 alpha Z z=z*Z^2/2 := by
  rw [nestedCircleAreaCoefficient_zero]
  ring

theorem nestedCircleAreaCoefficient_base_pos (alpha Z z : ℝ) (hZ : Z≠0) (hz : 0<z) :
    0<nestedCircleAreaCoefficient 0 0 alpha Z z := by
  rw [nestedCircleAreaCoefficient_base]
  exact div_pos (mul_pos hz (sq_pos_of_ne_zero hZ)) (by norm_num)

theorem nestedInternalAreaQuotient_eq_circle (t eta alpha : ℝ) (y : NestedChartVariables)
    (hu1 : y 2=0) (hu2 : y 3=0) (hr : ∀ i,nestedChartRadii t eta alpha y i=1) :
    nestedInternalAreaQuotient t eta alpha y=
      t*nestedCircleAreaCoefficient t eta alpha (y 5) (y 6) := by
  have hin : nestedInnerDirection t eta alpha y=nestedInnerUnitDirection t eta alpha y := by
    unfold nestedInnerDirection nestedInnerUnitDirection pairPointDirection
    have hb := (nestedInner_coordinates t eta alpha y 1).1
    change pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 1=
      nestedChartRadii t eta alpha y 1 at hb
    rw [hb,hr 1]
    simp [nestedInnerVariables,hu2]
  have hout : nestedOuterDirection t eta alpha y 0=nestedOuterUnitDirection t eta alpha y 0 := by
    unfold nestedOuterDirection nestedOuterUnitDirection pairPointDirection
    rw [(nestedOuter_coordinates t eta alpha y 0).2.1,hr 2]
    simp [nestedOuterVariables,nestedOuterRadialGaps,hu1,hu2]
  rw [nestedInternalAreaQuotient,hin,hout]
  unfold nestedInnerUnitDirection nestedOuterUnitDirection pairUnitDirection
  rw [det2_smul_left,det2_smul_right,det2_quarterTurn,unit_polar_det]
  dsimp [nestedInnerVariables,nestedOuterVariables,nestedOuterAngularGaps,
    nestedChartAngles,nestedCoordinates]
  have hm : y 4-(1-eta^3)*t*y 5-(1-alpha)*t*eta*y 6+
      (1-1/2)*t*(y 5+(1-alpha)*eta*y 6)-
      (y 4-(1-eta^3)*t*y 5+(alpha-1/2)*(t*eta)*y 6) =
        t*(y 5-alpha*eta*y 6)/2 := by ring
  rw [hm,← sinc_mul_argument]
  unfold nestedCircleAreaCoefficient
  ring

theorem nestedCircleAreaCoefficient_contDiff (n : ℕ∞ω) (eta alpha : ℝ) :
    ContDiff ℝ n (fun p : ℝ × (Fin 2 → ℝ) =>
      nestedCircleAreaCoefficient p.1 eta alpha (p.2 0) (p.2 1)) := by
  simp only [nestedCircleAreaCoefficient]
  fun_prop

theorem nestedAreaAlongZeroRoot_hasDerivAt (eta alpha : ℝ)
    (branch : ℝ → NestedChartVariables) (hsmooth : ContDiffAt ℝ 1 branch 0)
    (hroots : ∀ᶠ t in 𝓝 (0 : ℝ),nestedChartExtendedRows 0 t eta alpha (branch t)=0)
    (hradii : ∀ᶠ t in 𝓝 (0 : ℝ),∀ i,0<nestedChartRadii t eta alpha (branch t) i) :
    HasDerivAt (fun t => nestedInternalAreaQuotient t eta alpha (branch t))
      ((branch 0) 6*((branch 0) 5+(1-alpha)*eta*(branch 0) 6)*
        ((branch 0) 5-alpha*eta*(branch 0) 6)/2) 0 := by
  have hg : ContDiffAt ℝ 1 (fun t => (![branch t 5,branch t 6] : Fin 2 → ℝ)) 0 := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact (contDiffAt_pi.mp hsmooth) 5
    · exact (contDiffAt_pi.mp hsmooth) 6
  have hc := ((nestedCircleAreaCoefficient_contDiff 1 eta alpha).contDiffAt.comp 0
    (contDiffAt_id.prodMk hg)).differentiableAt (by norm_num : (1 : ℕ∞ω)≠0)
  have hd := (hasDerivAt_id (0 : ℝ)).mul hc.hasDerivAt
  have heq : (fun t => nestedInternalAreaQuotient t eta alpha (branch t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => t*nestedCircleAreaCoefficient t eta alpha (branch t 5) (branch t 6)) := by
    filter_upwards [hroots,hradii] with t hroot hr
    have hu := nestedChart_zero_eps_all_scale_faces t eta alpha (branch t) hr hroot
    exact nestedInternalAreaQuotient_eq_circle t eta alpha (branch t) hu.2.1 hu.2.2.1 hu.1
  have hd' := hd.congr_of_eventuallyEq heq
  simpa only [nestedCircleAreaCoefficient_zero,Matrix.cons_val_zero,Matrix.cons_val_one,
    one_mul,zero_mul,add_zero,Function.comp_apply,id_eq] using hd'

theorem nestedAreaAlongZeroRoot_base_deriv_pos (alpha : ℝ)
    (branch : ℝ → NestedChartVariables) (hsmooth : ContDiffAt ℝ 1 branch 0)
    (hroots : ∀ᶠ t in 𝓝 (0 : ℝ),nestedChartExtendedRows 0 t 0 alpha (branch t)=0)
    (hradii : ∀ᶠ t in 𝓝 (0 : ℝ),∀ i,0<nestedChartRadii t 0 alpha (branch t) i)
    (hZ : (branch 0) 5≠0) (hz : 0<(branch 0) 6) :
    0<deriv (fun t => nestedInternalAreaQuotient t 0 alpha (branch t)) 0 := by
  rw [(nestedAreaAlongZeroRoot_hasDerivAt 0 alpha branch hsmooth hroots hradii).deriv]
  have h : 0<(branch 0) 6*((branch 0) 5)^2/2 :=
    div_pos (mul_pos hz (sq_pos_of_ne_zero hZ)) (by norm_num)
  nlinarith

end DominantFiveBody
