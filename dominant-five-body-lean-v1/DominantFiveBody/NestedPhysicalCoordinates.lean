import DominantFiveBody.NestedHessian
import DominantFiveBody.TriplePhysicalCoordinates

/-! # Explicit physical inverse coordinates for the nested chart

The two scales are the cube roots of the current total cluster mass
and of the current inner-pair fraction. The coordinate inverse uses
the actual two weighted means and the two divided differences.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
namespace DominantFiveBody
set_option maxHeartbeats 800000

def nestedVariablesFromPolar (t eta alpha : ℝ) (r theta : Satellite → ℝ) : NestedChartVariables :=
  nestedFromFixedSlice t eta alpha (tripleRawSlice r theta)

theorem nestedVariablesFromPolar_eq (t eta alpha : ℝ) (r theta : Satellite → ℝ) :
    nestedVariablesFromPolar t eta alpha r theta=
      ![r 3,nestedRowAverage eta alpha r,nestedRowOuterDifference t alpha r,
        nestedRowInnerDifference t eta r,nestedRowAverage eta alpha theta,
        nestedRowOuterDifference t alpha theta,nestedRowInnerDifference t eta theta] := by
  funext i
  fin_cases i
  all_goals simp [nestedVariablesFromPolar,nestedFromFixedSlice,nestedVariableProjection,
    tripleRawSlice,nestedRowAverage,nestedPairAverage,nestedRowOuterDifference,
    nestedRowInnerDifference,smul_eq_mul,div_eq_mul_inv]
  all_goals ring

theorem nestedVariablesFromPolar_radii (t eta alpha : ℝ) (r theta : Satellite → ℝ)
    (ht : t≠0) (heta : eta≠0) :
    nestedChartRadii t eta alpha (nestedVariablesFromPolar t eta alpha r theta)=r := by
  rw [← fixedAngleRadii_nestedToFixedSlice,nestedVariablesFromPolar,
    nestedToFixedSlice_nestedFromFixedSlice t eta alpha ht heta]
  funext i
  fin_cases i <;> rfl

theorem nestedVariablesFromPolar_angles (t eta alpha : ℝ) (r theta : Satellite → ℝ)
    (ht : t≠0) (heta : eta≠0) (hfixed : theta 3=0) :
    nestedChartAngles t eta alpha (nestedVariablesFromPolar t eta alpha r theta)=theta := by
  rw [← fixedAngleAngles_nestedToFixedSlice,nestedVariablesFromPolar,
    nestedToFixedSlice_nestedFromFixedSlice t eta alpha ht heta]
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact hfixed.symm

theorem nestedVariablesFromPolar_points (t eta alpha : ℝ) (r theta : Satellite → ℝ)
    (ht : t≠0) (heta : eta≠0) (hfixed : theta 3=0) :
    nestedChartPoints t eta alpha (nestedVariablesFromPolar t eta alpha r theta)=polarSatellites r theta := by
  rw [nestedChartPoints,nestedVariablesFromPolar_radii t eta alpha r theta ht heta,
    nestedVariablesFromPolar_angles t eta alpha r theta ht heta hfixed]

def nestedPhysicalInnerMass (mu : MassRatio) : ℝ := mu 0+mu 1
def nestedPhysicalScale (mu : MassRatio) : ℝ := triplePhysicalScale mu
def nestedPhysicalEta (mu : MassRatio) : ℝ :=
  Real.rpow (nestedPhysicalInnerMass mu/triplePhysicalClusterMass mu) (1/3)
def nestedPhysicalAlpha (mu : MassRatio) : ℝ := mu 0/nestedPhysicalInnerMass mu

theorem nestedPhysicalInnerMass_pos (mu : MassRatio) (hm : PositiveRatio mu) :
    0<nestedPhysicalInnerMass mu := add_pos (hm.1 0) (hm.1 1)

theorem nestedPhysicalEta_cube (mu : MassRatio) (hm : PositiveRatio mu) :
    nestedPhysicalEta mu^3=nestedPhysicalInnerMass mu/triplePhysicalClusterMass mu := by
  simpa [nestedPhysicalEta,one_div] using Real.rpow_inv_natCast_pow
    (div_pos (nestedPhysicalInnerMass_pos mu hm) (triplePhysicalClusterMass_pos mu hm)).le
    (by decide : (3 : ℕ)≠0)

theorem nestedPhysicalParameters_bounds (mu : MassRatio) (hm : PositiveRatio mu) :
    0<nestedPhysicalScale mu ∧ nestedPhysicalScale mu<1 ∧
    0<nestedPhysicalEta mu ∧ nestedPhysicalEta mu<1 ∧
    0<nestedPhysicalAlpha mu ∧ nestedPhysicalAlpha mu<1 := by
  have hp := nestedPhysicalInnerMass_pos mu hm
  have hc := triplePhysicalClusterMass_pos mu hm
  have hfrac : 0<nestedPhysicalInnerMass mu/triplePhysicalClusterMass mu := div_pos hp hc
  have hsum : nestedPhysicalInnerMass mu+mu 2=triplePhysicalClusterMass mu := by
    simp [nestedPhysicalInnerMass,triplePhysicalClusterMass,Fin.sum_univ_three]
  have hfrac1 : nestedPhysicalInnerMass mu/triplePhysicalClusterMass mu<1 :=
    (div_lt_one hc).mpr (by linarith [hm.1 2])
  have he : 0<nestedPhysicalEta mu := Real.rpow_pos_of_pos hfrac _
  have he1 : nestedPhysicalEta mu<1 := by
    have hcube := nestedPhysicalEta_cube mu hm
    by_contra hn
    have hle := le_of_not_gt hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg (nestedPhysicalEta mu))]
  have ht := triplePhysicalParameters_bounds mu hm
  refine ⟨ht.1,ht.2.1,he,he1,div_pos (hm.1 0) hp,?_⟩
  exact (div_lt_one hp).mpr (by unfold nestedPhysicalInnerMass; linarith [hm.1 1])

theorem nestedPhysicalParameters_mass (mu : MassRatio) (hm : PositiveRatio mu) :
    nestedChartMass (nestedPhysicalScale mu) (nestedPhysicalEta mu) (nestedPhysicalAlpha mu)=mu := by
  have hp := (nestedPhysicalInnerMass_pos mu hm).ne'
  have hc := (triplePhysicalClusterMass_pos mu hm).ne'
  have hsum : triplePhysicalClusterMass mu+mu 3=1 := by
    simpa [triplePhysicalClusterMass,Fin.sum_univ_three,Fin.sum_univ_four] using hm.2
  funext i
  fin_cases i
  all_goals simp [nestedChartMass,nestedPhysicalScale,triplePhysicalScale_cube mu hm,
    nestedPhysicalEta_cube mu hm,nestedPhysicalAlpha]
  all_goals first
    | solve | field_simp [hp,hc] <;> simp [nestedPhysicalInnerMass,triplePhysicalClusterMass,Fin.sum_univ_three] <;> ring
    | solve | linarith

theorem nestedVariablesFromPolar_regular (eps t eta alpha : ℝ) (r theta : Satellite → ℝ)
    (heps : 1+eps≠0) (ht : t≠0) (heta : eta≠0) (hr : ∀ i,0<r i)
    (hfixed : theta 3=0) (hcf : RelativeCollisionFree (polarSatellites r theta)) :
    NestedChartRegular eps t eta alpha (nestedVariablesFromPolar t eta alpha r theta) := by
  let y := nestedVariablesFromPolar t eta alpha r theta
  have hradii := nestedVariablesFromPolar_radii t eta alpha r theta ht heta
  have hpoints := nestedVariablesFromPolar_points t eta alpha r theta ht heta hfixed
  have hin : nestedInnerDirection t eta alpha y≠0 := by
    intro hzero
    have h := nestedInnerDirection_identity t eta alpha y
    rw [hzero,smul_zero,hpoints] at h
    exact hcf.2 1 0 (by decide) (sub_eq_zero.mp h)
  have hout (i : Fin 2) : nestedOuterDirection t eta alpha y i≠0 := by
    intro hzero
    have h := nestedOuterDirection_identity t eta alpha y i
    rw [hzero,smul_zero,hpoints] at h
    exact hcf.2 2 (i.castAdd 2) (by fin_cases i <;> decide) (sub_eq_zero.mp h)
  refine ⟨heps,?_,?_,?_,?_⟩
  · intro i
    rw [hradii]
    exact (hr i).ne'
  · rw [← nestedInnerDirection_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hin)
  · intro i
    rw [← nestedOuterDirection_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (hout i))
  · intro i
    rw [hpoints]
    exact hcf.2 3 i.castSucc (by fin_cases i <;> decide)

theorem nestedPhysicalCoordinates_root (eps : ℝ) (mu : MassRatio) (heps : 0<eps)
    (hm : PositiveRatio mu) (r theta : Satellite → ℝ) (hr : ∀ i,0<r i)
    (hfixed : theta 3=0) (hcf : RelativeCollisionFree (polarSatellites r theta))
    (hx : NormalizedCentralConfiguration (masses eps mu)
      (centeredFromRelative eps mu (polarSatellites r theta))) :
    nestedChartExtendedRows eps (nestedPhysicalScale mu) (nestedPhysicalEta mu) (nestedPhysicalAlpha mu)
      (nestedVariablesFromPolar (nestedPhysicalScale mu) (nestedPhysicalEta mu) (nestedPhysicalAlpha mu) r theta)=0 := by
  obtain ⟨ht,_,heta,_⟩ := nestedPhysicalParameters_bounds mu hm
  have hmass := nestedPhysicalParameters_mass mu hm
  have hradii := nestedVariablesFromPolar_radii (nestedPhysicalScale mu) (nestedPhysicalEta mu)
    (nestedPhysicalAlpha mu) r theta ht.ne' heta.ne'
  have hpoints := nestedVariablesFromPolar_points (nestedPhysicalScale mu) (nestedPhysicalEta mu)
    (nestedPhysicalAlpha mu) r theta ht.ne' heta.ne' hfixed
  have hreg := nestedVariablesFromPolar_regular eps (nestedPhysicalScale mu) (nestedPhysicalEta mu)
    (nestedPhysicalAlpha mu) r theta (by linarith) ht.ne' heta.ne' hr hfixed hcf
  apply (nestedChartExtendedRows_zero_iff_normalized _ _ _ _ _ heps ht heta
    (by rwa [hmass]) hreg (by intro i; rw [hradii]; exact hr i)).mpr
  simpa only [hmass,hpoints] using hx

end DominantFiveBody
