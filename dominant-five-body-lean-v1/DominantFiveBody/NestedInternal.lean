import DominantFiveBody.NestedKernelFormulas

/-! # Exact nested internal interaction rows

The physical masses cancel positive distance scales before extension.
Mean and difference identities retain α=0,1 and both scale faces.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

set_option maxHeartbeats 800000

def nestedInnerM (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  -pairInternalAngularDifference eps (t*eta) alpha (nestedInnerVariables t eta y)

def nestedInnerJ (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  pairInternalRadialMean eps (t*eta) alpha (nestedInnerVariables t eta y)

def nestedInnerJOverT (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  -eps*eta*alpha*(1-alpha)*(nestedChartRadii t eta alpha y 0+nestedChartRadii t eta alpha y 1)*
    singleScaleChi (t*eta) (y 6)*(nestedInnerW t eta alpha y^3)⁻¹

theorem nestedInnerM_formula (eps t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedInnerM eps t eta alpha y=nestedChartRadii t eta alpha y 0*nestedChartRadii t eta alpha y 1*
      y 6*Real.sinc (t*eta*y 6)*((nestedInnerW t eta alpha y^3)⁻¹-t^3*eta^3/(1+eps)) := by
  have ha := (nestedInner_coordinates t eta alpha y 0).1
  have hb := (nestedInner_coordinates t eta alpha y 1).1
  change pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartRadii t eta alpha y 0 at ha
  change pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartRadii t eta alpha y 1 at hb
  unfold nestedInnerM pairInternalAngularDifference
  rw [ha,hb]
  change -(-nestedChartRadii t eta alpha y 0*nestedChartRadii t eta alpha y 1*y 6*
    Real.sinc (t*eta*y 6)*((nestedInnerW t eta alpha y^3)⁻¹-(t*eta)^3/(1+eps)))=_
  ring

theorem nestedInnerJ_factor (eps t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedInnerJ eps t eta alpha y=t*nestedInnerJOverT eps t eta alpha y := by
  have ha := (nestedInner_coordinates t eta alpha y 0).1
  have hb := (nestedInner_coordinates t eta alpha y 1).1
  change pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartRadii t eta alpha y 0 at ha
  change pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartRadii t eta alpha y 1 at hb
  unfold nestedInnerJ pairInternalRadialMean
  rw [ha,hb]
  change -eps*(t*eta)*alpha*(1-alpha)*(nestedChartRadii t eta alpha y 0+nestedChartRadii t eta alpha y 1)*
    singleScaleChi (t*eta) (y 6)*(nestedInnerW t eta alpha y^3)⁻¹=_
  unfold nestedInnerJOverT
  ring

def nestedInternalRadial (eps t eta alpha : ℝ) (y : NestedChartVariables) : Satellite → ℝ :=
  ![eps*t*(1-eta^3)*nestedOuterN t eta alpha y 0+
      pairInternalRadialA eps (t*eta) alpha (nestedInnerVariables t eta y),
    eps*t*(1-eta^3)*nestedOuterN t eta alpha y 1+
      pairInternalRadialB eps (t*eta) alpha (nestedInnerVariables t eta y),
    -eps*t*eta^3*(alpha*nestedOuterO t eta alpha y 0+(1-alpha)*nestedOuterO t eta alpha y 1),0]

def nestedInternalAngular (eps t eta alpha : ℝ) (y : NestedChartVariables) : Satellite → ℝ :=
  ![t*(1-eta^3)*nestedOuterL eps t eta alpha y 0+
      pairInternalAngularA eps (t*eta) alpha (nestedInnerVariables t eta y),
    t*(1-eta^3)*nestedOuterL eps t eta alpha y 1+
      pairInternalAngularB eps (t*eta) alpha (nestedInnerVariables t eta y),
    -t*eta^3*(alpha*nestedOuterL eps t eta alpha y 0+(1-alpha)*nestedOuterL eps t eta alpha y 1),0]

def nestedInternalRadialMean (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  eps*t*eta^3*(1-eta^3)*(alpha*(nestedOuterN t eta alpha y 0-nestedOuterO t eta alpha y 0)+
    (1-alpha)*(nestedOuterN t eta alpha y 1-nestedOuterO t eta alpha y 1))+eta^3*nestedInnerJ eps t eta alpha y

def nestedInternalRadialOuterDifference (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  -eps*(eta^3*(alpha*nestedOuterO t eta alpha y 0+(1-alpha)*nestedOuterO t eta alpha y 1)+
    (1-eta^3)*(alpha*nestedOuterN t eta alpha y 0+(1-alpha)*nestedOuterN t eta alpha y 1))-
      nestedInnerJOverT eps t eta alpha y

def nestedInternalRadialInnerDifference (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  eps*(1-eta^3)*nestedOuterNDifference t eta alpha y+
    pairInternalRadialDifference eps (t*eta) alpha (nestedInnerVariables t eta y)

def nestedInternalAngularOuterDifference (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  -(alpha*nestedOuterL eps t eta alpha y 0+(1-alpha)*nestedOuterL eps t eta alpha y 1)

def nestedInternalAngularInnerDifference (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  (1-eta^3)*nestedOuterLDifference eps t eta alpha y-nestedInnerM eps t eta alpha y

theorem nestedInternalRadial_mean (eps t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedRowAverage eta alpha (nestedInternalRadial eps t eta alpha y)=
      nestedInternalRadialMean eps t eta alpha y := by
  have h := pairInternalRadial_mean_identity eps (t*eta) alpha (nestedInnerVariables t eta y)
  change _=nestedInnerJ eps t eta alpha y at h
  dsimp [nestedRowAverage,nestedPairAverage,nestedInternalRadial,nestedInternalRadialMean]
  linear_combination eta^3*h

theorem nestedInternalRadial_outer_difference (eps t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedInternalRadial eps t eta alpha y 2-nestedPairAverage alpha (nestedInternalRadial eps t eta alpha y)=
      t*nestedInternalRadialOuterDifference eps t eta alpha y := by
  have h := pairInternalRadial_mean_identity eps (t*eta) alpha (nestedInnerVariables t eta y)
  change _=nestedInnerJ eps t eta alpha y at h
  rw [nestedInnerJ_factor] at h
  dsimp [nestedInternalRadial,nestedPairAverage,nestedInternalRadialOuterDifference]
  linear_combination -h

theorem nestedInternalRadial_inner_difference (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (hV : ∀ i, 0<nestedOuterWSq t eta alpha y i) :
    nestedInternalRadial eps t eta alpha y 1-nestedInternalRadial eps t eta alpha y 0=
      (t*eta)*nestedInternalRadialInnerDifference eps t eta alpha y := by
  have hn := nestedOuterN_difference t eta alpha y hV
  have hi := pairInternalRadial_difference_identity eps (t*eta) alpha (nestedInnerVariables t eta y)
  dsimp [nestedInternalRadial,nestedInternalRadialInnerDifference]
  linear_combination eps*t*(1-eta^3)*hn+hi

theorem nestedInternalAngular_mean (eps t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedRowAverage eta alpha (nestedInternalAngular eps t eta alpha y)=0 := by
  have h := pairInternalAngular_mean_identity eps (t*eta) alpha (nestedInnerVariables t eta y)
  dsimp [nestedRowAverage,nestedPairAverage,nestedInternalAngular]
  linear_combination eta^3*h

theorem nestedInternalAngular_outer_difference (eps t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedInternalAngular eps t eta alpha y 2-nestedPairAverage alpha (nestedInternalAngular eps t eta alpha y)=
      t*nestedInternalAngularOuterDifference eps t eta alpha y := by
  have h := pairInternalAngular_mean_identity eps (t*eta) alpha (nestedInnerVariables t eta y)
  dsimp [nestedInternalAngular,nestedPairAverage,nestedInternalAngularOuterDifference]
  linear_combination -h

theorem nestedInternalAngular_inner_difference (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (hV : ∀ i, 0<nestedOuterWSq t eta alpha y i) :
    nestedInternalAngular eps t eta alpha y 1-nestedInternalAngular eps t eta alpha y 0=
      (t*eta)*nestedInternalAngularInnerDifference eps t eta alpha y := by
  have hn := nestedOuterL_difference eps t eta alpha y hV
  have hi := pairInternalAngular_difference_identity eps (t*eta) alpha (nestedInnerVariables t eta y)
  dsimp [nestedInternalAngular,nestedInternalAngularInnerDifference,nestedInnerM]
  linear_combination t*(1-eta^3)*hn+hi

end DominantFiveBody
