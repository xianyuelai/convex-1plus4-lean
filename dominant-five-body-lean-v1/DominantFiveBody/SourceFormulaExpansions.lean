import DominantFiveBody.CollisionNestedRectangleControls
import DominantFiveBody.BackgroundSlow
import DominantFiveBody.TripleScalarSeed
import DominantFiveBody.NestedSlowCoordinates

/-! Literal source formulas, tied to the actual fields and their derivatives.
These statements do not introduce surrogate residuals. -/
noncomputable section
open scoped BigOperators ContDiff
namespace DominantFiveBody

theorem strictConvex_primaryRelative_all_edges (x : Configuration) (sigma : HullOrder)
    (hconv : StrictConvexInOrder sigma x) (k j : Label) (hjk : j≠k) (hjn : j≠k+1) :
    0 < det2 (primaryRelative x (sigma.labels (k+1))-primaryRelative x (sigma.labels k))
      (primaryRelative x (sigma.labels j)-primaryRelative x (sigma.labels k)) := by
  simpa only [primaryRelative,sub_sub_sub_cancel_right,orientedArea] using hconv k j hjk hjn

theorem pairExteriorFields_source_formulas (mu r theta : Satellite → ℝ)
    (q : SatelliteConfiguration) (a b : Satellite) (x : Plane) (rho v : ℝ) :
    pairExteriorField mu q a b x =
      ∑ j ∈ pairExteriorLabels a b,(mu j / ‖q j-x‖^3) • (q j-x) ∧
    physicalPairExteriorAngularField mu r theta a b rho v =
      ∑ j ∈ pairExteriorLabels a b,mu j*r j*Real.sin (theta j-v)*
        ((‖polarPoint rho v-polarPoint (r j) (theta j)‖^3)⁻¹-(r j^3)⁻¹) := by
  constructor
  · simp only [pairExteriorField,norm_sub_rev x]
  · rfl

theorem pairExteriorAngular_source_derivatives (mu r theta : Satellite → ℝ)
    (a b : Satellite) (rho v : ℝ) (hr : ∀ i,0<r i)
    (hsep : ∀ j∈pairExteriorLabels a b,polarPoint (r j) (theta j)≠polarPoint rho v) :
    deriv (fun s => physicalPairExteriorAngularField mu r theta a b s v) rho =
      -3 * ∑ j∈pairExteriorLabels a b,mu j*r j*Real.sin (theta j-v)*
        (rho-r j*Real.cos (theta j-v)) *
          (‖polarPoint rho v-polarPoint (r j) (theta j)‖^5)⁻¹ ∧
    deriv (fun w => physicalPairExteriorAngularField mu r theta a b rho w) v =
      ∑ j∈pairExteriorLabels a b,mu j*r j*
        (-Real.cos (theta j-v)*
          ((‖polarPoint rho v-polarPoint (r j) (theta j)‖^3)⁻¹-(r j^3)⁻¹)+
          3*rho*r j*(Real.sin (theta j-v))^2*
            (‖polarPoint rho v-polarPoint (r j) (theta j)‖^5)⁻¹) := by
  obtain ⟨hR,hV⟩ := physicalPairExteriorAngularField_named_derivatives mu r theta a b rho v hr hsep
  constructor
  · rw [hR.deriv,physicalPairExteriorAngularRadialDerivative,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold physicalSourceAngularRadialDerivative
    ring
  · rw [hV.deriv,physicalPairExteriorAngularAngularDerivative]
    apply Finset.sum_congr rfl
    intro j _
    unfold physicalSourceAngularAngularDerivative
    ring

theorem tripleExteriorJ_source_formula (eps s angle rho v : ℝ) :
    physicalSourceFullAngularField eps s angle rho v =
      rho*s*Real.sin (angle-v)*
        ((‖polarPoint rho v-polarPoint s angle‖^3)⁻¹-(1+eps)⁻¹) := rfl

theorem backgroundProbeField_source_formula (eps : ℝ) (q : Plane) :
    backgroundProbeField eps q = q-(‖q‖^3)⁻¹ • q +
      (eps/‖backgroundExterior eps-q‖^3) • (backgroundExterior eps-q)-
      (eps/backgroundRadius eps^3) • backgroundExterior eps := by
  simp only [backgroundProbeField,newtonTargetField,zero_sub,norm_neg,smul_neg,
    ← sub_eq_add_neg,div_eq_mul_inv,smul_smul]

theorem scalarSlow_source_equations (omega s : TripleVector)
    (hm : TripleWeights omega) (hs : TripleOrdered s)
    (hroot : ∀ i,tripleScalarResidual omega s i=0) :
    (∀ i,tripleD0*s i-∑ j∈Finset.univ.erase i,
      omega j*(s i-s j)/|s i-s j|^3=0) ∧
    (∀ i j,i≠j → s i≠s j) ∧ (∑ i,omega i*s i=0) ∧ ∑ i,omega i=1 := by
  refine ⟨?_,tripleOrdered_distinct hs,tripleScalar_root_weighted_center omega s hroot,hm.2⟩
  intro i
  simpa only [tripleScalarResidual,tripleScalarForce,mul_div_assoc] using hroot i

theorem scalarSlow_positive_seed (omega : TripleVector)
    (hm : ∀ i,0<omega i) (hsum : ∑ i,omega i=1) :
    ∃ s : TripleVector,TripleOrdered s ∧
      (∀ i,tripleD0*s i-∑ j∈Finset.univ.erase i,
        omega j*(s i-s j)/|s i-s j|^3=0) ∧
      (∀ i j,i≠j → s i≠s j) ∧ (∑ i,omega i*s i=0) ∧ ∑ i,omega i=1 := by
  obtain ⟨s,hs,hr⟩ := tripleScalar_positive_root_exists omega hm hsum
  exact ⟨s,hs,scalarSlow_source_equations omega s ⟨fun i => (hm i).le,hsum⟩ hs hr⟩

end DominantFiveBody
