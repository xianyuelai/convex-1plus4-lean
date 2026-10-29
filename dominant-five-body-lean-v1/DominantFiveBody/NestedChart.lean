import DominantFiveBody.PairChart

/-! # Actual nested-triple coordinates and physical rows

Source: §5.4, nest-masses, nest-coordinates, nest-rows, nest-recovery.
Labels 0,1 form the inner pair, label 2 the third member, label 3 the
exterior. Parameters ε,t,η,α are independent. The coordinates here are
polynomial at every signed scale; the physical divided rows require tη≠0.
-/

noncomputable section
open scoped BigOperators Matrix

namespace DominantFiveBody

abbrev NestedChartVariables := Fin 7 → ℝ
abbrev NestedChartParameters := Fin 4 → ℝ
abbrev NestedJointVariables := NestedChartParameters × NestedChartVariables

def nestedChartMass (t eta alpha : ℝ) : MassRatio :=
  ![t^3*eta^3*alpha,t^3*eta^3*(1-alpha),t^3*(1-eta^3),1-t^3]

def nestedCoordinates (t eta alpha R u v : ℝ) : Fin 3 → ℝ :=
  ![R-(1-eta^3)*t*u-(1-alpha)*t*eta*v,
    R-(1-eta^3)*t*u+alpha*t*eta*v,R+eta^3*t*u]

def nestedChartRadii (t eta alpha : ℝ) (y : NestedChartVariables) : Satellite → ℝ :=
  let r := nestedCoordinates t eta alpha (y 1) (y 2) (y 3)
  ![r 0,r 1,r 2,y 0]

def nestedChartAngles (t eta alpha : ℝ) (y : NestedChartVariables) : Satellite → ℝ :=
  let theta := nestedCoordinates t eta alpha (y 4) (y 5) (y 6)
  ![theta 0,theta 1,theta 2,0]

def nestedChartPoints (t eta alpha : ℝ) (y : NestedChartVariables) : SatelliteConfiguration :=
  polarSatellites (nestedChartRadii t eta alpha y) (nestedChartAngles t eta alpha y)

theorem nestedChartMass_sum (t eta alpha : ℝ) : ∑ i, nestedChartMass t eta alpha i=1 := by
  simp [Fin.sum_univ_four,nestedChartMass]
  ring

theorem nestedChartMass_positive (t eta alpha : ℝ) (ht : 0<t) (ht1 : t<1)
    (he : 0<eta) (he1 : eta<1) (ha : 0<alpha) (ha1 : alpha<1) :
    PositiveRatio (nestedChartMass t eta alpha) := by
  refine ⟨?_,nestedChartMass_sum t eta alpha⟩
  have ht3 : t^3<1 := by nlinarith [pow_pos ht 2, sq_nonneg (t-1)]
  have he3 : eta^3<1 := by nlinarith [pow_pos he 2, sq_nonneg (eta-1)]
  intro i
  fin_cases i
  · change 0<t^3*eta^3*alpha
    positivity
  · change 0<t^3*eta^3*(1-alpha)
    positivity
  · change 0<t^3*(1-eta^3)
    positivity
  · change 0<1-t^3
    linarith

def nestedPairAverage (alpha : ℝ) (rows : Satellite → ℝ) : ℝ :=
  alpha*rows 0+(1-alpha)*rows 1

def nestedRowAverage (eta alpha : ℝ) (rows : Satellite → ℝ) : ℝ :=
  eta^3*nestedPairAverage alpha rows+(1-eta^3)*rows 2

def nestedRowOuterDifference (t alpha : ℝ) (rows : Satellite → ℝ) : ℝ :=
  (rows 2-nestedPairAverage alpha rows)/t

def nestedRowInnerDifference (t eta : ℝ) (rows : Satellite → ℝ) : ℝ :=
  (rows 1-rows 0)/(t*eta)

/-- Both endpoint mass fractions are retained by the algebraic inverse. -/
theorem nestedRows_recovery (t eta alpha : ℝ) (rows : Satellite → ℝ)
    (ht : t≠0) (he : eta≠0) :
    nestedPairAverage alpha rows=nestedRowAverage eta alpha rows-
      (1-eta^3)*t*nestedRowOuterDifference t alpha rows ∧
    rows 2=nestedRowAverage eta alpha rows+eta^3*t*nestedRowOuterDifference t alpha rows ∧
    rows 0=nestedPairAverage alpha rows-(1-alpha)*t*eta*nestedRowInnerDifference t eta rows ∧
    rows 1=nestedPairAverage alpha rows+alpha*t*eta*nestedRowInnerDifference t eta rows := by
  dsimp [nestedPairAverage,nestedRowAverage,nestedRowOuterDifference,nestedRowInnerDifference]
  refine ⟨?_,?_,?_,?_⟩ <;> field_simp <;> ring

theorem nestedRows_zero_iff (t eta alpha : ℝ) (rows : Satellite → ℝ)
    (ht : t≠0) (he : eta≠0) :
    nestedRowAverage eta alpha rows=0 ∧ nestedRowOuterDifference t alpha rows=0 ∧
      nestedRowInnerDifference t eta rows=0 ↔ rows 0=0 ∧ rows 1=0 ∧ rows 2=0 := by
  constructor
  · rintro ⟨hA,hB,hC⟩
    obtain ⟨h0,h2,ha,hb⟩ := nestedRows_recovery t eta alpha rows ht he
    simp only [hA,hB,hC,mul_zero,sub_zero,add_zero] at h0 h2 ha hb
    exact ⟨ha.trans h0,hb.trans h0,h2⟩
  · rintro ⟨ha,hb,hc⟩
    simp [nestedRowAverage,nestedPairAverage,nestedRowOuterDifference,nestedRowInnerDifference,ha,hb,hc]

def nestedCoordinateMatrix (t eta alpha : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,-(1-eta^3)*t,-(1-alpha)*t*eta;
     1,-(1-eta^3)*t,alpha*t*eta;
     1,eta^3*t,0]

theorem nestedCoordinateMatrix_det (t eta alpha : ℝ) :
    (nestedCoordinateMatrix t eta alpha).det= -(t^2*eta) := by
  rw [nestedCoordinateMatrix,Matrix.det_fin_three]
  simp
  ring

theorem nestedCoordinateMatrix_isUnit (t eta alpha : ℝ) (ht : t≠0) (he : eta≠0) :
    IsUnit (nestedCoordinateMatrix t eta alpha) := by
  rw [Matrix.isUnit_iff_isUnit_det,nestedCoordinateMatrix_det,isUnit_iff_ne_zero]
  exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 ht) he)

theorem nestedCoordinates_recovery (t eta alpha R u v : ℝ) (ht : t≠0) (he : eta≠0) :
    let r : Satellite → ℝ := ![nestedCoordinates t eta alpha R u v 0,
      nestedCoordinates t eta alpha R u v 1,nestedCoordinates t eta alpha R u v 2,0]
    nestedRowAverage eta alpha r=R ∧ nestedRowOuterDifference t alpha r=u ∧
      nestedRowInnerDifference t eta r=v := by
  dsimp [nestedCoordinates,nestedRowAverage,nestedPairAverage,nestedRowOuterDifference,nestedRowInnerDifference]
  refine ⟨?_,?_,?_⟩ <;> field_simp <;> ring

def nestedChartPhysicalRows (eps t eta alpha : ℝ) (y : NestedChartVariables) : NestedChartVariables :=
  let R := radialResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
    (nestedChartAngles t eta alpha y)
  let T := angularResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
    (nestedChartAngles t eta alpha y)
  ![R 3,nestedRowAverage eta alpha R,nestedRowOuterDifference t alpha R,
    nestedRowInnerDifference t eta R,nestedRowAverage eta alpha T,
    nestedRowOuterDifference t alpha T,nestedRowInnerDifference t eta T]

/-- The only mass divided out is the explicitly nonzero exterior mass. -/
theorem nestedChartPhysicalRows_zero_iff (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : t≠0) (he : eta≠0) (hp : 1-t^3≠0) :
    nestedChartPhysicalRows eps t eta alpha y=0 ↔
      (∀ i, radialResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
        (nestedChartAngles t eta alpha y) i=0) ∧
      (∀ i, angularResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
        (nestedChartAngles t eta alpha y) i=0) := by
  let R := radialResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
    (nestedChartAngles t eta alpha y)
  let T := angularResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
    (nestedChartAngles t eta alpha y)
  change nestedChartPhysicalRows eps t eta alpha y=0 ↔ (∀ i,R i=0) ∧ ∀ i,T i=0
  constructor
  · intro h
    have hRp : R 3=0 := congrFun h 0
    have hRA : nestedRowAverage eta alpha R=0 := congrFun h 1
    have hRB : nestedRowOuterDifference t alpha R=0 := congrFun h 2
    have hRC : nestedRowInnerDifference t eta R=0 := congrFun h 3
    have hTA : nestedRowAverage eta alpha T=0 := congrFun h 4
    have hTB : nestedRowOuterDifference t alpha T=0 := congrFun h 5
    have hTC : nestedRowInnerDifference t eta T=0 := congrFun h 6
    have hR := (nestedRows_zero_iff t eta alpha R ht he).mp ⟨hRA,hRB,hRC⟩
    have hT := (nestedRows_zero_iff t eta alpha T ht he).mp ⟨hTA,hTB,hTC⟩
    have hother : ∀ i : Satellite, i≠3 → T i=0 := by
      intro i hi
      fin_cases i
      · exact hT.1
      · exact hT.2.1
      · exact hT.2.2
      · exact (hi rfl).elim
    have hTp : T 3=0 := angularResidual_omitted_row eps (nestedChartMass t eta alpha)
      (nestedChartRadii t eta alpha y) (nestedChartAngles t eta alpha y) 3 hp hother
    constructor
    · intro i
      fin_cases i
      · exact hR.1
      · exact hR.2.1
      · exact hR.2.2
      · exact hRp
    · intro i
      by_cases hi : i=3
      · simpa only [hi] using hTp
      · exact hother i hi
  · rintro ⟨hR,hT⟩
    have hRfun : R=0 := funext hR
    have hTfun : T=0 := funext hT
    change (![R 3,nestedRowAverage eta alpha R,nestedRowOuterDifference t alpha R,
      nestedRowInnerDifference t eta R,nestedRowAverage eta alpha T,
      nestedRowOuterDifference t alpha T,nestedRowInnerDifference t eta T] : NestedChartVariables)=0
    rw [hRfun,hTfun]
    ext i
    fin_cases i <;> simp [nestedRowAverage,nestedPairAverage,nestedRowOuterDifference,nestedRowInnerDifference]

end DominantFiveBody
