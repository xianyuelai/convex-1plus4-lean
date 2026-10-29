import DominantFiveBody.SingleScaleKernel
import DominantFiveBody.ResidualEquivalence

/-! # The actual complete-pair chart coordinates and rows

Source: §5.2 `eq:pair-chart-mass`, `eq:pair-coordinates` and row recovery.
Satellite labels 0,1 are a,b and 2,3 are c,d. The seven variables are
(ρc,ρd,R,u,ω,ψ,z). The physical divided rows below are used only for t≠0;
their extension at t=0 is a separate proof, not Lean's total division value.
-/

noncomputable section
open scoped BigOperators Matrix

namespace DominantFiveBody

abbrev PairChartVariables := Fin 7 → ℝ

def pairChartMass (t p alpha : ℝ) : MassRatio :=
  ![t^3*alpha,t^3*(1-alpha),(1-t^3)*p,(1-t^3)*(1-p)]

def pairChartRadii (t alpha : ℝ) (y : PairChartVariables) : Satellite → ℝ :=
  ![y 2-(1-alpha)*t*y 3,y 2+alpha*t*y 3,y 0,y 1]

def pairChartAngles (t alpha : ℝ) (y : PairChartVariables) : Satellite → ℝ :=
  ![y 5-(1-alpha)*t*y 6,y 5+alpha*t*y 6,0,y 4]

theorem pairChartMass_sum (t p alpha : ℝ) : ∑ i, pairChartMass t p alpha i=1 := by
  simp [Fin.sum_univ_four, pairChartMass]
  ring

def pairCoordinateMatrix (t alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,-(1-alpha)*t;1,alpha*t]

def pairMeanDifferenceMatrix (t alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![alpha,1-alpha;-(t⁻¹),t⁻¹]

theorem pairCoordinateMatrix_det (t alpha : ℝ) : (pairCoordinateMatrix t alpha).det=t := by
  rw [pairCoordinateMatrix, Matrix.det_fin_two]
  simp
  ring

theorem pairMeanDifferenceMatrix_det (t alpha : ℝ) : (pairMeanDifferenceMatrix t alpha).det=t⁻¹ := by
  rw [pairMeanDifferenceMatrix, Matrix.det_fin_two]
  simp
  ring

theorem pairCoordinateMatrix_isUnit (t alpha : ℝ) (ht : t≠0) :
    IsUnit (pairCoordinateMatrix t alpha) := by
  rw [Matrix.isUnit_iff_isUnit_det, pairCoordinateMatrix_det, isUnit_iff_ne_zero]
  exact ht

theorem pairMeanDifferenceMatrix_isUnit (t alpha : ℝ) (ht : t≠0) :
    IsUnit (pairMeanDifferenceMatrix t alpha) := by
  rw [Matrix.isUnit_iff_isUnit_det, pairMeanDifferenceMatrix_det, isUnit_iff_ne_zero]
  exact inv_ne_zero ht

theorem pairChartRadii_recovery (t alpha : ℝ) (y : PairChartVariables) (ht : t≠0) :
    alpha*pairChartRadii t alpha y 0+(1-alpha)*pairChartRadii t alpha y 1=y 2 ∧
      (pairChartRadii t alpha y 1-pairChartRadii t alpha y 0)/t=y 3 := by
  simp only [pairChartRadii, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · ring
  · field_simp
    ring

theorem pairChartAngles_recovery (t alpha : ℝ) (y : PairChartVariables) (ht : t≠0) :
    alpha*pairChartAngles t alpha y 0+(1-alpha)*pairChartAngles t alpha y 1=y 5 ∧
      (pairChartAngles t alpha y 1-pairChartAngles t alpha y 0)/t=y 6 := by
  simp only [pairChartAngles, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · ring
  · field_simp
    ring

def pairRowAverage (alpha : ℝ) (rows : Satellite → ℝ) : ℝ :=
  alpha*rows 0+(1-alpha)*rows 1

def pairRowDifference (t : ℝ) (rows : Satellite → ℝ) : ℝ := (rows 1-rows 0)/t

/-- Endpoint-safe recovery: no α or 1−α denominator appears. -/
theorem pairRows_recovery (t alpha : ℝ) (rows : Satellite → ℝ) (ht : t≠0) :
    rows 0=pairRowAverage alpha rows-(1-alpha)*t*pairRowDifference t rows ∧
      rows 1=pairRowAverage alpha rows+alpha*t*pairRowDifference t rows := by
  unfold pairRowAverage pairRowDifference
  constructor <;> field_simp <;> ring

theorem pairRows_zero_iff (t alpha : ℝ) (rows : Satellite → ℝ) (ht : t≠0) :
    pairRowAverage alpha rows=0 ∧ pairRowDifference t rows=0 ↔ rows 0=0 ∧ rows 1=0 := by
  constructor
  · rintro ⟨hA,hB⟩
    have h := pairRows_recovery t alpha rows ht
    simpa only [hA,hB,mul_zero,sub_zero,zero_add] using h
  · rintro ⟨ha,hb⟩
    simp [pairRowAverage,pairRowDifference,ha,hb]

def pairChartPhysicalRows (eps t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) : PairChartVariables :=
  let R := radialResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y) (pairChartAngles t alpha y)
  let T := angularResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y) (pairChartAngles t alpha y)
  ![R 2,R 3,pairRowAverage alpha R,pairRowDifference t R,
    T (if keepD then 3 else 2),pairRowAverage alpha T,pairRowDifference t T]

/-- Mean/difference retains both probe rows even at α=0 or α=1. The sole
mass cancellation is the explicitly nonzero omitted exterior mass. -/
theorem pairChartPhysicalRows_zero_iff (eps t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) (ht : t≠0)
    (homit : pairChartMass t p alpha (if keepD then 2 else 3)≠0) :
    pairChartPhysicalRows eps t p alpha keepD y=0 ↔
      (∀ i, radialResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y)
        (pairChartAngles t alpha y) i=0) ∧
      (∀ i, angularResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y)
        (pairChartAngles t alpha y) i=0) := by
  let R := radialResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y) (pairChartAngles t alpha y)
  let T := angularResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y) (pairChartAngles t alpha y)
  change pairChartPhysicalRows eps t p alpha keepD y=0 ↔ (∀ i, R i=0) ∧ ∀ i, T i=0
  constructor
  · intro h
    have hRc : R 2=0 := congrFun h 0
    have hRd : R 3=0 := congrFun h 1
    have hRA : pairRowAverage alpha R=0 := congrFun h 2
    have hRB : pairRowDifference t R=0 := congrFun h 3
    have hTo : T (if keepD then 3 else 2)=0 := congrFun h 4
    have hTA : pairRowAverage alpha T=0 := congrFun h 5
    have hTB : pairRowDifference t T=0 := congrFun h 6
    have hRab := (pairRows_zero_iff t alpha R ht).mp ⟨hRA,hRB⟩
    have hTab := (pairRows_zero_iff t alpha T ht).mp ⟨hTA,hTB⟩
    have hTother : ∀ i, i≠(if keepD then 2 else 3) → T i=0 := by
      intro i hi
      fin_cases i
      · exact hTab.1
      · exact hTab.2
      · cases keepD
        · exact hTo
        · exact (hi rfl).elim
      · cases keepD
        · exact (hi rfl).elim
        · exact hTo
    have hTomit : T (if keepD then 2 else 3)=0 :=
      angularResidual_omitted_row eps (pairChartMass t p alpha) (pairChartRadii t alpha y)
        (pairChartAngles t alpha y) (if keepD then 2 else 3) homit hTother
    constructor
    · intro i
      fin_cases i
      · exact hRab.1
      · exact hRab.2
      · exact hRc
      · exact hRd
    · intro i
      by_cases hi : i=(if keepD then 2 else 3)
      · simpa only [hi] using hTomit
      · exact hTother i hi
  · rintro ⟨hR,hT⟩
    have hRfun : R=0 := funext hR
    have hTfun : T=0 := funext hT
    change (![R 2,R 3,pairRowAverage alpha R,pairRowDifference t R,
      T (if keepD then 3 else 2),pairRowAverage alpha T,pairRowDifference t T] : PairChartVariables)=0
    rw [hRfun,hTfun]
    ext i
    fin_cases i <;> simp [pairRowAverage,pairRowDifference]

end DominantFiveBody
