import DominantFiveBody.CollisionGeometry
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! Literal entries and determinant in the span-pi contradiction of
Proposition 4.1. This checks the original determinant route independently
of the previously verified row-by-row kernel contradiction. -/
noncomputable section
open scoped BigOperators Matrix
open Filter Topology
namespace DominantFiveBody
open Coorbital

theorem fullAngularMatrix_source_entries (eps : ℝ) (r theta : Satellite → ℝ) :
    (∀ i j, fullAngularMatrix eps r theta i j =
      r i*r j*Real.sin (theta j-theta i)*
        ((satelliteDistance (polarSatellites r theta) i j)^(-3:ℤ)-(1+eps)⁻¹)) ∧
    (∀ i, fullAngularMatrix eps r theta i i=0) := by
  constructor
  · intro i j
    simp [fullAngularMatrix,zpow_neg,zpow_ofNat]
  · exact fullAngularMatrix_self eps r theta

theorem fullAngularMatrix_pi_entries (theta : Satellite → ℝ)
    (hgaps : theta 1-theta 0≤h ∧ theta 2-theta 1≤h ∧ theta 3-theta 2≤h)
    (hspan : theta 3-theta 0=Real.pi) :
    fullAngularMatrix 0 (fun _ => 1) theta =
      ![![0,0,kernelF (2*h),0], ![0,0,0,kernelF (2*h)],
        ![-kernelF (2*h),0,0,0], ![0,-kernelF (2*h),0,0]] := by
  have hh : 0<h := by unfold h; positivity
  have hthree : 3*h=Real.pi := by unfold h; ring
  have h01 : theta 1-theta 0=h := by linarith [hgaps.1,hgaps.2.1,hgaps.2.2]
  have h12 : theta 2-theta 1=h := by linarith [hgaps.1,hgaps.2.1,hgaps.2.2]
  have h23 : theta 3-theta 2=h := by linarith [hgaps.1,hgaps.2.1,hgaps.2.2]
  have h02 : theta 2-theta 0=2*h := by linarith
  have h13 : theta 3-theta 1=2*h := by linarith
  let M := fullAngularMatrix 0 (fun _ => 1) theta
  have hdiag (i : Satellite) : M i i=0 := fullAngularMatrix_self _ _ _ _
  have hrev (i j : Satellite) : M j i= -M i j := fullAngularMatrix_reverse _ _ _ _ _
  have hz01 : M 0 1=0 := by
    rw [show M 0 1=kernelF (theta 1-theta 0) from
      fullAngularMatrix_unit_positive_gap theta 0 1 ⟨by linarith,by linarith⟩,h01,kernelF_h]
  have hz12 : M 1 2=0 := by
    rw [show M 1 2=kernelF (theta 2-theta 1) from
      fullAngularMatrix_unit_positive_gap theta 1 2 ⟨by linarith,by linarith⟩,h12,kernelF_h]
  have hz23 : M 2 3=0 := by
    rw [show M 2 3=kernelF (theta 3-theta 2) from
      fullAngularMatrix_unit_positive_gap theta 2 3 ⟨by linarith,by linarith⟩,h23,kernelF_h]
  have hz03 : M 0 3=0 := by
    rw [show M 0 3=kernelF (theta 3-theta 0) from
      fullAngularMatrix_unit_positive_gap theta 0 3 ⟨by linarith,by linarith⟩,hspan,kernelF_pi]
  have hz02 : M 0 2=kernelF (2*h) := by
    rw [show M 0 2=kernelF (theta 2-theta 0) from
      fullAngularMatrix_unit_positive_gap theta 0 2 ⟨by linarith,by linarith⟩,h02]
  have hz13 : M 1 3=kernelF (2*h) := by
    rw [show M 1 3=kernelF (theta 3-theta 1) from
      fullAngularMatrix_unit_positive_gap theta 1 3 ⟨by linarith,by linarith⟩,h13]
  change M = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hdiag,hz01,hz12,hz23,hz03,hz02,hz13,
      hrev 0 1,hrev 0 2,hrev 0 3,hrev 1 2,hrev 1 3,hrev 2 3]

theorem sparse_span_pi_matrix_det (c : ℝ) :
    Matrix.det (![![0,0,c,0],![0,0,0,c],![-c,0,0,0],![0,-c,0,0]] : Matrix (Fin 4) (Fin 4) ℝ)=c^4 := by
  let A : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
    if i=0 ∧ j=2 then c else if i=1 ∧ j=3 then c else
    if i=2 ∧ j=0 then -c else if i=3 ∧ j=1 then -c else 0
  have heq : (![![0,0,c,0],![0,0,0,c],![-c,0,0,0],![0,-c,0,0]] : Matrix (Fin 4) (Fin 4) ℝ)=A := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [heq,Matrix.det_succ_row_zero A,Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply]
  dsimp [A, Fin.succAbove]
  ring

theorem fullAngularMatrix_pi_det (theta : Satellite → ℝ)
    (hgaps : theta 1-theta 0≤h ∧ theta 2-theta 1≤h ∧ theta 3-theta 2≤h)
    (hspan : theta 3-theta 0=Real.pi) :
    (fullAngularMatrix 0 (fun _ => 1) theta).det=kernelF (2*h)^4 ∧ 0<kernelF (2*h)^4 := by
  refine ⟨?_,?_⟩
  · rw [fullAngularMatrix_pi_entries theta hgaps hspan]
    exact sparse_span_pi_matrix_det _
  · have hn : kernelF (2*h)<0 := kernelF_neg_on_long_arc
      (by unfold h; linarith [Real.pi_pos]) (by unfold h; linarith [Real.pi_pos])
    exact pow_pos (neg_pos.mpr hn) 4 |>.trans_eq (by ring)

theorem fullAngularMatrix_determinant_tendsto
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (nhds 0))
    (r theta : ℕ → Satellite → ℝ) (rLimit thetaLimit : Satellite → ℝ)
    (hrt : Tendsto r atTop (nhds rLimit)) (htt : Tendsto theta atTop (nhds thetaLimit))
    (hsep : ∀ i j,i≠j → satelliteDistance (polarSatellites rLimit thetaLimit) i j≠0) :
    Tendsto (fun n => (fullAngularMatrix (eps n) (r n) (theta n)).det)
      atTop (nhds (fullAngularMatrix 0 rLimit thetaLimit).det) := by
  apply (continuous_id.matrix_det.tendsto _).comp
  exact tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr
    (fun j => fullAngularMatrix_tendsto eps heps r theta rLimit thetaLimit hrt htt hsep i j))

theorem fullAngularMatrix_pi_determinant_limit
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (nhds 0))
    (r theta : ℕ → Satellite → ℝ) (thetaLimit : Satellite → ℝ)
    (hrt : Tendsto r atTop (nhds (fun _ => 1))) (htt : Tendsto theta atTop (nhds thetaLimit))
    (hsep : ∀ i j,i≠j → satelliteDistance (polarSatellites (fun _ => 1) thetaLimit) i j≠0)
    (hgaps : thetaLimit 1-thetaLimit 0≤h ∧ thetaLimit 2-thetaLimit 1≤h ∧ thetaLimit 3-thetaLimit 2≤h)
    (hspan : thetaLimit 3-thetaLimit 0=Real.pi) :
    Tendsto (fun n => (fullAngularMatrix (eps n) (r n) (theta n)).det)
      atTop (nhds (kernelF (2*h)^4)) ∧ 0<kernelF (2*h)^4 := by
  have hd := fullAngularMatrix_pi_det thetaLimit hgaps hspan
  refine ⟨?_,hd.2⟩
  simpa only [hd.1] using fullAngularMatrix_determinant_tendsto eps heps r theta _ thetaLimit hrt htt hsep

theorem fullAngularMatrix_pi_separated (theta : Satellite → ℝ)
    (hgaps : theta 1-theta 0≤h ∧ theta 2-theta 1≤h ∧ theta 3-theta 2≤h)
    (hspan : theta 3-theta 0=Real.pi) :
    ∀ i j,i≠j → satelliteDistance (polarSatellites (fun _ => 1) theta) i j≠0 := by
  have hh : 3*h=Real.pi := by unfold h; ring
  have hstrict : StrictMono theta := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro k
    fin_cases k
    · change theta 0 < theta 1
      linarith [hgaps.1,hgaps.2.1,hgaps.2.2,Real.pi_pos]
    · change theta 1 < theta 2
      linarith [hgaps.1,hgaps.2.1,hgaps.2.2,Real.pi_pos]
    · change theta 2 < theta 3
      linarith [hgaps.1,hgaps.2.1,hgaps.2.2,Real.pi_pos]
  have hp (a b : Satellite) (hab : a<b) :
      0<satelliteDistance (polarSatellites (fun _ => 1) theta) a b := by
    have hgap : 0<theta b-theta a := sub_pos.mpr (hstrict hab)
    have hbound : theta b-theta a≤Real.pi := by
      have hlo := hstrict.monotone (Fin.zero_le a)
      have hhi := hstrict.monotone (Fin.le_last b)
      change theta b≤theta 3 at hhi
      linarith
    simpa only [satelliteDistance,polarSatellites,norm_sub_rev] using
      unit_polar_distance_pos_closed (theta a) (theta b) ⟨hgap,hbound⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij'|hji'
  · exact ne_of_gt (hp i j hij')
  · have he : satelliteDistance (polarSatellites (fun _ => 1) theta) i j=
        satelliteDistance (polarSatellites (fun _ => 1) theta) j i := norm_sub_rev _ _
    rw [he]
    exact ne_of_gt (hp j i hji')

theorem fullAngularMatrix_det_zero_of_root (eps : ℝ) (mu r theta : Satellite → ℝ)
    (hsum : ∑ i,mu i=1) (hroot : ∀ i,angularResidual eps mu r theta i=0) :
    (fullAngularMatrix eps r theta).det=0 := by
  have hker : fullAngularMatrix eps r theta *ᵥ mu=0 := by
    ext i
    have hi := (angularResidual_eq_full_matrix_sum eps mu r theta i).symm.trans (hroot i)
    simpa only [Matrix.mulVec,dotProduct,mul_comm,Pi.zero_apply] using hi
  by_contra hn
  have hmu := Matrix.eq_zero_of_mulVec_eq_zero hn hker
  simp [hmu] at hsum

/-- The manuscript's determinant contradiction, from actual four-row roots,
with no limiting-mass positivity assumption or limiting mass vector needed. -/
theorem no_full_angular_sequence_at_pi_by_determinant
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (nhds 0))
    (mu r theta : ℕ → Satellite → ℝ) (thetaLimit : Satellite → ℝ)
    (hsum : ∀ n,∑ i,mu n i=1)
    (hroot : ∀ n i,angularResidual (eps n) (mu n) (r n) (theta n) i=0)
    (hrt : Tendsto r atTop (nhds (fun _ => 1))) (htt : Tendsto theta atTop (nhds thetaLimit))
    (hgaps : thetaLimit 1-thetaLimit 0≤h ∧ thetaLimit 2-thetaLimit 1≤h ∧ thetaLimit 3-thetaLimit 2≤h)
    (hspan : thetaLimit 3-thetaLimit 0=Real.pi) : False := by
  obtain ⟨hlim,hpos⟩ := fullAngularMatrix_pi_determinant_limit eps heps r theta thetaLimit hrt htt
    (fullAngularMatrix_pi_separated thetaLimit hgaps hspan) hgaps hspan
  have hz : Tendsto (fun n => (fullAngularMatrix (eps n) (r n) (theta n)).det)
      atTop (nhds (0:ℝ)) := by
    simpa only [fullAngularMatrix_det_zero_of_root _ _ _ _ (hsum _) (hroot _)] using
      (tendsto_const_nhds (x := (0:ℝ)))
  exact (ne_of_gt hpos) (tendsto_nhds_unique hlim hz)

end DominantFiveBody
