import DominantFiveBody.CompactRootLipschitz
import DominantFiveBody.TriplePhysicalContinuation
import DominantFiveBody.NestedContinuation
import DominantFiveBody.NestedZeroFaces

/-! The original locally uniform O(epsilon) bounds, evaluated along the
actual implicit roots. Epsilon is reset while every other parameter is fixed. -/
noncomputable section
open scoped BigOperators ContDiff Matrix
open Filter Set Topology
namespace DominantFiveBody
open Coorbital

def zeroEpsilon {k : ℕ} (q : Fin (k+1) → ℝ) : Fin (k+1) → ℝ := Function.update q 0 0

theorem zeroEpsilon_dist_base {k : ℕ} (q p : Fin (k+1) → ℝ) (hp : p 0 = 0)
    (r : ℝ) (hr : 0 < r) (hq : dist q p < r) : dist (zeroEpsilon q) p < r := by
  apply (dist_pi_lt_iff hr).mpr
  intro i
  by_cases hi : i = 0
  · subst i
    simpa [zeroEpsilon,hp] using hr
  · simpa [zeroEpsilon,hi] using (dist_pi_lt_iff hr).mp hq i

theorem dist_zeroEpsilon_le {k : ℕ} (q : Fin (k+1) → ℝ) :
    dist q (zeroEpsilon q) ≤ |q 0| := by
  apply (dist_pi_le_iff (abs_nonneg _)).mpr
  intro i
  by_cases hi : i = 0
  · subst i
    simp [zeroEpsilon]
  · simp [zeroEpsilon,hi]

theorem radial_four_sum_le_of_dist (y z : Fin 7 → ℝ) (B : ℝ)
    (h : dist y z ≤ B) (h0 : z 0=1) (h1 : z 1=1) (h2 : z 2=0) (h3 : z 3=0) :
    |y 0-1|+|y 1-1|+|y 2|+|y 3| ≤ 4*B := by
  have h₀ := (dist_le_pi_dist y z 0).trans h
  have h₁ := (dist_le_pi_dist y z 1).trans h
  have h₂ := (dist_le_pi_dist y z 2).trans h
  have h₃ := (dist_le_pi_dist y z 3).trans h
  simp only [Real.dist_eq,h0,h1,h2,h3,sub_zero] at h₀ h₁ h₂ h₃
  linarith

/-- All four radial unknowns satisfy a single bound on an independent
parameter neighborhood of each actual regular triple seed. -/
theorem tripleChart_radial_uniform_epsilon_bound (alpha : TripleVector) (ha : TripleWeights alpha)
    (psi : ℝ) (hangle : |psi|=h) (g : TripleGaps)
    (hdist : ∀ i j, i≠j → (tripleCenteringMatrix alpha *ᵥ g) i ≠
      (tripleCenteringMatrix alpha *ᵥ g) j)
    (hroot : ∀ i, tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ g) i=0) :
    ∃ delta C : ℝ, 0<delta ∧ 0<C ∧
      ∃ branch : TripleChartParameters → TripleChartVariables,
        branch (tripleBoundaryParameter alpha)=tripleUnitPoint psi g ∧
        ContDiffOn ℝ ∞ branch (Metric.ball (tripleBoundaryParameter alpha) delta) ∧
        ∀ q, dist q (tripleBoundaryParameter alpha)<delta →
          tripleChartParameterRows q (branch q)=0 ∧
          ((∑ i, tripleJointAlpha q i)=1 →
            |branch q 0-1|+|branch q 1-1|+|branch q 2|+|branch q 3| ≤ C*|q 0|) := by
  obtain ⟨eta,r,A,heta,_,_,_,_,branch,hbase,hs,hrows⟩ :=
    tripleChart_physical_continuation alpha ha psi hangle g hdist hroot 1 (by norm_num)
  have hs0 : ContDiffAt ℝ 1 branch (tripleBoundaryParameter alpha) :=
    ((hs _ (Metric.mem_ball_self heta)).contDiffAt (Metric.ball_mem_nhds _ heta)).of_le (by norm_num)
  obtain ⟨L,U,hU,hL⟩ := hs0.exists_lipschitzOnWith
  obtain ⟨s,hspos,hball⟩ := Metric.mem_nhds_iff.mp hU
  let delta := min eta s
  have hd : 0<delta := lt_min heta hspos
  have hC : 0 < 4*((L:ℝ)+1) := by positivity
  refine ⟨delta,4*((L:ℝ)+1),hd,hC,branch,hbase,
    hs.mono (Metric.ball_subset_ball (min_le_left eta s)),?_⟩
  intro q hq
  have hqeta := lt_of_lt_of_le hq (min_le_left eta s)
  have hq0 := zeroEpsilon_dist_base q (tripleBoundaryParameter alpha) rfl delta hd hq
  have hq0eta := lt_of_lt_of_le hq0 (min_le_left eta s)
  have hrootq := (hrows q hqeta).2.2.2.2.2.1
  refine ⟨hrootq,?_⟩
  intro hsum
  have hzrows : tripleChartExtendedRows 0 (q 1) (tripleJointAlpha q)
      (branch (zeroEpsilon q))=0 := by
    simpa [tripleChartParameterRows,zeroEpsilon,tripleJointAlpha] using
      (hrows (zeroEpsilon q) hq0eta).2.2.2.2.2.1
  have hrad : ∀ i, 0<tripleChartRadii (q 1) (tripleJointAlpha q) (branch (zeroEpsilon q)) i := by
    simpa [zeroEpsilon,tripleJointAlpha] using (hrows (zeroEpsilon q) hq0eta).2.2.1.1
  obtain ⟨_,hgap,hzero,hone⟩ := tripleChart_zero_eps_all_scale_faces _ _ _ hsum hrad hzrows
  have htwo : branch (zeroEpsilon q) 2=0 := congrFun hgap 0
  have hthree : branch (zeroEpsilon q) 3=0 := congrFun hgap 1
  have hdistance := hL.dist_le_mul q (hball (lt_of_lt_of_le hq (min_le_right eta s)))
    (zeroEpsilon q) (hball (lt_of_lt_of_le hq0 (min_le_right eta s)))
  have hbound : dist (branch q) (branch (zeroEpsilon q)) ≤ ((L:ℝ)+1)*|q 0| := by
    exact hdistance.trans ((mul_le_mul_of_nonneg_left (dist_zeroEpsilon_le q) L.coe_nonneg).trans
      (mul_le_mul_of_nonneg_right (by linarith : (L:ℝ) ≤ (L:ℝ)+1) (abs_nonneg _)))
  have hfinal := radial_four_sum_le_of_dist _ _ _ hbound hzero hone htwo hthree
  nlinarith

/-- A single constant and independent parameter radius work for every
inner mass fraction, including both endpoints. The branch itself supplies
the fixed-scale zero-epsilon root used in the comparison. -/
theorem nestedChart_radial_uniform_epsilon_bound (psi omega : ℝ)
    (hangle : |psi|=h) (hw : |omega|=1) :
    ∃ delta C : ℝ, 0<delta ∧ 0<C ∧
      ∀ alpha ∈ Icc (0:ℝ) 1, ∃ branch : NestedChartParameters → NestedChartVariables,
        branch ![0,0,0,alpha]=nestedBasePoint psi omega ∧
        ContDiffOn ℝ ∞ branch (Metric.ball ![0,0,0,alpha] delta) ∧
        ∀ q, dist q ![0,0,0,alpha]<delta →
          NestedContinuationDomain (q,branch q) ∧ nestedChartParameterRows q (branch q)=0 ∧
          |branch q 0-1|+|branch q 1-1|+|branch q 2|+|branch q 3| ≤ C*|q 0| := by
  let y0 := nestedBasePoint psi omega
  let K : Set NestedJointVariables :=
    (fun alpha : ℝ => ((![0,0,0,alpha] : NestedChartParameters),y0)) '' Icc 0 1
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hdata : ∀ a ∈ K, ContDiffAt ℝ ∞ (Function.uncurry nestedChartParameterRows) a ∧
      nestedChartParameterRows a.1 a.2=0 ∧
      (CompactImplicit.jacobian nestedChartParameterRows a.1 a.2).IsInvertible := by
    rintro a ⟨alpha,_,rfl⟩
    refine ⟨?_,nestedChartExtendedRows_base_root alpha psi omega hangle hw,
      nestedChartJacobian_boundary_isInvertible alpha psi omega hangle hw⟩
    exact nestedChartExtendedRows_joint_contDiffAt ∞ _
      (nestedBasePoint_regular alpha psi omega hangle hw)
  obtain ⟨d,B,hd,hB,hbound⟩ := CompactImplicit.compact_root_lipschitz _ K hK hdata
  obtain ⟨eta,r,A,heta,hr,_,hrd,_,hbranches⟩ :=
    nestedChart_compact_boundary_continuation psi omega hangle hw d hd
  let delta := min eta d
  have hdelta : 0<delta := lt_min heta hd
  refine ⟨delta,4*B,hdelta,mul_pos (by norm_num) hB,?_⟩
  intro alpha halpha
  obtain ⟨branch,hbase,hs,hrows⟩ := hbranches alpha halpha
  refine ⟨branch,hbase,hs.mono (Metric.ball_subset_ball (min_le_left eta d)),?_⟩
  intro q hq
  have hqeta := lt_of_lt_of_le hq (min_le_left eta d)
  have hq0 := zeroEpsilon_dist_base q (![0,0,0,alpha] : NestedChartParameters) rfl delta hdelta hq
  have hq0eta := lt_of_lt_of_le hq0 (min_le_left eta d)
  have hp := hrows q hqeta
  have hz := hrows (zeroEpsilon q) hq0eta
  refine ⟨hp.2.1,hp.2.2.2.2.1,?_⟩
  have hzrows : nestedChartExtendedRows 0 (q 1) (q 2) (q 3) (branch (zeroEpsilon q))=0 := by
    simpa [nestedChartParameterRows,zeroEpsilon] using hz.2.2.2.2.1
  have hrad : ∀ i,0<nestedChartRadii (q 1) (q 2) (q 3) (branch (zeroEpsilon q)) i := by
    simpa [zeroEpsilon] using hz.2.1.2.1
  obtain ⟨_,hu,hv,hr0,hR⟩ := nestedChart_zero_eps_all_scale_faces _ _ _ _ hrad hzrows
  have hdistance := hbound ((![0,0,0,alpha] : NestedChartParameters),y0) ⟨alpha,halpha,rfl⟩
    q (zeroEpsilon q) (branch q) (branch (zeroEpsilon q))
    (lt_of_lt_of_le hq (min_le_right eta d))
    (lt_of_lt_of_le hq0 (min_le_right eta d))
    (lt_of_lt_of_le hp.1 (by linarith : r/2 ≤ d))
    (lt_of_lt_of_le hz.1 (by linarith : r/2 ≤ d)) hp.2.2.2.2.1 hz.2.2.2.2.1
  have hfinal := radial_four_sum_le_of_dist _ _ _
    (hdistance.trans (mul_le_mul_of_nonneg_left (dist_zeroEpsilon_le q) hB.le)) hr0 hR hu hv
  nlinarith

end DominantFiveBody
