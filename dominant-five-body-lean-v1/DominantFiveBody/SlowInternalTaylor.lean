import DominantFiveBody.SlowNewtonTaylor
import DominantFiveBody.TripleAreas

/-! The actual Cartesian internal-force quotient in source prose:833.
Its exact positive-scale identity and smoothness, rather than only an
endpoint row identity, supply the first-order internal vector term. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology Asymptotics
namespace DominantFiveBody
set_option maxHeartbeats 1000000

local instance slowInternalPlaneAddCommGroup : AddCommGroup Plane :=
  (inferInstance : NormedAddCommGroup Plane).toAddCommGroup
local instance slowInternalPlaneModule : Module ℝ Plane :=
  (inferInstance : NormedSpace ℝ Plane).toModule

def tripleInternalVectorQuotient (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel) : Plane :=
  ∑ j ∈ Finset.univ.erase i,
    (alpha j / tripleChartW t alpha y i j ^ 3) • triplePointDirection t alpha y i j

theorem tripleInternalCartesian_scaling (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel) (ht : 0 < t)
    (hW : ∀ j, j ≠ i → 0 < tripleChartWSq t alpha y i j) :
    (∑ j ∈ Finset.univ.erase i,
      (tripleChartMass t alpha j.castSucc /
        satelliteDistance (tripleChartPoints t alpha y) i.castSucc j.castSucc ^ 3) •
        (tripleChartPoints t alpha y j.castSucc - tripleChartPoints t alpha y i.castSucc)) =
      t • tripleInternalVectorQuotient t alpha y i := by
  rw [tripleInternalVectorQuotient, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hw := hW j (Finset.mem_erase.mp hj).1
  have hwn : tripleChartW t alpha y i j ≠ 0 :=
    (Real.sqrt_pos.mpr hw).ne'
  have hm : tripleChartMass t alpha j.castSucc = t ^ 3 * alpha j := by
    fin_cases j <;> rfl
  rw [hm, tripleChart_cluster_distance t alpha y i j ht hw,
    triplePointDirection_identity, smul_smul, smul_smul]
  congr 1
  field_simp [ht.ne', hwn]

theorem tripleInternalVectorQuotient_zero (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel) :
    tripleInternalVectorQuotient 0 alpha y i = -tripleBoundaryInternalForce alpha y i := by
  rw [tripleInternalVectorQuotient, tripleBoundaryInternalForce, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← tripleBoundaryDisplacement_difference, newtonTargetField,
    tripleBoundaryDisplacement_distance]
  simp only [div_eq_mul_inv, smul_smul]
  module

theorem slowInternal_parameter_alpha (eps t : ℝ) (alpha : TripleVector) :
    tripleJointAlpha (tripleParameter eps t alpha) = alpha := by
  ext i
  fin_cases i <;> rfl

theorem tripleInternalVectorQuotient_contDiffAt (n : ℕ∞ω) (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel)
    (hW : ∀ j, j ≠ i → 0 < tripleChartWSq 0 alpha y i j) :
    ContDiffAt ℝ n (fun t : ℝ => tripleInternalVectorQuotient t alpha y i) 0 := by
  have hp : ContDiff ℝ n (fun t : ℝ => (tripleParameter 0 t alpha, y)) := by
    apply ContDiff.prodMk _ contDiff_const
    apply contDiff_pi.mpr
    intro k
    fin_cases k <;> simp [tripleParameter] <;> fun_prop
  unfold tripleInternalVectorQuotient
  apply ContDiffAt.sum
  intro j hj
  have hw := hW j (Finset.mem_erase.mp hj).1
  have hs := tripleChartW_joint_contDiffAt n (tripleParameter 0 0 alpha, y) i j
    (by simpa only [slowInternal_parameter_alpha, show tripleParameter 0 0 alpha 1 = 0 from rfl] using hw)
  have hc := hs.comp (f := fun t : ℝ => (tripleParameter 0 t alpha, y)) 0 hp.contDiffAt
  have hdist : ContDiffAt ℝ n (fun t : ℝ => tripleChartW t alpha y i j) 0 := by
    simpa only [Function.comp_def, slowInternal_parameter_alpha,
      show ∀ t : ℝ, tripleParameter 0 t alpha 1 = t from fun _ => rfl] using hc
  have hd := (triplePointDirection_joint_contDiff n i j).comp hp
  have hdir : ContDiff ℝ n (fun t : ℝ => triplePointDirection t alpha y i j) := by
    simpa only [Function.comp_def, slowInternal_parameter_alpha,
      show ∀ t : ℝ, tripleParameter 0 t alpha 1 = t from fun _ => rfl] using hd
  exact (contDiffAt_const.div (hdist.pow 3)
    (pow_ne_zero 3 (Real.sqrt_pos.mpr hw).ne')).smul hdir.contDiffAt

theorem tripleInternalVectorQuotient_Olinear (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel)
    (hW : ∀ j, j ≠ i → 0 < tripleChartWSq 0 alpha y i j) :
    (fun t : ℝ => tripleInternalVectorQuotient t alpha y i +
      tripleBoundaryInternalForce alpha y i) =O[𝓝 0] (fun t : ℝ => t) := by
  have hd := (tripleInternalVectorQuotient_contDiffAt 1 alpha y i hW).differentiableAt
    (by norm_num)
  have ho := hd.hasDerivAt.isBigO_sub
  simpa only [sub_zero, tripleInternalVectorQuotient_zero, sub_neg_eq_add] using ho

theorem tripleInternalCartesian_Osquare (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel)
    (hW : ∀ j, j ≠ i → 0 < tripleChartWSq 0 alpha y i j) :
    (fun t : ℝ =>
      (∑ j ∈ Finset.univ.erase i,
        (tripleChartMass t alpha j.castSucc /
          satelliteDistance (tripleChartPoints t alpha y) i.castSucc j.castSucc ^ 3) •
          (tripleChartPoints t alpha y j.castSucc - tripleChartPoints t alpha y i.castSucc)) +
      t • tripleBoundaryInternalForce alpha y i)
      =O[𝓝[Ioi 0] 0] (fun t : ℝ => t ^ 2) := by
  have hp : ContDiff ℝ 0 (fun t : ℝ => (tripleParameter 0 t alpha, y)) := by
    apply ContDiff.prodMk _ contDiff_const
    apply contDiff_pi.mpr
    intro k
    fin_cases k <;> simp [tripleParameter] <;> fun_prop
  have hWnear : ∀ᶠ t : ℝ in 𝓝 0,
      ∀ j, j ≠ i → 0 < tripleChartWSq t alpha y i j := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : j = i
    · exact Eventually.of_forall (fun _ hji => False.elim (hji hij))
    · have hc := (tripleChartWSq_joint_contDiff 0 i j).comp hp
      have hcont : Continuous (fun t : ℝ => tripleChartWSq t alpha y i j) := by
        simpa only [Function.comp_def, slowInternal_parameter_alpha,
          show ∀ t : ℝ, tripleParameter 0 t alpha 1 = t from fun _ => rfl] using hc.continuous
      filter_upwards [(hcont.tendsto 0).eventually (Ioi_mem_nhds (hW j hij))] with t ht
      exact fun _ => ht
  have hmul := (isBigO_refl (fun t : ℝ => t) (𝓝 (0 : ℝ))).smul
    (tripleInternalVectorQuotient_Olinear alpha y i hW)
  have hO : (fun t : ℝ => t • (tripleInternalVectorQuotient t alpha y i +
      tripleBoundaryInternalForce alpha y i)) =O[𝓝[Ioi 0] 0] (fun t : ℝ => t ^ 2) := by
    simpa only [smul_eq_mul, pow_two] using hmul.mono nhdsWithin_le_nhds
  have heq : (fun t : ℝ =>
      (∑ j ∈ Finset.univ.erase i,
        (tripleChartMass t alpha j.castSucc /
          satelliteDistance (tripleChartPoints t alpha y) i.castSucc j.castSucc ^ 3) •
          (tripleChartPoints t alpha y j.castSucc - tripleChartPoints t alpha y i.castSucc)) +
      t • tripleBoundaryInternalForce alpha y i) =ᶠ[𝓝[Ioi 0] 0]
      (fun t : ℝ => t • (tripleInternalVectorQuotient t alpha y i +
        tripleBoundaryInternalForce alpha y i)) := by
    filter_upwards [hWnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t hw ht
    rw [tripleInternalCartesian_scaling t alpha y i ht hw, smul_add]
  exact hO.congr' heq.symm EventuallyEq.rfl

end DominantFiveBody
