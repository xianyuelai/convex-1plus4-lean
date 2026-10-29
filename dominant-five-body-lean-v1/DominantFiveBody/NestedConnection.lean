import DominantFiveBody.NestedSequenceCapture
import DominantFiveBody.UniformThreshold

/-! # The nested chart supplies actual Section 7 captured branches

Only sequences with the proved/classified nested limits enter here.
This module does not assert the global connection property.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 800000

def physicalFixedLabelEndpoint (p : PhysicalParameter) (gauge : Satellite) : Configuration :=
  fixedLabelCoorbitalEndpoint p.1.val p.2 gauge

def physicalNondegenerateRoot (p : PhysicalParameter) (eps : ℝ) (x : Configuration) : Prop :=
  NondegenerateCentralConfiguration (masses eps p.1.val) x

theorem nestedChartConfiguration_epsilon_continuousOn (t eta alpha radius : ℝ)
    (branch : ℝ → NestedChartVariables) (hbranch : ContinuousOn branch (Ico (0 : ℝ) radius)) :
    ContinuousOn (fun s => nestedChartConfiguration (nestedParameter s t eta alpha) (branch s))
      (Ico 0 radius) := by
  let interval := Ico (0 : ℝ) radius
  have hfixedGraph : Continuous (fun y : NestedChartVariables => (nestedParameter 0 t eta alpha,y)) :=
    continuous_const.prodMk continuous_id
  have hpoints : ContinuousOn (fun s => nestedChartPoints t eta alpha (branch s)) interval := by
    apply continuousOn_pi.mpr
    intro i
    have hfixed := (nestedChartPoints_joint_contDiff 0 i).continuous.comp hfixedGraph
    have hcomp := hfixed.comp_continuousOn hbranch
    exact hcomp
  have hlift := liftRelative_continuous.comp_continuousOn hpoints
  have hmean : ContinuousOn (fun s => relativeAverage (nestedChartMass t eta alpha)
      (nestedChartPoints t eta alpha (branch s))) interval := by
    simpa only [Function.comp_def,relativeAverageLinear_apply] using
      (relativeAverageLinear (nestedChartMass t eta alpha)).continuous.comp_continuousOn hpoints
  have hquot : ContinuousOn (fun s : ℝ => s/(1+s)) interval :=
    continuousOn_id.div (continuousOn_const.add continuousOn_id) (by intro s hs; dsimp; linarith [hs.1])
  apply continuousOn_pi.mpr
  intro i
  exact ((continuousOn_pi.mp hlift) i).sub (hquot.smul hmean)

theorem NestedCapturedBranches.toPhysicalCapturedBranches {eps t eta alpha : ℕ → ℝ}
    {y : ℕ → NestedChartVariables} {tau omega : ℝ}
    (c : NestedCapturedBranches eps t eta alpha y tau omega)
    (hm : ∀ n,PositiveRatio (nestedChartMass (t n) (eta n) (alpha n))) :
    Nonempty (CapturedBranches PhysicalRoot physicalNondegenerateRoot
      (fun p => physicalFixedLabelEndpoint p 3)
      (fun n : ℕ => ((⟨nestedChartMass (t n) (eta n) (alpha n),hm n⟩ : {mu : MassRatio // PositiveRatio mu}),
        nestedBoundaryHullOrder tau omega)) eps
      (fun n => nestedChartConfiguration (nestedParameter (eps n) (t n) (eta n) (alpha n)) (y n))) := by
  let q (n : ℕ) (s : ℝ) := nestedParameter s (t (c.tailStart+n)) (eta (c.tailStart+n)) (alpha (c.tailStart+n))
  let branch (n : ℕ) (s : ℝ) := nestedChartConfiguration (q n s) (c.branch n s)
  refine ⟨{
    subseq := fun n => c.tailStart+n
    subseq_strictMono := by intro i j hij; change c.tailStart+i<c.tailStart+j; omega
    radius := c.radius
    radius_pos := c.radius_pos
    parameters_lt_radius := c.parameters_lt_radius
    branch := branch
    continuous := ?_
    hits := ?_
    roots := ?_
    nondegenerate_at := ?_
    endpoints := ?_ }⟩
  · intro n
    exact nestedChartConfiguration_epsilon_continuousOn _ _ _ _ _ (c.continuous n)
  · intro n
    change nestedChartConfiguration (q n (eps (c.tailStart+n)))
      (c.branch n (eps (c.tailStart+n)))=_
    rw [c.hits n]
  · intro n s hs hsrad
    exact (c.physical n s hs hsrad).1
  · intro n s hs hsrad
    exact (c.physical n s hs hsrad).2
  · intro n
    exact c.endpoint_eq hm n

end DominantFiveBody
