import DominantFiveBody.TripleCollinearity
import DominantFiveBody.NestedCollinearity

/-! Actual common-chart roots, with all seven slow coordinates identified
by the genuine local uniqueness theorem. The scalar seed is the same
branch evaluated at epsilon=t=0 and the current normalized weights. -/
noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1000000

theorem tripleSlowPoint_source_formula (eps tau : ℝ) (v : TripleGaps) :
    tripleSlowPoint eps tau v =
      ![backgroundRadius eps, backgroundRadius eps,
        backgroundRadius eps * backgroundSlowK eps tau * backgroundAngularScale eps tau * v 0,
        backgroundRadius eps * backgroundSlowK eps tau * backgroundAngularScale eps tau * v 1,
        tau * h, backgroundAngularScale eps tau * v 0, backgroundAngularScale eps tau * v 1] := rfl

theorem nestedSlowPoint_source_formula (eps tau Z z : ℝ) :
    nestedSlowPoint eps tau Z z =
      ![backgroundRadius eps, backgroundRadius eps,
        backgroundRadius eps * backgroundSlowK eps tau * backgroundAngularScale eps tau * Z,
        backgroundRadius eps * backgroundSlowK eps tau * backgroundAngularScale eps tau * z,
        tau * h, backgroundAngularScale eps tau * Z, backgroundAngularScale eps tau * z] := rfl

theorem nestedBoundaryScalarPositions_source_formula (eta alpha Z z : ℝ) :
    tripleCenteringMatrix (nestedTripleWeights eta alpha) *ᵥ ![eta * z, Z - alpha * eta * z] =
      ![-(1 - eta ^ 3) * Z - (1 - alpha) * eta * z,
        -(1 - eta ^ 3) * Z + alpha * eta * z, eta ^ 3 * Z] := by
  ext i
  fin_cases i <;> simp [tripleCenteringMatrix, nestedTripleWeights, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two] <;> ring

theorem nestedBoundaryScalarPositions_weighted_center (eta alpha Z z : ℝ) :
    eta ^ 3 * alpha * (-(1 - eta ^ 3) * Z - (1 - alpha) * eta * z) +
      eta ^ 3 * (1 - alpha) * (-(1 - eta ^ 3) * Z + alpha * eta * z) +
      (1 - eta ^ 3) * (eta ^ 3 * Z) = 0 := by ring

def nestedSlowRootCandidate (tau : ℝ)
    (branch : NestedChartParameters → NestedChartVariables) (q : NestedChartParameters) :
    NestedChartVariables :=
  nestedSlowPoint (q 0) tau (branch (nestedParameter 0 0 (q 2) (q 3)) 5)
    (branch (nestedParameter 0 0 (q 2) (q 3)) 6)

/-- Joint smoothness in independent epsilon, eta, and alpha, also at both
individual zero-weight faces. No division by eta or alpha is involved. -/
theorem nestedSlowRootCandidate_contDiffAt (n : ℕ∞ω) (tau : ℝ)
    (branch : NestedChartParameters → NestedChartVariables) (q : NestedChartParameters)
    (heps : |q 0| < 1 / 4)
    (hbranch : ContDiffAt ℝ n branch (nestedParameter 0 0 (q 2) (q 3))) :
    ContDiffAt ℝ n (nestedSlowRootCandidate tau branch) q := by
  let seed (p : NestedChartParameters) := branch (nestedParameter 0 0 (p 2) (p 3))
  have hparam : ContDiff ℝ n (fun p : NestedChartParameters => nestedParameter 0 0 (p 2) (p 3)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [nestedParameter] <;> fun_prop
  have hseed : ContDiffAt ℝ n seed q := hbranch.comp q hparam.contDiffAt
  have hmap : ContDiffAt ℝ n (fun p : NestedChartParameters =>
      (p 0, (![seed p 5, seed p 6] : Fin 2 → ℝ))) q := by
    apply ContDiffAt.prodMk (by fun_prop)
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact (contDiffAt_pi.mp hseed) 5
    · exact (contDiffAt_pi.mp hseed) 6
  have hslow := nestedSlowPoint_joint_contDiffAt n (q 0) tau (seed q 5) (seed q 6) heps
  exact hslow.comp q hmap

theorem nestedSlowRootCandidate_contDiffOn (n : ℕ∞ω) (tau : ℝ)
    (branch : NestedChartParameters → NestedChartVariables) (base : NestedChartParameters)
    (d : ℝ) (hsmooth : ContDiffOn ℝ n branch (Metric.ball base d)) :
    ContDiffOn ℝ n (nestedSlowRootCandidate tau branch)
      {q | |q 0| < 1 / 4 ∧ dist (nestedParameter 0 0 (q 2) (q 3)) base < d} := by
  intro q hq
  exact (nestedSlowRootCandidate_contDiffAt n tau branch q hq.1
    (hsmooth.contDiffAt (Metric.isOpen_ball.mem_nhds hq.2))).contDiffWithinAt

theorem tripleChart_zero_face_eq_slowPoint_of_local_uniqueness
    (alpha0 z0 : TripleVector) (ha : TripleWeights alpha0) (hz : TripleOrdered z0)
    (hscalar : ∀ i, tripleScalarResidual alpha0 z0 i = 0)
    (tau : ℝ) (htau : tau = 1 ∨ tau = -1)
    (eta r : ℝ) (heta : 0 < eta) (hr : 0 < r)
    (branch : TripleChartParameters → TripleChartVariables)
    (huniq : ∀ q, dist q (tripleBoundaryParameter alpha0) < eta →
      ∀ y, dist y (tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z0)) < r →
        (tripleChartParameterRows q y = 0 ↔ branch q = y)) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ eps alpha, |eps| < delta → dist alpha alpha0 < delta → (∑ i, alpha i = 1) →
        branch (tripleParameter eps 0 alpha) = tripleSlowPoint eps tau
          (tripleChartAngularGaps (branch (tripleParameter 0 0 alpha))) := by
  obtain ⟨scalarBranch, hscalarBase, hscalarSmooth, hscalarRoots, _⟩ :=
    tripleScalar_root_local_implicitFunction alpha0 z0 ha.1 hz hscalar
  let g (alpha : TripleVector) : TripleGaps := tripleGapMatrix *ᵥ scalarBranch alpha
  let y0 := tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z0)
  let candidate (p : ℝ × TripleVector) := tripleSlowPoint p.1 tau (g p.2)
  have hg : ContinuousAt g alpha0 := by
    exact tripleGapLinear.continuous.continuousAt.comp hscalarSmooth.continuousAt
  have hfst : ContinuousAt (fun p : ℝ × TripleVector => p.1) (0, alpha0) := continuousAt_fst
  have hsnd : ContinuousAt (fun p : ℝ × TripleVector => p.2) (0, alpha0) := continuousAt_snd
  have hslow : ContinuousAt (fun p : ℝ × TripleGaps => tripleSlowPoint p.1 tau p.2)
      (0, g alpha0) :=
    (tripleSlowPoint_joint_contDiffAt 0 0 tau (g alpha0) (by norm_num)).continuousAt
  have hmap : ContinuousAt (fun p : ℝ × TripleVector => (p.1, g p.2)) (0, alpha0) :=
    hfst.prodMk (ContinuousAt.comp' (f := fun p : ℝ × TripleVector => p.2) hg hsnd)
  have hc : ContinuousAt candidate (0, alpha0) := by
    exact ContinuousAt.comp' (f := fun p : ℝ × TripleVector => (p.1, g p.2))
      (g := fun p : ℝ × TripleGaps => tripleSlowPoint p.1 tau p.2) hslow hmap
  have hbase : candidate (0, alpha0) = y0 := by
    simp only [candidate, g, hscalarBase, tripleSlowPoint_zero, y0]
  have hcnear : ∀ᶠ p : ℝ × TripleVector in 𝓝 (0, alpha0), dist (candidate p) y0 < r := by
    rw [← hbase]
    exact hc.eventually (Metric.ball_mem_nhds _ hr)
  have hqcont : Continuous (fun p : ℝ × TripleVector => tripleParameter p.1 0 p.2) := by
    simp only [tripleParameter]
    fun_prop
  have hqnear : ∀ᶠ p : ℝ × TripleVector in 𝓝 (0, alpha0),
      dist (tripleParameter p.1 0 p.2) (tripleBoundaryParameter alpha0) < eta :=
    hqcont.continuousAt.eventually (Metric.ball_mem_nhds _ heta)
  have hene : ∀ᶠ p : ℝ × TripleVector in 𝓝 (0, alpha0), |p.1| < 1 / 4 :=
    continuousAt_fst.abs.eventually (Iio_mem_nhds (by norm_num : |(0 : ℝ)| < 1 / 4))
  have hsnear : ∀ᶠ p : ℝ × TripleVector in 𝓝 (0, alpha0),
      ∀ i, tripleScalarResidual p.2 (scalarBranch p.2) i = 0 :=
    hsnd.eventually hscalarRoots
  have hnear := hene.and (hsnear.and (hqnear.and hcnear))
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨delta, hdelta, ?_⟩
  intro eps alpha heps halpha hasum
  have hd : dist (eps, alpha) (0, alpha0) < delta := by
    rw [Prod.dist_eq]
    simpa only [Real.dist_eq, sub_zero] using max_lt heps halpha
  obtain ⟨he, hs, hq, hcy⟩ := hball hd
  have hgroot : ∀ j, tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ g alpha) j = 0 := by
    have hrec := tripleScalar_root_gap_recovery alpha (scalarBranch alpha) hasum hs
    simpa only [g, hrec] using hs
  have hcroot : tripleChartParameterRows (tripleParameter eps 0 alpha) (candidate (eps, alpha)) = 0 := by
    have halphaq : tripleJointAlpha (tripleParameter eps 0 alpha) = alpha := by
      ext j
      fin_cases j <;> rfl
    simp only [tripleChartParameterRows, halphaq]
    exact tripleSlowPoint_root eps tau alpha (g alpha) he htau hasum hgroot
  have heq := (huniq (tripleParameter eps 0 alpha) hq (candidate (eps, alpha)) hcy).mp hcroot
  have hd0 : dist ((0 : ℝ), alpha) (0, alpha0) < delta := by
    rw [Prod.dist_eq]
    simpa only [Real.dist_eq, sub_zero, abs_zero] using max_lt hdelta halpha
  obtain ⟨he0, _, hq0, hcy0⟩ := hball hd0
  have hcroot0 : tripleChartParameterRows (tripleParameter 0 0 alpha) (candidate (0, alpha)) = 0 := by
    have halphaq : tripleJointAlpha (tripleParameter 0 0 alpha) = alpha := by
      ext j
      fin_cases j <;> rfl
    simp only [tripleChartParameterRows, halphaq]
    exact tripleSlowPoint_root 0 tau alpha (g alpha) he0 htau hasum hgroot
  have heq0 := (huniq (tripleParameter 0 0 alpha) hq0 (candidate (0, alpha)) hcy0).mp hcroot0
  have hgap : tripleChartAngularGaps (branch (tripleParameter 0 0 alpha)) = g alpha := by
    rw [heq0]
    ext j
    fin_cases j <;> simp [candidate, tripleChartAngularGaps, tripleSlowPoint]
  rw [hgap]
  exact heq

theorem nestedChart_zero_face_eq_slowPoint_of_local_uniqueness
    (alpha0 tau omega : ℝ) (htau : tau=1 ∨ tau= -1)
    (d r : ℝ) (hd : 0<d) (hr : 0<r)
    (branch : NestedChartParameters → NestedChartVariables)
    (hbase : branch (nestedParameter 0 0 0 alpha0)=nestedBasePoint (tau*h) omega)
    (hsmooth : ContDiffOn ℝ ∞ branch (Metric.ball (nestedParameter 0 0 0 alpha0) d))
    (hdomain : ∀ q,dist q (nestedParameter 0 0 0 alpha0)<d → NestedContinuationDomain (q,branch q))
    (hroots : ∀ q,dist q (nestedParameter 0 0 0 alpha0)<d → nestedChartParameterRows q (branch q)=0)
    (huniq : ∀ q,dist q (nestedParameter 0 0 0 alpha0)<d →
      ∀ y,dist y (nestedBasePoint (tau*h) omega)<r →
        (nestedChartParameterRows q y=0 ↔ branch q=y)) :
    ∃ delta : ℝ,0<delta ∧ delta≤d ∧ ∀ eps eta alpha,
      dist (nestedParameter eps 0 eta alpha) (nestedParameter 0 0 0 alpha0)<delta →
      0<eta → alpha∈Icc (0 : ℝ) 1 →
      branch (nestedParameter eps 0 eta alpha) =
        nestedSlowPoint eps tau (branch (nestedParameter 0 0 eta alpha) 5)
          (branch (nestedParameter 0 0 eta alpha) 6) := by
  let q0 := nestedParameter 0 0 0 alpha0
  let y0 := nestedBasePoint (tau*h) omega
  let seedParameter (q : NestedChartParameters) := nestedParameter 0 0 (q 2) (q 3)
  let seed (q : NestedChartParameters) := branch (seedParameter q)
  let candidate (q : NestedChartParameters) := nestedSlowPoint (q 0) tau (seed q 5) (seed q 6)
  have hseedParam : Continuous seedParameter := by unfold seedParameter nestedParameter; fun_prop
  have hseedParam0 : seedParameter q0=q0 := rfl
  have hbc : ContinuousAt branch q0 :=
    (hsmooth.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hd))).continuousAt
  have hseed : ContinuousAt seed q0 := by
    exact hbc.comp hseedParam.continuousAt
  have hseed0 : seed q0=y0 := hbase
  have hmap : ContinuousAt (fun q : NestedChartParameters =>
      (q 0,(![seed q 5,seed q 6] : Fin 2 → ℝ))) q0 := by
    apply ContinuousAt.prodMk ((continuous_apply 0).continuousAt)
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact (continuousAt_pi.mp hseed) 5
    · exact (continuousAt_pi.mp hseed) 6
  have hslow := (nestedSlowPoint_joint_contDiffAt 0 0 tau (y0 5) (y0 6) (by norm_num)).continuousAt
  have hcand : ContinuousAt candidate q0 := by
    have hh : ContinuousAt (fun p : ℝ × (Fin 2 → ℝ) => nestedSlowPoint p.1 tau (p.2 0) (p.2 1))
        (q0 0,![seed q0 5,seed q0 6]) := by
      simpa only [hseed0,show q0 0=0 from rfl] using hslow
    exact ContinuousAt.comp' (f := fun q : NestedChartParameters =>
      (q 0,(![seed q 5,seed q 6] : Fin 2 → ℝ))) hh hmap
  have hcand0 : candidate q0=y0 := by
    dsimp [candidate]
    rw [show q0 0=0 from rfl,hseed0,nestedSlowPoint_zero]
    rfl
  have hqnear : ∀ᶠ q in 𝓝 q0,dist q q0<d := Metric.ball_mem_nhds _ hd
  have hsnear : ∀ᶠ q in 𝓝 q0,dist (seedParameter q) q0<d := by
    rw [← hseedParam0]
    exact hseedParam.continuousAt.eventually (Metric.ball_mem_nhds _ hd)
  have hcnear : ∀ᶠ q in 𝓝 q0,dist (candidate q) y0<r := by
    rw [← hcand0]
    exact hcand.eventually (Metric.ball_mem_nhds _ hr)
  have hangleNear : ∀ᶠ q in 𝓝 q0,|seed q 4-tau*h|<h := by
    have hca := ((continuousAt_pi.mp hseed) 4).sub_const (tau*h) |>.abs
    have hpos : |seed q0 4-tau*h|<h := by
      rw [hseed0]
      change |tau*h-tau*h|<h
      simp only [sub_self,abs_zero]
      unfold h
      positivity
    exact hca.eventually (Iio_mem_nhds hpos)
  have hsmall : ∀ᶠ q : NestedChartParameters in 𝓝 q0,|q 0|<1/4 ∧ q 2<1 := by
    have he : ∀ᶠ q : NestedChartParameters in 𝓝 q0,|q 0|<1/4 :=
      (continuous_apply 0).continuousAt.abs.eventually (Iio_mem_nhds (by norm_num [q0,nestedParameter]))
    have heta : ∀ᶠ q : NestedChartParameters in 𝓝 q0,q 2<1 :=
      (continuous_apply 2).continuousAt.eventually (Iio_mem_nhds (by change (0 : ℝ)<1; norm_num))
    exact he.and heta
  obtain ⟨d0,hd0,hnear⟩ := Metric.eventually_nhds_iff.mp
    (hqnear.and (hsnear.and (hcnear.and (hangleNear.and hsmall))))
  let delta := min d d0
  have hdelta : 0<delta := lt_min hd hd0
  refine ⟨delta,hdelta,min_le_left _ _,?_⟩
  intro eps eta alpha hq heta halpha
  let q := nestedParameter eps 0 eta alpha
  obtain ⟨hqdom,hsdom,hcball,hseedAngle,heps,heta1⟩ := hnear (y := q)
    (lt_of_lt_of_le hq (min_le_right d d0))
  have hsd := hdomain (seedParameter q) hsdom
  have hsroot := hroots (seedParameter q) hsdom
  have hsreg : NestedChartRegular 0 0 eta alpha (seed q) := hsd.1
  have hsradii : ∀ i,0<nestedChartRadii 0 eta alpha (seed q) i := hsd.2.1
  have hspi : |seed q 4|<Real.pi := by
    have hh := hsd.2.2 0 3
    change |nestedChartAngles 0 eta alpha (seed q) 3-nestedChartAngles 0 eta alpha (seed q) 0|<Real.pi at hh
    simpa [nestedChartAngles,nestedCoordinates] using hh
  have hsroot' : nestedChartExtendedRows 0 0 eta alpha (seed q)=0 := hsroot
  have hseq := nestedZeroRoot_eq_unitPoint eta alpha tau (seed q) htau hsreg hsradii hspi hseedAngle hsroot'
  have hsreg' : NestedChartRegular 0 0 eta alpha (nestedUnitPoint (tau*h) (seed q 5) (seed q 6)) := by
    rw [← hseq]
    exact hsreg
  have hroot' : nestedChartExtendedRows 0 0 eta alpha (nestedUnitPoint (tau*h) (seed q 5) (seed q 6))=0 := by
    rw [← hseq]
    exact hsroot'
  have htangle : |tau*h|=h := by
    rcases htau with rfl | rfl
    · simp [abs_of_pos (show 0<h by unfold h; positivity)]
    · simp [abs_of_pos (show 0<h by unfold h; positivity)]
  have hscalar := nestedUnitPoint_scalar_root eta alpha (tau*h) (seed q 5) (seed q 6)
    heta (le_of_lt heta1) halpha.1 halpha.2 htangle hsreg' hroot'
  obtain ⟨hz,hZ0,hZ1⟩ := nestedUnitPoint_regular_gaps 0 eta alpha (tau*h) (seed q 5) (seed q 6) hsreg'
  have hcroot : nestedChartParameterRows q (candidate q)=0 :=
    nestedSlowPoint_root eps tau eta alpha (seed q 5) (seed q 6) heps htau heta hz hZ0 hZ1 hscalar
  have heq := (huniq q hqdom (candidate q) hcball).mp hcroot
  exact heq


end DominantFiveBody
