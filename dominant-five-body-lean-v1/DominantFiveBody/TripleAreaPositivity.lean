import DominantFiveBody.TripleCollinearity
import DominantFiveBody.TripleAreaDerivative

/-! # Positive cubic area factor along the actual regular-triple branch

Source §6.2. The derivative is taken in the independent scale parameter
after composition with the full smooth root, not at fixed unknowns.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

def tripleScaleDirection : TripleChartParameters := ![0, 1, 0, 0, 0]

@[simp] theorem tripleParameter_alpha (eps t : ℝ) (alpha : TripleVector) :
    tripleJointAlpha (tripleParameter eps t alpha) = alpha := by
  ext i
  fin_cases i <;> rfl

theorem tripleParameter_hasDerivAt (eps t : ℝ) (alpha : TripleVector) :
    HasDerivAt (fun s => tripleParameter eps s alpha) tripleScaleDirection t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_const t eps
  · exact hasDerivAt_id t
  · exact hasDerivAt_const t (alpha 0)
  · exact hasDerivAt_const t (alpha 1)
  · exact hasDerivAt_const t (alpha 2)

def tripleAreaParameterRoot (branch : TripleChartParameters → TripleChartVariables)
    (q : TripleChartParameters) : ℝ :=
  tripleInternalAreaQuotient (q 1) (tripleJointAlpha q) (branch q)

def tripleAreaPartialDerivative (branch : TripleChartParameters → TripleChartVariables)
    (q : TripleChartParameters) : ℝ :=
  fderiv ℝ (tripleAreaParameterRoot branch) q tripleScaleDirection

theorem tripleAreaParameterRoot_contDiffOn (branch : TripleChartParameters → TripleChartVariables)
    (s : Set TripleChartParameters) (n : ℕ∞ω) (hs : ContDiffOn ℝ n branch s) :
    ContDiffOn ℝ n (tripleAreaParameterRoot branch) s := by
  have hp : ContDiffOn ℝ n (fun q : TripleChartParameters => (q, branch q)) s :=
    contDiffOn_id.prodMk hs
  convert! (tripleInternalAreaQuotient_joint_contDiff n).comp_contDiffOn hp using 1

theorem tripleAreaAlongRoot_hasDerivAt_of_joint (branch : TripleChartParameters → TripleChartVariables)
    (eps t : ℝ) (alpha : TripleVector)
    (hd : DifferentiableAt ℝ (tripleAreaParameterRoot branch) (tripleParameter eps t alpha)) :
    HasDerivAt (tripleAreaAlongRoot branch eps alpha)
      (tripleAreaPartialDerivative branch (tripleParameter eps t alpha)) t := by
  have h := hd.hasFDerivAt.comp_hasDerivAt t (tripleParameter_hasDerivAt eps t alpha)
  convert! h using 1

theorem tripleAreaAlongRoot_deriv_eq_partial (branch : TripleChartParameters → TripleChartVariables)
    (eps t : ℝ) (alpha : TripleVector)
    (hd : DifferentiableAt ℝ (tripleAreaParameterRoot branch) (tripleParameter eps t alpha)) :
    deriv (tripleAreaAlongRoot branch eps alpha) t =
      tripleAreaPartialDerivative branch (tripleParameter eps t alpha) :=
  (tripleAreaAlongRoot_hasDerivAt_of_joint branch eps t alpha hd).deriv

theorem tripleAreaPartialDerivative_continuousOn (branch : TripleChartParameters → TripleChartVariables)
    (s : Set TripleChartParameters) (hs : IsOpen s) (hb : ContDiffOn ℝ 2 branch s) :
    ContinuousOn (tripleAreaPartialDerivative branch) s :=
  (((tripleAreaParameterRoot_contDiffOn branch s 2 hb).fderiv_of_isOpen hs
    (by norm_num : (0 : ℕ∞ω) + 1 ≤ 2)).clm_apply contDiffOn_const).continuousOn

theorem tripleParameter_scale_segment_mem_ball (alpha0 alpha : TripleVector) (eps t delta : ℝ)
    (hdelta : 0 < delta) (hq : dist (tripleParameter eps t alpha) (tripleBoundaryParameter alpha0) < delta)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    dist (tripleParameter eps (s * t) alpha) (tripleBoundaryParameter alpha0) < delta := by
  have hc := (dist_pi_lt_iff hdelta).mp hq
  apply (dist_pi_lt_iff hdelta).mpr
  intro i
  fin_cases i
  · exact hc 0
  · have ht : |t| < delta := by simpa [tripleParameter, tripleBoundaryParameter, Real.dist_eq] using hc 1
    change dist (s * t) 0 < delta
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hs.1]
    exact lt_of_le_of_lt (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hs.2 (abs_nonneg t)) ht
  · exact hc 2
  · exact hc 3
  · exact hc 4

/-- Actual local chart roots have a strictly positive full-root cubic
area coefficient on a smaller independent parameter neighborhood. -/
theorem tripleChart_internal_area_positive_neighborhood
    (alpha0 z0 : TripleVector) (ha : TripleWeights alpha0) (hz : TripleOrdered z0)
    (hscalar : ∀ i, tripleScalarResidual alpha0 z0 i = 0)
    (tau : ℝ) (htau : tau = 1 ∨ tau = -1)
    (eta r : ℝ) (heta : 0 < eta) (hr : 0 < r)
    (branch : TripleChartParameters → TripleChartVariables)
    (hbase : branch (tripleBoundaryParameter alpha0) =
      tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z0))
    (hsmooth : ContDiffOn ℝ ∞ branch (Metric.ball (tripleBoundaryParameter alpha0) eta))
    (hroots : ∀ q, dist q (tripleBoundaryParameter alpha0) < eta →
      tripleChartParameterRows q (branch q) = 0)
    (hradii : ∀ q, dist q (tripleBoundaryParameter alpha0) < eta →
      ∀ i, 0 < tripleChartRadii (q 1) (tripleJointAlpha q) (branch q) i)
    (huniq : ∀ q, dist q (tripleBoundaryParameter alpha0) < eta →
      ∀ y, dist y (tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z0)) < r →
        (tripleChartParameterRows q y = 0 ↔ branch q = y)) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ eta ∧
      ∀ eps t alpha, dist (tripleParameter eps t alpha) (tripleBoundaryParameter alpha0) < delta →
        (∑ i, alpha i = 1) →
        orientedArea (liftRelative (tripleChartPoints t alpha (branch (tripleParameter eps t alpha))))
          1 2 3 = t ^ 3 * tripleAreaCoefficientAlongRoot branch eps t alpha ∧
        0 < tripleAreaCoefficientAlongRoot branch eps t alpha := by
  let q0 := tripleBoundaryParameter alpha0
  let interval := Metric.ball q0 eta
  have hq0 : q0 ∈ interval := Metric.mem_ball_self heta
  have hopen : IsOpen interval := Metric.isOpen_ball
  have hb2 : ContDiffOn ℝ 2 branch interval := hsmooth.of_le
    (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hB2 := tripleAreaParameterRoot_contDiffOn branch interval 2 hb2
  have hBdiff (q : TripleChartParameters) (hq : q ∈ interval) :
      DifferentiableAt ℝ (tripleAreaParameterRoot branch) q :=
    (hB2.contDiffAt (hopen.mem_nhds hq)).differentiableAt (by norm_num)
  have hpath : ContDiff ℝ 1 (fun t : ℝ => tripleParameter 0 t alpha0) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [tripleParameter] <;> fun_prop
  have hbsmooth : ContDiffAt ℝ 1 (fun t => branch (tripleParameter 0 t alpha0)) 0 :=
    (hb2.contDiffAt (hopen.mem_nhds hq0)).of_le (by norm_num) |>.comp 0 hpath.contDiffAt
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), dist (tripleParameter 0 t alpha0) q0 < eta :=
    hpath.continuous.continuousAt.eventually (Metric.ball_mem_nhds q0 heta)
  have hzeroRoots : ∀ᶠ t in 𝓝 (0 : ℝ),
      tripleChartExtendedRows 0 t alpha0 (branch (tripleParameter 0 t alpha0)) = 0 := by
    filter_upwards [hnear] with t ht
    simpa only [tripleChartParameterRows, tripleParameter_alpha,
      show tripleParameter 0 t alpha0 0 = 0 from rfl,
      show tripleParameter 0 t alpha0 1 = t from rfl] using hroots _ ht
  have hzeroRadii : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ i, 0 < tripleChartRadii t alpha0 (branch (tripleParameter 0 t alpha0)) i := by
    filter_upwards [hnear] with t ht
    simpa only [tripleParameter_alpha, show tripleParameter 0 t alpha0 1 = t from rfl] using hradii _ ht
  have hactual := tripleAreaAlongZeroRoot_hasDerivAt alpha0 ha.2
    (fun t => branch (tripleParameter 0 t alpha0)) hbsmooth hzeroRoots hzeroRadii
  have hjoint := tripleAreaAlongRoot_hasDerivAt_of_joint branch 0 0 alpha0 (hBdiff q0 hq0)
  have hbasePartial : tripleAreaPartialDerivative branch q0 =
      (tripleGapMatrix *ᵥ z0) 0 * (tripleGapMatrix *ᵥ z0) 1 *
        ((tripleGapMatrix *ᵥ z0) 0 + (tripleGapMatrix *ᵥ z0) 1) / 2 := by
    have he := hjoint.unique hactual
    change tripleAreaPartialDerivative branch q0 =
      branch q0 5 * branch q0 6 * (branch q0 5 + branch q0 6) / 2 at he
    rw [show branch q0 = tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z0) from hbase] at he
    simpa [tripleUnitPoint] using he
  have hg0 : 0 < (tripleGapMatrix *ᵥ z0) 0 := by
    rw [tripleGapMatrix_mulVec_entry]
    exact sub_pos.mpr (hz 0 1 (by decide))
  have hg1 : 0 < (tripleGapMatrix *ᵥ z0) 1 := by
    rw [tripleGapMatrix_mulVec_entry]
    exact sub_pos.mpr (hz 1 2 (by decide))
  have hpartialPos : 0 < tripleAreaPartialDerivative branch q0 := by
    rw [hbasePartial]
    positivity
  have hPC := tripleAreaPartialDerivative_continuousOn branch interval hopen hb2
  have hPnear := (hPC.continuousAt (hopen.mem_nhds hq0)).eventually (Ioi_mem_nhds hpartialPos)
  obtain ⟨dP, hdP, hP⟩ := Metric.eventually_nhds_iff.mp hPnear
  obtain ⟨dZ, hdZ, hZ⟩ := tripleChart_zero_face_area_zero_of_local_uniqueness
    alpha0 z0 ha hz hscalar tau htau eta r heta hr branch huniq
  let delta := min eta (min dP dZ)
  have hdelta : 0 < delta := lt_min heta (lt_min hdP hdZ)
  have hde : delta ≤ eta := min_le_left _ _
  have hdP' : delta ≤ dP := (min_le_right _ _).trans (min_le_left _ _)
  have hdZ' : delta ≤ dZ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨delta, hdelta, hde, ?_⟩
  intro eps t alpha hq hasum
  have hcoord := (dist_pi_lt_iff hdelta).mp hq
  have heps : |eps| < dZ := by
    have hepsδ : |eps| < delta := by
      simpa [tripleParameter, tripleBoundaryParameter, Real.dist_eq] using hcoord 0
    exact lt_of_lt_of_le hepsδ hdZ'
  have halpha : dist alpha alpha0 < dZ := by
    apply lt_of_lt_of_le _ hdZ'
    apply (dist_pi_lt_iff hdelta).mpr
    intro i
    fin_cases i
    · exact hcoord 2
    · exact hcoord 3
    · exact hcoord 4
  have hface := hZ eps alpha heps halpha hasum
  have hmap (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      tripleParameter eps (s * t) alpha ∈ interval :=
    lt_of_lt_of_le (tripleParameter_scale_segment_mem_ball alpha0 alpha eps t delta hdelta hq s hs) hde
  have hD (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      DifferentiableAt ℝ (tripleAreaAlongRoot branch eps alpha) (s * t) :=
    (tripleAreaAlongRoot_hasDerivAt_of_joint branch eps (s * t) alpha (hBdiff _ (hmap s hs))).differentiableAt
  have hderivEq (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      deriv (tripleAreaAlongRoot branch eps alpha) (s * t) =
        tripleAreaPartialDerivative branch (tripleParameter eps (s * t) alpha) :=
    tripleAreaAlongRoot_deriv_eq_partial branch eps (s * t) alpha (hBdiff _ (hmap s hs))
  have hscalarCont : Continuous (fun s : ℝ => tripleParameter eps (s * t) alpha) := by
    simp only [tripleParameter]
    fun_prop
  have hcont : ContinuousOn (fun s : ℝ => deriv (tripleAreaAlongRoot branch eps alpha) (s * t))
      (Icc 0 1) := (hPC.comp hscalarCont.continuousOn hmap).congr (fun s hs => hderivEq s hs)
  have hpos (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      0 < deriv (tripleAreaAlongRoot branch eps alpha) (s * t) := by
    rw [hderivEq s hs]
    apply hP
    exact lt_of_lt_of_le (tripleParameter_scale_segment_mem_ball alpha0 alpha eps t delta hdelta hq s hs) hdP'
  refine ⟨tripleInternalArea_factor_cubic_along_root branch eps t alpha hface hD hcont, ?_⟩
  apply intervalIntegral.integral_pos (by norm_num) hcont
  · intro s hs
    exact (hpos s ⟨hs.1.le, hs.2⟩).le
  · exact ⟨0, by norm_num, hpos 0 (by norm_num)⟩

end DominantFiveBody
