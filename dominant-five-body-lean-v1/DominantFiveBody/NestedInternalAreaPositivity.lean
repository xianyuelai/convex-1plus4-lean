import DominantFiveBody.NestedAreaPositivity

/-! # Positivity of the cubic nested area factor along the whole root

The zero-face identity is an explicit input here. The companion
collinearity theorem supplies it from actual equations and uniqueness.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

def nestedScaleDirection : NestedChartParameters := ![0,1,0,0]

theorem nestedParameter_hasDerivAt (eps t eta alpha : ℝ) :
    HasDerivAt (fun s => nestedParameter eps s eta alpha) nestedScaleDirection t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_const t eps
  · exact hasDerivAt_id t
  · exact hasDerivAt_const t eta
  · exact hasDerivAt_const t alpha

def nestedAreaParameterRoot (branch : NestedChartParameters → NestedChartVariables)
    (q : NestedChartParameters) : ℝ :=
  nestedInternalAreaQuotient (q 1) (q 2) (q 3) (branch q)

def nestedAreaPartialDerivative (branch : NestedChartParameters → NestedChartVariables)
    (q : NestedChartParameters) : ℝ :=
  fderiv ℝ (nestedAreaParameterRoot branch) q nestedScaleDirection

theorem nestedAreaParameterRoot_contDiffOn (branch : NestedChartParameters → NestedChartVariables)
    (s : Set NestedChartParameters) (n : ℕ∞ω) (hs : ContDiffOn ℝ n branch s) :
    ContDiffOn ℝ n (nestedAreaParameterRoot branch) s := by
  have hp : ContDiffOn ℝ n (fun q : NestedChartParameters => (q,branch q)) s :=
    contDiffOn_id.prodMk hs
  convert! (nestedInternalAreaQuotient_joint_contDiff n).comp_contDiffOn hp using 1

theorem nestedAreaAlongRoot_hasDerivAt_of_joint (branch : NestedChartParameters → NestedChartVariables)
    (eps t eta alpha : ℝ)
    (hd : DifferentiableAt ℝ (nestedAreaParameterRoot branch) (nestedParameter eps t eta alpha)) :
    HasDerivAt (nestedAreaAlongRoot branch eps eta alpha)
      (nestedAreaPartialDerivative branch (nestedParameter eps t eta alpha)) t := by
  have h := hd.hasFDerivAt.comp_hasDerivAt t (nestedParameter_hasDerivAt eps t eta alpha)
  convert! h using 1

theorem nestedAreaAlongRoot_deriv_eq_partial (branch : NestedChartParameters → NestedChartVariables)
    (eps t eta alpha : ℝ)
    (hd : DifferentiableAt ℝ (nestedAreaParameterRoot branch) (nestedParameter eps t eta alpha)) :
    deriv (nestedAreaAlongRoot branch eps eta alpha) t=
      nestedAreaPartialDerivative branch (nestedParameter eps t eta alpha) :=
  (nestedAreaAlongRoot_hasDerivAt_of_joint branch eps t eta alpha hd).deriv

theorem nestedAreaPartialDerivative_continuousOn (branch : NestedChartParameters → NestedChartVariables)
    (s : Set NestedChartParameters) (hs : IsOpen s) (hb : ContDiffOn ℝ 2 branch s) :
    ContinuousOn (nestedAreaPartialDerivative branch) s :=
  (((nestedAreaParameterRoot_contDiffOn branch s 2 hb).fderiv_of_isOpen hs
    (by norm_num : (0 : ℕ∞ω)+1≤2)).clm_apply contDiffOn_const).continuousOn

theorem nestedParameter_scale_segment_mem_ball (alpha0 eps t eta alpha delta : ℝ)
    (hdelta : 0<delta) (hq : dist (nestedParameter eps t eta alpha) (nestedParameter 0 0 0 alpha0)<delta)
    (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) :
    dist (nestedParameter eps (s*t) eta alpha) (nestedParameter 0 0 0 alpha0)<delta := by
  have hc := (dist_pi_lt_iff hdelta).mp hq
  apply (dist_pi_lt_iff hdelta).mpr
  intro i
  fin_cases i
  · exact hc 0
  · have ht : |t|<delta := by simpa [nestedParameter,Real.dist_eq] using hc 1
    change dist (s*t) 0<delta
    rw [Real.dist_eq,sub_zero,abs_mul,abs_of_nonneg hs.1]
    exact lt_of_le_of_lt (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hs.2 (abs_nonneg t)) ht
  · exact hc 2
  · exact hc 3

theorem nestedChart_internal_area_positive_neighborhood_of_zero_face
    (alpha0 tau omega radius : ℝ) (hw : |omega|=1) (hrad : 0<radius)
    (branch : NestedChartParameters → NestedChartVariables)
    (hbase : branch (nestedParameter 0 0 0 alpha0)=nestedBasePoint (tau*h) omega)
    (hsmooth : ContDiffOn ℝ ∞ branch (Metric.ball (nestedParameter 0 0 0 alpha0) radius))
    (hroots : ∀ q,dist q (nestedParameter 0 0 0 alpha0)<radius →
      nestedChartParameterRows q (branch q)=0)
    (hradii : ∀ q,dist q (nestedParameter 0 0 0 alpha0)<radius →
      ∀ i,0<nestedChartRadii (q 1) (q 2) (q 3) (branch q) i)
    (hzero : ∀ eps eta alpha,dist (nestedParameter eps 0 eta alpha)
        (nestedParameter 0 0 0 alpha0)<radius → 0<eta → alpha∈Icc (0 : ℝ) 1 →
      nestedAreaAlongRoot branch eps eta alpha 0=0) :
    ∃ delta : ℝ,0<delta ∧ delta≤radius ∧
      ∀ eps t eta alpha,dist (nestedParameter eps t eta alpha)
        (nestedParameter 0 0 0 alpha0)<delta → 0<eta → alpha∈Icc (0 : ℝ) 1 →
        orientedArea (liftRelative (nestedChartPoints t eta alpha
          (branch (nestedParameter eps t eta alpha)))) 1 2 3=
          t^3*eta*nestedAreaCoefficientAlongRoot branch eps t eta alpha ∧
        0<nestedAreaCoefficientAlongRoot branch eps t eta alpha := by
  let q0 := nestedParameter 0 0 0 alpha0
  let interval := Metric.ball q0 radius
  have hq0 : q0∈interval := Metric.mem_ball_self hrad
  have hopen : IsOpen interval := Metric.isOpen_ball
  have hb2 : ContDiffOn ℝ 2 branch interval := hsmooth.of_le
    (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞)≤⊤))
  have hB2 := nestedAreaParameterRoot_contDiffOn branch interval 2 hb2
  have hBdiff (q : NestedChartParameters) (hq : q∈interval) :
      DifferentiableAt ℝ (nestedAreaParameterRoot branch) q :=
    (hB2.contDiffAt (hopen.mem_nhds hq)).differentiableAt (by norm_num)
  have hpath : ContDiff ℝ 1 (fun t : ℝ => nestedParameter 0 t 0 alpha0) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [nestedParameter] <;> fun_prop
  have hbsmooth : ContDiffAt ℝ 1 (fun t => branch (nestedParameter 0 t 0 alpha0)) 0 :=
    (hb2.contDiffAt (hopen.mem_nhds hq0)).of_le (by norm_num) |>.comp 0 hpath.contDiffAt
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ),dist (nestedParameter 0 t 0 alpha0) q0<radius :=
    hpath.continuous.continuousAt.eventually (Metric.ball_mem_nhds q0 hrad)
  have hzeroRoots : ∀ᶠ t in 𝓝 (0 : ℝ),
      nestedChartExtendedRows 0 t 0 alpha0 (branch (nestedParameter 0 t 0 alpha0))=0 := by
    filter_upwards [hnear] with t ht
    exact hroots _ ht
  have hzeroRadii : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ i,0<nestedChartRadii t 0 alpha0 (branch (nestedParameter 0 t 0 alpha0)) i := by
    filter_upwards [hnear] with t ht
    exact hradii _ ht
  have hZ : branch q0 5≠0 := by
    rw [show branch q0=nestedBasePoint (tau*h) omega from hbase]
    exact nestedBasePoint_outer_ne_zero omega hw
  have hz : 0<branch q0 6 := by
    rw [show branch q0=nestedBasePoint (tau*h) omega from hbase]
    exact pairBoundaryScale_pos (3*tripleD0) (mul_pos (by norm_num) tripleD0_pos)
  have hactualPos := nestedAreaAlongZeroRoot_base_deriv_pos alpha0
    (fun t => branch (nestedParameter 0 t 0 alpha0)) hbsmooth hzeroRoots hzeroRadii hZ hz
  have hjoint := nestedAreaAlongRoot_hasDerivAt_of_joint branch 0 0 0 alpha0 (hBdiff q0 hq0)
  have hpartialPos : 0<nestedAreaPartialDerivative branch q0 := by
    change 0<deriv (nestedAreaAlongRoot branch 0 0 alpha0) 0 at hactualPos
    rwa [hjoint.deriv] at hactualPos
  have hPC := nestedAreaPartialDerivative_continuousOn branch interval hopen hb2
  have hPnear := (hPC.continuousAt (hopen.mem_nhds hq0)).eventually (Ioi_mem_nhds hpartialPos)
  obtain ⟨dP,hdP,hP⟩ := Metric.eventually_nhds_iff.mp hPnear
  let delta := min radius dP
  have hdelta : 0<delta := lt_min hrad hdP
  have hde : delta≤radius := min_le_left _ _
  have hdP' : delta≤dP := min_le_right _ _
  refine ⟨delta,hdelta,hde,?_⟩
  intro eps t eta alpha hq heta halpha
  have hfaceBall : dist (nestedParameter eps 0 eta alpha) q0<radius := by
    apply lt_of_lt_of_le _ hde
    simpa using nestedParameter_scale_segment_mem_ball alpha0 eps t eta alpha delta hdelta hq
      (0 : ℝ) (by norm_num)
  have hface : nestedAreaAlongRoot branch eps eta alpha 0=0 :=
    hzero eps eta alpha hfaceBall heta halpha
  have hmap (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) :
      nestedParameter eps (s*t) eta alpha∈interval :=
    lt_of_lt_of_le (nestedParameter_scale_segment_mem_ball alpha0 eps t eta alpha delta hdelta hq s hs) hde
  have hD (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) :
      DifferentiableAt ℝ (nestedAreaAlongRoot branch eps eta alpha) (s*t) :=
    (nestedAreaAlongRoot_hasDerivAt_of_joint branch eps (s*t) eta alpha (hBdiff _ (hmap s hs))).differentiableAt
  have hderivEq (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) :
      deriv (nestedAreaAlongRoot branch eps eta alpha) (s*t)=
        nestedAreaPartialDerivative branch (nestedParameter eps (s*t) eta alpha) :=
    nestedAreaAlongRoot_deriv_eq_partial branch eps (s*t) eta alpha (hBdiff _ (hmap s hs))
  have hscalarCont : Continuous (fun s : ℝ => nestedParameter eps (s*t) eta alpha) := by
    simp only [nestedParameter]
    fun_prop
  have hcont : ContinuousOn (fun s : ℝ => deriv (nestedAreaAlongRoot branch eps eta alpha) (s*t))
      (Icc 0 1) := (hPC.comp hscalarCont.continuousOn hmap).congr (fun s hs => hderivEq s hs)
  have hpos (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) :
      0<deriv (nestedAreaAlongRoot branch eps eta alpha) (s*t) := by
    rw [hderivEq s hs]
    apply hP
    exact lt_of_lt_of_le (nestedParameter_scale_segment_mem_ball alpha0 eps t eta alpha delta hdelta hq s hs) hdP'
  refine ⟨nestedInternalArea_factor_cubic_along_root branch eps t eta alpha hface hD hcont,?_⟩
  apply intervalIntegral.integral_pos (by norm_num) hcont
  · intro s hs
    exact (hpos s ⟨hs.1.le,hs.2⟩).le
  · exact ⟨0,by norm_num,hpos 0 (by norm_num)⟩

end DominantFiveBody
