import DominantFiveBody.NestedConvexContinuation
import DominantFiveBody.NestedPhysicalCoordinates
import DominantFiveBody.FixedLabelEndpoint

/-! # Capture of actual nested chart sequences in one smooth branch

The current positive t,eta,alpha are retained throughout each epsilon
connection interval. Its endpoint is epsilon zero at those fixed masses.
The fraction may vary and converge on the chosen subsequence.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

structure NestedCapturedBranches (eps t eta alpha : ℕ → ℝ) (y : ℕ → NestedChartVariables)
    (tau omega : ℝ) where
  tailStart : ℕ
  radius : ℝ
  radius_pos : 0<radius
  inverseBound : ℝ
  inverseBound_pos : 0 < inverseBound
  branch : ℕ → ℝ → NestedChartVariables
  parameters_pos : ∀ n,0<eps (tailStart+n)
  parameters_lt_radius : ∀ n,eps (tailStart+n)<radius
  continuous : ∀ n,ContinuousOn (branch n) (Ico 0 radius)
  hits : ∀ n,branch n (eps (tailStart+n))=y (tailStart+n)
  regular_roots : ∀ n s,s∈Ico 0 radius →
    NestedChartRegular s (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n)) (branch n s) ∧
    nestedChartExtendedRows s (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n)) (branch n s)=0
  domain : ∀ n s,s∈Ico 0 radius →
    NestedContinuationDomain (nestedParameter s (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n)),branch n s)
  invertible : ∀ n s,s∈Ico 0 radius →
    (nestedChartJacobian s (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n)) (branch n s)).IsInvertible
  inverse_norm : ∀ n s,s∈Ico 0 radius →
    ‖(nestedChartJacobian s (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n)) (branch n s)).inverse‖ ≤ inverseBound
  convex : ∀ n s,s∈Ico 0 radius →
    StrictConvexInOrder (nestedBoundaryHullOrder tau omega)
      (liftRelative (nestedChartPoints (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n)) (branch n s)))
  physical : ∀ n s,0<s → s<radius →
    StrictConvexCentralConfiguration
      (masses s (nestedChartMass (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n))))
      (nestedBoundaryHullOrder tau omega)
      (nestedChartConfiguration (nestedParameter s (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n))) (branch n s)) ∧
    NondegenerateCentralConfiguration
      (masses s (nestedChartMass (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n))))
      (nestedChartConfiguration (nestedParameter s (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n))) (branch n s))
  endpoints : ∀ n,
    (∀ i,nestedChartRadii (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n)) (branch n 0) i=1) ∧
    branch n 0 2=0 ∧ branch n 0 3=0 ∧
    RelativeCollisionFree (nestedChartPoints (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n)) (branch n 0)) ∧
    SeparatedSemicircle (nestedChartAngles (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n)) (branch n 0)) ∧
    ∀ i,coorbitalResidual (nestedChartMass (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n)))
      (nestedChartAngles (t (tailStart+n)) (eta (tailStart+n)) (alpha (tailStart+n)) (branch n 0)) i=0

theorem nestedFixedMassEndpoint_eq_fixedLabelEndpoint (t eta alpha : ℝ)
    (y : NestedChartVariables) (sigma : HullOrder)
    (hm : PositiveRatio (nestedChartMass t eta alpha))
    (hunit : ∀ i,nestedChartRadii t eta alpha y i=1)
    (hwidth : ∀ i j,|nestedChartAngles t eta alpha y j-nestedChartAngles t eta alpha y i|<Real.pi)
    (hconv : StrictConvexInOrder sigma (liftRelative (nestedChartPoints t eta alpha y)))
    (hco : ∀ i,coorbitalResidual (nestedChartMass t eta alpha) (nestedChartAngles t eta alpha y) i=0) :
    nestedChartConfiguration (nestedParameter 0 t eta alpha) y=
      fixedLabelCoorbitalEndpoint (nestedChartMass t eta alpha) sigma 3 := by
  have hconvUnit : StrictConvexInOrder sigma
      (liftRelative (polarSatellites (fun _ => 1) (nestedChartAngles t eta alpha y))) := by
    simpa only [nestedChartPoints,funext hunit] using hconv
  have hangles := actualCoorbitalAngles_eq_fixedLabelEndpoint (nestedChartMass t eta alpha)
    sigma 3 (nestedChartAngles t eta alpha y) hm rfl hwidth hconvUnit hco
  change centeredFromRelative 0 (nestedChartMass t eta alpha) (nestedChartPoints t eta alpha y)=_
  rw [nestedChartPoints,funext hunit,hangles]
  funext i
  simp [centeredFromRelative,fixedLabelCoorbitalEndpoint]

theorem NestedCapturedBranches.endpoint_eq {eps t eta alpha : ℕ → ℝ}
    {y : ℕ → NestedChartVariables} {tau omega : ℝ}
    (c : NestedCapturedBranches eps t eta alpha y tau omega)
    (hm : ∀ n,PositiveRatio (nestedChartMass (t n) (eta n) (alpha n))) (n : ℕ) :
    nestedChartConfiguration (nestedParameter 0 (t (c.tailStart+n)) (eta (c.tailStart+n))
      (alpha (c.tailStart+n))) (c.branch n 0)=
      fixedLabelCoorbitalEndpoint (nestedChartMass (t (c.tailStart+n)) (eta (c.tailStart+n))
        (alpha (c.tailStart+n))) (nestedBoundaryHullOrder tau omega) 3 := by
  have hzero : (0 : ℝ)∈Ico 0 c.radius := ⟨le_rfl,c.radius_pos⟩
  obtain ⟨hu,_,_,_,_,hco⟩ := c.endpoints n
  exact nestedFixedMassEndpoint_eq_fixedLabelEndpoint _ _ _ _ _ (hm (c.tailStart+n)) hu
    (c.domain n 0 hzero).2.2 (c.convex n 0 hzero) hco

theorem nestedChart_sequence_capture_of_scaled_limits (alpha0 tau omega : ℝ)
    (ha0 : alpha0∈Icc (0 : ℝ) 1) (htau : tau=1 ∨ tau=-1) (hw : omega=1 ∨ omega=-1)
    (eps t eta alpha : ℕ → ℝ) (y : ℕ → NestedChartVariables)
    (heps : ∀ n,0<eps n) (ht : ∀ n,0<t n) (heta : ∀ n,0<eta n)
    (ha : ∀ n,alpha n∈Icc (0 : ℝ) 1)
    (hm : ∀ n,PositiveRatio (nestedChartMass (t n) (eta n) (alpha n)))
    (hepslim : Tendsto eps atTop (𝓝 0)) (htlim : Tendsto t atTop (𝓝 0))
    (hetalim : Tendsto eta atTop (𝓝 0)) (halim : Tendsto alpha atTop (𝓝 alpha0))
    (hylim : Tendsto y atTop (𝓝 (nestedBasePoint (tau*h) omega)))
    (hroots : ∀ n,nestedChartExtendedRows (eps n) (t n) (eta n) (alpha n) (y n)=0) :
    Nonempty (NestedCapturedBranches eps t eta alpha y tau omega) := by
  classical
  obtain ⟨d,r,C,hd,hr,hC,_,_,B,_,hBsmooth,hB⟩ :=
    nestedChart_convex_physical_continuation alpha0 tau omega ha0 htau hw 1 (by norm_num)
  have hepsnear : ∀ᶠ n in atTop,|eps n|<d := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using
      hepslim.eventually (Metric.ball_mem_nhds (0 : ℝ) hd)
  have htnear : ∀ᶠ n in atTop,|t n|<d := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using
      htlim.eventually (Metric.ball_mem_nhds (0 : ℝ) hd)
  have hetanear : ∀ᶠ n in atTop,|eta n|<d := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using
      hetalim.eventually (Metric.ball_mem_nhds (0 : ℝ) hd)
  have hanear : ∀ᶠ n in atTop,dist (alpha n) alpha0<d :=
    halim.eventually (Metric.ball_mem_nhds alpha0 hd)
  have hynear : ∀ᶠ n in atTop,dist (y n) (nestedBasePoint (tau*h) omega)<r :=
    hylim.eventually (Metric.ball_mem_nhds _ hr)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp
    (hepsnear.and (htnear.and (hetanear.and (hanear.and hynear))))
  have htail (n : ℕ) := hN (N+n) (Nat.le_add_right N n)
  let q (n : ℕ) (s : ℝ) := nestedParameter s (t (N+n)) (eta (N+n)) (alpha (N+n))
  let branch (n : ℕ) (s : ℝ) := B (q n s)
  have hdist (n : ℕ) (s : ℝ) (hs : |s|<d) :
      dist (q n s) (nestedParameter 0 0 0 alpha0)<d := by
    apply (dist_pi_lt_iff hd).mpr
    intro i
    fin_cases i
    · simpa [q,nestedParameter,Real.dist_eq] using hs
    · simpa [q,nestedParameter,Real.dist_eq] using (htail n).2.1
    · simpa [q,nestedParameter,Real.dist_eq] using (htail n).2.2.1
    · exact (htail n).2.2.2.1
  have hdata (n : ℕ) (s : ℝ) (hs : |s|<d) := hB (q n s) (hdist n s hs)
  refine ⟨{
    tailStart := N
    radius := d
    radius_pos := hd
    inverseBound := C
    inverseBound_pos := hC
    branch := branch
    parameters_pos := fun n => heps (N+n)
    parameters_lt_radius := fun n => lt_of_le_of_lt (le_abs_self _) (htail n).1
    continuous := ?_
    hits := ?_
    regular_roots := ?_
    domain := ?_
    invertible := ?_
    inverse_norm := ?_
    convex := ?_
    physical := ?_
    endpoints := ?_ }⟩
  · intro n
    apply hBsmooth.continuousOn.comp (show Continuous (q n) by
      unfold q nestedParameter
      fun_prop).continuousOn
    intro s hs
    exact hdist n s (by simpa only [abs_of_nonneg hs.1] using hs.2)
  · intro n
    obtain ⟨_,_,_,_,_,huniq,_⟩ := hdata n (eps (N+n)) (htail n).1
    exact (huniq (y (N+n)) (htail n).2.2.2.2).mp (hroots (N+n))
  · intro n s hs
    obtain ⟨_,hdomain,_,_,hroot,_⟩ := hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)
    exact ⟨hdomain.1,hroot⟩
  · intro n s hs
    exact (hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)).2.1
  · intro n s hs
    exact (hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)).2.2.1
  · intro n s hs
    exact (hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)).2.2.2.1
  · intro n s hs
    obtain ⟨_,_,_,_,_,_,hconv,_⟩ := hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)
    exact hconv (ht (N+n)) (heta (N+n)) (ha (N+n))
  · intro n s hs hsδ
    obtain ⟨_,_,_,_,_,_,_,hphys,_⟩ := hdata n s (by simpa only [abs_of_pos hs] using hsδ)
    exact hphys hs (ht (N+n)) (heta (N+n)) (ha (N+n)) (hm (N+n))
  · intro n
    obtain ⟨_,_,_,_,_,_,_,_,hend⟩ := hdata n 0 (by simpa using hd)
    exact hend rfl (ht (N+n)) (heta (N+n)) (hm (N+n))

/-- The compact fraction can be arbitrary on the original sequence.
Its convergence is obtained by extracting a strictly increasing
subsequence; it is not a restriction on the physical mass family. -/
theorem nestedChart_subsequence_capture_of_scaled_limits (tau omega : ℝ)
    (htau : tau=1 ∨ tau=-1) (hw : omega=1 ∨ omega=-1)
    (eps t eta alpha : ℕ → ℝ) (y : ℕ → NestedChartVariables)
    (heps : ∀ n,0<eps n) (ht : ∀ n,0<t n) (heta : ∀ n,0<eta n)
    (ha : ∀ n,alpha n∈Icc (0 : ℝ) 1)
    (hm : ∀ n,PositiveRatio (nestedChartMass (t n) (eta n) (alpha n)))
    (hepslim : Tendsto eps atTop (𝓝 0)) (htlim : Tendsto t atTop (𝓝 0))
    (hetalim : Tendsto eta atTop (𝓝 0))
    (hylim : Tendsto y atTop (𝓝 (nestedBasePoint (tau*h) omega)))
    (hroots : ∀ n,nestedChartExtendedRows (eps n) (t n) (eta n) (alpha n) (y n)=0) :
    ∃ alpha0∈Icc (0 : ℝ) 1,∃ subseq : ℕ → ℕ,StrictMono subseq ∧
      Nonempty (NestedCapturedBranches (eps ∘ subseq) (t ∘ subseq) (eta ∘ subseq)
        (alpha ∘ subseq) (y ∘ subseq) tau omega) := by
  obtain ⟨alpha0,ha0,subseq,hmono,halim⟩ := isCompact_Icc.isSeqCompact ha
  refine ⟨alpha0,ha0,subseq,hmono,?_⟩
  exact nestedChart_sequence_capture_of_scaled_limits alpha0 tau omega ha0 htau hw
    (eps ∘ subseq) (t ∘ subseq) (eta ∘ subseq) (alpha ∘ subseq) (y ∘ subseq)
    (fun n => heps (subseq n)) (fun n => ht (subseq n)) (fun n => heta (subseq n))
    (fun n => ha (subseq n)) (fun n => hm (subseq n))
    (hepslim.comp hmono.tendsto_atTop) (htlim.comp hmono.tendsto_atTop)
    (hetalim.comp hmono.tendsto_atTop) halim (hylim.comp hmono.tendsto_atTop)
    (fun n => hroots (subseq n))

/-- Physical entry point: the chart equations are proved from the
original normalized equations and the explicit two-scale inverse.
Only the classified scale and coordinate limits remain as inputs. -/
theorem nestedPhysical_subsequence_capture_of_scaled_limits (tau omega : ℝ)
    (htau : tau=1 ∨ tau=-1) (hw : omega=1 ∨ omega=-1)
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (r theta : ℕ → Satellite → ℝ)
    (heps : ∀ n,0<eps n) (hm : ∀ n,PositiveRatio (mu n))
    (hr : ∀ n i,0<r n i) (hfixed : ∀ n,theta n 3=0)
    (hcf : ∀ n,RelativeCollisionFree (polarSatellites (r n) (theta n)))
    (hphysical : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n))
      (centeredFromRelative (eps n) (mu n) (polarSatellites (r n) (theta n))))
    (hepslim : Tendsto eps atTop (𝓝 0))
    (htlim : Tendsto (fun n => nestedPhysicalScale (mu n)) atTop (𝓝 0))
    (hetalim : Tendsto (fun n => nestedPhysicalEta (mu n)) atTop (𝓝 0))
    (hylim : Tendsto (fun n => nestedVariablesFromPolar (nestedPhysicalScale (mu n))
      (nestedPhysicalEta (mu n)) (nestedPhysicalAlpha (mu n)) (r n) (theta n)) atTop
      (𝓝 (nestedBasePoint (tau*h) omega))) :
    ∃ alpha0∈Icc (0 : ℝ) 1,∃ subseq : ℕ → ℕ,StrictMono subseq ∧
      Nonempty (NestedCapturedBranches (eps ∘ subseq)
        ((fun n => nestedPhysicalScale (mu n)) ∘ subseq)
        ((fun n => nestedPhysicalEta (mu n)) ∘ subseq)
        ((fun n => nestedPhysicalAlpha (mu n)) ∘ subseq)
        ((fun n => nestedVariablesFromPolar (nestedPhysicalScale (mu n)) (nestedPhysicalEta (mu n))
          (nestedPhysicalAlpha (mu n)) (r n) (theta n)) ∘ subseq) tau omega) := by
  apply nestedChart_subsequence_capture_of_scaled_limits tau omega htau hw eps _ _ _ _ heps
    (fun n => (nestedPhysicalParameters_bounds (mu n) (hm n)).1)
    (fun n => (nestedPhysicalParameters_bounds (mu n) (hm n)).2.2.1)
    (fun n => ⟨(nestedPhysicalParameters_bounds (mu n) (hm n)).2.2.2.2.1.le,
      (nestedPhysicalParameters_bounds (mu n) (hm n)).2.2.2.2.2.le⟩)
    (fun n => by rw [nestedPhysicalParameters_mass _ (hm n)]; exact hm n)
    hepslim htlim hetalim hylim
  intro n
  exact nestedPhysicalCoordinates_root (eps n) (mu n) (heps n) (hm n) (r n) (theta n)
    (hr n) (hfixed n) (hcf n) (hphysical n)

end DominantFiveBody
