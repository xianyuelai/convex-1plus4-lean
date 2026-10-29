import DominantFiveBody.NestedSlowCoordinates
import DominantFiveBody.NestedZeroSeed
import DominantFiveBody.NestedContinuation

/-! # Exact zero-scale collinearity of the actual nested implicit root

The seed is the branch's own epsilon-zero root at the same positive eta
and alpha. Its full scalar probe system is recovered from actual rows.
The proved slow candidate is identified using the genuine root-ball
uniqueness. Epsilon and eta vary independently throughout.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1000000

theorem nestedChart_zero_face_parallel_of_local_uniqueness
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
      let y := branch (nestedParameter eps 0 eta alpha)
      y 3*y 5-y 2*y 6=0 := by
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
  change branch q 3*branch q 5-branch q 2*branch q 6=0
  rw [heq]
  exact nestedSlowPoint_parallel eps tau (seed q 5) (seed q 6)

theorem nestedChart_zero_face_area_zero_of_local_uniqueness
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
      0<eta → alpha∈Icc (0 : ℝ) 1 → nestedAreaAlongRoot branch eps eta alpha 0=0 := by
  obtain ⟨delta,hdelta,hdd,hpar⟩ := nestedChart_zero_face_parallel_of_local_uniqueness
    alpha0 tau omega htau d r hd hr branch hbase hsmooth hdomain hroots huniq
  refine ⟨delta,hdelta,hdd,?_⟩
  intro eps eta alpha hq he ha
  exact nestedInternalAreaQuotient_zero_of_parallel eta alpha _ (hpar eps eta alpha hq he ha)

theorem nestedChart_zero_face_area_zero_nonnegative_eta
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
      0≤eta → alpha∈Icc (0 : ℝ) 1 → nestedAreaAlongRoot branch eps eta alpha 0=0 := by
  obtain ⟨delta,hdelta,hdd,hzero⟩ := nestedChart_zero_face_area_zero_of_local_uniqueness
    alpha0 tau omega htau d r hd hr branch hbase hsmooth hdomain hroots huniq
  refine ⟨delta,hdelta,hdd,?_⟩
  intro eps eta alpha hq he ha
  rcases he.eq_or_lt with he0 | hep
  · subst eta
    let q0 := nestedParameter 0 0 0 alpha0
    let p (s : ℝ) := nestedParameter eps 0 s alpha
    have hp : Continuous p := by unfold p nestedParameter; fun_prop
    have hb0 : ContinuousAt branch (p 0) := hsmooth.continuousOn.continuousAt
      (Metric.isOpen_ball.mem_nhds (lt_of_lt_of_le hq hdd))
    have hb : ContinuousAt (fun s => branch (p s)) 0 :=
      ContinuousAt.comp' (f := p) hb0 hp.continuousAt
    have hgraph : ContinuousAt (fun s => (p s,branch (p s))) 0 := hp.continuousAt.prodMk hb
    have hBA : ContinuousAt (fun v : NestedJointVariables =>
        nestedInternalAreaQuotient (v.1 1) (v.1 2) (v.1 3) v.2) (p 0,branch (p 0)) :=
      (nestedInternalAreaQuotient_joint_contDiff 0).continuous.continuousAt
    have hB : ContinuousAt (fun s => nestedAreaAlongRoot branch eps s alpha 0) 0 :=
      ContinuousAt.comp' (f := fun s => (p s,branch (p s))) hBA hgraph
    have hnear : ∀ᶠ s in 𝓝 (0 : ℝ),dist (p s) q0<delta :=
      hp.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hq)
    have hn : ∀ᶠ s in 𝓝[>] (0 : ℝ),dist (p s) q0<delta :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear
    have hz : (fun s => nestedAreaAlongRoot branch eps s alpha 0) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [hn,self_mem_nhdsWithin] with s hs hspos
      exact hzero eps s alpha hs hspos ha
    exact tendsto_nhds_unique (hB.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hz.symm)
  · exact hzero eps eta alpha hq hep ha

end DominantFiveBody
