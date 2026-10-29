import DominantFiveBody.CoorbitalEqualMass
import DominantFiveBody.LocalContinuation
import DominantFiveBody.CoorbitalFiberCount
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.IsLocalHomeomorph

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

abbrev CoorbitalFreeAngles := Fin 3 → ℝ

theorem coorbitalKernel_contDiffAt (n : ℕ∞ω) {t : ℝ}
    (ht : t ≠ 0) (htpi : |t| < Real.pi) : ContDiffAt ℝ n coorbitalKernel t := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have hp : 0 < -t := neg_pos.mpr hneg
    have hpi : -t < Real.pi := by simpa [abs_of_neg hneg] using htpi
    have hc := (kernelF_contDiffAt n hp hpi).comp t
      (f := fun x : ℝ => -x) (by fun_prop)
    have heq : coorbitalKernel =ᶠ[𝓝 t] (fun x : ℝ => -kernelF (-x)) := by
      filter_upwards [Iio_mem_nhds hneg] with x hx
      simp [coorbitalKernel, not_le.mpr (show x < 0 from hx)]
    exact hc.neg.congr_of_eventuallyEq heq
  · have hpi : t < Real.pi := by simpa [abs_of_pos hpos] using htpi
    have heq : coorbitalKernel =ᶠ[𝓝 t] kernelF := by
      filter_upwards [Ioi_mem_nhds hpos] with x hx
      exact coorbitalKernel_eq_positive_formula x (le_of_lt hx)
    exact (kernelF_contDiffAt n hpos hpi).congr_of_eventuallyEq heq

def coorbitalReducedResidual (m : MassRatio) (a : CoorbitalFreeAngles) : CoorbitalFreeAngles :=
  coorbitalFreeRows (fun i => coorbitalResidual m (coorbitalAngleInjection a) i)

def coorbitalReducedDifferential (m : MassRatio) (theta : Satellite → ℝ) :
    CoorbitalFreeAngles →L[ℝ] CoorbitalFreeAngles :=
  coorbitalFreeRows.comp ((angularDifferential m theta).comp coorbitalAngleInjection)

theorem coorbitalReducedResidual_joint_contDiffAt (n : ℕ∞ω) (m : MassRatio)
    (a : CoorbitalFreeAngles) (hsep : SeparatedSemicircle (coorbitalAngleInjection a)) :
    ContDiffAt ℝ n (fun z : MassRatio × CoorbitalFreeAngles =>
      coorbitalReducedResidual z.1 z.2) (m, a) := by
  classical
  apply contDiffAt_pi.mpr
  intro i
  change ContDiffAt ℝ n (fun z : MassRatio × CoorbitalFreeAngles =>
    ∑ j ∈ Finset.univ.erase i.succ,
      z.1 j * coorbitalKernel (coorbitalAngleInjection z.2 j -
        coorbitalAngleInjection z.2 i.succ)) (m, a)
  apply ContDiffAt.sum
  intro j hj
  have h := hsep i.succ j (Ne.symm (Finset.mem_erase.mp hj).1)
  have hk := (coorbitalKernel_contDiffAt n (sub_ne_zero.mpr h.1.symm) h.2).comp (m, a)
    (f := fun z : MassRatio × CoorbitalFreeAngles =>
      coorbitalAngleInjection z.2 j - coorbitalAngleInjection z.2 i.succ) (by fun_prop)
  exact (by fun_prop : ContDiffAt ℝ n (fun z : MassRatio × CoorbitalFreeAngles => z.1 j) (m, a)).mul hk

theorem coorbitalReducedResidual_hasFDerivAt (m : MassRatio) (a : CoorbitalFreeAngles)
    (hsep : SeparatedSemicircle (coorbitalAngleInjection a)) :
    HasFDerivAt (coorbitalReducedResidual m)
      (coorbitalReducedDifferential m (coorbitalAngleInjection a)) a := by
  exact coorbitalFreeRows.hasFDerivAt.comp a
    ((coorbitalResidual_hasFDerivAt m (coorbitalAngleInjection a) hsep).comp a
      coorbitalAngleInjection.hasFDerivAt)

theorem coorbitalReducedDifferential_isInvertible (m : MassRatio) (theta : Satellite → ℝ)
    (hm : ∀ i, 0 < m i) (harc : OrderedSemicircle theta)
    (hroot : ∀ i, coorbitalResidual m theta i = 0) :
    (coorbitalReducedDifferential m theta).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  apply (LinearMap.ker_eq_bot (f := (coorbitalReducedDifferential m theta).toLinearMap)).mp
  apply (LinearMap.ker_eq_bot' (f := (coorbitalReducedDifferential m theta).toLinearMap)).mpr
  intro a ha
  let u := coorbitalAngleInjection a
  have hothers : ∀ i : Satellite, i ≠ 0 → angularDifferential m theta u i = 0 := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    have h := congrFun ha j
    simpa [coorbitalReducedDifferential, coorbitalFreeRows, u, Fin.succAbove_zero] using h
  have hzero : angularDifferential m theta u = 0 := by
    funext i
    by_cases hi : i = 0
    · subst i; exact angularDifferential_recover_row m theta u 0 (hm 0) hothers
    · exact hothers i hi
  have hc := (angularDifferential_kernel_iff_positive m theta u hm harc hroot).mp hzero
  funext j
  have h := hc j.succ 0
  simpa [u] using h

theorem coorbitalReducedResidual_local_implicitFunction (m : MassRatio)
    (a : CoorbitalFreeAngles) (hm : PositiveRatio m)
    (hdomain : CoorbitalAngleDomain (coorbitalAngleInjection a))
    (hroot : ∀ i, coorbitalResidual m (coorbitalAngleInjection a) i = 0) :
    ∃ psi : MassRatio → CoorbitalFreeAngles,
      psi m = a ∧ ContDiffAt ℝ ∞ psi m ∧
      (∀ᶠ q in 𝓝 m, coorbitalReducedResidual q (psi q) = 0) ∧
      (∀ᶠ z : MassRatio × CoorbitalFreeAngles in 𝓝 (m, a),
        coorbitalReducedResidual z.1 z.2 = 0 ↔ psi z.1 = z.2) := by
  have harc := orderedSemicircle_of_coorbitalAngleDomain _ hdomain
  have hsep := slice_separatedSemicircle_of_ordered _ harc
  let cdf := coorbitalReducedResidual_joint_contDiffAt ∞ m a hsep
  have hpartial_eq : fderiv ℝ (fun z : MassRatio × CoorbitalFreeAngles =>
      coorbitalReducedResidual z.1 z.2) (m, a) ∘L
      ContinuousLinearMap.inr ℝ MassRatio CoorbitalFreeAngles =
        coorbitalReducedDifferential m (coorbitalAngleInjection a) := by
    have hprod := cdf.differentiableAt (by simp) |>.hasFDerivAt
    have h := hprod.comp a ((hasFDerivAt_const m a).prodMk (hasFDerivAt_id a))
    convert! h.unique (coorbitalReducedResidual_hasFDerivAt m a hsep) using 1
  have hpartial : (fderiv ℝ (fun z : MassRatio × CoorbitalFreeAngles =>
      coorbitalReducedResidual z.1 z.2) (m, a) ∘L
      ContinuousLinearMap.inr ℝ MassRatio CoorbitalFreeAngles).IsInvertible := by
    rw [hpartial_eq]
    exact coorbitalReducedDifferential_isInvertible m _ hm.1 harc hroot
  have hz : coorbitalReducedResidual m a = 0 := by
    ext i; exact hroot i.succ
  let psi := cdf.implicitFunction (by simp) hpartial
  refine ⟨psi, cdf.implicitFunction_apply_self (by simp) hpartial,
    cdf.contDiffAt_implicitFunction (by simp) hpartial, ?_, ?_⟩
  · simpa only [hz] using cdf.eventually_apply_implicitFunction (by simp) hpartial
  · simpa only [hz] using cdf.eventually_apply_eq_iff_implicitFunction (by simp) hpartial

theorem coorbitalAngleInjection_freeRows (theta : Satellite → ℝ) (h0 : theta 0 = 0) :
    coorbitalAngleInjection (coorbitalFreeRows theta) = theta := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using h0.symm
  · simp [coorbitalFreeRows]

theorem coorbitalFreeRows_angleInjection (a : CoorbitalFreeAngles) :
    coorbitalFreeRows (coorbitalAngleInjection a) = a := by
  ext i; simp [coorbitalFreeRows]

theorem coorbitalFreeAngleDomain_iff (a : CoorbitalFreeAngles) :
    CoorbitalAngleDomain (coorbitalAngleInjection a) ↔
      OrderedSemicircle (coorbitalAngleInjection a) := by
  constructor
  · exact orderedSemicircle_of_coorbitalAngleDomain _
  · intro h
    refine ⟨by simp, ?_, ?_⟩
    · intro i j hij; exact sub_pos.mp (h i j hij).1
    · simpa using (h 0 3 (by decide)).2

theorem isOpen_coorbitalFreeAngleDomain :
    IsOpen {a : CoorbitalFreeAngles | CoorbitalAngleDomain (coorbitalAngleInjection a)} := by
  convert (isOpen_orderedSemicircle 4).preimage coorbitalAngleInjection.continuous using 1
  ext a; exact coorbitalFreeAngleDomain_iff a

theorem coorbitalReducedResidual_local_product (m : MassRatio)
    (a : CoorbitalFreeAngles) (hm : PositiveRatio m)
    (hdomain : CoorbitalAngleDomain (coorbitalAngleInjection a))
    (hroot : ∀ i, coorbitalResidual m (coorbitalAngleInjection a) i = 0) :
    ∃ psi : MassRatio → CoorbitalFreeAngles, ∃ eta zeta : ℝ,
      0 < eta ∧ 0 < zeta ∧ psi m = a ∧ ContDiffAt ℝ ∞ psi m ∧
      ContinuousOn psi (Metric.ball m eta) ∧
      ∀ q, dist q m < eta →
        CoorbitalAngleDomain (coorbitalAngleInjection (psi q)) ∧ dist (psi q) a < zeta ∧
        coorbitalReducedResidual q (psi q) = 0 ∧
        (∀ b, dist b a < zeta → (coorbitalReducedResidual q b = 0 ↔ psi q = b)) := by
  obtain ⟨psi, hbase, hsmooth, hroots, huniq⟩ :=
    coorbitalReducedResidual_local_implicitFunction m a hm hdomain hroot
  obtain ⟨r, hr, huniqNear⟩ := Metric.eventually_nhds_iff.mp huniq
  have hnear : ∀ᶠ q in 𝓝 m,
      CoorbitalAngleDomain (coorbitalAngleInjection (psi q)) ∧
        dist (psi q) a < r ∧ coorbitalReducedResidual q (psi q) = 0 := by
    have hdom := (coorbitalAngleInjection.continuous.continuousAt.comp
      hsmooth.continuousAt).tendsto.eventually
        ((isOpen_orderedSemicircle 4).mem_nhds
          (by change OrderedSemicircle (coorbitalAngleInjection (psi m))
              rw [hbase]; exact orderedSemicircle_of_coorbitalAngleDomain _ hdomain))
    have hball := hsmooth.continuousAt.tendsto.eventually (Metric.ball_mem_nhds (psi m) hr)
    filter_upwards [hdom, hball, hroots] with q hq hqb hqr
    exact ⟨(coorbitalFreeAngleDomain_iff _).mpr hq, by simpa [hbase] using hqb, hqr⟩
  obtain ⟨s, hs, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨W, hW, hcontinuous⟩ := hsmooth.contDiffOn (m := 0) (by simp) (by simp)
  obtain ⟨t, ht, htW⟩ := Metric.mem_nhds_iff.mp hW
  let eta := min r (min s t)
  refine ⟨psi, eta, r, lt_min hr (lt_min hs ht), hr, hbase, hsmooth,
    hcontinuous.continuousOn.mono ?_, ?_⟩
  · intro q hq
    exact htW (lt_of_lt_of_le hq ((min_le_right r _).trans (min_le_right s t)))
  · intro q hq
    obtain ⟨hd, hb, hz⟩ := hnear
      (lt_of_lt_of_le hq ((min_le_right r _).trans (min_le_left s t)))
    refine ⟨hd, hb, hz, ?_⟩
    intro b hb
    apply huniqNear (y := (q, b))
    simpa only [Prod.dist_eq] using max_lt (lt_of_lt_of_le hq (min_le_left r _)) hb

theorem coorbitalReducedResidual_zero_iff (m : MassRatio) (a : CoorbitalFreeAngles)
    (hm : 0 < m 0) :
    coorbitalReducedResidual m a = 0 ↔
      ∀ i, coorbitalResidual m (coorbitalAngleInjection a) i = 0 := by
  constructor
  · intro hz
    have hothers : ∀ i : Satellite, i ≠ 0 →
        coorbitalResidual m (coorbitalAngleInjection a) i = 0 := by
      intro i hi
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      have h := congrFun hz j
      simpa [coorbitalReducedResidual, coorbitalFreeRows, Fin.succAbove_zero] using h
    intro i
    by_cases hi : i = 0
    · subst i; exact coorbital_recover_positive_mass_row m _ 0 hm hothers
    · exact hothers i hi
  · intro hz; ext i; exact hz i.succ

/-- The actual root-space mass projection is a local homeomorphism.
The inverse chart is the genuine three-row implicit function restricted
to positive normalized masses, and all four angular equations are recovered. -/
theorem coorbitalMassProjection_isLocalHomeomorphOn :
    IsLocalHomeomorphOn coorbitalMassProjection Set.univ := by
  intro z _
  let a := coorbitalFreeRows z.val.2
  have haeq : coorbitalAngleInjection a = z.val.2 :=
    coorbitalAngleInjection_freeRows _ z.property.2.1.1
  have hdomain : CoorbitalAngleDomain (coorbitalAngleInjection a) := by
    rw [haeq]; exact z.property.2.1
  have hroot : ∀ i, coorbitalResidual z.val.1 (coorbitalAngleInjection a) i = 0 := by
    rw [haeq]; exact z.property.2.2
  obtain ⟨psi, eta, zeta, heta, hzeta, hbase, _, hpcont, hlocal⟩ :=
    coorbitalReducedResidual_local_product z.val.1 a z.property.1 hdomain hroot
  let U : Set CoorbitalMassSpace := {q | dist q.val z.val.1 < eta}
  have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hzU : coorbitalMassProjection z ∈ U := by simpa [U, coorbitalMassProjection] using heta
  let S : Set CoorbitalRootSpace :=
    {q | coorbitalMassProjection q ∈ U ∧ dist (coorbitalFreeRows q.val.2) a < zeta}
  have hS : IsOpen S := (hU.preimage coorbitalMassProjection_continuous).inter
    (isOpen_lt (show Continuous (fun q : CoorbitalRootSpace =>
      dist (coorbitalFreeRows q.val.2) a) by fun_prop) continuous_const)
  have hzS : z ∈ S := ⟨hzU, by simpa [a] using hzeta⟩
  let inv : CoorbitalMassSpace → CoorbitalRootSpace := fun q =>
    if hq : q ∈ U then
      ⟨(q.val, coorbitalAngleInjection (psi q.val)), q.property,
        (hlocal q.val hq).1,
        (coorbitalReducedResidual_zero_iff q.val (psi q.val) (q.property.1 0)).mp
          (hlocal q.val hq).2.2.1⟩
    else z
  have hinv (q : CoorbitalMassSpace) (hq : q ∈ U) :
      (inv q).val = (q.val, coorbitalAngleInjection (psi q.val)) := by
    simp only [inv, dif_pos hq]
  have hleft (q : CoorbitalRootSpace) (hq : q ∈ S) :
      inv (coorbitalMassProjection q) = q := by
    have hqangle := coorbitalAngleInjection_freeRows q.val.2 q.property.2.1.1
    have hzero : coorbitalReducedResidual q.val.1 (coorbitalFreeRows q.val.2) = 0 := by
      unfold coorbitalReducedResidual
      rw [hqangle]
      ext i; exact q.property.2.2 i.succ
    have heq := ((hlocal q.val.1 hq.1).2.2.2 _ hq.2).mp hzero
    apply Subtype.ext
    rw [hinv _ hq.1]
    apply Prod.ext
    · rfl
    · change coorbitalAngleInjection (psi q.val.1) = q.val.2
      rw [heq]
      exact hqangle
  have hright (q : CoorbitalMassSpace) (hq : q ∈ U) :
      coorbitalMassProjection (inv q) = q := by
    apply Subtype.ext
    change (inv q).val.1 = q.val
    rw [hinv q hq]
  have htarget (q : CoorbitalMassSpace) (hq : q ∈ U) : inv q ∈ S := by
    refine ⟨by rwa [hright q hq], ?_⟩
    rw [hinv q hq, coorbitalFreeRows_angleInjection]
    exact (hlocal q.val hq).2.1
  have hcontinuous : ContinuousOn inv U := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    have hpsi : ContinuousOn (fun q : CoorbitalMassSpace => psi q.val) U :=
      hpcont.comp continuous_subtype_val.continuousOn (fun _ hq => hq)
    have hpair := continuous_subtype_val.continuousOn.prodMk
      (coorbitalAngleInjection.continuous.comp_continuousOn hpsi)
    exact hpair.congr (fun q hq => hinv q hq)
  let e : OpenPartialHomeomorph CoorbitalRootSpace CoorbitalMassSpace :=
    { toFun := coorbitalMassProjection
      invFun := inv
      source := S
      target := U
      map_source' := fun _ hq => hq.1
      map_target' := htarget
      left_inv' := hleft
      right_inv' := hright
      open_source := hS
      open_target := hU
      continuousOn_toFun := coorbitalMassProjection_continuous.continuousOn
      continuousOn_invFun := hcontinuous }
  exact ⟨e, hzS, rfl⟩

theorem coorbitalMassProjection_fiber_finite (m : CoorbitalMassSpace) :
    (coorbitalMassProjection ⁻¹' {m}).Finite := by
  have hcompact := coorbitalMassProjection_isProperMap.isCompact_preimage
    (isCompact_singleton (x := m))
  have hdiscrete : IsDiscrete (coorbitalMassProjection ⁻¹' {m}) :=
    IsDiscrete.of_openPartialHomeomorph coorbitalMassProjection subset_rfl (by
      intro z _
      obtain ⟨e, he, hf⟩ := coorbitalMassProjection_isLocalHomeomorphOn z (mem_univ z)
      exact ⟨e, he, hf.symm⟩)
  exact hcompact.finite hdiscrete

/-- Manuscript Theorem 2.2: the genuine mass projection is a finite covering
of the entire positive normalized mass simplex. -/
theorem coorbitalMassProjection_isCoveringMapOn :
    IsCoveringMapOn coorbitalMassProjection Set.univ :=
  coorbitalMassProjection_isProperMap.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun m _ => coorbitalMassProjection_fiber_finite m)
    (coorbitalMassProjection_isLocalHomeomorphOn.mono (by simp))

theorem positiveRatio_convex : Convex ℝ {m : MassRatio | PositiveRatio m} := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change 0 < a * x i + b * y i
    have hxpos := hx.1 i
    have hypos := hy.1 i
    have hax : 0 ≤ a * x i := mul_nonneg ha hxpos.le
    have hby : 0 ≤ b * y i := mul_nonneg hb hypos.le
    rcases lt_or_eq_of_le ha with hap | haz
    · exact add_pos_of_pos_of_nonneg (mul_pos hap hxpos) hby
    · have hbpos : 0 < b := by linarith
      exact add_pos_of_nonneg_of_pos hax (mul_pos hbpos hypos)
  · change ∑ i, (a * x i + b * y i) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]
    simpa using hab

theorem coorbitalMassSpace_preconnected : PreconnectedSpace CoorbitalMassSpace :=
  isPreconnected_iff_preconnectedSpace.mp positiveRatio_convex.isPreconnected

theorem equalMassProjection_unique_fiber :
    ∃! z : CoorbitalRootSpace,
      coorbitalMassProjection z = (⟨equalMassRatio, equalMassRatio_positive⟩ : CoorbitalMassSpace) := by
  obtain ⟨theta, htheta, huniq⟩ := equalMass_coorbital_existsUnique
  let z : CoorbitalRootSpace := ⟨(equalMassRatio, theta), equalMassRatio_positive, htheta⟩
  refine ⟨z, rfl, ?_⟩
  intro q hq
  have hmass : q.val.1 = equalMassRatio := congrArg Subtype.val hq
  have hroot : ∀ i, coorbitalResidual equalMassRatio q.val.2 i = 0 := by
    rw [← hmass]; exact q.property.2.2
  have hangle : q.val.2 = theta := huniq q.val.2 ⟨q.property.2.1, hroot⟩
  exact Subtype.ext (Prod.ext hmass hangle)

/-- Every strictly positive normalized mass vector has exactly one actual
anchored open-semicircle coorbital root. The equal-mass fiber is transported
through genuine covering charts on the connected positive mass simplex. -/
theorem coorbitalMassProjection_unique_fiber (m : CoorbitalMassSpace) :
    ∃! z : CoorbitalRootSpace, coorbitalMassProjection z = m := by
  let : PreconnectedSpace CoorbitalMassSpace := coorbitalMassSpace_preconnected
  exact covering_unique_fiber_of_preconnected coorbitalMassProjection
    coorbitalMassProjection_isCoveringMapOn equalMassProjection_unique_fiber m

theorem coorbital_existsUnique (m : MassRatio) (hm : PositiveRatio m) :
    ∃! theta : Satellite → ℝ, CoorbitalAngleDomain theta ∧
      ∀ i, coorbitalResidual m theta i = 0 := by
  obtain ⟨z, hz, huniq⟩ := coorbitalMassProjection_unique_fiber ⟨m, hm⟩
  have hmass : z.val.1 = m := congrArg Subtype.val hz
  have hroot : ∀ i, coorbitalResidual m z.val.2 i = 0 := by
    rw [← hmass]; exact z.property.2.2
  refine ⟨z.val.2, ⟨z.property.2.1, hroot⟩, ?_⟩
  intro theta htheta
  let q : CoorbitalRootSpace := ⟨(m, theta), hm, htheta⟩
  have hq : coorbitalMassProjection q = (⟨m, hm⟩ : CoorbitalMassSpace) := rfl
  have heq := huniq q hq
  exact congrArg (fun r : CoorbitalRootSpace => r.val.2) heq

def coorbitalRootAngles (m : MassRatio) : Satellite → ℝ := by
  classical
  exact if hm : PositiveRatio m then Classical.choose (coorbital_existsUnique m hm).exists else 0

theorem coorbitalRootAngles_spec (m : MassRatio) (hm : PositiveRatio m) :
    CoorbitalAngleDomain (coorbitalRootAngles m) ∧
      ∀ i, coorbitalResidual m (coorbitalRootAngles m) i = 0 := by
  simp only [coorbitalRootAngles, dif_pos hm]
  exact Classical.choose_spec (coorbital_existsUnique m hm).exists

theorem coorbitalRootAngles_eq_of_root (m : MassRatio) (hm : PositiveRatio m)
    (theta : Satellite → ℝ) (htheta : CoorbitalAngleDomain theta)
    (hroot : ∀ i, coorbitalResidual m theta i = 0) : coorbitalRootAngles m = theta := by
  obtain ⟨a, _, huniq⟩ := coorbital_existsUnique m hm
  exact (huniq (coorbitalRootAngles m) (coorbitalRootAngles_spec m hm)).trans
    (huniq theta ⟨htheta, hroot⟩).symm

theorem coorbitalRootAngles_contDiffWithinAt (m : MassRatio) (hm : PositiveRatio m) :
    ContDiffWithinAt ℝ ∞ coorbitalRootAngles {q | PositiveRatio q} m := by
  have hspec := coorbitalRootAngles_spec m hm
  let a := coorbitalFreeRows (coorbitalRootAngles m)
  have heq : coorbitalAngleInjection a = coorbitalRootAngles m :=
    coorbitalAngleInjection_freeRows _ hspec.1.1
  obtain ⟨psi, eta, _, heta, _, _, hsmooth, _, hlocal⟩ :=
    coorbitalReducedResidual_local_product m a hm
      (by rw [heq]; exact hspec.1) (by rw [heq]; exact hspec.2)
  have hevent : coorbitalRootAngles =ᶠ[𝓝[{q | PositiveRatio q}] m]
      (fun q => coorbitalAngleInjection (psi q)) := by
    have hball : ∀ᶠ q in 𝓝 m, dist q m < eta := Metric.ball_mem_nhds m heta
    filter_upwards [hball.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with q hq hqm
    have h := hlocal q hq
    exact coorbitalRootAngles_eq_of_root q hqm _ h.1
      ((coorbitalReducedResidual_zero_iff q (psi q) (hqm.1 0)).mp h.2.2.1)
  have hcont : ContDiffAt ℝ ∞ (fun q => coorbitalAngleInjection (psi q)) m :=
    coorbitalAngleInjection.contDiff.contDiffAt.comp m hsmooth
  exact hcont.contDiffWithinAt.congr_of_eventuallyEq_of_mem hevent hm

theorem coorbitalRootAngles_continuousOn :
    ContinuousOn coorbitalRootAngles {m | PositiveRatio m} := by
  intro m hm
  exact (coorbitalRootAngles_contDiffWithinAt m hm).continuousWithinAt

def coorbitalRootGraph (m : CoorbitalMassSpace) : CoorbitalRootSpace :=
  ⟨(m.val, coorbitalRootAngles m.val), m.property, coorbitalRootAngles_spec m.val m.property⟩

@[simp] theorem coorbitalRootGraph_massProjection (m : CoorbitalMassSpace) :
    coorbitalMassProjection (coorbitalRootGraph m) = m := rfl

@[simp] theorem coorbitalMassProjection_rootGraph (z : CoorbitalRootSpace) :
    coorbitalRootGraph (coorbitalMassProjection z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact coorbitalRootAngles_eq_of_root z.val.1 z.property.1 z.val.2
      z.property.2.1 z.property.2.2

theorem coorbitalRootGraph_continuous : Continuous coorbitalRootGraph := by
  unfold coorbitalRootGraph
  apply Continuous.subtype_mk
  exact continuous_subtype_val.prodMk coorbitalRootAngles_continuousOn.domRestrict

def coorbitalMassProjectionHomeomorph : CoorbitalRootSpace ≃ₜ CoorbitalMassSpace where
  toFun := coorbitalMassProjection
  invFun := coorbitalRootGraph
  left_inv := coorbitalMassProjection_rootGraph
  right_inv := coorbitalRootGraph_massProjection
  continuous_toFun := coorbitalMassProjection_continuous
  continuous_invFun := coorbitalRootGraph_continuous

theorem coorbitalRootGraph_image_isCompact (K : Set CoorbitalMassSpace) (hK : IsCompact K) :
    IsCompact (coorbitalRootGraph '' K) := hK.image coorbitalRootGraph_continuous

/-- Full content of manuscript Theorem 2.2, with all actual equations,
existence, global uniqueness, and smooth mass dependence discharged. -/
theorem coorbital_global_complete :
    (∀ m : MassRatio, PositiveRatio m →
      ∃! theta : Satellite → ℝ, CoorbitalAngleDomain theta ∧
        ∀ i, coorbitalResidual m theta i = 0) ∧
    ContDiffOn ℝ ∞ coorbitalRootAngles {m | PositiveRatio m} ∧
    (∀ m : MassRatio, PositiveRatio m → ∀ u : Satellite → ℝ,
      u 0 = 0 → u ≠ 0 → 0 < coorbitalPhysicalHessian m (coorbitalRootAngles m) u u) ∧
    IsProperMap coorbitalMassProjection ∧
    IsCoveringMapOn coorbitalMassProjection Set.univ := by
  refine ⟨coorbital_existsUnique, coorbitalRootAngles_contDiffWithinAt, ?_,
    coorbitalMassProjection_isProperMap, coorbitalMassProjection_isCoveringMapOn⟩
  intro m hm u h0 hu
  have hspec := coorbitalRootAngles_spec m hm
  exact coorbital_hessian_positive_on_slice m (coorbitalRootAngles m) u 0 hm.1
    hspec.1 hspec.2 h0 hu

end DominantFiveBody
