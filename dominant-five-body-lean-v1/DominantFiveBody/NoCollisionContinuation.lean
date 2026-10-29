import DominantFiveBody.CoorbitalContinuation
import DominantFiveBody.FixedAngleRows
import DominantFiveBody.SeparatedBaseContinuation

/-! # Actual continuation and capture at a distinct closed-mass limit

The anchor has a positive limiting mass; the other limiting masses may
vanish.  The actual separated angular root supplies the base Jacobian,
strict convexity, and independent parameter implicit-function branches.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

def satelliteHullOrder (e : Equiv.Perm Satellite) : HullOrder :=
  ⟨satelliteLabelPermutation e,rfl⟩

theorem unit_polar_strictConvex_permutation (θ : Satellite → ℝ) (e : Equiv.Perm Satellite)
    (hθ : OrderedSemicircle (θ ∘ e)) :
    StrictConvexInOrder (satelliteHullOrder e) (liftRelative (polarSatellites (fun _ => 1) θ)) := by
  have hc := unit_polar_strictConvex (θ ∘ e) hθ
  have hq : liftRelative (polarSatellites (fun _ => 1) (θ ∘ e))=
      liftRelative (polarSatellites (fun _ => 1) θ) ∘ satelliteLabelPermutation e := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  simpa only [hq,StrictConvexInOrder,satelliteHullOrder,standardHullOrder,
    Equiv.refl_apply,orientedArea,Function.comp_apply] using hc

theorem slice_unit_strictConvex_permutation (μ : MassRatio) (y : SliceCoordinates)
    (hunit : ∀ i, sliceRadii y i=1) (e : Equiv.Perm Satellite)
    (hθ : OrderedSemicircle (sliceAngles y ∘ e)) :
    StrictConvexInOrder (satelliteHullOrder e) (slicePhysicalConfiguration (0,μ) y) := by
  have hc := unit_polar_strictConvex_permutation (sliceAngles y) e hθ
  have hq : sliceSatellites y=polarSatellites (fun _ => 1) (sliceAngles y) := by
    simp only [sliceSatellites,funext hunit]
  have hc' := (strictConvex_centeredFromRelative_iff (satelliteHullOrder e) 0 μ
    (sliceSatellites y)).mpr (by simpa only [hq] using hc)
  simpa only [slicePhysicalConfiguration,relativeCenteredContinuous_apply] using hc'

theorem reducedResidual_zero_eps_unit_radii (μ : MassRatio) (y : SliceCoordinates)
    (hreg : SliceRegular (0,μ) y) (hroot : reducedResidual (0,μ) y=0) :
    ∀ i, sliceRadii y i=1 := by
  intro i
  have hg : sliceRadii y i-(sliceRadii y i^2)⁻¹=0 := by
    have h := congrFun hroot (i.castAdd 3)
    simpa only [reducedResidual,Fin.append_left,radialResidual_at_zero,Pi.zero_apply] using h
  have hp := hreg.2.1 i
  have he : sliceRadii y i^3=1 := by
    have hmul := (eq_div_iff (pow_ne_zero 2 hp.ne')).mp
      (show sliceRadii y i=1/(sliceRadii y i)^2 by simpa only [one_div] using sub_eq_zero.mp hg)
    nlinarith
  exact (pow_eq_one_iff_of_nonneg hp.le (by decide : (3 : ℕ)≠0)).mp he

theorem reducedResidual_fixed_mass_zero_endpoint (μ : MassRatio) (y : SliceCoordinates)
    (hμ₀ : μ 0≠0) (hreg : SliceRegular (0,μ) y)
    (hsep : SeparatedSemicircle (sliceAngles y)) (hroot : reducedResidual (0,μ) y=0) :
    (∀ i, sliceRadii y i=1) ∧ RelativeCollisionFree (sliceSatellites y) ∧
      ∀ i, coorbitalResidual μ (sliceAngles y) i=0 := by
  have hunit := reducedResidual_zero_eps_unit_radii μ y hreg hroot
  have hT : ∀ i, angularResidual 0 μ (sliceRadii y) (sliceAngles y) i=0 := by
    have hothers : ∀ i : Satellite, i≠0 → angularResidual 0 μ (sliceRadii y) (sliceAngles y) i=0 := by
      intro i hi
      obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi
      have h := congrFun hroot (j.natAdd 4)
      simpa only [reducedResidual,Fin.append_right,Pi.zero_apply,Fin.succAbove_zero] using h
    intro i
    by_cases hi : i=0
    · subst i
      exact angularResidual_omitted_row 0 μ (sliceRadii y) (sliceAngles y) 0 hμ₀ hothers
    · exact hothers i hi
  refine ⟨hunit,sliceSatellites_relativeCollisionFree (0,μ) y hreg,?_⟩
  intro i
  have h := hT i
  rwa [funext hunit,angularResidual_zero_unit_separated μ (sliceAngles y) hsep i] at h

theorem coorbitalResidual_sub_constant (μ θ : Satellite → ℝ) (a : ℝ) (i : Satellite) :
    coorbitalResidual μ (fun j => θ j-a) i=coorbitalResidual μ θ i := by
  unfold coorbitalResidual
  apply Finset.sum_congr rfl
  intro j _
  rw [show (θ j-a)-(θ i-a)=θ j-θ i by ring]

theorem coorbitalRootAngles_eq_sorted_shift (μ θ : Satellite → ℝ)
    (hμ : PositiveRatio μ) (e : Equiv.Perm Satellite) (hθ : OrderedSemicircle (θ ∘ e))
    (hroot : ∀ i, coorbitalResidual μ θ i=0) :
    coorbitalRootAngles (μ ∘ e)=fun i => θ (e i)-θ (e 0) := by
  apply coorbitalRootAngles_eq_of_root _ (positiveRatio_satellitePermutation μ hμ e)
  · refine ⟨by simp,?_,?_⟩
    · intro i j hij
      have h := (hθ i j hij).1
      dsimp only [Function.comp_apply] at h
      linarith
    · exact (hθ 0 3 (by decide)).2
  · intro i
    rw [coorbitalResidual_sub_constant]
    change coorbitalResidual (μ ∘ e) (θ ∘ e) i=0
    rw [coorbitalResidual_reindex]
    exact hroot (e i)

/-- The actual §5.1 branch, including arbitrary closed-simplex masses,
physical convexity, the original shape Hessian and fixed-current-mass
coorbital endpoint identification. -/
theorem noCollision_physical_local_continuation (μ : MassRatio) (y : SliceCoordinates)
    (hunit : ∀ i, sliceRadii y i=1) (hμ : ∀ i, 0≤μ i) (hsum : ∑ i, μ i=1)
    (hμ₀ : 0<μ 0) (hsep : SeparatedSemicircle (sliceAngles y))
    (hroot : ∀ i, coorbitalResidual μ (sliceAngles y) i=0) :
    ∃ e : Equiv.Perm Satellite, ∃ η r C : ℝ, 0<η ∧ 0<r ∧ 0<C ∧
      ∃ ψ : ContinuationParameter → SliceCoordinates,
        OrderedSemicircle (sliceAngles y ∘ e) ∧ ψ (0,μ)=y ∧
        ContDiffOn ℝ ∞ ψ (Metric.ball (0,μ) η) ∧
        ∀ ε ν, |ε|<η → dist ν μ<η →
          StrictConvexInOrder (satelliteHullOrder e) (slicePhysicalConfiguration (ε,ν) (ψ (ε,ν))) ∧
          OrderedSemicircle (sliceAngles (ψ (ε,ν)) ∘ e) ∧
          dist (ψ (ε,ν)) y<r/2 ∧ SliceRegular (ε,ν) (ψ (ε,ν)) ∧
          (reducedJacobian (ε,ν) (ψ (ε,ν))).IsInvertible ∧
          ‖(reducedJacobian (ε,ν) (ψ (ε,ν))).inverse‖≤C ∧ reducedResidual (ε,ν) (ψ (ε,ν))=0 ∧
          (∀ z, dist z y<r → (reducedResidual (ε,ν) z=0 ↔ ψ (ε,ν)=z)) ∧
          (0<ε → PositiveRatio ν →
            NormalizedCentralConfiguration (masses ε ν) (slicePhysicalConfiguration (ε,ν) (ψ (ε,ν))) ∧
            StrictConvexCentralConfiguration (masses ε ν) (satelliteHullOrder e)
              (slicePhysicalConfiguration (ε,ν) (ψ (ε,ν))) ∧
            ShapeHessianNondegenerate (masses ε ν) 1 (slicePhysicalConfiguration (ε,ν) (ψ (ε,ν)))) ∧
          (ε=0 → PositiveRatio ν →
            (∀ i, sliceRadii (ψ (ε,ν)) i=1) ∧
            RelativeCollisionFree (sliceSatellites (ψ (ε,ν))) ∧
            (∀ i, coorbitalResidual ν (sliceAngles (ψ (ε,ν))) i=0) ∧
            coorbitalRootAngles (ν ∘ e)=
              fun i => sliceAngles (ψ (ε,ν)) (e i)-sliceAngles (ψ (ε,ν)) (e 0)) := by
  classical
  obtain ⟨e,he⟩ := exists_ordered_semicircle_permutation (sliceAngles y) hsep
  let K : Set RootGraphPoint := {((0,μ),y)}
  let V : Set RootGraphPoint := {a |
    StrictConvexInOrder (satelliteHullOrder e) (slicePhysicalConfiguration a.1 a.2) ∧
      OrderedSemicircle (sliceAngles a.2 ∘ e)}
  have hdata : ∀ a ∈ K, SliceRegular a.1 a.2 ∧ reducedResidual a.1 a.2=0 ∧
      (reducedJacobian a.1 a.2).IsInvertible := by
    intro a ha
    have ha' : a=((0,μ),y) := Set.mem_singleton_iff.mp ha
    subst a
    exact ⟨sliceRegular_at_coorbital_separated μ y hunit hsep,
      reducedResidual_at_coorbital_root_separated μ y hunit hsep hroot,
      reducedJacobian_at_closed_separated_root_isInvertible μ y hunit hμ hsum hμ₀ hsep hroot⟩
  have hV : ∀ a ∈ K, V ∈ 𝓝 a := by
    intro a ha
    have ha' : a=((0,μ),y) := Set.mem_singleton_iff.mp ha
    subst a
    have hconv := slicePhysical_strictConvex_neighborhood (satelliteHullOrder e) (0,μ) y
      (slice_unit_strictConvex_permutation μ y hunit e he)
    have hc : Continuous (fun a : RootGraphPoint => sliceAngles a.2 ∘ e) := by
      apply continuous_pi
      intro i
      exact (sliceAngles_contDiff 0 (e i)).continuous.comp continuous_snd
    have hangles := (hc.continuousAt (x := ((0,μ),y))).eventually
      ((isOpen_orderedSemicircle 4).mem_nhds he)
    exact Filter.Eventually.and hconv hangles
  obtain ⟨η,r,C,hη,hr,hC,hbranches⟩ :=
    reducedResidual_compact_product_preserving K V isCompact_singleton hdata hV
  obtain ⟨ψ,hbase,hsmooth,hbranch⟩ := hbranches ((0,μ),y) (Set.mem_singleton _)
  refine ⟨e,η,r,C,hη,hr,hC,ψ,he,hbase,hsmooth,?_⟩
  intro ε ν hε hν
  have hd : dist (ε,ν) (0,μ)<η := by
    simpa only [Prod.dist_eq,Real.dist_eq,sub_zero] using max_lt hε hν
  obtain ⟨⟨hconv,hθ⟩,hy,hreg,hJ,hinv,hzero,huniq⟩ := hbranch (ε,ν) hd
  refine ⟨hconv,hθ,hy,hreg,hJ,hinv,hzero,huniq,?_,?_⟩
  · intro heps hmass
    have hx := normalizedCC_of_reducedResidual_zero (ε,ν) (ψ (ε,ν)) hreg heps hmass hzero
    exact ⟨hx,⟨normalized_is_central _ _ hx,hconv⟩,
      (reducedJacobian_isInvertible_iff_shape (ε,ν) (ψ (ε,ν)) hreg heps hmass hzero).mp hJ⟩
  · intro heps hmass
    subst ε
    have hseparated : SeparatedSemicircle (sliceAngles (ψ (0,ν))) := by
      intro i j hij
      have h := separatedSemicircle_of_ordered _ hθ (e.symm i) (e.symm j) (e.symm.injective.ne hij)
      simpa only [Function.comp_apply,Equiv.apply_symm_apply] using h
    obtain ⟨hu,hcf,hco⟩ := reducedResidual_fixed_mass_zero_endpoint ν (ψ (0,ν))
      (ne_of_gt (hmass.1 0)) hreg hseparated hzero
    exact ⟨hu,hcf,hco,coorbitalRootAngles_eq_sorted_shift ν _ hmass e hθ hco⟩

def labelledCoorbitalEndpointAngles (μ : MassRatio) (e : Equiv.Perm Satellite) : Satellite → ℝ :=
  fun i => coorbitalRootAngles (μ ∘ e) (e.symm i)-coorbitalRootAngles (μ ∘ e) (e.symm 0)

def labelledCoorbitalEndpointSlice (μ : MassRatio) (e : Equiv.Perm Satellite) : SliceCoordinates :=
  coorbitalSliceOfAngles (labelledCoorbitalEndpointAngles μ e)

theorem sliceCoordinates_ext (y z : SliceCoordinates) (hr : sliceRadii y=sliceRadii z)
    (hθ : sliceAngles y=sliceAngles z) : y=z := by
  funext k
  refine Fin.addCases (motive := fun k => y k=z k) (fun i : Fin 4 => ?_) (fun j : Fin 3 => ?_) k
  · exact congrFun hr i
  · exact congrFun hθ j.succ

/-- The endpoint is an explicit function of the current positive masses
and the actual hull ordering. Its original labels and fixed angle zero
are recovered exactly, rather than only up to a residual oracle. -/
theorem slice_unit_eq_labelledCoorbitalEndpoint (μ : MassRatio) (hμ : PositiveRatio μ)
    (y : SliceCoordinates) (e : Equiv.Perm Satellite) (hunit : ∀ i, sliceRadii y i=1)
    (hθ : OrderedSemicircle (sliceAngles y ∘ e))
    (hroot : ∀ i, coorbitalResidual μ (sliceAngles y) i=0) :
    y=labelledCoorbitalEndpointSlice μ e := by
  have heq := coorbitalRootAngles_eq_sorted_shift μ (sliceAngles y) hμ e hθ hroot
  have hangles : sliceAngles y=labelledCoorbitalEndpointAngles μ e := by
    funext i
    have hi := congrFun heq (e.symm i)
    have h0 := congrFun heq (e.symm 0)
    have hzero : sliceAngles y 0=0 := rfl
    simp only [Equiv.apply_symm_apply,hzero] at h0
    simp only [Equiv.apply_symm_apply] at hi
    unfold labelledCoorbitalEndpointAngles
    linarith
  apply sliceCoordinates_ext
  · funext i
    exact (hunit i).trans (coorbitalSliceOfAngles_radii _ i).symm
  · have hzero : labelledCoorbitalEndpointAngles μ e 0=0 := sub_self _
    exact hangles.trans (coorbitalSliceOfAngles_angles _ hzero).symm

/-- The actual data captured from a converging distinct-root sequence.
The branch at index n retains the mass ratio of the original index N+n. -/
structure NoCollisionCapturedBranches (ν : ℕ → MassRatio) (ε : ℕ → ℝ)
    (y : ℕ → SliceCoordinates) where
  tailStart : ℕ
  order : Equiv.Perm Satellite
  radius : ℝ
  radius_pos : 0<radius
  branch : ℕ → ℝ → SliceCoordinates
  parameters_pos : ∀ n, 0<ε (tailStart+n)
  parameters_lt_radius : ∀ n, ε (tailStart+n)<radius
  continuous : ∀ n, ContinuousOn (branch n) (Set.Ico 0 radius)
  hits : ∀ n, branch n (ε (tailStart+n))=y (tailStart+n)
  regular_roots : ∀ n s, s∈Set.Ico 0 radius →
    SliceRegular (s,ν (tailStart+n)) (branch n s) ∧
      reducedResidual (s,ν (tailStart+n)) (branch n s)=0
  ordered_angles : ∀ n s, s∈Set.Ico 0 radius →
    OrderedSemicircle (sliceAngles (branch n s) ∘ order)
  physical_roots : ∀ n s, 0<s → s<radius →
    StrictConvexCentralConfiguration (masses s (ν (tailStart+n))) (satelliteHullOrder order)
      (slicePhysicalConfiguration (s,ν (tailStart+n)) (branch n s))
  nondegenerate : ∀ n s, 0<s → s<radius →
    ShapeHessianNondegenerate (masses s (ν (tailStart+n))) 1
      (slicePhysicalConfiguration (s,ν (tailStart+n)) (branch n s))
  endpoint_eq : ∀ n, branch n 0=labelledCoorbitalEndpointSlice (ν (tailStart+n)) order
  endpoints : ∀ n,
    (∀ i, sliceRadii (branch n 0) i=1) ∧
    RelativeCollisionFree (sliceSatellites (branch n 0)) ∧
    (∀ i, coorbitalResidual (ν (tailStart+n)) (sliceAngles (branch n 0)) i=0) ∧
    coorbitalRootAngles (ν (tailStart+n) ∘ order)=
      fun i => sliceAngles (branch n 0) (order i)-sliceAngles (branch n 0) (order 0)

/-- Convergence into the actual common uniqueness ball captures every
root in a whole tail. The common positive connection interval is
independent of the index, and ε=0 keeps each current positive mass. -/
theorem noCollision_actual_sequence_capture (μ : MassRatio) (y₀ : SliceCoordinates)
    (hunit : ∀ i, sliceRadii y₀ i=1) (hμ : ∀ i, 0≤μ i) (hsum : ∑ i, μ i=1)
    (hμ₀ : 0<μ 0) (hsep : SeparatedSemicircle (sliceAngles y₀))
    (hco : ∀ i, coorbitalResidual μ (sliceAngles y₀) i=0)
    (ν : ℕ → MassRatio) (ε : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (hν : ∀ n, PositiveRatio (ν n)) (hε : ∀ n, 0<ε n)
    (hνlim : Tendsto ν atTop (𝓝 μ)) (hεlim : Tendsto ε atTop (𝓝 0))
    (hylim : Tendsto y atTop (𝓝 y₀))
    (hroots : ∀ n, reducedResidual (ε n,ν n) (y n)=0) :
    Nonempty (NoCollisionCapturedBranches ν ε y) := by
  obtain ⟨e,η,r,C,hη,hr,_,ψ,_,_,hsmooth,hbranch⟩ :=
    noCollision_physical_local_continuation μ y₀ hunit hμ hsum hμ₀ hsep hco
  have hεnear : ∀ᶠ n in atTop, |ε n|<η := by
    have h := hεlim.eventually (Metric.ball_mem_nhds (0 : ℝ) hη)
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using h
  have hνnear : ∀ᶠ n in atTop, dist (ν n) μ<η :=
    hνlim.eventually (Metric.ball_mem_nhds μ hη)
  have hynear : ∀ᶠ n in atTop, dist (y n) y₀<r :=
    hylim.eventually (Metric.ball_mem_nhds y₀ hr)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (hεnear.and (hνnear.and hynear))
  have htail (n : ℕ) := hN (N+n) (Nat.le_add_right N n)
  let branch : ℕ → ℝ → SliceCoordinates := fun n s => ψ (s,ν (N+n))
  have hdata (n : ℕ) (s : ℝ) (hs : |s|<η) :=
    hbranch s (ν (N+n)) hs (htail n).2.1
  refine ⟨{
    tailStart := N
    order := e
    radius := η
    radius_pos := hη
    branch := branch
    parameters_pos := fun n => hε (N+n)
    parameters_lt_radius := ?_
    continuous := ?_
    hits := ?_
    regular_roots := ?_
    ordered_angles := ?_
    physical_roots := ?_
    nondegenerate := ?_
    endpoint_eq := ?_
    endpoints := ?_ }⟩
  · intro n
    exact lt_of_le_of_lt (le_abs_self _) (htail n).1
  · intro n
    apply hsmooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
    intro s hs
    change dist (s,ν (N+n)) (0,μ)<η
    rw [Prod.dist_eq,Real.dist_eq,sub_zero,abs_of_nonneg hs.1]
    exact max_lt hs.2 (htail n).2.1
  · intro n
    exact ((hdata n (ε (N+n)) (htail n).1).2.2.2.2.2.2.2.1
      (y (N+n)) (htail n).2.2).mp (hroots (N+n))
  · intro n s hs
    have h := hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)
    exact ⟨h.2.2.2.1,h.2.2.2.2.2.2.1⟩
  · intro n s hs
    exact (hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)).2.1
  · intro n s hs hsη
    have h := (hdata n s (by simpa only [abs_of_pos hs] using hsη)).2.2.2.2.2.2.2.2.1 hs (hν (N+n))
    exact h.2.1
  · intro n s hs hsη
    have h := (hdata n s (by simpa only [abs_of_pos hs] using hsη)).2.2.2.2.2.2.2.2.1 hs (hν (N+n))
    exact h.2.2
  · intro n
    have h := hdata n 0 (by simpa using hη)
    have hend := h.2.2.2.2.2.2.2.2.2 rfl (hν (N+n))
    exact slice_unit_eq_labelledCoorbitalEndpoint (ν (N+n)) (hν (N+n)) (branch n 0)
      e hend.1 h.2.1 hend.2.2.1
  · intro n
    exact (hdata n 0 (by simpa using hη)).2.2.2.2.2.2.2.2.2 rfl (hν (N+n))

theorem reducedResidual_limit_zero (p : ℕ → ContinuationParameter) (y : ℕ → SliceCoordinates)
    (p₀ : ContinuationParameter) (y₀ : SliceCoordinates) (hreg : SliceRegular p₀ y₀)
    (hp : Tendsto p atTop (𝓝 p₀)) (hy : Tendsto y atTop (𝓝 y₀))
    (hroot : ∀ n, reducedResidual (p n) (y n)=0) : reducedResidual p₀ y₀=0 := by
  have hc := (reducedResidual_joint_contDiffAt 0 p₀ y₀ hreg).continuousAt
  have ht := hc.tendsto.comp (hp.prodMk_nhds hy)
  have heq : (fun n => reducedResidual (p n) (y n))=fun _ => (0 : SliceCoordinates) := funext hroot
  change Tendsto (fun n => reducedResidual (p n) (y n)) atTop (𝓝 (reducedResidual p₀ y₀)) at ht
  rw [heq] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- Neither the unit-radius condition nor the limiting coorbital
equations are supplied as an oracle: both follow from the actual root
sequence and the genuine regular limiting chart. -/
theorem noCollision_actual_sequence_capture_of_regular_limit (μ : MassRatio) (y₀ : SliceCoordinates)
    (hμ : ∀ i, 0≤μ i) (hsum : ∑ i, μ i=1) (hμ₀ : 0<μ 0)
    (hreg : SliceRegular (0,μ) y₀) (hsep : SeparatedSemicircle (sliceAngles y₀))
    (ν : ℕ → MassRatio) (ε : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (hν : ∀ n, PositiveRatio (ν n)) (hε : ∀ n, 0<ε n)
    (hνlim : Tendsto ν atTop (𝓝 μ)) (hεlim : Tendsto ε atTop (𝓝 0))
    (hylim : Tendsto y atTop (𝓝 y₀))
    (hroots : ∀ n, reducedResidual (ε n,ν n) (y n)=0) :
    Nonempty (NoCollisionCapturedBranches ν ε y) := by
  have hzero := reducedResidual_limit_zero (fun n => (ε n,ν n)) y (0,μ) y₀ hreg
    (hεlim.prodMk_nhds hνlim) hylim hroots
  obtain ⟨hunit,_,hco⟩ := reducedResidual_fixed_mass_zero_endpoint μ y₀ hμ₀.ne' hreg hsep hzero
  exact noCollision_actual_sequence_capture μ y₀ hunit hμ hsum hμ₀ hsep hco
    ν ε y hν hε hνlim hεlim hylim hroots

theorem NoCollisionCapturedBranches.tail_strictMono {ν : ℕ → MassRatio} {ε : ℕ → ℝ}
    {y : ℕ → SliceCoordinates} (c : NoCollisionCapturedBranches ν ε y) :
    StrictMono (fun n => c.tailStart+n) := by
  intro i j hij
  exact Nat.add_lt_add_left hij c.tailStart

end DominantFiveBody




