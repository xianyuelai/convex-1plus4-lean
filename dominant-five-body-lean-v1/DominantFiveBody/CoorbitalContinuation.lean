import DominantFiveBody.ConvexContinuation

/-! The full physical coorbital continuation of Proposition 3.3. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

def coorbitalSliceOfAngles (θ : Satellite → ℝ) : SliceCoordinates :=
  Fin.append (fun _ : Fin 4 => 1) (fun i : Fin 3 => θ i.succ)

@[simp] theorem coorbitalSliceOfAngles_radii (θ : Satellite → ℝ) (i : Satellite) :
    sliceRadii (coorbitalSliceOfAngles θ) i = 1 := by
  simp [sliceRadii, coorbitalSliceOfAngles]

theorem coorbitalSliceOfAngles_angles (θ : Satellite → ℝ) (hθ : θ 0 = 0) :
    sliceAngles (coorbitalSliceOfAngles θ) = θ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [sliceAngles, Fin.cases_zero] using hθ.symm
  · simp [sliceAngles, coorbitalSliceOfAngles]

theorem coorbitalSliceOfAngles_contDiff (n : ℕ∞ω) : ContDiff ℝ n coorbitalSliceOfAngles := by
  apply contDiff_pi.mpr
  intro k
  refine Fin.addCases (motive := fun k => ContDiff ℝ n
      (fun θ : Satellite → ℝ => coorbitalSliceOfAngles θ k))
    (fun i : Fin 4 => ?_) (fun i : Fin 3 => ?_) k
  · simp only [coorbitalSliceOfAngles, Fin.append_left]; exact contDiff_const
  · simp only [coorbitalSliceOfAngles, Fin.append_right]; fun_prop

def coorbitalBaseSlice (μ : MassRatio) : SliceCoordinates :=
  coorbitalSliceOfAngles (coorbitalRootAngles μ)

@[simp] theorem coorbitalBaseSlice_radii (μ : MassRatio) (i : Satellite) :
    sliceRadii (coorbitalBaseSlice μ) i = 1 := coorbitalSliceOfAngles_radii _ _

theorem coorbitalBaseSlice_angles (μ : MassRatio) (hμ : PositiveRatio μ) :
    sliceAngles (coorbitalBaseSlice μ) = coorbitalRootAngles μ :=
  coorbitalSliceOfAngles_angles _ (coorbitalRootAngles_spec μ hμ).1.1

theorem coorbitalBaseSlice_continuousOn : ContinuousOn coorbitalBaseSlice {μ | PositiveRatio μ} :=
  (coorbitalSliceOfAngles_contDiff 0).continuous.comp_continuousOn coorbitalRootAngles_continuousOn

def coorbitalBaseGraph (μ : MassRatio) : RootGraphPoint := ((0, μ), coorbitalBaseSlice μ)

theorem coorbitalBaseGraph_image_isCompact (K : Set MassRatio) (hK : IsCompact K)
    (hpositive : ∀ μ ∈ K, PositiveRatio μ) : IsCompact (coorbitalBaseGraph '' K) := by
  have hc : ContinuousOn coorbitalBaseGraph K :=
    (continuousOn_const.prodMk continuousOn_id).prodMk
      (coorbitalBaseSlice_continuousOn.mono hpositive)
  exact hK.image_of_continuousOn hc

theorem coorbitalBaseSlice_actual_data (μ : MassRatio) (hμ : PositiveRatio μ) :
    SliceRegular (0, μ) (coorbitalBaseSlice μ) ∧
    reducedResidual (0, μ) (coorbitalBaseSlice μ) = 0 ∧
    (reducedJacobian (0, μ) (coorbitalBaseSlice μ)).IsInvertible := by
  have hspec := coorbitalRootAngles_spec μ hμ
  have harc : OrderedSemicircle (sliceAngles (coorbitalBaseSlice μ)) := by
    rw [coorbitalBaseSlice_angles μ hμ]
    exact orderedSemicircle_of_coorbitalAngleDomain _ hspec.1
  have hroot : ∀ i, coorbitalResidual μ (sliceAngles (coorbitalBaseSlice μ)) i = 0 := by
    rw [coorbitalBaseSlice_angles μ hμ]
    exact hspec.2
  exact ⟨sliceRegular_at_coorbital μ _ (coorbitalBaseSlice_radii μ) harc,
    reducedResidual_at_coorbital_root μ _ (coorbitalBaseSlice_radii μ) harc hroot,
    reducedJacobian_at_coorbital_root_isInvertible μ _ (coorbitalBaseSlice_radii μ) hμ.1 harc hroot⟩

theorem coorbitalBaseSlice_strictConvex (μ : MassRatio) (hμ : PositiveRatio μ) :
    StrictConvexInOrder standardHullOrder (slicePhysicalConfiguration (0, μ) (coorbitalBaseSlice μ)) := by
  have hspec := coorbitalRootAngles_spec μ hμ
  have hc := unit_polar_strictConvex (coorbitalRootAngles μ)
    (orderedSemicircle_of_coorbitalAngleDomain _ hspec.1)
  have hq : sliceSatellites (coorbitalBaseSlice μ) =
      polarSatellites (fun _ => 1) (coorbitalRootAngles μ) := by
    simp only [sliceSatellites, funext (coorbitalBaseSlice_radii μ), coorbitalBaseSlice_angles μ hμ]
  have hc' := (strictConvex_centeredFromRelative_iff standardHullOrder 0 μ
    (sliceSatellites (coorbitalBaseSlice μ))).mpr (by simpa only [hq] using hc)
  simpa only [slicePhysicalConfiguration, relativeCenteredContinuous_apply] using hc'

/-- Full Proposition 3.3 on any compact subset of the *whole* positive
mass simplex. The actual unique coorbital base, compact graph, independent
parameter products, physical CC recovery, strict convexity and original
six-dimensional shape nondegeneracy are all proved. -/
theorem coorbital_compact_physical_continuation (K : Set MassRatio) (hK : IsCompact K)
    (hpositive : ∀ μ ∈ K, PositiveRatio μ) :
    ∃ η r C : ℝ, 0 < η ∧ 0 < r ∧ 0 < C ∧ ∀ μ ∈ K,
      ∃ ψ : ContinuationParameter → SliceCoordinates,
        ψ (0, μ) = coorbitalBaseSlice μ ∧ ContDiffOn ℝ ∞ ψ (Metric.ball (0, μ) η) ∧
        ∀ ε ν, |ε| < η → dist ν μ < η →
          StrictConvexInOrder standardHullOrder (slicePhysicalConfiguration (ε, ν) (ψ (ε, ν))) ∧
          dist (ψ (ε, ν)) (coorbitalBaseSlice μ) < r / 2 ∧
          SliceRegular (ε, ν) (ψ (ε, ν)) ∧ (reducedJacobian (ε, ν) (ψ (ε, ν))).IsInvertible ∧
          ‖(reducedJacobian (ε, ν) (ψ (ε, ν))).inverse‖ ≤ C ∧
          reducedResidual (ε, ν) (ψ (ε, ν)) = 0 ∧
          (∀ z, dist z (coorbitalBaseSlice μ) < r →
            (reducedResidual (ε, ν) z = 0 ↔ ψ (ε, ν) = z)) ∧
          (0 < ε → PositiveRatio ν →
            NormalizedCentralConfiguration (masses ε ν) (slicePhysicalConfiguration (ε, ν) (ψ (ε, ν))) ∧
            StrictConvexCentralConfiguration (masses ε ν) standardHullOrder
              (slicePhysicalConfiguration (ε, ν) (ψ (ε, ν))) ∧
            ShapeHessianNondegenerate (masses ε ν) 1 (slicePhysicalConfiguration (ε, ν) (ψ (ε, ν)))) := by
  let G : Set RootGraphPoint := coorbitalBaseGraph '' K
  let V : Set RootGraphPoint := {a | StrictConvexInOrder standardHullOrder
    (slicePhysicalConfiguration a.1 a.2)}
  have hG : IsCompact G := coorbitalBaseGraph_image_isCompact K hK hpositive
  have hdata : ∀ a ∈ G, SliceRegular a.1 a.2 ∧ reducedResidual a.1 a.2 = 0 ∧
      (reducedJacobian a.1 a.2).IsInvertible := by
    rintro a ⟨μ, hμK, rfl⟩
    exact coorbitalBaseSlice_actual_data μ (hpositive μ hμK)
  have hV : ∀ a ∈ G, V ∈ 𝓝 a := by
    rintro a ⟨μ, hμK, rfl⟩
    exact slicePhysical_strictConvex_neighborhood standardHullOrder (0, μ) (coorbitalBaseSlice μ)
      (coorbitalBaseSlice_strictConvex μ (hpositive μ hμK))
  obtain ⟨η, r, C, hη, hr, hC, hbranches⟩ :=
    reducedResidual_compact_product_preserving G V hG hdata hV
  refine ⟨η, r, C, hη, hr, hC, ?_⟩
  intro μ hμK
  obtain ⟨ψ, hbase, hsmooth, hbranch⟩ := hbranches (coorbitalBaseGraph μ) (Set.mem_image_of_mem _ hμK)
  refine ⟨ψ, hbase, hsmooth, ?_⟩
  intro ε ν hε hν
  have hdist : dist (ε, ν) (0, μ) < η := by
    simpa only [Prod.dist_eq, Real.dist_eq, sub_zero] using max_lt hε hν
  obtain ⟨hconv, hrootdist, hreg, hJ, hinv, hroot, huniq⟩ := hbranch (ε, ν) hdist
  refine ⟨hconv, hrootdist, hreg, hJ, hinv, hroot, huniq, ?_⟩
  intro heps hmass
  have hx := normalizedCC_of_reducedResidual_zero (ε, ν) (ψ (ε, ν)) hreg heps hmass hroot
  exact ⟨hx, ⟨normalized_is_central _ _ hx, hconv⟩,
    (reducedJacobian_isInvertible_iff_shape (ε, ν) (ψ (ε, ν)) hreg heps hmass hroot).mp hJ⟩

end DominantFiveBody
