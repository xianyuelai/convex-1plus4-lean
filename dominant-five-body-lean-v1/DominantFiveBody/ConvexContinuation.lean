import DominantFiveBody.CompactContinuation
import DominantFiveBody.CoorbitalCovering

/-! Actual strict convexity of the coorbital base and its independent
parameter continuation, including the primary hull vertex. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

def standardHullOrder : HullOrder := ⟨Equiv.refl Label, rfl⟩

theorem orientedArea_cyclic (x : Configuration) (i j k : Label) :
    orientedArea x i j k = orientedArea x j k i := by
  simp only [orientedArea, det2, PiLp.sub_apply]
  ring

theorem standardStrictConvex_of_increasing_triples (x : Configuration)
    (h : ∀ i j k : Label, i < j → j < k → 0 < orientedArea x i j k) :
    StrictConvexInOrder standardHullOrder x := by
  intro k j hj hk
  change 0 < orientedArea x k (k + 1) j
  have hcyc₁ {a b c : Label} (ha : 0 < orientedArea x a b c) :
      0 < orientedArea x b c a := by rwa [← orientedArea_cyclic x a b c]
  have hcyc₂ {a b c : Label} (ha : 0 < orientedArea x a b c) :
      0 < orientedArea x c a b := hcyc₁ (hcyc₁ ha)
  fin_cases k <;> fin_cases j <;> norm_num at *
  all_goals try { exact False.elim (hk (by decide)) }
  all_goals first
    | solve | exact h _ _ _ (by decide) (by decide)
    | solve | apply hcyc₁; exact h _ _ _ (by decide) (by decide)
    | solve | apply hcyc₂; exact h _ _ _ (by decide) (by decide)

theorem unit_polar_det (a b : ℝ) :
    det2 (polarPoint 1 a) (polarPoint 1 b) = Real.sin (b - a) := by
  simp [det2, polarPoint, point, Real.sin_sub]
  ring

theorem unit_polar_triangle_det (a b c : ℝ) :
    det2 (polarPoint 1 b - polarPoint 1 a) (polarPoint 1 c - polarPoint 1 a) =
      Real.sin (b - a) + Real.sin (c - b) - Real.sin (c - a) := by
  simp [det2, polarPoint, point, PiLp.sub_apply, Real.sin_sub]
  ring

theorem unit_polar_triangle_det_pos (a b c : ℝ)
    (hab : 0 < b - a) (hbc : 0 < c - b) (hac : c - a < Real.pi) :
    0 < det2 (polarPoint 1 b - polarPoint 1 a) (polarPoint 1 c - polarPoint 1 a) := by
  have hba : b - a < Real.pi := by linarith
  have hcb : c - b < Real.pi := by linarith
  have hsa := Real.sin_pos_of_pos_of_lt_pi hab hba
  have hsb := Real.sin_pos_of_pos_of_lt_pi hbc hcb
  have hca : Real.cos (b - a) < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (by norm_num) hba.le hab
  have hcc : Real.cos (c - b) < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (by norm_num) hcb.le hbc
  have he : Real.sin (c - a) = Real.sin (b - a) * Real.cos (c - b) +
      Real.cos (b - a) * Real.sin (c - b) := by
    rw [show c - a = (b - a) + (c - b) by ring, Real.sin_add]
  rw [unit_polar_triangle_det, he]
  nlinarith [mul_pos hsa (sub_pos.mpr hcc), mul_pos hsb (sub_pos.mpr hca)]

theorem unit_polar_primary_area_pos (θ : Satellite → ℝ) (hθ : OrderedSemicircle θ)
    (i j : Satellite) (hij : i < j) :
    0 < orientedArea (liftRelative (polarSatellites (fun _ => 1) θ)) 0 i.succ j.succ := by
  simpa only [orientedArea, liftRelative, Fin.cases_zero, Fin.cases_succ,
    sub_zero, polarSatellites, unit_polar_det] using
    Real.sin_pos_of_pos_of_lt_pi (hθ i j hij).1 (hθ i j hij).2

theorem unit_polar_satellite_area_pos (θ : Satellite → ℝ) (hθ : OrderedSemicircle θ)
    (i j k : Satellite) (hij : i < j) (hjk : j < k) :
    0 < orientedArea (liftRelative (polarSatellites (fun _ => 1) θ)) i.succ j.succ k.succ := by
  simpa only [orientedArea, liftRelative, Fin.cases_succ, polarSatellites] using
    unit_polar_triangle_det_pos (θ i) (θ j) (θ k) (hθ i j hij).1 (hθ j k hjk).1
      (hθ i k (lt_trans hij hjk)).2

/-- All ten actual cyclic triple areas, including those involving the
dominant body, have positive coorbital limits. -/
theorem unit_polar_strictConvex (θ : Satellite → ℝ) (hθ : OrderedSemicircle θ) :
    StrictConvexInOrder standardHullOrder (liftRelative (polarSatellites (fun _ => 1) θ)) := by
  apply standardStrictConvex_of_increasing_triples
  intro i j k hij hjk
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨b, rfl⟩
  · exact False.elim (not_lt_of_ge (Fin.zero_le i) hij)
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨c, rfl⟩
  · exact False.elim (not_lt_of_ge (Fin.zero_le b.succ) hjk)
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨a, rfl⟩
  · exact unit_polar_primary_area_pos θ hθ b c (by simpa using hjk)
  · exact unit_polar_satellite_area_pos θ hθ a b c (by simpa using hij) (by simpa using hjk)

theorem orientedArea_translate (x : Configuration) (b : Plane) (i j k : Label) :
    orientedArea (fun l => x l - b) i j k = orientedArea x i j k := by
  unfold orientedArea
  congr 1 <;> ext l <;> simp only [PiLp.sub_apply] <;> ring

theorem strictConvex_centeredFromRelative_iff (σ : HullOrder) (ε : ℝ) (μ : MassRatio)
    (q : SatelliteConfiguration) :
    StrictConvexInOrder σ (centeredFromRelative ε μ q) ↔ StrictConvexInOrder σ (liftRelative q) := by
  unfold StrictConvexInOrder centeredFromRelative
  simp only [orientedArea_translate]

theorem orientedArea_continuous (i j k : Label) :
    Continuous (fun x : Configuration => orientedArea x i j k) := by
  unfold orientedArea det2
  fun_prop

theorem isOpen_strictConvexInOrder (σ : HullOrder) :
    IsOpen {x : Configuration | StrictConvexInOrder σ x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  apply Filter.eventually_all.mpr
  intro k
  apply Filter.eventually_all.mpr
  intro j
  by_cases hj : j = k
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hj))
  by_cases hk : j = k + 1
  · exact Filter.Eventually.of_forall (fun _ _ h => False.elim (h hk))
  have h := (orientedArea_continuous (σ.labels k) (σ.labels (k + 1)) (σ.labels j)).continuousAt
    |>.tendsto.eventually ((isOpen_lt continuous_const continuous_id).mem_nhds (hx k j hj hk))
  filter_upwards [h] with y hy
  exact fun _ _ => hy

theorem sliceSatellites_continuous : Continuous sliceSatellites := by
  exact continuous_pi (fun i => (sliceSatellites_contDiff 0 i).continuous)

theorem liftRelative_continuous : Continuous liftRelative := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [liftRelative, Fin.cases_zero]; exact continuous_const
  · simp only [liftRelative, Fin.cases_succ]; fun_prop

theorem slicePhysical_strictConvex_neighborhood (σ : HullOrder)
    (p : ContinuationParameter) (y : SliceCoordinates)
    (hconv : StrictConvexInOrder σ (slicePhysicalConfiguration p y)) :
    {a : RootGraphPoint | StrictConvexInOrder σ (slicePhysicalConfiguration a.1 a.2)} ∈ 𝓝 (p, y) := by
  have hc : Continuous (fun a : RootGraphPoint => liftRelative (sliceSatellites a.2)) :=
    liftRelative_continuous.comp (sliceSatellites_continuous.comp continuous_snd)
  have hbase : StrictConvexInOrder σ (liftRelative (sliceSatellites y)) := by
    apply (strictConvex_centeredFromRelative_iff σ p.1 p.2 (sliceSatellites y)).mp
    simpa only [slicePhysicalConfiguration, relativeCenteredContinuous_apply] using hconv
  have h : ∀ᶠ a : RootGraphPoint in 𝓝 (p, y),
      StrictConvexInOrder σ (liftRelative (sliceSatellites a.2)) :=
    (hc.continuousAt (x := (p, y))).tendsto.eventually
      ((isOpen_strictConvexInOrder σ).mem_nhds hbase)
  filter_upwards [h] with a ha
  have h' := (strictConvex_centeredFromRelative_iff σ a.1.1 a.1.2 (sliceSatellites a.2)).mpr ha
  simpa only [slicePhysicalConfiguration, relativeCenteredContinuous_apply] using h'

end DominantFiveBody
