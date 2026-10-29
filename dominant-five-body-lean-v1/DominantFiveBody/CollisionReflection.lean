import DominantFiveBody.OrderedPhysicalSequence
import Mathlib.Data.Fin.Rev

/-! Reflection together with reversed satellite labels preserves the
standard convex order. This is a symmetry used to prove estimates for
both endpoint triples; it is never included in `OrientedSimilar`. -/

noncomputable section
open scoped BigOperators
open Filter Set Topology
namespace DominantFiveBody

def planeReflection : Plane ≃ₗᵢ[ℝ] Plane where
  toFun v := point (v 0) (-v 1)
  invFun v := point (v 0) (-v 1)
  left_inv v := by ext i; fin_cases i <;> simp [point]
  right_inv v := by ext i; fin_cases i <;> simp [point]
  map_add' v w := by ext i; fin_cases i <;> simp [point,PiLp.add_apply,add_comm]
  map_smul' c v := by ext i; fin_cases i <;> simp [point,PiLp.smul_apply]
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two,point]

@[simp] theorem planeReflection_polar (r theta : ℝ) :
    planeReflection (polarPoint r theta)=polarPoint r (-theta) := by
  ext i
  fin_cases i <;> simp [planeReflection,polarPoint,point]

theorem planeReflection_det2 (v w : Plane) :
    det2 (planeReflection v) (planeReflection w)= -det2 v w := by
  simp [planeReflection,det2,point]
  ring

def reversedSatelliteLabels : Equiv.Perm Label := satelliteLabelPermutation Fin.revPerm

theorem reversedSatelliteLabels_edge (k : Label) :
    reversedSatelliteLabels (k+1)+1=reversedSatelliteLabels k := by
  fin_cases k <;> rfl

def mirrorConfiguration (x : Configuration) : Configuration :=
  rotateConfiguration planeReflection (x ∘ reversedSatelliteLabels)

theorem mirrorConfiguration_normalized (eps : ℝ) (mu : MassRatio) (x : Configuration)
    (hx : NormalizedCentralConfiguration (masses eps mu) x) :
    NormalizedCentralConfiguration (masses eps (mu ∘ Fin.revPerm)) (mirrorConfiguration x) := by
  rw [masses_satellitePermutation]
  exact normalizedCC_rotateConfiguration _ _ _ (normalizedCC_permutation _ _ hx reversedSatelliteLabels)

theorem mirrorConfiguration_strictConvex (x : Configuration)
    (hc : StrictConvexInOrder standardHullOrder x) :
    StrictConvexInOrder standardHullOrder (mirrorConfiguration x) := by
  intro k j hj hjnext
  have hh := hc (reversedSatelliteLabels (k+1)) (reversedSatelliteLabels j)
    (reversedSatelliteLabels.injective.ne hjnext)
    (by rw [reversedSatelliteLabels_edge]; exact reversedSatelliteLabels.injective.ne hj)
  change 0<orientedArea x (reversedSatelliteLabels (k+1))
    (reversedSatelliteLabels (k+1)+1) (reversedSatelliteLabels j) at hh
  rw [reversedSatelliteLabels_edge] at hh
  change 0<det2 (planeReflection (x (reversedSatelliteLabels (k+1)))-planeReflection (x (reversedSatelliteLabels k)))
    (planeReflection (x (reversedSatelliteLabels j))-planeReflection (x (reversedSatelliteLabels k)))
  rw [←map_sub,←map_sub,planeReflection_det2]
  have he : -det2 (x (reversedSatelliteLabels (k+1))-x (reversedSatelliteLabels k))
      (x (reversedSatelliteLabels j)-x (reversedSatelliteLabels k))=
      orientedArea x (reversedSatelliteLabels (k+1)) (reversedSatelliteLabels k) (reversedSatelliteLabels j) := by
    simp only [orientedArea,det2,PiLp.sub_apply]
    ring
  rw [he]
  exact hh

theorem mirrorConfiguration_relative (x : Configuration) :
    satellitesRelative (mirrorConfiguration x)=fun i => planeReflection (satellitesRelative x (Fin.rev i)) := by
  funext i
  simp only [satellitesRelative,primaryRelative,mirrorConfiguration,rotateConfiguration,
    reversedSatelliteLabels,Function.comp_apply,satelliteLabelPermutation_zero,
    satelliteLabelPermutation_succ,Fin.revPerm_apply,map_sub]

theorem mirrorConfiguration_polar (x : Configuration) (r theta : Satellite → ℝ)
    (hp : satellitesRelative x=polarSatellites r theta) :
    satellitesRelative (mirrorConfiguration x)=polarSatellites (r ∘ Fin.revPerm)
      (fun i => -theta (Fin.rev i)) := by
  rw [mirrorConfiguration_relative,hp]
  funext i
  exact planeReflection_polar _ _

theorem mirrorAngles_ordered (theta : Satellite → ℝ) (h : OrderedSemicircle theta) :
    OrderedSemicircle (fun i => -theta (Fin.rev i)) := by
  intro i j hij
  have hh := h j.rev i.rev (Fin.rev_lt_rev.mpr hij)
  simpa only [neg_sub_neg] using hh

theorem mirrorConfiguration_relative_limit (x : ℕ → Configuration) (q : SatelliteConfiguration)
    (hx : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 q)) :
    Tendsto (fun n => satellitesRelative (mirrorConfiguration (x n))) atTop
      (𝓝 (fun i => planeReflection (q (Fin.rev i)))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  simpa only [mirrorConfiguration_relative,Function.comp_def] using
    planeReflection.continuous.continuousAt.tendsto.comp ((continuous_apply i.rev).continuousAt.tendsto.comp hx)

theorem complete_upper_triple_mirror (q : SatelliteConfiguration) (c : Plane)
    (hq : CompleteLimitingSatelliteTriple q 0 c) :
    CompleteLimitingSatelliteTriple (fun i => planeReflection (q (Fin.rev i))) 3 (planeReflection c) := by
  intro i
  rw [planeReflection.injective.eq_iff,hq]
  fin_cases i <;> decide

theorem mirrorConfiguration_pairDistance (x : Configuration) (i j : Satellite) :
    satelliteDistance (satellitesRelative (mirrorConfiguration x)) i j=
      satelliteDistance (satellitesRelative x) i.rev j.rev := by
  simp only [satelliteDistance,mirrorConfiguration_relative,←map_sub,planeReflection.norm_map]

end DominantFiveBody
