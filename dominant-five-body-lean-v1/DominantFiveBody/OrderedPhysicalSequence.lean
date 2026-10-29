import DominantFiveBody.CollisionSubsequence
import DominantFiveBody.PhysicalHullRelabeling

/-! Actual roots in any oriented hull order admit a common ordered gauge.
Masses and labels are transported together, and the remaining transformation
is an orientation-preserving rotation. No chart hypothesis is used. -/

noncomputable section
open scoped BigOperators
open Filter Set Topology
namespace DominantFiveBody

theorem strictConvex_gauged_ordered_polar (x : Configuration)
    (hconv : StrictConvexInOrder standardHullOrder x) (hcollision : CollisionFree x)
    (hgauge : FirstSatelliteGauge x) :
    ∃ r theta : Satellite → ℝ,(∀ i,0<r i) ∧ theta 0=0 ∧
      (∀ i j,i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi) ∧
      satellitesRelative x=polarSatellites r theta := by
  obtain ⟨r,theta,phi,hr,hzero,horder,hpolar⟩ :=
    strictConvexInOrder_exists_ordered_polar standardHullOrder x hconv hcollision
  have hanchor : satellitesRelative x 0=polarPoint (r 0) phi := by
    simpa only [standardHullOrder,Equiv.refl_apply,hzero,zero_add,
      satellitesRelative,primaryRelative] using hpolar 0
  have hs : Real.sin phi=0 := by
    have hz := hgauge.2
    rw [hanchor] at hz
    change r 0*Real.sin phi=0 at hz
    exact (mul_eq_zero.mp hz).resolve_left (hr 0).ne'
  have hcp : 0<Real.cos phi := by
    have hp := hgauge.1
    rw [hanchor] at hp
    change 0<r 0*Real.cos phi at hp
    exact (mul_pos_iff_of_pos_left (hr 0)).mp hp
  have hc : Real.cos phi=1 := by
    have ht := Real.sin_sq_add_cos_sq phi
    rw [hs] at ht
    nlinarith
  refine ⟨r,theta,hr,hzero,horder,?_⟩
  funext i
  have hi : satellitesRelative x i=polarPoint (r i) (theta i+phi) := hpolar i
  rw [hi]
  simp only [polarSatellites,polarPoint,Real.cos_add,Real.sin_add,hs,hc,
    mul_zero,mul_one,sub_zero,add_zero]

def orderedGaugeConfiguration (sigma : HullOrder) (x : Configuration) : Configuration :=
  rotateConfiguration (firstSatelliteRotation (x ∘ sigma.labels)) (x ∘ sigma.labels)

theorem orderedGaugeConfiguration_normalized (eps : ℝ) (mu : MassRatio)
    (sigma : HullOrder) (x : Configuration)
    (hx : NormalizedCentralConfiguration (masses eps mu) x) :
    NormalizedCentralConfiguration (masses eps (mu ∘ hullSatellitePermutation sigma))
      (orderedGaugeConfiguration sigma x) := by
  have h := normalized_reindex (masses eps mu) x hx sigma.labels
  rw [← masses_hull_reindex] at h
  exact normalizedCC_rotateConfiguration _ _ _ h

theorem orderedGaugeConfiguration_convex (sigma : HullOrder) (x : Configuration)
    (hc : StrictConvexInOrder sigma x) :
    StrictConvexInOrder standardHullOrder (orderedGaugeConfiguration sigma x) := by
  apply (strictConvex_rotateConfiguration_iff _ _ _ (firstSatelliteRotation_det _)).mpr
  exact (strictConvex_hull_reindex_iff sigma x).mpr hc

theorem orderedGaugeConfiguration_gauge (sigma : HullOrder) (x : Configuration)
    (hx : CollisionFree x) : FirstSatelliteGauge (orderedGaugeConfiguration sigma x) := by
  apply firstSatelliteGauge_rotation
  intro i j hij
  exact hx _ _ (sigma.labels.injective.ne hij)

theorem orderedGaugeConfiguration_ordered_polar (sigma : HullOrder) (x : Configuration)
    (hc : StrictConvexInOrder sigma x) (hx : CollisionFree x) :
    ∃ r theta : Satellite → ℝ,(∀ i,0<r i) ∧ theta 0=0 ∧
      (∀ i j,i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi) ∧
      satellitesRelative (orderedGaugeConfiguration sigma x)=polarSatellites r theta := by
  apply strictConvex_gauged_ordered_polar _ (orderedGaugeConfiguration_convex sigma x hc)
    _ (orderedGaugeConfiguration_gauge sigma x hx)
  apply collisionFree_rotateConfiguration
  intro i j hij
  exact hx _ _ (sigma.labels.injective.ne hij)

theorem normalized_any_order_collision_subsequence
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (sigma : ℕ → HullOrder) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hc : ∀ n,StrictConvexInOrder (sigma n) (x n)) :
    let muOrdered := fun n => mu n ∘ hullSatellitePermutation (sigma n)
    let xOrdered := fun n => orderedGaugeConfiguration (sigma n) (x n)
    ∃ r theta : ℕ → Satellite → ℝ,
      (∀ n i,0<r n i) ∧ (∀ n,theta n 0=0) ∧
      (∀ n i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi) ∧
      (∀ n,satellitesRelative (xOrdered n)=polarSatellites (r n) (theta n)) ∧
      ∃ (phi : ℕ → ℕ) (muLimit thetaLimit : Satellite → ℝ),StrictMono phi ∧
        Tendsto (muOrdered ∘ phi) atTop (𝓝 muLimit) ∧
        Tendsto (theta ∘ phi) atTop (𝓝 thetaLimit) ∧
        (∀ i,0≤muLimit i) ∧ (∑ i,muLimit i=1) ∧
        let qLimit := polarSatellites (fun _ => 1) thetaLimit
        Tendsto (fun n => satellitesRelative (xOrdered (phi n))) atTop (𝓝 qLimit) ∧
        (Function.Injective qLimit ∨
          (∃ a b : Satellite,a<b ∧ CompleteLimitingSatellitePair qLimit a b (qLimit a)) ∨
          (∃ p : Satellite,(p=0 ∨ p=3) ∧ ∃ c,CompleteLimitingSatelliteTriple qLimit p c)) := by
  classical
  dsimp only
  choose r theta hr hzero horder hpolar using
    (fun n => orderedGaugeConfiguration_ordered_polar (sigma n) (x n) (hc n) (hx n).1)
  refine ⟨r,theta,hr,hzero,horder,hpolar,?_⟩
  exact normalized_ordered_collision_subsequence eps
    (fun n => mu n ∘ hullSatellitePermutation (sigma n))
    (fun n => orderedGaugeConfiguration (sigma n) (x n)) heps hepst
    (fun n => positiveRatio_hull_reindex (mu n) (sigma n) (hm n))
    (fun n => orderedGaugeConfiguration_normalized (eps n) (mu n) (sigma n) (x n) (hx n))
    (fun n => orderedGaugeConfiguration_convex (sigma n) (x n) (hc n))
    r theta hr hpolar hzero horder

end DominantFiveBody
