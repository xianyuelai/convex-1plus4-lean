import DominantFiveBody.RelativeAction
import DominantFiveBody.ForceBalance

/-! # The actual normalized five-body equations imply every polar row

Source: §3, equations `eq:G`, `eq:R`, `eq:T`, and `eq:Q`. These are identities
of the original accelerations; no abstract root predicate is substituted.
-/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody

theorem acceleration_translate (m : MassVector) (x : Configuration) (b : Plane) (i : Label) :
    acceleration m (fun j => x j-b) i=acceleration m x i := by
  unfold acceleration pairDistance
  congr 1
  ext j
  have heq : (x j-b)-(x i-b)=x j-x i := by abel
  have heq' : (x i-b)-(x j-b)=x i-x j := by abel
  rw [heq, heq']

theorem acceleration_liftRelative_primary (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) :
    acceleration (masses eps mu) (liftRelative q) 0=eps • relativeField mu q := by
  unfold acceleration
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Label)), Fin.sum_univ_succ]
  simp [masses_primary, masses_satellite, pairDistance, liftRelative,
    relativeField, Finset.smul_sum, smul_smul, mul_div_assoc]

theorem acceleration_liftRelative_satellite (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) (i : Satellite) :
    acceleration (masses eps mu) (liftRelative q) i.succ =
      -((‖q i‖^3)⁻¹ • q i)+eps • satelliteInteraction mu q i := by
  unfold acceleration
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i.succ), Fin.sum_univ_succ]
  simp [masses_primary, masses_satellite, pairDistance, liftRelative,
    satelliteInteraction, satelliteDistance, Finset.sum_erase_eq_sub,
    Finset.smul_sum, smul_smul, mul_div_assoc]

theorem liftRelative_satellitesRelative (x : Configuration) :
    liftRelative (satellitesRelative x)=primaryRelative x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftRelative, primaryRelative]
  · rfl

theorem vectorResidual_eq_acceleration_difference (eps : ℝ) (mu : MassRatio)
    (x : Configuration) (i : Satellite) :
    vectorResidual eps mu (satellitesRelative x) i =
      satellitesRelative x i + acceleration (masses eps mu) x i.succ-
        acceleration (masses eps mu) x 0 := by
  have ha (j : Label) : acceleration (masses eps mu) (liftRelative (satellitesRelative x)) j =
      acceleration (masses eps mu) x j := by
    rw [liftRelative_satellitesRelative]
    exact acceleration_translate _ x (x 0) j
  rw [← ha i.succ, ← ha 0, acceleration_liftRelative_primary,
    acceleration_liftRelative_satellite]
  change satellitesRelative x i - (‖satellitesRelative x i‖^3)⁻¹ • satellitesRelative x i +
    eps • satelliteInteraction mu (satellitesRelative x) i - eps • relativeField mu (satellitesRelative x) = _
  abel

theorem vectorResidual_zero_of_normalized (eps : ℝ) (mu : MassRatio)
    (x : Configuration) (hx : NormalizedCentralConfiguration (masses eps mu) x) :
    ∀ i, vectorResidual eps mu (satellitesRelative x) i=0 := by
  intro i
  rw [vectorResidual_eq_acceleration_difference, hx.2.2 i.succ, hx.2.2 0]
  unfold satellitesRelative primaryRelative
  abel

theorem polarResiduals_zero_of_normalized (eps : ℝ) (mu : MassRatio)
    (x : Configuration) (hx : NormalizedCentralConfiguration (masses eps mu) x)
    (hm : PositiveRatio mu) (heps : 0<eps) (r theta : Satellite → ℝ)
    (hr : ∀ i, 0<r i) (hpolar : satellitesRelative x=polarSatellites r theta) :
    (∀ i, radialResidual eps mu r theta i=0) ∧
      (∀ i, angularResidual eps mu r theta i=0) := by
  apply polarResiduals_zero_of_vectorResidual_zero eps mu r theta hm heps hr
  rw [← hpolar]
  exact vectorResidual_zero_of_normalized eps mu x hx

theorem vectorResidual_tangential (eps : ℝ) (mu r theta : Satellite → ℝ)
    (hr : ∀ i, 0<r i) (i : Satellite) :
    inner ℝ (vectorResidual eps mu (polarSatellites r theta) i)
      (quarterTurn (polarSatellites r theta i)) =
        eps*r i*tangentialResidual mu r theta i := by
  have hint : inner ℝ (satelliteInteraction mu (polarSatellites r theta) i)
      (quarterTurn (polarSatellites r theta i)) =
      ∑ j ∈ Finset.univ.erase i, mu j*r i*r j*Real.sin (theta j-theta i)/
        satelliteDistance (polarSatellites r theta) i j^3 := by
    unfold satelliteInteraction
    simp only [sum_inner, real_inner_smul_left, inner_sub_left, quarterTurn_inner_self,
      sub_zero, polarSatellites, polarPoint_inner_rotation]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hfield : inner ℝ (relativeField mu (polarSatellites r theta))
      (quarterTurn (polarSatellites r theta i)) =
      ∑ j ∈ Finset.univ.erase i, mu j*r i*r j*Real.sin (theta j-theta i)/(r j^3) := by
    simp only [relativeField, sum_inner, real_inner_smul_left]
    have hn (j : Satellite) : ‖polarSatellites r theta j‖=r j := by
      simpa only [polarSatellites, abs_of_pos (hr j)] using polarPoint_norm (r j) (theta j)
    simp_rw [hn]
    simp only [polarSatellites, polarPoint_inner_rotation]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp only [sub_self, Real.sin_zero, mul_zero, zero_div, sub_zero]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change inner ℝ (polarSatellites r theta i-(‖polarSatellites r theta i‖^3)⁻¹ •
    polarSatellites r theta i+eps • satelliteInteraction mu (polarSatellites r theta) i-
    eps • relativeField mu (polarSatellites r theta))
    (quarterTurn (polarSatellites r theta i)) = _
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, quarterTurn_inner_self,
    mul_zero, sub_zero, zero_add, hint, hfield]
  unfold tangentialResidual
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tangentialResidual_zero_of_vectorResidual_zero (eps : ℝ)
    (mu r theta : Satellite → ℝ) (heps : eps≠0) (hr : ∀ i, 0<r i)
    (hroot : ∀ i, vectorResidual eps mu (polarSatellites r theta) i=0) :
    ∀ i, tangentialResidual mu r theta i=0 := by
  intro i
  have h := vectorResidual_tangential eps mu r theta hr i
  rw [hroot i, inner_zero_left] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (mul_ne_zero heps (ne_of_gt (hr i)))

theorem tangentialResidual_zero_of_normalized (eps : ℝ) (mu : MassRatio)
    (x : Configuration) (hx : NormalizedCentralConfiguration (masses eps mu) x)
    (heps : eps≠0) (r theta : Satellite → ℝ) (hr : ∀ i, 0<r i)
    (hpolar : satellitesRelative x=polarSatellites r theta) :
    ∀ i, tangentialResidual mu r theta i=0 := by
  apply tangentialResidual_zero_of_vectorResidual_zero eps mu r theta heps hr
  rw [← hpolar]
  exact vectorResidual_zero_of_normalized eps mu x hx

theorem collisionFree_liftRelative_iff (q : SatelliteConfiguration) :
    CollisionFree (liftRelative q) ↔ RelativeCollisionFree q := by
  constructor
  · intro hc
    constructor
    · intro i
      simpa only [liftRelative, Fin.cases_succ, Fin.cases_zero] using
        hc i.succ 0 (Fin.succ_ne_zero i)
    · intro i j hij
      simpa only [liftRelative, Fin.cases_succ] using
        hc i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))
  · intro hq i
    refine Fin.cases ?_ (fun a => ?_) i
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro h
        exact (h rfl).elim
      · intro _
        simpa only [liftRelative, Fin.cases_zero, Fin.cases_succ] using (hq.1 b).symm
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro _
        simpa only [liftRelative, Fin.cases_zero, Fin.cases_succ] using hq.1 a
      · intro hab
        simpa only [liftRelative, Fin.cases_succ] using hq.2 a b
          (by intro heq; apply hab; exact congrArg Fin.succ heq)

theorem collisionFree_centeredFromRelative (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) (hq : RelativeCollisionFree q) :
    CollisionFree (centeredFromRelative eps mu q) := by
  intro i j hij heq
  apply (collisionFree_liftRelative_iff q).mpr hq i j hij
  exact sub_left_injective heq

theorem normalized_of_vectorResidual_zero (eps : ℝ) (mu : MassRatio)
    (heps : -1<eps) (hm : PositiveRatio mu) (q : SatelliteConfiguration)
    (hq : RelativeCollisionFree q) (hroot : ∀ i, vectorResidual eps mu q i=0) :
    NormalizedCentralConfiguration (masses eps mu) (centeredFromRelative eps mu q) := by
  apply normalized_of_primary_differences
    (masses eps mu) (centeredFromRelative eps mu q)
  · rw [totalMass_masses eps mu hm]
    exact parameter_denominator_ne_zero eps heps
  · exact collisionFree_centeredFromRelative eps mu q hq
  · exact centeredFromRelative_weightedPosition_zero eps mu hm heps q
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · have hf := vectorResidual_eq_acceleration_difference eps mu
        (centeredFromRelative eps mu q) j
      rw [satellitesRelative_centeredFromRelative] at hf
      rw [hroot j] at hf
      have hqj : q j=centeredFromRelative eps mu q j.succ-centeredFromRelative eps mu q 0 := by
        simp [centeredFromRelative, liftRelative]
      rw [hqj] at hf
      apply eq_neg_of_add_eq_zero_right
      have heq := hf.symm
      calc
        (centeredFromRelative eps mu q j.succ-centeredFromRelative eps mu q 0)+
          (acceleration (masses eps mu) (centeredFromRelative eps mu q) j.succ-
            acceleration (masses eps mu) (centeredFromRelative eps mu q) 0) =
            (centeredFromRelative eps mu q j.succ-centeredFromRelative eps mu q 0)+
              acceleration (masses eps mu) (centeredFromRelative eps mu q) j.succ-
                acceleration (masses eps mu) (centeredFromRelative eps mu q) 0 := by abel
        _ = 0 := heq

theorem normalized_centeredFromRelative_iff_vectorRoot (eps : ℝ) (mu : MassRatio)
    (heps : -1<eps) (hm : PositiveRatio mu) (q : SatelliteConfiguration)
    (hq : RelativeCollisionFree q) :
    NormalizedCentralConfiguration (masses eps mu) (centeredFromRelative eps mu q) ↔
      (∀ i, vectorResidual eps mu q i=0) := by
  constructor
  · intro hx
    have h := vectorResidual_zero_of_normalized eps mu _ hx
    rwa [satellitesRelative_centeredFromRelative] at h
  · exact normalized_of_vectorResidual_zero eps mu heps hm q hq

end DominantFiveBody
