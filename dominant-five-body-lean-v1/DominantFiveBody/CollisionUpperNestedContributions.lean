import DominantFiveBody.CollisionUpperNestedRectangle
import DominantFiveBody.CollisionNestedRectangleContributions

/-! # Both signed contributions on the actual upper nested rectangle -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1800000

theorem normalized_complete_upper_triple_nested_rectangle_individual_limits
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder standardHullOrder (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,OrderedSemicircle (theta n))
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htt : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 0 center)
    (a b c : TripleLabel) (hab : a<b) (hca : c≠a) (hcb : c≠b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.succ b.succ/
      tripleHighDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,
      ∀ rho∈uIcc (r n a.succ) (r n b.succ),∀ v∈uIcc (theta n a.succ) (theta n b.succ),
      |mu n c.succ*physicalSourceAngularRadialDerivative (r n c.succ) (theta n c.succ) rho v|<eta ∧
      |mu n c.succ*physicalSourceAngularAngularDerivative (r n c.succ) (theta n c.succ) rho v-
        2*mu n c.succ/tripleHighDiameter (satellitesRelative (x n))^3|<eta ∧
      |mu n 0*physicalSourceAngularRadialDerivative (r n 0) (theta n 0) rho v-3*Real.sqrt 3/4|<eta ∧
      |mu n 0*physicalSourceAngularAngularDerivative (r n 0) (theta n 0) rho v-(9/4 : ℝ)|<eta := by
  have hrev (i : TripleLabel) : (i.rev.castSucc : Satellite).rev=i.succ := by fin_cases i <;> rfl
  have hdist (n : ℕ) : satelliteDistance (satellitesRelative (mirrorConfiguration (x n))) b.rev.castSucc a.rev.castSucc=
      satelliteDistance (satellitesRelative (x n)) a.succ b.succ := by
    rw [mirrorConfiguration_pairDistance,hrev,hrev]
    exact norm_sub_rev _ _
  have hmt' : Tendsto (fun n => mu n ∘ Fin.revPerm) atTop (𝓝 (muLimit ∘ Fin.revPerm)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact (continuous_apply i.rev).continuousAt.tendsto.comp hmt
  have htt' : Tendsto (fun n i => -theta n (Fin.rev i)) atTop (𝓝 (fun i => -theta0 (Fin.rev i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact ((continuous_apply i.rev).continuousAt.tendsto.comp htt).neg
  have hpair' : Tendsto (fun n => satelliteDistance (satellitesRelative (mirrorConfiguration (x n)))
      b.rev.castSucc a.rev.castSucc/tripleLowDiameter (satellitesRelative (mirrorConfiguration (x n))))
      atTop (𝓝 0) := by simpa only [hdist,tripleLowDiameter_mirror] using hpair
  have hlow := normalized_complete_lower_triple_nested_rectangle_individual_limits eps
    (fun n => mu n ∘ Fin.revPerm) (fun n => mirrorConfiguration (x n)) heps hepst
    (fun n => positiveRatio_satellitePermutation _ (hm n) Fin.revPerm)
    (fun n => mirrorConfiguration_normalized _ _ _ (hx n))
    (fun n => mirrorConfiguration_strictConvex _ (hconv n))
    (fun n => r n ∘ Fin.revPerm) (fun n i => -theta n (Fin.rev i))
    (fun n i => hr n i.rev) (fun n => mirrorConfiguration_polar _ _ _ (hpolar n))
    (fun n => mirrorAngles_ordered _ (horder n)) (muLimit ∘ Fin.revPerm) hmt'
    (fun i => planeReflection (qLimit (Fin.rev i))) (mirrorConfiguration_relative_limit x qLimit hqt)
    (fun i => -theta0 (Fin.rev i)) htt' (planeReflection center)
    (complete_upper_triple_mirror qLimit center htriple) b.rev a.rev c.rev
    (Fin.rev_lt_rev.mpr hab) (Fin.rev_injective.ne hcb) (Fin.rev_injective.ne hca) hpair'
  intro eta heta
  filter_upwards [hlow eta heta] with n hn
  intro rho hrho v hv
  have hrho' : rho∈uIcc ((r n ∘ Fin.revPerm) b.rev.castSucc) ((r n ∘ Fin.revPerm) a.rev.castSucc) := by
    simpa only [Function.comp_apply,Fin.revPerm_apply,hrev,uIcc_comm] using hrho
  have hv' : -v∈uIcc (-theta n (Fin.rev b.rev.castSucc)) (-theta n (Fin.rev a.rev.castSucc)) := by
    rw [hrev,hrev,mem_uIcc]
    rcases mem_uIcc.mp hv with hv|hv
    · exact Or.inl ⟨neg_le_neg hv.2,neg_le_neg hv.1⟩
    · exact Or.inr ⟨neg_le_neg hv.2,neg_le_neg hv.1⟩
  have hh := hn rho hrho' (-v) hv'
  simp only [Function.comp_apply,Fin.revPerm_apply,hrev,
    show (Fin.rev (3 : Satellite))=(0 : Satellite) from rfl,
    physicalSourceAngularRadialDerivative_neg_angles,
    physicalSourceAngularAngularDerivative_neg_angles,tripleLowDiameter_mirror] at hh
  refine ⟨?_,hh.2.1,?_,hh.2.2.2⟩
  · simpa only [mul_neg,abs_neg] using hh.1
  · convert hh.2.2.1 using 1
    rw [← abs_neg]
    congr 1
    ring

end DominantFiveBody
