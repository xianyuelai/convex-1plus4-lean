import DominantFiveBody.CollisionNestedRectangleControls
import DominantFiveBody.CollisionUpperNestedComplete

/-! # Actual upper nested polar-rectangle estimates -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1500000

theorem physicalSourceAngularRadialDerivative_neg_angles (s angle rho v : ℝ) :
    physicalSourceAngularRadialDerivative s (-angle) rho (-v)=
      -physicalSourceAngularRadialDerivative s angle rho v := by
  unfold physicalSourceAngularRadialDerivative
  rw [show -angle- -v= -(angle-v) by ring,Real.sin_neg,Real.cos_neg,
    polarPoint_distance_neg_angles]
  ring

theorem physicalSourceAngularAngularDerivative_neg_angles (s angle rho v : ℝ) :
    physicalSourceAngularAngularDerivative s (-angle) rho (-v)=
      physicalSourceAngularAngularDerivative s angle rho v := by
  unfold physicalSourceAngularAngularDerivative
  rw [show -angle- -v= -(angle-v) by ring,Real.sin_neg,Real.cos_neg,
    polarPoint_distance_neg_angles]
  ring

theorem normalized_complete_upper_triple_nested_rectangle_uniform_limits
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
      |mu n c.succ*physicalSourceAngularRadialDerivative (r n c.succ) (theta n c.succ) rho v+
        mu n 0*physicalSourceAngularRadialDerivative (r n 0) (theta n 0) rho v-3*Real.sqrt 3/4|<eta ∧
      |mu n c.succ*physicalSourceAngularAngularDerivative (r n c.succ) (theta n c.succ) rho v+
        mu n 0*physicalSourceAngularAngularDerivative (r n 0) (theta n 0) rho v-(27/4 : ℝ)|<eta := by
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
  have hlow := normalized_complete_lower_triple_nested_rectangle_uniform_limits eps
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
    physicalSourceAngularAngularDerivative_neg_angles] at hh
  refine ⟨?_,hh.2⟩
  convert hh.1 using 1
  rw [← abs_neg]
  congr 1
  ring

theorem normalized_complete_upper_triple_nested_rectangle_controls
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
    (clusterCenter : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 0 clusterCenter)
    (a b c : TripleLabel) (hab : a<b) (hca : c≠a) (hcb : c≠b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.succ b.succ/
      tripleHighDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    (∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,
      ∀ rho∈uIcc (r n a.succ) (r n b.succ),∀ v∈uIcc (theta n a.succ) (theta n b.succ),
      -physicalPairExteriorAngularRadialDerivative (mu n) (r n) (theta n) a.succ b.succ rho v≤ -C⁻¹ ∧
      |physicalPairExteriorAngularRadialDerivative (mu n) (r n) (theta n) a.succ b.succ rho v|+
        |physicalPairExteriorAngularAngularDerivative (mu n) (r n) (theta n) a.succ b.succ rho v|≤C) ∧
    (∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,
      ∀ rho∈uIcc (r n a.succ) (r n b.succ),∀ v∈uIcc (theta n a.succ) (theta n b.succ),
      |physicalPairExteriorAngularAngularDerivative (mu n) (r n) (theta n) a.succ b.succ rho v-
        ((9/4 : ℝ)+2*mu n c.succ/tripleHighDiameter (satellitesRelative (x n))^3)|<eta) := by
  have hsuccNe {i j : TripleLabel} (hij : i≠j) : i.succ≠j.succ := by
    intro he
    apply hij
    apply Fin.ext
    have hv := congrArg (fun k : Satellite => k.val) he
    simp only [Fin.val_succ] at hv
    omega
  have hhighNe (i : TripleLabel) : i.succ≠(0 : Satellite) := by fin_cases i <;> decide
  have hc : c.succ∈pairExteriorLabels a.succ b.succ := by
    simp only [pairExteriorLabels,Finset.mem_erase,Finset.mem_univ,and_true]
    exact ⟨hsuccNe hcb,hsuccNe hca⟩
  have hp : (0 : Satellite)∈pairExteriorLabels a.succ b.succ := by
    simp only [pairExteriorLabels,Finset.mem_erase,Finset.mem_univ,and_true]
    exact ⟨(hhighNe b).symm,(hhighNe a).symm⟩
  have hU := normalized_complete_upper_triple_nested_rectangle_uniform_limits eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt clusterCenter htriple a b c hab hca hcb hpair
  let R := fun n rho v => -physicalPairExteriorAngularRadialDerivative (mu n) (r n) (theta n) a.succ b.succ rho v
  let V := fun n rho v => physicalPairExteriorAngularAngularDerivative (mu n) (r n) (theta n) a.succ b.succ rho v
  have hU' : ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,
      ∀ rho∈uIcc (r n a.succ) (r n b.succ),∀ v∈uIcc (theta n a.succ) (theta n b.succ),
      |R n rho v+3*Real.sqrt 3/4|<eta ∧ |V n rho v-(27/4 : ℝ)|<eta := by
    intro eta heta
    filter_upwards [hU eta heta] with n hn
    intro rho hrho v hv
    have hh := hn rho hrho v hv
    dsimp only [R,V]
    rw [physicalPairExteriorAngularRadialDerivative_eq_selected _ _ _ _ _ _ _
      (hsuccNe hab.ne) (hhighNe c) hc hp,
      physicalPairExteriorAngularAngularDerivative_eq_selected _ _ _ _ _ _ _
        (hsuccNe hab.ne) (hhighNe c) hc hp]
    refine ⟨?_,hh.2⟩
    convert hh.1 using 1
    rw [← abs_neg]
    congr 1
    ring
  have hA : 0<3*Real.sqrt 3/4 := by positivity
  refine ⟨?_,?_⟩
  · simpa only [R,V,abs_neg] using moving_rectangle_uniform_sign_bound R V _ _ _ _
      (3*Real.sqrt 3/4) (27/4) hA (by norm_num) hU'
  have hV : ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,
      ∀ rho∈uIcc (r n a.succ) (r n b.succ),∀ v∈uIcc (theta n a.succ) (theta n b.succ),
      |V n rho v-(27/4 : ℝ)|<eta := by
    intro eta heta
    filter_upwards [hU' eta heta] with n hn
    exact fun rho hrho v hv => (hn rho hrho v hv).2
  have hfull := normalized_complete_upper_triple_nested_scale_complete eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt clusterCenter htriple a b c hab hca hcb hpair
  have hnu (n : ℕ) : 0<mu n 1+mu n 2+mu n 3 := by
    have h1 := (hm n).1 1
    have h2 := (hm n).1 2
    have h3 := (hm n).1 3
    linarith
  have hscaledXi : Tendsto (fun n => (mu n a.succ+mu n b.succ)/
      tripleHighDiameter (satellitesRelative (x n))^3) atTop (nhds (0 : ℝ)) := by
    convert! hfull.2.1.mul hfull.2.2.1 using 1
    · funext n
      field_simp [ne_of_gt (hnu n)]
    · norm_num
  have hsum (n : ℕ) : mu n 1+mu n 2+mu n 3=mu n a.succ+mu n b.succ+mu n c.succ := by
    fin_cases a <;> fin_cases b <;> fin_cases c
    all_goals simp_all
    all_goals ring
  have hmc : Tendsto (fun n => mu n c.succ/tripleHighDiameter (satellitesRelative (x n))^3)
      atTop (nhds (9/4 : ℝ)) := by
    convert! hfull.2.2.1.sub hscaledXi using 1
    · funext n
      rw [← sub_div]
      congr 1
      linarith [hsum n]
    · norm_num
  have hcenter : Tendsto (fun n => (9/4 : ℝ)+2*mu n c.succ/
      tripleHighDiameter (satellitesRelative (x n))^3) atTop (nhds (27/4 : ℝ)) := by
    convert! (hmc.const_mul 2).const_add (9/4) using 1
    · funext n; ring
    · norm_num
  exact moving_rectangle_uniform_change_center V _ _ _ _ _ (27/4) hV hcenter

end DominantFiveBody
