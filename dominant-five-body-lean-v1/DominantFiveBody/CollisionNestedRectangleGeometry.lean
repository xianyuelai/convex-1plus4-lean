import DominantFiveBody.CollisionNestedRectangleContributions

/-! # The signed near-source geometry on the complete moving polar rectangle -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1800000

theorem physical_nested_polar_rectangle_near_geometry_uniform
    (rc vc ra va rb vb d : ℕ → ℝ) (psi omega : ℝ)
    (hrc : Tendsto rc atTop (𝓝 1)) (hra : Tendsto ra atTop (𝓝 1)) (hrb : Tendsto rb atTop (𝓝 1))
    (hvc : Tendsto vc atTop (𝓝 psi)) (hva : Tendsto va atTop (𝓝 psi)) (hvb : Tendsto vb atTop (𝓝 psi))
    (hd : ∀ n,0<d n) (homega : omega^2=1)
    (hrab : Tendsto (fun n => (rb n-ra n)/d n) atTop (𝓝 0))
    (hvab : Tendsto (fun n => (vb n-va n)/d n) atTop (𝓝 0))
    (hrac : Tendsto (fun n => (rc n-ra n)/d n) atTop (𝓝 0))
    (hvac : Tendsto (fun n => (vc n-va n)/d n) atTop (𝓝 omega)) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,∀ rho∈uIcc (ra n) (rb n),∀ v∈uIcc (va n) (vb n),
      |(vc n-v)/d n-omega|<eta ∧ |(rho-rc n)/d n|<eta ∧
      |‖polarPoint rho v-polarPoint (rc n) (vc n)‖/d n-1|<eta := by
  let S : ℕ → Set (ℝ×ℝ) := fun n => uIcc (ra n) (rb n) ×ˢ uIcc (va n) (vb n)
  let F : ℕ → (ℝ×ℝ) → ℝ×(ℝ×ℝ) := fun n z =>
    ((vc n-z.2)/d n,((z.1-rc n)/d n,‖polarPoint z.1 z.2-polarPoint (rc n) (vc n)‖/d n))
  have hseq : ∀ z : ℕ → ℝ×ℝ,(∀ n,z n∈S n) → Tendsto (fun n => F n (z n)) atTop (𝓝 (omega,(0,1))) := by
    intro z hz
    have hzR (n : ℕ) := (hz n).1
    have hzV (n : ℕ) := (hz n).2
    have hrho := between_tendsto_common_limit ra rb (fun n => (z n).1) 1 hzR hra hrb
    have hv := between_tendsto_common_limit va vb (fun n => (z n).2) psi hzV hva hvb
    have hrTarget := between_scaled_difference_tendsto_zero ra rb (fun n => (z n).1) d hd hzR hrab
    have hvTarget := between_scaled_difference_tendsto_zero va vb (fun n => (z n).2) d hd hzV hvab
    have hrd : Tendsto (fun n => ((z n).1-rc n)/d n) atTop (nhds 0) := by
      convert! hrTarget.sub hrac using 1
      · funext n; ring
      · ring
    have hgd : Tendsto (fun n => (vc n-(z n).2)/d n) atTop (nhds omega) := by
      convert! hvac.sub hvTarget using 1
      · funext n; ring
      · ring
    have hrdRev : Tendsto (fun n => (rc n-(z n).1)/d n) atTop (nhds 0) := by
      convert! hrd.neg using 1
      · funext n; ring
      · ring
    have hdisplacement := polar_scaled_displacement_tendsto (fun n => (z n).1) (fun n => (z n).2)
      rc vc d psi omega hrho hrc hv hvc hd hrdRev hgd
    have hJnorm : ‖quarterTurn (polarPoint 1 psi)‖=1 := by
      have he : ‖quarterTurn (polarPoint 1 psi)‖^2=1 := by
        rw [← real_inner_self_eq_norm_sq,quarterTurn_inner_quarterTurn,real_inner_self_eq_norm_sq,
          polarPoint_norm,abs_one]
        norm_num
      nlinarith [norm_nonneg (quarterTurn (polarPoint 1 psi))]
    have homegaAbs : |omega|=1 := by nlinarith [sq_abs omega,abs_nonneg omega]
    have hDd : Tendsto (fun n => ‖polarPoint ((z n).1) ((z n).2)-polarPoint (rc n) (vc n)‖/d n)
        atTop (nhds 1) := by
      convert! hdisplacement.norm using 1
      · funext n
        rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd n),norm_sub_rev]
        ring
      · rw [norm_smul,Real.norm_eq_abs,homegaAbs,hJnorm,mul_one]
    exact hgd.prodMk_nhds (hrd.prodMk_nhds hDd)
  have hU := limit_on_moving_sets_of_all_selections S (fun n => (ra n,va n))
    (fun _ => ⟨left_mem_uIcc,left_mem_uIcc⟩) F _ hseq
  intro eta heta
  filter_upwards [hU eta heta] with n hn
  intro rho hr v hv
  simpa only [F,Prod.dist_eq,Real.dist_eq,max_lt_iff,sub_zero] using hn (rho,v) ⟨hr,hv⟩

theorem normalized_complete_lower_triple_nested_rectangle_near_geometry_uniform
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
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (a b c : TripleLabel) (hab : a<b) (hca : c≠a) (hcb : c≠b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc/
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,
      ∀ rho∈uIcc (r n a.castSucc) (r n b.castSucc),∀ v∈uIcc (theta n a.castSucc) (theta n b.castSucc),
      |(theta n c.castSucc-v)/tripleLowDiameter (satellitesRelative (x n))-lowNestedOrientation a c|<eta ∧
      |(rho-r n c.castSucc)/tripleLowDiameter (satellitesRelative (x n))|<eta ∧
      |‖polarPoint rho v-polarPoint (r n c.castSucc) (theta n c.castSucc)‖/
        tripleLowDiameter (satellitesRelative (x n))-1|<eta := by
  have hdir := normalized_complete_lower_triple_nested_directions eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  have hrad := normalized_complete_lower_triple_nested_radial_limits eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab.ne hca hcb hpair
  obtain ⟨hrt,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (𝓝 1) :=
    (continuous_apply i).continuousAt.tendsto.comp hrt
  have htat (i : TripleLabel) : Tendsto (fun n => theta n i.castSucc) atTop (𝓝 (theta0 0)) := by
    have he := complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple i 0
    simpa only [Function.comp_def,he,show (0 : TripleLabel).castSucc=(0 : Satellite) from rfl] using
      (continuous_apply i.castSucc).continuousAt.tendsto.comp htt
  have homega : (lowNestedOrientation a c)^2=1 := by
    unfold lowNestedOrientation
    split_ifs <;> norm_num
  exact physical_nested_polar_rectangle_near_geometry_uniform
    (fun n => r n c.castSucc) (fun n => theta n c.castSucc)
    (fun n => r n a.castSucc) (fun n => theta n a.castSucc)
    (fun n => r n b.castSucc) (fun n => theta n b.castSucc)
    (fun n => tripleLowDiameter (satellitesRelative (x n))) (theta0 0) (lowNestedOrientation a c)
    (hrat c.castSucc) (hrat a.castSucc) (hrat b.castSucc) (htat c) (htat a) (htat b)
    (fun n => tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1)) homega
    (hrad a b) hdir.2.1 (hrad a c) (hdir.2.2.1 a (by simp))

end DominantFiveBody
