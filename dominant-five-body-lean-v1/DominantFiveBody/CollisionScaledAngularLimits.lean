import DominantFiveBody.CollisionScaledAngularGroups

/-! # Polar angle limits and original current angular group cancellation -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1800000

theorem polar_scaled_angle_difference_limit
    (ra va rb vb d : ℕ → ℝ) (psi : ℝ) (u : Plane)
    (hra : Tendsto ra atTop (𝓝 1)) (hrb : Tendsto rb atTop (𝓝 1))
    (hva : Tendsto va atTop (𝓝 psi)) (hvb : Tendsto vb atTop (𝓝 psi))
    (hdir : Tendsto (fun n => (d n)⁻¹ •
      (polarPoint (rb n) (vb n)-polarPoint (ra n) (va n))) atTop (𝓝 u)) :
    Tendsto (fun n => (vb n-va n)/d n) atTop
      (𝓝 (inner ℝ u (quarterTurn (polarPoint 1 psi)))) := by
  let mid := fun n => (va n+vb n)/2
  have hmid : Tendsto mid atTop (𝓝 psi) := by
    convert! (hva.add hvb).div_const 2 using 1
    ring
  have he := ((polarPoint_contDiff ∞).continuous.tendsto (1,psi)).comp
    (tendsto_const_nhds.prodMk_nhds hmid)
  have hJ := quarterTurnLinear.toContinuousLinearMap.continuous.tendsto _ |>.comp he
  change Tendsto (fun n => quarterTurn (polarPoint 1 (mid n))) atTop
    (𝓝 (quarterTurn (polarPoint 1 psi))) at hJ
  have hi := hdir.inner (𝕜 := ℝ) hJ
  have hsinc : Tendsto (fun n => Real.sinc ((vb n-va n)/2)) atTop (𝓝 1) := by
    simpa only [Function.comp_def,sub_self,zero_div,Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp ((hvb.sub hva).div_const 2)
  let C := fun n => ((rb n+ra n)/2)*Real.sinc ((vb n-va n)/2)
  have hC : Tendsto C atTop (𝓝 1) := by
    convert! (((hrb.add hra).div_const 2).mul hsinc) using 1
    norm_num
  have hquot := hi.div hC (by norm_num : (1 : ℝ)≠0)
  simp only [div_one] at hquot
  apply hquot.congr'
  filter_upwards [hC.eventually_ne (by norm_num : (1 : ℝ)≠0)] with n hn
  change inner ℝ ((d n)⁻¹ • (polarPoint (rb n) (vb n)-polarPoint (ra n) (va n)))
    (quarterTurn (polarPoint 1 (mid n)))/C n=(vb n-va n)/d n
  apply (div_eq_iff hn).mpr
  dsimp only [C,mid]
  simp only [real_inner_smul_left,inner_sub_left,polarPoint_inner_rotation]
  rw [show vb n-(va n+vb n)/2=(vb n-va n)/2 by ring,
    show va n-(va n+vb n)/2= -((vb n-va n)/2) by ring,Real.sin_neg,
    ← sinc_mul_argument ((vb n-va n)/2)]
  ring

theorem actual_group_near_angular_scaled_tendsto_zero
    (eps : ℕ → ℝ) (mu r theta : ℕ → Satellite → ℝ) (d : ℕ → ℝ)
    (hm : ∀ n,PositiveRatio (mu n)) (heps : ∀ n,0≤eps n)
    (S : Finset Satellite) (hS : S.Nonempty) (p : Satellite)
    (eta : ℝ) (heta : 0<eta) (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (𝓝 0))
    (hnu : Tendsto (fun n => (∑ j∈Finset.univ.erase p,mu n j)/d n^3) atTop (𝓝 0))
    (hr : ∀ n i,0<r n i)
    (hrbound : ∀ᶠ n in atTop,∀ i∈Finset.univ.erase p,r n i≤2)
    (hSsub : S⊆Finset.univ.erase p)
    (hgap : ∀ᶠ n in atTop,∀ i∈S,∀ j∈Sᶜ.erase p,|theta n j-theta n i|≤2*d n)
    (hsep : ∀ᶠ n in atTop,∀ i∈S,∀ j∈Sᶜ.erase p,
      eta*d n≤satelliteDistance (polarSatellites (r n) (theta n)) i j) :
    Tendsto (fun n => satelliteGroupScalarAverage (mu n) S
      (fun i => ∑ j∈Sᶜ.erase p,mu n j*fullAngularMatrix (eps n) (r n) (theta n) i j)/d n)
      atTop (𝓝 0) := by
  have hupper : Tendsto (fun n => ((8/eta^3)+8*d n^3)*
      ((∑ j∈Finset.univ.erase p,mu n j)/d n^3)) atTop (𝓝 0) := by
    convert! (((hdt.pow 3).const_mul 8).const_add (8/eta^3)).mul hnu using 1
    simp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun n => norm_nonneg _)
  · filter_upwards [hrbound,hgap,hsep] with n hnR hnGap hnSep
    have hdn := hd n
    rw [Real.norm_eq_abs]
    apply current_group_near_angular_scaled_abs_bound (mu n) (hm n)
      (fullAngularMatrix (eps n) (r n) (theta n)) S hS p (d n) ((8/eta^3)+8*d n^3) (hd n) (by positivity)
    intro i hi j hj
    have hjE : j∈Finset.univ.erase p := Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hj).1,Finset.mem_univ _⟩
    exact fullAngularMatrix_cross_distance_abs_bound (eps n) (r n) (theta n) i j
      (heps n) (hr n i) (hr n j) (hnR i (hSsub hi)) (hnR j hjE)
      (d n) eta (hd n) heta (hnGap i hi j hj) (hnSep i hi j hj)

theorem actual_current_angular_group_representative_scaled_limit
    (eps : ℕ → ℝ) (mu r theta : ℕ → Satellite → ℝ) (d : ℕ → ℝ)
    (hm : ∀ n,PositiveRatio (mu n)) (hd : ∀ n,0<d n)
    (hroot : ∀ n i,angularResidual (eps n) (mu n) (r n) (theta n) i=0)
    (S : Finset Satellite) (hS : S.Nonempty) (p : Satellite) (hp : p∉S)
    (a : Satellite) (hmp : Tendsto (fun n => mu n p) atTop (𝓝 1))
    (hnear : Tendsto (fun n => satelliteGroupScalarAverage (mu n) S
      (fun i => ∑ j∈Sᶜ.erase p,mu n j*fullAngularMatrix (eps n) (r n) (theta n) i j)/d n)
      atTop (𝓝 0))
    (hsmall : ∀ i∈S,Tendsto (fun n =>
      (physicalSourceFullAngularField (eps n) (r n p) (theta n p) (r n i) (theta n i)-
        physicalSourceFullAngularField (eps n) (r n p) (theta n p) (r n a) (theta n a))/d n)
      atTop (𝓝 0)) :
    Tendsto (fun n => physicalSourceFullAngularField (eps n) (r n p) (theta n p) (r n a) (theta n a)/d n)
      atTop (𝓝 0) := by
  let J := fun n i => physicalSourceFullAngularField (eps n) (r n p) (theta n p) (r n i) (theta n i)
  have herr := current_positive_finset_weighted_average_tendsto S hS mu
    (fun n i => (J n i-J n a)/d n) 0 (fun n i _ => (hm n).1 i) hsmall
  have havg : Tendsto (fun n => satelliteGroupScalarAverage (mu n) S (J n)/d n) atTop (𝓝 0) := by
    have ht := hnear.neg.div hmp (by norm_num : (1 : ℝ)≠0)
    simp only [neg_zero,zero_div] at ht
    convert! ht using 1
    funext n
    change satelliteGroupScalarAverage (mu n) S (J n)/d n=
      -(satelliteGroupScalarAverage (mu n) S
        (fun i => ∑ j∈Sᶜ.erase p,mu n j*fullAngularMatrix (eps n) (r n) (theta n) i j)/d n)/mu n p
    have he := physical_current_group_full_angular_average (eps n) (mu n) (r n) (theta n)
      (hm n) (hroot n) S hS p hp
    dsimp only [J]
    field_simp [ne_of_gt (hd n),ne_of_gt ((hm n).1 p)]
    linear_combination he
  have ht := havg.sub herr
  simp only [sub_self] at ht
  apply ht.congr
  intro n
  change satelliteGroupScalarAverage (mu n) S (J n)/d n-
    satelliteGroupScalarAverage (mu n) S (fun i => (J n i-J n a)/d n)=J n a/d n
  rw [satelliteGroupScalarAverage_difference_div _ _ (fun i _ => (hm n).1 i) hS]
  ring

end DominantFiveBody
