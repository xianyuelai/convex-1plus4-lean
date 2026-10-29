import DominantFiveBody.CollisionNestedPairSecant

/-! # Precise real two-level mass scales for a nested triple -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody

theorem physical_nested_pair_mass_cube_limit_of_tangential
    (mu r theta : ℕ → Satellite → ℝ) (d : ℕ → ℝ) (a b c p : Satellite)
    (hab : a≠b) (hcp : c≠p) (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b)
    (hcf : ∀ n,RelativeCollisionFree (polarSatellites (r n) (theta n)))
    (hm : ∀ n i,0<mu n i) (hr : ∀ n i,0<r n i)
    (hQ : ∀ n i,tangentialResidual (mu n) (r n) (theta n) i=0)
    (hrt : ∀ i,Tendsto (fun n => r n i) atTop (nhds 1))
    (hmat : Tendsto (fun n => mu n a) atTop (nhds 0))
    (hmbt : Tendsto (fun n => mu n b) atTop (nhds 0))
    (psi angle0 : ℝ) (htha : Tendsto (fun n => theta n a) atTop (nhds psi))
    (hthb : Tendsto (fun n => theta n b) atTop (nhds psi))
    (hthc : Tendsto (fun n => theta n c) atTop (nhds psi))
    (hthp : Tendsto (fun n => theta n p) atTop (nhds angle0))
    (hne : angle0≠psi) (hpi : |angle0-psi|<Real.pi)
    (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (nhds 0)) (U : Plane)
    (hU : ‖U‖=1) (hUr : inner ℝ U (polarPoint 1 psi)=0) (L : ℝ)
    (hsource : Tendsto (fun n => (d n)⁻¹ •
      (polarPoint (r n c) (theta n c)-polarPoint (r n a) (theta n a))) atTop (nhds U))
    (hsmall : Tendsto (fun n => satelliteDistance (polarSatellites (r n) (theta n)) a b/d n) atTop (nhds 0))
    (hv : Tendsto (fun n => physicalPairDirection (polarSatellites (r n) (theta n)) a b)
      atTop (nhds (quarterTurn (polarPoint 1 psi))))
    (hmd : Tendsto (fun n => mu n c/d n^3) atTop (nhds L))
    (hmp : Tendsto (fun n => mu n p) atTop (nhds 1))
    (horder : ∀ n,0<theta n b-theta n a ∧ theta n b-theta n a<Real.pi)
    (hgd : Tendsto (fun n => (theta n b-theta n a)/
      satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds 1))
    (hrd : Tendsto (fun n => (r n b-r n a)/
      satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds 0)) :
    Tendsto (fun n => (mu n a+mu n b)/satelliteDistance (polarSatellites (r n) (theta n)) a b^3)
      atTop (nhds (Coorbital.kappa |psi-angle0|+2*L)) := by
  let s : ℕ → ℝ := fun n => satelliteDistance (polarSatellites (r n) (theta n)) a b
  have hs (n : ℕ) : 0<s n := norm_pos_iff.mpr (sub_ne_zero.mpr ((hcf n).2 a b hab))
  have hca := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
  have hcb := (Finset.mem_erase.mp hc).1
  have hnear0 := physical_pair_near_angular_secant_limit (fun n => mu n c) d r theta a b c hab hca hcb
    hcf (fun n => hr n c) (fun n => hr n b) (hrt c) (hrt b) psi htha hthb hthc hd hdt U
    (quarterTurn (polarPoint 1 psi)) hU hUr L hsource hsmall hv hmd
  have hJJ : inner ℝ (quarterTurn (polarPoint 1 psi)) (quarterTurn (polarPoint 1 psi))=1 := by
    rw [quarterTurn_inner_quarterTurn,polarPoint_inner_radial]
    simp
  have hnear : Tendsto (fun n => mu n c*(physicalSourceAngularField (r n c) (theta n c) (r n b) (theta n b)-
      physicalSourceAngularField (r n c) (theta n c) (r n a) (theta n a))/s n) atTop (nhds (2*L)) := by
    simpa only [hJJ,mul_one] using hnear0
  have hfar0 := physicalSourceAngularField_moving_secant_limit _ _ _ _ _ _ s angle0 psi
    (hrt p) hthp (hrt a) (hrt b) htha hthb hs hrd hgd hne hpi
  have hfar := hmp.mul hfar0
  have hHt : Tendsto (fun n => (physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
      physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a))/s n)
      atTop (nhds (Coorbital.kappa |psi-angle0|+2*L)) := by
    convert! hnear.add hfar using 1
    · funext n
      rw [physicalPairExteriorAngularField_eq_selected_sources _ _ _ a b c p hab hcp hc hp,
        physicalPairExteriorAngularField_eq_selected_sources _ _ _ a b c p hab hcp hc hp]
      ring
    · ring
  apply pair_mass_cube_tendsto_of_angular_difference mu r theta a b s hm hr hs horder hmat hmbt
    (hrt a) (hrt b) (by simpa only [sub_self] using hthb.sub htha) hgd _ _ hHt
  exact fun n => physical_pair_tangential_difference (mu n) (r n) (theta n) a b hab (hr n) (hQ n)

/-- The small-pair cube scale first makes its macro contribution vanish.
The exact macro cube limit then determines the extracted third-mass limit,
and the micro cube coefficient becomes three times the macro coefficient. -/
theorem nested_precise_two_cube_limits_of_selected
    (xi mc s d : ℕ → ℝ) (D L : ℝ) (hs : ∀ n,0<s n) (hd : ∀ n,0<d n)
    (hsmall : Tendsto (fun n => s n/d n) atTop (nhds 0))
    (hmacro : Tendsto (fun n => (xi n+mc n)/d n^3) atTop (nhds D))
    (hinner : Tendsto (fun n => xi n/s n^3) atTop (nhds (D+2*L)))
    (hmc : Tendsto (fun n => mc n/d n^3) atTop (nhds L)) :
    L=D ∧ Tendsto (fun n => xi n/d n^3) atTop (nhds 0) ∧
      Tendsto (fun n => mc n/d n^3) atTop (nhds D) ∧
      Tendsto (fun n => xi n/s n^3) atTop (nhds (3*D)) := by
  have hx : Tendsto (fun n => xi n/d n^3) atTop (nhds 0) := by
    convert! hinner.mul (hsmall.pow 3) using 1
    · funext n
      field_simp [ne_of_gt (hs n),ne_of_gt (hd n)]
    · ring
  have hmct : Tendsto (fun n => mc n/d n^3) atTop (nhds D) := by
    convert! hmacro.sub hx using 1
    · funext n; ring
    · ring
  have hLD := tendsto_nhds_unique hmc hmct
  refine ⟨hLD,hx,hmct,?_⟩
  convert! hinner using 1
  rw [hLD]
  ring

end DominantFiveBody
