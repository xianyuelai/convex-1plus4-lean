from pathlib import Path
root=Path(__file__).resolve().parents[1]
old=(root/'DominantFiveBody/CollisionUpperRectangleGeometry.lean').read_text(encoding='utf-8')
signature=old[old.index('theorem normalized_complete_upper_triple_nested_rectangle_near_geometry_uniform'):old.index('    ∀ eta : ℝ')].replace('normalized_complete_upper_triple_nested_rectangle_near_geometry_uniform','normalized_complete_upper_triple_nested_segment_scaled_geometry_uniform')
body=old[old.index('  have hrev'):old.index('  intro eta heta')].replace('normalized_complete_lower_triple_nested_rectangle_near_geometry_uniform','normalized_complete_lower_triple_nested_segment_scaled_geometry_uniform')
result=r'''    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,∀ t∈Icc (0 : ℝ) 1,
      ‖(tripleHighDiameter (satellitesRelative (x n)))⁻¹ •
        (satellitesRelative (x n) c.succ-
          physicalPairSegmentPoint (satellitesRelative (x n) a.succ)
            (satellitesRelative (x n) b.succ) t)-
        (lowNestedOrientation a c) • quarterTurn (polarPoint 1 (theta0 3))‖<eta := by
'''
helper=r'''
theorem planeReflection_quarterTurn (v : Plane) :
    planeReflection (quarterTurn v)= -quarterTurn (planeReflection v) := by
  ext i
  fin_cases i <;> simp [planeReflection,quarterTurn,point,PiLp.neg_apply]

theorem planeReflection_physicalPairSegmentPoint (qa qb : Plane) (t : ℝ) :
    planeReflection (physicalPairSegmentPoint qa qb t)=
      physicalPairSegmentPoint (planeReflection qa) (planeReflection qb) t := by
  simp only [physicalPairSegmentPoint,map_add,map_smul]

theorem physicalPairSegmentPoint_reverse (qa qb : Plane) (t : ℝ) :
    physicalPairSegmentPoint qb qa (1-t)=physicalPairSegmentPoint qa qb t := by
  unfold physicalPairSegmentPoint
  module
'''
tail=r'''
  intro eta heta
  filter_upwards [hlow eta heta] with n hn
  intro t ht
  have ht' : 1-t∈Icc (0 : ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hh := hn (1-t) ht'
  rw [tripleLowDiameter_mirror] at hh
  simp only [mirrorConfiguration_relative,hrev,Fin.rev_zero,
    homega] at hh
  rw [show (Fin.last 3 : Satellite)=(3 : Satellite) from rfl] at hh
  have he :
      (tripleHighDiameter (satellitesRelative (x n)))⁻¹ •
        (planeReflection (satellitesRelative (x n) c.succ)-
          physicalPairSegmentPoint (planeReflection (satellitesRelative (x n) b.succ))
            (planeReflection (satellitesRelative (x n) a.succ)) (1-t))-
        (-lowNestedOrientation a c) • quarterTurn (polarPoint 1 (-theta0 3)) =
      planeReflection ((tripleHighDiameter (satellitesRelative (x n)))⁻¹ •
        (satellitesRelative (x n) c.succ-
          physicalPairSegmentPoint (satellitesRelative (x n) a.succ)
            (satellitesRelative (x n) b.succ) t)-
        (lowNestedOrientation a c) • quarterTurn (polarPoint 1 (theta0 3))) := by
    rw [←planeReflection_physicalPairSegmentPoint,physicalPairSegmentPoint_reverse]
    simp only [map_sub,map_smul,planeReflection_quarterTurn,planeReflection_polar]
    module
  rw [he,planeReflection.norm_map] at hh
  exact hh

end DominantFiveBody
'''
(root/'DominantFiveBody/CollisionUpperSegmentVectors.lean').write_text(
    'import DominantFiveBody.CollisionUpperRectangleGeometry\nimport DominantFiveBody.CollisionNestedSegmentVectors\n\nnoncomputable section\nopen scoped BigOperators ContDiff\nopen Filter Set Topology\nnamespace DominantFiveBody\nset_option maxHeartbeats 1800000\n'+helper+'\n'+signature+result+body+tail,encoding='utf-8')
