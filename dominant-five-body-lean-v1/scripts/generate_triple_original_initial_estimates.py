from pathlib import Path

root=Path(__file__).resolve().parents[1]
original=(root/'DominantFiveBody/CollisionTripleInitialScale.lean').read_text(encoding='utf-8')
signature=original[original.index('theorem normalized_complete_lower_triple_initial_scales'):original.index('    ∃ K C : ℝ')]
signature=signature.replace('normalized_complete_lower_triple_initial_scales','normalized_complete_lower_triple_original_initial_estimates')
body=original[original.index('  classical\n',original.index('theorem normalized_complete_lower_triple_initial_scales')):original.index('  refine ⟨?_, ?_, ?_⟩')]
body=body.replace('  refine ⟨K, 16 * B * K, hK, by positivity, ?_⟩','  refine ⟨k, A, 16 * B * K, hk, hA, by positivity, ?_⟩')

helpers=r'''
theorem physical_triple_extreme_source_signs (eps : ℝ) (mu r theta : Satellite → ℝ)
    (hm : PositiveRatio mu)
    (hgap01 : 0 < theta 1-theta 0) (hgap12 : 0 < theta 2-theta 1)
    (hco01 : 0 < tripleAngularCoefficient eps r theta 0 1)
    (hco02 : 0 < tripleAngularCoefficient eps r theta 0 2)
    (hco12 : 0 < tripleAngularCoefficient eps r theta 1 2)
    (hroot : ∀ i,angularResidual eps mu r theta i=0) :
    physicalSourceFullAngularField eps (r 3) (theta 3) (r 0) (theta 0)<0 ∧
      0<physicalSourceFullAngularField eps (r 3) (theta 3) (r 2) (theta 2) := by
  have h0 := hroot 0
  have h2 := hroot 2
  rw [angularResidual_eq_full_matrix_sum,Fin.sum_univ_four] at h0 h2
  simp only [fullAngularMatrix_self,mul_zero,zero_add,add_zero] at h0 h2
  rw [fullAngularMatrix_reverse eps r theta 0 2,fullAngularMatrix_reverse eps r theta 1 2] at h2
  simp only [fullAngularMatrix_eq_physicalSourceFullAngularField] at h0 h2
  have h01 := fullAngularMatrix_eq_gap_coefficient eps r theta 0 1
  have h02 := fullAngularMatrix_eq_gap_coefficient eps r theta 0 2
  have h12 := fullAngularMatrix_eq_gap_coefficient eps r theta 1 2
  simp only [fullAngularMatrix_eq_physicalSourceFullAngularField] at h01 h02 h12
  rw [h01,h02] at h0
  rw [h02,h12] at h2
  have hw : 0<theta 2-theta 0 := by linarith
  have hp0 : 0<mu 1*((theta 1-theta 0)*tripleAngularCoefficient eps r theta 0 1)+
      mu 2*((theta 2-theta 0)*tripleAngularCoefficient eps r theta 0 2) :=
    add_pos (mul_pos (hm.1 1) (mul_pos hgap01 hco01)) (mul_pos (hm.1 2) (mul_pos hw hco02))
  have hp2 : 0<mu 0*((theta 2-theta 0)*tripleAngularCoefficient eps r theta 0 2)+
      mu 1*((theta 2-theta 1)*tripleAngularCoefficient eps r theta 1 2) :=
    add_pos (mul_pos (hm.1 0) (mul_pos hw hco02)) (mul_pos (hm.1 1) (mul_pos hgap12 hco12))
  constructor <;> nlinarith [hm.1 3]

theorem physical_triple_extreme_mass_width_bound (eps d : ℝ) (mu r theta : Satellite → ℝ)
    (hm : PositiveRatio mu) (hgap01 : 0<theta 1-theta 0) (hgap12 : 0<theta 2-theta 1)
    (hco01 : 1/(16*d^3)≤tripleAngularCoefficient eps r theta 0 1)
    (hco02 : 1/(16*d^3)≤tripleAngularCoefficient eps r theta 0 2)
    (hco12 : 1/(16*d^3)≤tripleAngularCoefficient eps r theta 1 2)
    (hroot : ∀ i,angularResidual eps mu r theta i=0) :
    (mu 0+mu 1+mu 2)*(theta 2-theta 0)/d^3≤
      16*mu 3*(physicalSourceFullAngularField eps (r 3) (theta 3) (r 2) (theta 2)-
        physicalSourceFullAngularField eps (r 3) (theta 3) (r 0) (theta 0)) := by
  have hwidth : 0<theta 2-theta 0 := by linarith
  have hlow01 := mul_le_mul_of_nonneg_left hco01 hgap01.le
  have hlow02 := mul_le_mul_of_nonneg_left hco02 hwidth.le
  have hlow12 := mul_le_mul_of_nonneg_left hco12 hgap12.le
  have hlow0 := mul_le_mul_of_nonneg_left hlow02 (add_pos (hm.1 0) (hm.1 2)).le
  have hlow1 := mul_le_mul_of_nonneg_left (add_le_add hlow01 hlow12) (hm.1 1).le
  have hlow : (mu 0+mu 1+mu 2)*(theta 2-theta 0)/(16*d^3)≤
      mu 3*(physicalSourceFullAngularField eps (r 3) (theta 3) (r 2) (theta 2)-
        physicalSourceFullAngularField eps (r 3) (theta 3) (r 0) (theta 0)) := by
    rw [physical_triple_extreme_angular_identity eps mu r theta hroot]
    convert! add_le_add hlow0 hlow1 using 1 <;> ring
  have hscaled := mul_le_mul_of_nonneg_left hlow (show (0:ℝ)≤16 by norm_num)
  convert! hscaled using 1 <;> ring
'''

result=r'''    ∃ k A C : ℝ,0<k ∧ 0<A ∧ 0<C ∧ ∀ᶠ n in atTop,
      physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0)<0 ∧
      0<physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2) ∧
      (r n 0≤r n 2 →
        0<physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2)-
            physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0) ∧
        physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2)-
            physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0)≤
          -k*(r n 2-r n 0)+A*(theta n 2-theta n 0)) ∧
      (mu n 0+mu n 1+mu n 2)*(theta n 2-theta n 0)/
          tripleLowDiameter (satellitesRelative (x n))^3≤
        16*mu n 3*(physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2)-
          physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0)) ∧
      16*mu n 3*(physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 2) (theta n 2)-
          physicalSourceFullAngularField (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0))≤
        C*mu n 3*(theta n 2-theta n 0) := by
'''
tail=r'''
  have hc01 : 0<tripleAngularCoefficient (eps n) (r n) (theta n) 0 1 :=
    (by positivity : 0<1/(16*d n^3)).trans_le hco01
  have hc02 : 0<tripleAngularCoefficient (eps n) (r n) (theta n) 0 2 :=
    (by positivity : 0<1/(16*d n^3)).trans_le hco02
  have hc12 : 0<tripleAngularCoefficient (eps n) (r n) (theta n) 1 2 :=
    (by positivity : 0<1/(16*d n^3)).trans_le hco12
  have hsign := physical_triple_extreme_source_signs (eps n) (mu n) (r n) (theta n)
    (hm n) h01 h12 hc01 hc02 hc12 (hroots n)
  refine ⟨hsign.1,hsign.2,?_,?_,?_⟩
  · intro hup
    refine ⟨hJpos,?_⟩
    have h := hcontrol (eps n) (r n 3) (theta n 3) (r n 0) (r n 2) (theta n 0) (theta n 2)
      (hepsN.trans_le heeta) (hsourceN.trans_le heeta) hup
      (h00.trans_le heeta) (h20.trans_le heeta) (h22.trans_le heeta)
    simpa only [abs_of_pos hW] using h
  · exact physical_triple_extreme_mass_width_bound (eps n) (d n) (mu n) (r n) (theta n)
      (hm n) h01 h12 hco01 hco02 hco12 (hroots n)
  · have hJ := (le_abs_self _).trans (hLip (eps n) (r n 3) (theta n 3) (r n 0) (theta n 0) (r n 2) (theta n 2)
      (hepsN.trans_le heLip) (hsourceN.trans_le heLip) (h00.trans_le heLip) (h22.trans_le heLip))
    rw [abs_of_pos hW] at hJ
    have hmax : max |r n 2-r n 0| (theta n 2-theta n 0)≤K*(theta n 2-theta n 0) :=
      max_le hs02 (by nlinarith)
    have hJbound := hJ.trans (mul_le_mul_of_nonneg_left hmax hB.le)
    have hm3 := (hm n).1 3
    have h := mul_le_mul_of_nonneg_left hJbound (by positivity : 0≤16*mu n 3)
    convert! h using 1
    ring

end DominantFiveBody
'''
(root/'DominantFiveBody/CollisionTripleOriginalInitialEstimates.lean').write_text(
    'import DominantFiveBody.CollisionTripleInitialScale\n\nnoncomputable section\nopen scoped BigOperators Matrix ContDiff\nopen Filter Set Topology\nnamespace DominantFiveBody\nopen Coorbital\nset_option maxHeartbeats 1800000\n'+helpers+'\n'+signature+result+body+tail,encoding='utf-8')
