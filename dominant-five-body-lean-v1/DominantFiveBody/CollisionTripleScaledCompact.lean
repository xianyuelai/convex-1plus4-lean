import DominantFiveBody.CollisionTripleScaledGroups

/-! # The original compact scaled-position extraction for a lower triple -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1200000

theorem lower_triple_scaled_positions_compact_subsequence
    (q : ℕ → SatelliteConfiguration) (hcf : ∀ n,RelativeCollisionFree (q n)) :
    ∃ (phi : ℕ → ℕ) (z : Satellite → Plane),StrictMono phi ∧
      (∀ i : TripleLabel,Tendsto (fun n =>
        (tripleLowDiameter (q (phi n)))⁻¹ • (q (phi n) i.castSucc-q (phi n) 0)) atTop (nhds (z i.castSucc))) ∧
      z 0=0 ∧ ((z 0≠z 1) ∨ (z 0≠z 2) ∨ (z 1≠z 2)) := by
  classical
  let d := fun n => tripleLowDiameter (q n)
  have hd (n : ℕ) : 0<d n := tripleLowDiameter_pos _ (hcf n)
  let U : ℕ → Satellite → Plane := fun n i => if i=3 then 0 else (d n)⁻¹ • (q n i-q n 0)
  have hlowNe (i : TripleLabel) : i.castSucc≠(3 : Satellite) := by fin_cases i <;> decide
  have hnorm (n : ℕ) (i : TripleLabel) : ‖(d n)⁻¹ • (q n i.castSucc-q n 0)‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd n)]
    have hb := tripleLowDiameter_bound (q n) i 0
    have hrew : (0 : TripleLabel).castSucc=(0 : Satellite) := rfl
    rw [hrew] at hb
    apply (inv_mul_le_iff₀ (hd n)).mpr
    simpa only [satelliteDistance,d,mul_one] using hb
  have hclosed (n : ℕ) : U n∈Metric.closedBall (0 : Satellite → Plane) 1 := by
    rw [Metric.mem_closedBall,dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ)≤1)).mpr
    intro i
    by_cases hip : i=3
    · simp only [U,hip,ite_true,norm_zero];norm_num
    · have hi := i.isLt
      have hn : i.val≠3 := by intro he;apply hip;apply Fin.ext;exact he
      let j : TripleLabel := ⟨i.val,by omega⟩
      have hj : j.castSucc=i := by apply Fin.ext;rfl
      simpa only [U,if_neg hip,hj] using hnorm n j
  obtain ⟨z,_,phi,hphi,hlim⟩ := (isCompact_closedBall (0 : Satellite → Plane) 1).tendsto_subseq hclosed
  have hz (i : TripleLabel) : Tendsto (fun n => (d (phi n))⁻¹ •
      (q (phi n) i.castSucc-q (phi n) 0)) atTop (nhds (z i.castSucc)) := by
    simpa only [Function.comp_def,U,if_neg (hlowNe i)] using (continuous_apply i.castSucc).continuousAt.tendsto.comp hlim
  have hz0 : z 0=0 := by
    have ht := hz 0
    simp only [show (0 : TripleLabel).castSucc=(0 : Satellite) from rfl,sub_self,smul_zero] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hdist (i j : TripleLabel) : Tendsto (fun n => satelliteDistance (q (phi n)) i.castSucc j.castSucc/d (phi n))
      atTop (nhds ‖z i.castSucc-z j.castSucc‖) := by
    have ht := (hz i).sub (hz j)
    have hv : Tendsto (fun n => (d (phi n))⁻¹ • (q (phi n) i.castSucc-q (phi n) j.castSucc))
        atTop (nhds (z i.castSucc-z j.castSucc)) := by
      convert! ht using 1
      funext n;module
    convert! hv.norm using 1
    funext n
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd (phi n))]
    simp only [satelliteDistance,div_eq_mul_inv,mul_comm]
  have hmax := (hdist 0 1).max ((hdist 0 2).max (hdist 1 2))
  have hmaxEq : max ‖z 0-z 1‖ (max ‖z 0-z 2‖ ‖z 1-z 2‖)=1 := by
    have ht : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
        (nhds (max ‖z 0-z 1‖ (max ‖z 0-z 2‖ ‖z 1-z 2‖))) := by
      convert! hmax using 1
      funext n
      rw [max_div_div_right (hd (phi n)).le,max_div_div_right (hd (phi n)).le]
      simp only [satelliteDistance]
      change 1=max ‖q (phi n) 0-q (phi n) 1‖
        (max ‖q (phi n) 0-q (phi n) 2‖ ‖q (phi n) 1-q (phi n) 2‖)/d (phi n)
      rw [norm_sub_rev (q (phi n) 0) (q (phi n) 1),
        norm_sub_rev (q (phi n) 0) (q (phi n) 2),norm_sub_rev (q (phi n) 1) (q (phi n) 2)]
      change 1=d (phi n)/d (phi n)
      rw [div_self (ne_of_gt (hd (phi n)))]
    exact tendsto_nhds_unique ht tendsto_const_nhds
  refine ⟨phi,z,hphi,hz,hz0,?_⟩
  by_contra he
  push Not at he
  simp only [he.1,he.2.2,sub_self,norm_zero,max_self] at hmaxEq
  norm_num at hmaxEq

end DominantFiveBody
