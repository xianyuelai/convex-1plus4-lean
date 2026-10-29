import DominantFiveBody.SingleScaleKernel

/-! # Endpoint-safe divided differences of the actual exterior Newton field

These explicit rationalized formulas provide the signed-scale extension of
the exterior target differences in §5. Source and target variables are all
retained, so subsequent derivatives include their full parameter dependence.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

def newtonTargetField (source target : Plane) : Plane :=
  (‖source-target‖^3)⁻¹ • (source-target)

def dividedInverseCube (source qa qb direction : Plane) : ℝ :=
  -(inner ℝ direction (qa+qb-(2 : ℝ) • source))*(‖source-qa‖^2+‖source-qa‖*‖source-qb‖+‖source-qb‖^2)/
    ((‖source-qa‖+‖source-qb‖)*‖source-qa‖^3*‖source-qb‖^3)

def dividedNewtonTargetField (source qa qb direction : Plane) : Plane :=
  dividedInverseCube source qa qb direction • (source-qb)-
    (‖source-qa‖^3)⁻¹ • direction

theorem newtonSquaredDistance_difference (source qa qb : Plane) :
    ‖source-qb‖^2-‖source-qa‖^2=inner ℝ (qb-qa) (qa+qb-(2 : ℝ) • source) := by
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [inner_sub_left, inner_sub_right, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm qa qb, real_inner_comm source qa, real_inner_comm source qb]
  ring

/-- The difference quotient is rationalized before any t is set to zero. -/
theorem dividedInverseCube_eq (source qa qb direction : Plane) (t : ℝ) (ht : t≠0)
    (ha : source≠qa) (hb : source≠qb) (hgap : qb-qa=t • direction) :
    dividedInverseCube source qa qb direction =
      ((‖source-qb‖^3)⁻¹-(‖source-qa‖^3)⁻¹)/t := by
  have hda : 0<‖source-qa‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ha)
  have hdb : 0<‖source-qb‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
  have hsum : ‖source-qa‖+‖source-qb‖≠0 := ne_of_gt (add_pos hda hdb)
  have hsq := newtonSquaredDistance_difference source qa qb
  rw [hgap, real_inner_smul_left] at hsq
  have hfactor : (‖source-qb‖-‖source-qa‖)*(‖source-qa‖+‖source-qb‖)=
      t*inner ℝ direction (qa+qb-(2 : ℝ) • source) := by nlinarith [hsq]
  unfold dividedInverseCube
  field_simp [ht, ne_of_gt hda, ne_of_gt hdb, hsum]
  nlinarith [congrArg (fun a : ℝ => a*(‖source-qa‖^2+‖source-qa‖*‖source-qb‖+‖source-qb‖^2)) hfactor]

theorem dividedNewtonTargetField_eq (source qa qb direction : Plane) (t : ℝ)
    (ht : t≠0) (ha : source≠qa) (hb : source≠qb) (hgap : qb-qa=t • direction) :
    dividedNewtonTargetField source qa qb direction =
      t⁻¹ • (newtonTargetField source qb-newtonTargetField source qa) := by
  rw [dividedNewtonTargetField, dividedInverseCube_eq source qa qb direction t ht ha hb hgap]
  have hdir : direction=t⁻¹ • (qb-qa) := by
    rw [hgap, smul_smul, inv_mul_cancel₀ ht, one_smul]
  rw [hdir]
  unfold newtonTargetField
  simp only [div_eq_mul_inv, smul_smul, smul_sub]
  module

abbrev DividedFieldVariables := (Plane×Plane)×(Plane×Plane)

theorem dividedInverseCube_joint_contDiffAt (n : ℕ∞ω) (v : DividedFieldVariables)
    (ha : v.1.1≠v.1.2) (hb : v.1.1≠v.2.1) :
    ContDiffAt ℝ n (fun w : DividedFieldVariables =>
      dividedInverseCube w.1.1 w.1.2 w.2.1 w.2.2) v := by
  have hda : 0<‖v.1.1-v.1.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ha)
  have hdb : 0<‖v.1.1-v.2.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
  have hs : ‖v.1.1-v.1.2‖+‖v.1.1-v.2.1‖≠0 := ne_of_gt (add_pos hda hdb)
  have hna : ContDiffAt ℝ n (fun w : DividedFieldVariables => ‖w.1.1-w.1.2‖) v := by
    exact (contDiffAt_fst.fst.sub contDiffAt_fst.snd).norm ℝ (sub_ne_zero.mpr ha)
  have hnb : ContDiffAt ℝ n (fun w : DividedFieldVariables => ‖w.1.1-w.2.1‖) v := by
    exact (contDiffAt_fst.fst.sub contDiffAt_snd.fst).norm ℝ (sub_ne_zero.mpr hb)
  have hd : (‖v.1.1-v.1.2‖+‖v.1.1-v.2.1‖)*‖v.1.1-v.1.2‖^3*‖v.1.1-v.2.1‖^3≠0 :=
    mul_ne_zero (mul_ne_zero hs (pow_ne_zero 3 (ne_of_gt hda))) (pow_ne_zero 3 (ne_of_gt hdb))
  have hvec : ContDiff ℝ n (fun w : DividedFieldVariables => w.1.2+w.2.1-(2 : ℝ) • w.1.1) := by
    fun_prop
  have hinner : ContDiffAt ℝ n (fun w : DividedFieldVariables =>
      inner ℝ w.2.2 (w.1.2+w.2.1-(2 : ℝ) • w.1.1)) v :=
    contDiffAt_snd.snd.inner ℝ hvec.contDiffAt
  unfold dividedInverseCube
  exact (hinner.neg.mul (((hna.pow 2).add (hna.mul hnb)).add (hnb.pow 2))).div
    (((hna.add hnb).mul (hna.pow 3)).mul (hnb.pow 3)) hd

theorem dividedNewtonTargetField_joint_contDiffAt (n : ℕ∞ω) (v : DividedFieldVariables)
    (ha : v.1.1≠v.1.2) (hb : v.1.1≠v.2.1) :
    ContDiffAt ℝ n (fun w : DividedFieldVariables =>
      dividedNewtonTargetField w.1.1 w.1.2 w.2.1 w.2.2) v := by
  have hcoef := dividedInverseCube_joint_contDiffAt n v ha hb
  have hna : ContDiffAt ℝ n (fun w : DividedFieldVariables => ‖w.1.1-w.1.2‖) v :=
    (contDiffAt_fst.fst.sub contDiffAt_fst.snd).norm ℝ (sub_ne_zero.mpr ha)
  have hn : ‖v.1.1-v.1.2‖^3≠0 := pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr ha))
  unfold dividedNewtonTargetField
  exact (hcoef.smul (contDiffAt_fst.fst.sub contDiffAt_snd.fst)).sub
    (((hna.pow 3).inv hn).smul contDiffAt_snd.snd)

end DominantFiveBody
