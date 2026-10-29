import DominantFiveBody.CollisionGeometry
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Order.LiminfLimsup

/-! Current-mass cluster virial identities used in Proposition `prop:uniform`.
The inertia and potential below concern actual collision-free configurations;
no regularized collision point is inserted into a physical theorem. -/

noncomputable section
open scoped BigOperators NNReal ContDiff
open Filter Topology

namespace DominantFiveBody

def clusterCenter (m : MassVector) (x : Configuration) (S : Finset Label) : Plane :=
  (clusterMass m S)⁻¹ • clusterPosition m x S

def clusterInertia (m : MassVector) (x : Configuration) (S : Finset Label) : ℝ :=
  ∑ i ∈ S, m i * ‖x i - clusterCenter m x S‖ ^ 2

/-- Half the ordered-pair sum counts each actual interaction once. The zero
diagonal follows from Lean's total division; off-diagonal physical use always
requires the separate `CollisionFree` hypothesis. -/
def clusterPotential (m : MassVector) (x : Configuration) (S : Finset Label) : ℝ :=
  (1 / 2) * ∑ i ∈ S, ∑ j ∈ S, m i * m j / pairDistance x i j

def exteriorAcceleration (m : MassVector) (x : Configuration)
    (S : Finset Label) (i : Label) : Plane :=
  ∑ j ∈ Sᶜ, (m j / pairDistance x i j ^ 3) • (x j - x i)

/-- A complete limiting cluster contains ALL labels at its limiting position. -/
def CompleteLimitingCluster (limit : Configuration) (S : Finset Label) (c : Plane) : Prop :=
  ∀ i, i ∈ S ↔ limit i = c

abbrev ExteriorData := (MassVector × Configuration) × Plane

/-- Exterior Newton field in joint source/mass/target coordinates. Varying
current masses are parameters, including every zero-mass boundary point. -/
def exteriorField (S : Finset Label) (d : ExteriorData) : Plane :=
  ∑ j ∈ Sᶜ, (d.1.1 j / ‖d.2 - d.1.2 j‖ ^ 3) • (d.1.2 j - d.2)

theorem exteriorField_at_position (m : MassVector) (x : Configuration)
    (S : Finset Label) (i : Label) :
    exteriorField S ((m,x),x i) = exteriorAcceleration m x S i := rfl

/-- The true exterior field is jointly smooth near every target separated
from its exterior labels; mass positivity is not needed for this analytic fact. -/
theorem exteriorField_contDiffAt (S : Finset Label) (d : ExteriorData)
    (hsep : ∀ j ∈ Sᶜ, d.2 ≠ d.1.2 j) :
    ContDiffAt ℝ ⊤ (exteriorField S) d := by
  unfold exteriorField
  apply ContDiffAt.sum
  intro j hj
  have hm : ContDiffAt ℝ ⊤ (fun a : ExteriorData => a.1.1 j) d :=
    (contDiffAt_apply ℝ ℝ j d.1.1).comp d contDiffAt_fst.fst
  have hx : ContDiffAt ℝ ⊤ (fun a : ExteriorData => a.1.2 j) d :=
    (contDiffAt_apply ℝ Plane j d.1.2).comp d contDiffAt_fst.snd
  have hv : ContDiffAt ℝ ⊤ (fun a : ExteriorData => a.1.2 j-a.2) d := hx.sub contDiffAt_snd
  have hn : ContDiffAt ℝ ⊤ (fun a : ExteriorData => ‖a.2-a.1.2 j‖) d :=
    (contDiffAt_snd.sub hx).norm ℝ (sub_ne_zero.mpr (hsep j hj))
  have hden : ‖d.2-d.1.2 j‖ ^ 3 ≠ 0 :=
    pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hsep j hj)))
  exact (hm.div (hn.pow 3) hden).smul hv

/-- Complete-cluster separation supplies a uniform LOCAL Lipschitz constant
for simultaneously varying sources, current masses and target positions. -/
theorem complete_cluster_exterior_lipschitz (limit : Configuration)
    (S : Finset Label) (c : Plane) (hC : CompleteLimitingCluster limit S c)
    (mLimit : MassVector) :
    ∃ K : ℝ≥0, ∃ U ∈ nhds ((mLimit,limit),c), LipschitzOnWith K (exteriorField S) U := by
  have hsep : ∀ j ∈ Sᶜ, c ≠ limit j := by
    intro j hj heq
    have hi : j ∈ S := (hC j).mpr heq.symm
    exact (Finset.mem_compl.mp hj) hi
  exact ((exteriorField_contDiffAt S ((mLimit,limit),c) hsep).of_le (by norm_num)).exists_lipschitzOnWith

/-- Specializing the joint Lipschitz neighborhood to one current mass/source
configuration gives exactly the pointwise exterior error used by the virial. -/
theorem exteriorField_target_lipschitz (S : Finset Label) (K : ℝ≥0)
    (U : Set ExteriorData) (hU : LipschitzOnWith K (exteriorField S) U)
    (m : MassVector) (x : Configuration) (z w : Plane)
    (hz : ((m,x),z) ∈ U) (hw : ((m,x),w) ∈ U) :
    ‖exteriorField S ((m,x),z)-exteriorField S ((m,x),w)‖ ≤ (K : ℝ) * ‖z-w‖ := by
  simpa [dist_eq_norm, Prod.dist_eq] using hU.dist_le_mul _ hz _ hw

theorem cluster_weighted_offsets_zero (m : MassVector) (x : Configuration)
    (S : Finset Label) (hS : clusterMass m S ≠ 0) :
    (∑ i ∈ S, m i • (x i - clusterCenter m x S)) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul]
  change clusterPosition m x S - clusterMass m S • clusterCenter m x S = 0
  rw [clusterCenter, smul_smul, mul_inv_cancel₀ hS, one_smul, sub_self]

theorem pair_virial (m : MassVector) (x : Configuration) (hx : CollisionFree x)
    (b : Plane) (i j : Label) :
    inner ℝ (x i - b) (pairForce m x i j) +
      inner ℝ (x j - b) (pairForce m x j i) =
        -(m i * m j / pairDistance x i j) := by
  by_cases hij : i = j
  · subst j
    simp [pairDistance]
  have hd := collision_distance_pos x hx i j hij
  rw [pairForce_reverse m x i j, inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left]
  have hsub : x i - b - (x j - b) = x i - x j := by abel
  rw [hsub, pairForce, real_inner_smul_right]
  have hrev : x j - x i = -(x i - x j) := by abel
  rw [hrev, inner_neg_right, real_inner_self_eq_norm_sq]
  change (m i * m j / pairDistance x i j ^ 3) * -(pairDistance x i j ^ 2) = _
  field_simp [ne_of_gt hd]

/-- Exact cluster internal virial, with every current mass retained. -/
theorem cluster_internal_virial (m : MassVector) (x : Configuration)
    (hx : CollisionFree x) (S : Finset Label) (b : Plane) :
    (∑ i ∈ S, ∑ j ∈ S, inner ℝ (x i - b) (pairForce m x i j)) =
      -clusterPotential m x S := by
  let W : ℝ := ∑ i ∈ S, ∑ j ∈ S,
    inner ℝ (x i - b) (pairForce m x i j)
  have hswap : W = ∑ i ∈ S, ∑ j ∈ S,
      inner ℝ (x j - b) (pairForce m x j i) := Finset.sum_comm
  have hadd : W + W = -(∑ i ∈ S, ∑ j ∈ S, m i * m j / pairDistance x i j) := by
    conv_lhs => rhs; rw [hswap]
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, pair_virial m x hx b]
    simp only [Finset.sum_neg_distrib]
  change W = -((1 / 2) * _)
  linarith

theorem weighted_exteriorAcceleration (m : MassVector) (x : Configuration)
    (S : Finset Label) (i : Label) :
    m i • exteriorAcceleration m x S i = ∑ j ∈ Sᶜ, pairForce m x i j := by
  simp [exteriorAcceleration, Finset.smul_sum, smul_smul, pairForce, mul_div_assoc]

/-- Actual normalized cluster virial. The exterior field is measured relative
to its value at the CURRENT cluster center, so no positive limiting mass is
needed when this identity is applied to a degenerating mass sequence. -/
theorem normalized_cluster_virial (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x)
    (S : Finset Label) (hS : S.Nonempty) (Acenter : Plane) :
    clusterPotential m x S = clusterInertia m x S +
      ∑ i ∈ S, m i * inner ℝ (x i - clusterCenter m x S)
        (exteriorAcceleration m x S i - Acenter) := by
  let b := clusterCenter m x S
  have hz := cluster_weighted_offsets_zero m x S (ne_of_gt (clusterMass_pos m hm S hS))
  have hcenter : (∑ i ∈ S, m i * inner ℝ (x i - b) Acenter) = 0 := by
    simpa [sum_inner, real_inner_smul_left, b] using
      congrArg (fun v => inner ℝ v Acenter) hz
  have hpos : (∑ i ∈ S, m i * inner ℝ (x i - b) (x i)) = clusterInertia m x S := by
    have hc : (∑ i ∈ S, m i * inner ℝ (x i - b) b) = 0 := by
      simpa [sum_inner, real_inner_smul_left, b] using
        congrArg (fun v => inner ℝ v b) hz
    have hdecomp (i : Label) : x i = (x i - b) + b := by abel
    have heach (i : Label) : inner ℝ (x i - b) (x i) =
        inner ℝ (x i - b) (x i - b) + inner ℝ (x i - b) b := by
      conv_lhs => rhs; rw [hdecomp i]
      rw [inner_add_right]
    simp_rw [heach]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hc, add_zero]
    simp [clusterInertia, b]
  have hfull : (∑ i ∈ S, inner ℝ (x i - b) (m i • acceleration m x i)) =
      -clusterInertia m x S := by
    simp only [hx.2.2, smul_neg, inner_neg_right, real_inner_smul_right,
      Finset.sum_neg_distrib]
    rw [hpos]
  have hsplit : (∑ i ∈ S, inner ℝ (x i - b) (m i • acceleration m x i)) =
      -clusterPotential m x S +
        ∑ i ∈ S, m i * inner ℝ (x i - b) (exteriorAcceleration m x S i) := by
    simp_rw [weighted_acceleration_as_pair_sum,
      ← Finset.sum_add_sum_compl S (fun j => pairForce m x _ j), inner_add_right,
      Finset.sum_add_distrib, inner_sum]
    rw [cluster_internal_virial m x hx.1 S b]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← inner_sum, ← weighted_exteriorAcceleration, real_inner_smul_right]
  simp only [inner_sub_right, mul_sub, Finset.sum_sub_distrib]
  change clusterPotential m x S = clusterInertia m x S +
    ((∑ i ∈ S, m i * inner ℝ (x i - b) (exteriorAcceleration m x S i)) - _)
  rw [hcenter]
  linarith

theorem clusterInertia_nonneg (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (S : Finset Label) : 0 ≤ clusterInertia m x S := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hm i).le (sq_nonneg _)

/-- The analytical exterior-field bound is explicit: when its pointwise error
is Lipschitz with constant `L`, the actual cluster virial gives `U≤(1+L)I`.
This is a derived estimate, not an assumption of the desired uniform radius theorem. -/
theorem normalized_cluster_virial_le (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x)
    (S : Finset Label) (hS : S.Nonempty) (Acenter : Plane) (L : ℝ)
    (hLip : ∀ i ∈ S,
      ‖exteriorAcceleration m x S i - Acenter‖ ≤ L * ‖x i - clusterCenter m x S‖) :
    clusterPotential m x S ≤ (1 + L) * clusterInertia m x S := by
  rw [normalized_cluster_virial m hm x hx S hS Acenter]
  have heach (i : Label) (hi : i ∈ S) :
      m i * inner ℝ (x i - clusterCenter m x S)
        (exteriorAcceleration m x S i - Acenter) ≤
      L * (m i * ‖x i - clusterCenter m x S‖ ^ 2) := by
    have hp := real_inner_le_norm (x i - clusterCenter m x S)
      (exteriorAcceleration m x S i - Acenter)
    have hbound := hp.trans (mul_le_mul_of_nonneg_left (hLip i hi) (norm_nonneg _))
    have hmass := mul_le_mul_of_nonneg_left hbound (hm i).le
    nlinarith [hmass]
  have hsum := Finset.sum_le_sum (fun i hi => heach i hi)
  rw [← Finset.mul_sum] at hsum
  change _ ≤ L * clusterInertia m x S at hsum
  nlinarith

/-- Current weighted inertia is minimal about the current mass center. -/
theorem cluster_parallel_axis (m : MassVector) (x : Configuration)
    (S : Finset Label) (hS : clusterMass m S ≠ 0) (z : Plane) :
    (∑ i ∈ S, m i * ‖x i - z‖ ^ 2) =
      clusterInertia m x S + clusterMass m S * ‖clusterCenter m x S - z‖ ^ 2 := by
  let b := clusterCenter m x S
  have hz := cluster_weighted_offsets_zero m x S hS
  have hinner : (∑ i ∈ S, m i * inner ℝ (x i - b) (b - z)) = 0 := by
    simpa [sum_inner, real_inner_smul_left, b] using
      congrArg (fun v => inner ℝ v (b-z)) hz
  have heach (i : Label) : m i * ‖x i - z‖ ^ 2 =
      m i * ‖x i - b‖ ^ 2 + 2 * (m i * inner ℝ (x i - b) (b-z)) +
        m i * ‖b-z‖ ^ 2 := by
    have heq : x i - z = (x i - b) + (b-z) := by abel
    rw [heq, norm_add_sq_real]
    ring
  simp_rw [heach]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hinner, mul_zero, add_zero, ← Finset.sum_mul]
  rfl

theorem clusterInertia_le_about (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (S : Finset Label) (hS : S.Nonempty) (z : Plane) :
    clusterInertia m x S ≤ ∑ i ∈ S, m i * ‖x i - z‖ ^ 2 := by
  rw [cluster_parallel_axis m x S (ne_of_gt (clusterMass_pos m hm S hS)) z]
  have hterm : 0 ≤ clusterMass m S * ‖clusterCenter m x S-z‖ ^ 2 :=
    mul_nonneg (clusterMass_pos m hm S hS).le (sq_nonneg _)
  linarith

theorem clusterPotential_nonneg (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (S : Finset Label) : 0 ≤ clusterPotential m x S := by
  unfold clusterPotential
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact div_nonneg (mul_pos (hm i) (hm j)).le (norm_nonneg _)

/-- Splitting the primary interactions out of a current cluster. -/
theorem clusterPotential_erase_primary (m : MassVector) (x : Configuration)
    (S : Finset Label) (h0 : (0 : Label) ∈ S) :
    clusterPotential m x S =
      (∑ i ∈ S.erase 0, m 0 * m i / pairDistance x 0 i) +
      clusterPotential m x (S.erase 0) := by
  have heq : S = insert 0 (S.erase 0) := (Finset.insert_erase h0).symm
  have hn : (0 : Label) ∉ S.erase 0 := by simp
  conv_lhs => rw [heq]
  simp only [clusterPotential, Finset.sum_insert hn]
  have hreverse : (∑ i ∈ S.erase 0, m i*m 0/pairDistance x i 0) =
      ∑ i ∈ S.erase 0, m 0*m i/pairDistance x 0 i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [pairDistance_reverse x 0 i, mul_comm (m i) (m 0)]
  simp only [pairDistance, sub_self, norm_zero, div_zero, zero_add]
  rw [Finset.sum_add_distrib]
  have hreverse' : (∑ i ∈ S.erase 0, m i * m 0 / ‖x i-x 0‖) =
      ∑ i ∈ S.erase 0, m 0 * m i / ‖x 0-x i‖ := hreverse
  rw [hreverse']
  ring

/-- The source lower bound `U_C≥m₀ s/d`, allowing the current satellite mass
`s` to become arbitrarily small. -/
theorem primary_cluster_potential_lower (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : CollisionFree x) (S : Finset Label)
    (h0 : (0 : Label) ∈ S) (d : ℝ) (_hd : 0 < d)
    (hdiam : ∀ i ∈ S, pairDistance x 0 i ≤ d) :
    m 0 * clusterMass m (S.erase 0) / d ≤ clusterPotential m x S := by
  rw [clusterPotential_erase_primary m x S h0]
  have hterms : (∑ i ∈ S.erase 0, m 0*m i/d) ≤
      ∑ i ∈ S.erase 0, m 0*m i/pairDistance x 0 i := by
    apply Finset.sum_le_sum
    intro i hi
    have hi0 : (0 : Label) ≠ i := (Finset.mem_erase.mp hi).1.symm
    exact div_le_div_of_nonneg_left (mul_pos (hm 0) (hm i)).le
      (collision_distance_pos x hx 0 i hi0) (hdiam i (Finset.mem_of_mem_erase hi))
  have hre : (∑ i ∈ S.erase 0, m 0*m i/d) = m 0 * clusterMass m (S.erase 0)/d := by
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    rw [← Finset.mul_sum]
    rfl
  rw [hre] at hterms
  exact hterms.trans (le_add_of_nonneg_right (clusterPotential_nonneg m hm x (S.erase 0)))

/-- The source upper bound `I_C≤s d²` uses the primary as the competing center
in the exact parallel-axis identity. The primary mass contributes zero here. -/
theorem primary_cluster_inertia_upper (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (S : Finset Label) (h0 : (0 : Label) ∈ S)
    (d : ℝ) (_hd : 0 < d)
    (hdiam : ∀ i ∈ S, pairDistance x 0 i ≤ d) :
    clusterInertia m x S ≤ clusterMass m (S.erase 0) * d ^ 2 := by
  have hbase := clusterInertia_le_about m hm x S ⟨0,h0⟩ (x 0)
  have heq : (∑ i ∈ S, m i * ‖x i-x 0‖^2) =
      ∑ i ∈ S.erase 0, m i * ‖x i-x 0‖^2 := by
    rw [← Finset.sum_erase_add _ _ h0]
    simp
  rw [heq] at hbase
  apply hbase.trans
  calc
    (∑ i ∈ S.erase 0, m i * ‖x i-x 0‖^2) ≤ ∑ i ∈ S.erase 0, m i * d^2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hm i).le
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa [pairDistance, norm_sub_rev] using hdiam i (Finset.mem_of_mem_erase hi)
    _ = clusterMass m (S.erase 0) * d^2 := by rw [← Finset.sum_mul]; rfl

/-- Quantitative primary-cluster virial contradiction: all current satellite
mass cancels, leaving `m₀≤(1+L)d³`. The exterior Lipschitz estimate remains
explicit and must be established on complete limiting clusters separately. -/
theorem primary_cluster_cube_lower (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x)
    (S : Finset Label) (h0 : (0 : Label) ∈ S) (hs : (S.erase 0).Nonempty)
    (d : ℝ) (hd : 0 < d) (hdiam : ∀ i ∈ S, pairDistance x 0 i ≤ d)
    (Acenter : Plane) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ i ∈ S,
      ‖exteriorAcceleration m x S i - Acenter‖ ≤ L * ‖x i-clusterCenter m x S‖) :
    m 0 ≤ (1+L) * d^3 := by
  have hmass := clusterMass_pos m hm (S.erase 0) hs
  have hlo := primary_cluster_potential_lower m hm x hx.1 S h0 d hd hdiam
  have hvir := normalized_cluster_virial_le m hm x hx S ⟨0,h0⟩ Acenter L hLip
  have hin := primary_cluster_inertia_upper m hm x S h0 d hd hdiam
  have hc := hlo.trans (hvir.trans (mul_le_mul_of_nonneg_left hin (by linarith : 0 ≤ 1+L)))
  have hmult := (div_le_iff₀ hd).mp hc
  have hrew : ((1+L) * (clusterMass m (S.erase 0)*d^2)) * d =
      ((1+L)*d^3) * clusterMass m (S.erase 0) := by ring
  rw [hrew] at hmult
  exact le_of_mul_le_mul_right hmult hmass

theorem clusterCenter_continuousAt (m : MassVector) (x : Configuration)
    (S : Finset Label) (hS : clusterMass m S ≠ 0) :
    ContinuousAt (fun a : MassVector × Configuration => clusterCenter a.1 a.2 S) (m,x) := by
  have hmass : Continuous (fun a : MassVector × Configuration => clusterMass a.1 S) := by
    unfold clusterMass
    fun_prop
  have hposition : Continuous (fun a : MassVector × Configuration => clusterPosition a.1 a.2 S) := by
    unfold clusterPosition
    fun_prop
  exact (hmass.continuousAt.inv₀ hS).smul hposition.continuousAt

theorem clusterCenter_of_common_position (m : MassVector) (x : Configuration)
    (S : Finset Label) (hS : clusterMass m S ≠ 0) (c : Plane)
    (hc : ∀ i ∈ S, x i = c) : clusterCenter m x S = c := by
  have hp : clusterPosition m x S = clusterMass m S • c := by
    unfold clusterPosition clusterMass
    calc
      _ = ∑ i ∈ S, m i • c := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hc i hi]
      _ = _ := Finset.sum_smul.symm
  rw [clusterCenter, hp, smul_smul, inv_mul_cancel₀ hS, one_smul]

/-- A complete primary-containing cluster cannot collapse along actual
normalized configurations. The true joint exterior field supplies the
uniform Lipschitz estimate; the satellite cluster masses may tend to zero. -/
theorem no_primary_complete_collision
    (m : ℕ → MassVector) (x : ℕ → Configuration)
    (hm : ∀ n, PositiveMasses (m n))
    (hx : ∀ n, NormalizedCentralConfiguration (m n) (x n))
    (hprimary : ∀ n, m n 0 = 1)
    (mLimit : MassVector) (xLimit : Configuration)
    (hmt : Tendsto m atTop (nhds mLimit))
    (hxt : Tendsto x atTop (nhds xLimit))
    (S : Finset Label) (h0 : (0 : Label) ∈ S) (hs : (S.erase 0).Nonempty)
    (hC : CompleteLimitingCluster xLimit S (xLimit 0)) : False := by
  have hm0 : mLimit 0 = 1 := by
    have ht := (continuous_apply (0 : Label)).tendsto mLimit |>.comp hmt
    change Tendsto (fun n => m n 0) atTop (nhds (mLimit 0)) at ht
    have hconst : (fun n => m n 0) = fun _ => (1 : ℝ) := funext hprimary
    rw [hconst] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hnonneg : ∀ i, 0 ≤ mLimit i := by
    intro i
    exact ge_of_tendsto ((continuous_apply i).tendsto mLimit |>.comp hmt)
      (Filter.Eventually.of_forall (fun n => (hm n i).le))
  have hmass : 0 < clusterMass mLimit S := by
    have hle : mLimit 0 ≤ clusterMass mLimit S :=
      Finset.single_le_sum (fun i _ => hnonneg i) h0
    rw [hm0] at hle
    linarith
  have hcenter0 : clusterCenter mLimit xLimit S = xLimit 0 :=
    clusterCenter_of_common_position mLimit xLimit S (ne_of_gt hmass) (xLimit 0)
      (fun i hi => (hC i).mp hi)
  have hbt : Tendsto (fun n => clusterCenter (m n) (x n) S) atTop (nhds (xLimit 0)) := by
    simpa [Function.comp_def,hcenter0] using
      (clusterCenter_continuousAt mLimit xLimit S (ne_of_gt hmass)).tendsto.comp (hmt.prodMk_nhds hxt)
  obtain ⟨K,U,hUnear,hLip⟩ := complete_cluster_exterior_lipschitz xLimit S (xLimit 0) hC mLimit
  have hcenterU : ∀ᶠ n in atTop, ((m n,x n),clusterCenter (m n) (x n) S) ∈ U :=
    (hmt.prodMk_nhds hxt |>.prodMk_nhds hbt).eventually hUnear
  have hpositionsU : ∀ᶠ n in atTop, ∀ i ∈ S, ((m n,x n),x n i) ∈ U := by
    apply (Finset.eventually_all S).mpr
    intro i hi
    have hit : Tendsto (fun n => x n i) atTop (nhds (xLimit 0)) := by
      simpa [Function.comp_def,(hC i).mp hi] using (continuous_apply i).tendsto xLimit |>.comp hxt
    exact (hmt.prodMk_nhds hxt |>.prodMk_nhds hit).eventually hUnear
  let d : ℕ → ℝ := fun n => ∑ i ∈ S, pairDistance (x n) 0 i
  have hd : ∀ n, 0 < d n := by
    intro n
    obtain ⟨i,hi⟩ := hs
    apply Finset.sum_pos' (fun j _ => norm_nonneg _)
    refine ⟨i, Finset.mem_of_mem_erase hi, ?_⟩
    exact collision_distance_pos (x n) (hx n).1 0 i (Finset.mem_erase.mp hi).1.symm
  have hdiam : ∀ n, ∀ i ∈ S, pairDistance (x n) 0 i ≤ d n := by
    intro n i hi
    change ‖x n 0-x n i‖ ≤ ∑ j ∈ S, ‖x n 0-x n j‖
    exact Finset.single_le_sum (fun j _ => norm_nonneg (x n 0-x n j)) hi
  have hdt : Tendsto d atTop (nhds 0) := by
    have heach : ∀ i ∈ S, Tendsto (fun n => pairDistance (x n) 0 i) atTop (nhds 0) := by
      intro i hi
      have hi0 : xLimit i = xLimit 0 := (hC i).mp hi
      simpa [pairDistance, hi0] using
        (((continuous_apply (0 : Label)).tendsto xLimit |>.comp hxt).sub
          ((continuous_apply i).tendsto xLimit |>.comp hxt)).norm
    simpa [d] using tendsto_finsetSum S heach
  have hcube : ∀ᶠ n in atTop, (1 : ℝ) ≤ (1+(K : ℝ))*d n^3 := by
    filter_upwards [hcenterU,hpositionsU] with n hb hp
    have hlocal : ∀ i ∈ S,
        ‖exteriorAcceleration (m n) (x n) S i -
          exteriorField S ((m n,x n),clusterCenter (m n) (x n) S)‖ ≤
        (K : ℝ) * ‖x n i-clusterCenter (m n) (x n) S‖ := by
      intro i hi
      exact exteriorField_target_lipschitz S K U hLip (m n) (x n) _ _ (hp i hi) hb
    simpa [hprimary] using primary_cluster_cube_lower (m n) (hm n) (x n) (hx n)
      S h0 hs (d n) (hd n) (hdiam n)
      (exteriorField S ((m n,x n),clusterCenter (m n) (x n) S)) (K : ℝ) K.coe_nonneg hlocal
  have hzero : Tendsto (fun n => (1+(K : ℝ))*d n^3) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (hdt.pow 3)
  have hf : (1 : ℝ) ≤ 0 := ge_of_tendsto hzero hcube
  norm_num at hf

/-- Proposition `prop:uniform`: no satellite can approach the primary,
uniformly over all positive ratios with bounded total satellite mass. -/
theorem dominant_primary_separation_for_label (E : ℝ) (hE : 0 < E)
    (i : Label) (hi : i ≠ 0) :
    ∃ b : ℝ, 0 < b ∧ ∀ (ε : ℝ) (μ : MassRatio) (x : Configuration),
      0 < ε → ε ≤ E → PositiveRatio μ →
      NormalizedCentralConfiguration (masses ε μ) x → b ≤ pairDistance x 0 i := by
  by_contra h
  push Not at h
  have hw (n : ℕ) : ∃ (ε : ℝ) (μ : MassRatio) (x : Configuration),
      0 < ε ∧ ε ≤ E ∧ PositiveRatio μ ∧
      NormalizedCentralConfiguration (masses ε μ) x ∧ pairDistance x 0 i < 1/((n:ℝ)+1) :=
    h (1/((n:ℝ)+1)) (by positivity)
  choose ε μ x hε hεE hμ hx hdist using hw
  let m : ℕ → MassVector := fun n => masses (ε n) (μ n)
  have hm : ∀ n, PositiveMasses (m n) := fun n => masses_positive _ _ (hε n) (hμ n)
  have hM : ∀ n, totalMass (m n) ≤ 1+E := by
    intro n
    rw [totalMass_masses (ε n) (μ n) (hμ n)]
    linarith [hεE n]
  let R : ℝ := max (1+E) (4*Real.rpow (1+E) (1/3))
  have hR : 0 ≤ R := le_trans (by linarith) (le_max_left _ _)
  have hbounded : ∀ n, (m n,x n) ∈ Metric.closedBall (0 : MassVector×Configuration) R := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    apply max_le
    · apply (pi_norm_le_iff_of_nonneg hR).mpr
      intro j
      rw [Real.norm_eq_abs, abs_of_pos (hm n j)]
      have hj : m n j ≤ totalMass (m n) :=
        Finset.single_le_sum (fun k _ => (hm n k).le) (Finset.mem_univ j)
      exact hj.trans ((hM n).trans (le_max_left _ _))
    · apply (pi_norm_le_iff_of_nonneg hR).mpr
      intro j
      have hj := normalized_position_norm_le (m n) (hm n) (x n) (hx n) j
      have hpow := Real.rpow_le_rpow (totalMass_pos (m n) (hm n)).le (hM n)
        (by norm_num : 0 ≤ (1/3 : ℝ))
      exact hj.trans ((mul_le_mul_of_nonneg_left hpow (by norm_num)).trans (le_max_right _ _))
  obtain ⟨limit,_,φ,hφ,ht⟩ := (isCompact_closedBall (0 : MassVector×Configuration) R).tendsto_subseq hbounded
  have hmt : Tendsto (m ∘ φ) atTop (nhds limit.1) := by
    simpa [Function.comp_def] using continuous_fst.tendsto limit |>.comp ht
  have hxt : Tendsto (x ∘ φ) atTop (nhds limit.2) := by
    simpa [Function.comp_def] using continuous_snd.tendsto limit |>.comp ht
  have hdist0 : Tendsto (fun n => pairDistance (x n) 0 i) atTop (nhds 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => (hdist n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlimdist : pairDistance limit.2 0 i = 0 := by
    have ht0 := hdist0.comp hφ.tendsto_atTop
    have hgeom : Tendsto (fun n => pairDistance (x (φ n)) 0 i) atTop
        (nhds (pairDistance limit.2 0 i)) := by
      simpa [pairDistance, Function.comp_def] using
        (((continuous_apply (0 : Label)).tendsto limit.2 |>.comp hxt).sub
          ((continuous_apply i).tendsto limit.2 |>.comp hxt)).norm
    exact tendsto_nhds_unique hgeom ht0
  have hcoll : limit.2 i = limit.2 0 := by
    exact (sub_eq_zero.mp (norm_eq_zero.mp hlimdist)).symm
  let S : Finset Label := Finset.univ.filter (fun j => limit.2 j = limit.2 0)
  have h0 : (0 : Label) ∈ S := by simp [S]
  have hs : (S.erase 0).Nonempty := ⟨i, by simp [S, hi, hcoll]⟩
  have hC : CompleteLimitingCluster limit.2 S (limit.2 0) := by
    intro j
    simp [S]
  exact no_primary_complete_collision (m ∘ φ) (x ∘ φ) (fun n => hm (φ n))
    (fun n => hx (φ n)) (fun n => masses_primary _ _) limit.1 limit.2 hmt hxt S h0 hs hC

/-- Full common lower radius bound in Proposition 4.1, quantified before all
positive satellite mass ratios and all configurations. -/
theorem dominant_primary_separation (E : ℝ) (hE : 0 < E) :
    ∃ b : ℝ, 0 < b ∧ ∀ (ε : ℝ) (μ : MassRatio) (x : Configuration),
      0 < ε → ε ≤ E → PositiveRatio μ →
      NormalizedCentralConfiguration (masses ε μ) x →
      ∀ i : Satellite, b ≤ pairDistance x 0 i.succ := by
  obtain ⟨b1,h1,hb1⟩ := dominant_primary_separation_for_label E hE 1 (by decide)
  obtain ⟨b2,h2,hb2⟩ := dominant_primary_separation_for_label E hE 2 (by decide)
  obtain ⟨b3,h3,hb3⟩ := dominant_primary_separation_for_label E hE 3 (by decide)
  obtain ⟨b4,h4,hb4⟩ := dominant_primary_separation_for_label E hE 4 (by decide)
  let b := min b1 (min b2 (min b3 b4))
  have hbb1 : b ≤ b1 := min_le_left _ _
  have hbb2 : b ≤ b2 := (min_le_right _ _).trans (min_le_left _ _)
  have hbb3 : b ≤ b3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbb4 : b ≤ b4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨b, lt_min h1 (lt_min h2 (lt_min h3 h4)), ?_⟩
  intro ε μ x hε hεE hμ hx i
  fin_cases i
  · exact hbb1.trans (hb1 ε μ x hε hεE hμ hx)
  · exact hbb2.trans (hb2 ε μ x hε hεE hμ hx)
  · exact hbb3.trans (hb3 ε μ x hε hεE hμ hx)
  · exact hbb4.trans (hb4 ε μ x hε hεE hμ hx)

theorem dominant_primary_relative_radius_lower (E : ℝ) (hE : 0 < E) :
    ∃ b : ℝ, 0 < b ∧ ∀ (ε : ℝ) (μ : MassRatio) (x : Configuration),
      0 < ε → ε ≤ E → PositiveRatio μ →
      NormalizedCentralConfiguration (masses ε μ) x →
      ∀ i : Satellite, b ≤ ‖satellitesRelative x i‖ := by
  obtain ⟨b,hb,hbound⟩ := dominant_primary_separation E hE
  refine ⟨b,hb,?_⟩
  intro ε μ x hε hεE hμ hx i
  simpa [satellitesRelative,primaryRelative,pairDistance,norm_sub_rev] using
    hbound ε μ x hε hεE hμ hx i

/-- A current positive-mass average stays in every common closed ball,
independently of how small the total current averaging mass is. -/
theorem clusterCenter_distance_le (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (S : Finset Label) (hS : S.Nonempty) (c : Plane) (r : ℝ)
    (hr : ∀ i ∈ S, ‖x i-c‖ ≤ r) : ‖clusterCenter m x S-c‖ ≤ r := by
  have hM := clusterMass_pos m hm S hS
  have hsum : (∑ i ∈ S, m i • (x i-c)) = clusterMass m S • (clusterCenter m x S-c) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
    change clusterPosition m x S - clusterMass m S • c = _
    rw [clusterCenter, smul_smul, mul_inv_cancel₀ (ne_of_gt hM), one_smul]
  have hnorm : ‖clusterMass m S • (clusterCenter m x S-c)‖ ≤ clusterMass m S*r := by
    rw [← hsum]
    apply (norm_sum_le _ _).trans
    calc
      (∑ i ∈ S, ‖m i • (x i-c)‖) ≤ ∑ i ∈ S, m i*r := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hm i)]
        exact mul_le_mul_of_nonneg_left (hr i hi) (hm i).le
      _ = _ := (Finset.sum_mul S m r).symm
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hM] at hnorm
  exact le_of_mul_le_mul_left hnorm hM

/-- Current normalized weights preserve convergence of a finite complete
cluster even when every member mass and its total mass tend to zero. -/
theorem clusterCenter_tendsto_current_weights (m : ℕ → MassVector)
    (hm : ∀ n, PositiveMasses (m n)) (x : ℕ → Configuration)
    (S : Finset Label) (hS : S.Nonempty) (c : Plane)
    (hxt : ∀ i ∈ S, Tendsto (fun n => x n i) atTop (nhds c)) :
    Tendsto (fun n => clusterCenter (m n) (x n) S) atTop (nhds c) := by
  apply Metric.tendsto_nhds.mpr
  intro r hr
  have heach : ∀ᶠ n in atTop, ∀ i ∈ S, ‖x n i-c‖ < r/2 := by
    apply (Finset.eventually_all S).mpr
    intro i hi
    simpa [dist_eq_norm] using (Metric.tendsto_nhds.mp (hxt i hi)) (r/2) (by linarith)
  filter_upwards [heach] with n hn
  rw [dist_eq_norm]
  exact (clusterCenter_distance_le (m n) (hm n) (x n) S hS c (r/2)
    (fun i hi => (hn i hi).le)).trans_lt (by linarith)

def primaryOnlyMass : MassVector := Fin.cases 1 (fun _ => 0)

@[simp] theorem primaryOnlyMass_zero : primaryOnlyMass 0 = 1 := rfl

theorem primaryOnlyMass_nonprimary (i : Label) (hi : i ≠ 0) : primaryOnlyMass i = 0 := by
  cases i using Fin.cases with
  | zero => exact (hi rfl).elim
  | succ i => rfl

/-- Small total satellite mass forces the full current mass vector to the
primary-only boundary, regardless of how its positive ratios vary. -/
theorem dominant_masses_tendsto_primary (ε : ℕ → ℝ) (μ : ℕ → MassRatio)
    (hε : ∀ n, 0 < ε n) (hμ : ∀ n, PositiveRatio (μ n))
    (hεt : Tendsto ε atTop (nhds 0)) :
    Tendsto (fun n => masses (ε n) (μ n)) atTop (nhds primaryOnlyMass) := by
  apply tendsto_pi_nhds.mpr
  intro i
  cases i using Fin.cases with
  | zero => simp [masses,primaryOnlyMass]
  | succ i =>
    change Tendsto (fun n => ε n*μ n i) atTop (nhds 0)
    apply squeeze_zero (fun n => (mul_pos (hε n) ((hμ n).1 i)).le) _ hεt
    intro n
    have hmi : μ n i ≤ 1 := by
      have hl := Finset.single_le_sum (fun j _ => ((hμ n).1 j).le) (Finset.mem_univ i)
      simpa [(hμ n).2] using hl
    exact (mul_le_mul_of_nonneg_left hmi (hε n).le).trans_eq (mul_one _)

theorem normalized_primary_limit_zero (m : ℕ → MassVector) (x : ℕ → Configuration)
    (hx : ∀ n, NormalizedCentralConfiguration (m n) (x n))
    (hmt : Tendsto m atTop (nhds primaryOnlyMass))
    (xLimit : Configuration) (hxt : Tendsto x atTop (nhds xLimit)) : xLimit 0 = 0 := by
  have hp : Continuous (fun a : MassVector×Configuration => weightedPosition a.1 a.2) := by
    unfold weightedPosition
    fun_prop
  have ht := hp.tendsto (primaryOnlyMass,xLimit) |>.comp (hmt.prodMk_nhds hxt)
  have ht' : Tendsto (fun _ : ℕ => (0 : Plane)) atTop
      (nhds (weightedPosition primaryOnlyMass xLimit)) := by
    simpa [Function.comp_def,(hx _).2.1] using ht
  have heq : weightedPosition primaryOnlyMass xLimit = 0 := tendsto_nhds_unique ht' tendsto_const_nhds
  simpa [weightedPosition,primaryOnlyMass,Fin.sum_univ_succ] using heq

theorem normalized_cluster_exterior_average (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) (S : Finset Label) :
    clusterCenter m (fun i => exteriorAcceleration m x S i) S = -clusterCenter m x S := by
  have hsum : clusterPosition m (fun i => exteriorAcceleration m x S i) S =
      clusterCrossForce m x S := by
    unfold clusterPosition clusterCrossForce
    simp_rw [weighted_exteriorAcceleration]
  rw [clusterCenter,hsum,normalized_cluster_cross_force m x hx,smul_neg]
  rfl

theorem primaryOnly_exteriorField (x : Configuration) (hx0 : x 0 = 0)
    (S : Finset Label) (h0 : (0 : Label) ∉ S) (c : Plane) :
    exteriorField S ((primaryOnlyMass,x),c) = -((‖c‖^3)⁻¹ • c) := by
  unfold exteriorField
  rw [Finset.sum_eq_single 0]
  · simp [hx0,one_div]
  · intro j _ hj
    simp [primaryOnlyMass_nonprimary j hj]
  · intro hbad
    exact (hbad (Finset.mem_compl.mpr h0)).elim

set_option maxHeartbeats 800000 in
/-- Every complete satellite cluster in the vanishing-total-mass limit has
unit radius. The limit is derived by averaging the CURRENT masses, so a
cluster with vanishing total mass is treated without any limiting mass floor. -/
theorem satellite_complete_cluster_limit_unit
    (m : ℕ → MassVector) (x : ℕ → Configuration)
    (hm : ∀ n, PositiveMasses (m n))
    (hx : ∀ n, NormalizedCentralConfiguration (m n) (x n))
    (hmt : Tendsto m atTop (nhds primaryOnlyMass))
    (xLimit : Configuration) (hxt : Tendsto x atTop (nhds xLimit))
    (S : Finset Label) (hS : S.Nonempty) (c : Plane) (hc : c ≠ 0)
    (hC : CompleteLimitingCluster xLimit S c) : ‖c‖ = 1 := by
  have hx0 := normalized_primary_limit_zero m x hx hmt xLimit hxt
  have h0 : (0 : Label) ∉ S := by
    intro hi
    have heq := (hC 0).mp hi
    rw [hx0] at heq
    exact hc heq.symm
  have hsep : ∀ j ∈ Sᶜ, c ≠ xLimit j := by
    intro j hj heq
    exact (Finset.mem_compl.mp hj) ((hC j).mpr heq.symm)
  let A := exteriorField S ((primaryOnlyMass,xLimit),c)
  have hfield : ∀ i ∈ S, Tendsto (fun n => exteriorAcceleration (m n) (x n) S i)
      atTop (nhds A) := by
    intro i hi
    have hit : Tendsto (fun n => x n i) atTop (nhds c) := by
      simpa [Function.comp_def,(hC i).mp hi] using (continuous_apply i).tendsto xLimit |>.comp hxt
    have hdata := hmt.prodMk_nhds hxt |>.prodMk_nhds hit
    have hcont : ContinuousAt (exteriorField S) ((primaryOnlyMass,xLimit),c) :=
      (exteriorField_contDiffAt S ((primaryOnlyMass,xLimit),c) hsep).continuousAt
    simpa only [Function.comp_def,exteriorField_at_position] using hcont.tendsto.comp hdata
  have haverage := clusterCenter_tendsto_current_weights m hm
    (fun n i => exteriorAcceleration (m n) (x n) S i) S hS A hfield
  have hcenter := clusterCenter_tendsto_current_weights m hm x S hS c (fun i hi => by
    simpa [Function.comp_def,(hC i).mp hi] using (continuous_apply i).tendsto xLimit |>.comp hxt)
  have hnegative : Tendsto (fun n => clusterCenter (m n) (fun i => exteriorAcceleration (m n) (x n) S i) S)
      atTop (nhds (-c)) := by
    simpa only [normalized_cluster_exterior_average _ _ (hx _)] using hcenter.neg
  have heq : A = -c := tendsto_nhds_unique haverage hnegative
  have hforce : (‖c‖^3)⁻¹ • c = c := by
    have ha := primaryOnly_exteriorField xLimit hx0 S h0 c
    change exteriorField S ((primaryOnlyMass,xLimit),c) = -c at heq
    rw [ha] at heq
    exact neg_injective heq
  have hscalar : (‖c‖^3)⁻¹ = (1 : ℝ) := by
    apply (smul_left_injective ℝ hc)
    simpa using hforce
  have hpow : ‖c‖^3 = (1 : ℝ)^3 := by
    have hn : ‖c‖^3 ≠ 0 := pow_ne_zero 3 (norm_ne_zero_iff.mpr hc)
    have hi := inv_mul_cancel₀ hn
    rw [hscalar] at hi
    simpa using hi
  exact (pow_left_inj₀ (norm_nonneg c) (by norm_num) (by decide : (3 : ℕ) ≠ 0)).mp hpow

/-- Fixed-label uniform radius convergence; the threshold depends on the
requested error but is independent of every positive satellite ratio. -/
theorem dominant_radius_uniform_for_label (i : Label) (hi : i ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ) (μ : MassRatio) (x : Configuration),
      0 < ε → ε < δ → PositiveRatio μ →
      NormalizedCentralConfiguration (masses ε μ) x →
      |pairDistance x 0 i-1| < η := by
  by_contra h
  push Not at h
  have hw (n : ℕ) : ∃ (ε : ℝ) (μ : MassRatio) (x : Configuration),
      0 < ε ∧ ε < min 1 (1/((n:ℝ)+1)) ∧ PositiveRatio μ ∧
      NormalizedCentralConfiguration (masses ε μ) x ∧ η ≤ |pairDistance x 0 i-1| :=
    h (min 1 (1/((n:ℝ)+1))) (lt_min (by norm_num) (by positivity))
  choose ε μ x hε hεsmall hμ hx hbad using hw
  let m : ℕ → MassVector := fun n => masses (ε n) (μ n)
  have hm : ∀ n, PositiveMasses (m n) := fun n => masses_positive _ _ (hε n) (hμ n)
  have hεone : ∀ n, ε n ≤ 1 := fun n =>
    ((hεsmall n).trans_le (min_le_left _ _)).le
  have hεt : Tendsto ε atTop (nhds 0) :=
    squeeze_zero (fun n => (hε n).le)
      (fun n => ((hεsmall n).trans_le (min_le_right _ _)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hmt := dominant_masses_tendsto_primary ε μ hε hμ hεt
  let R := 4*Real.rpow 2 (1/3)
  have hR : 0 ≤ R := mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  have hbounded : ∀ n, x n ∈ Metric.closedBall (0 : Configuration) R := by
    intro n
    rw [Metric.mem_closedBall,dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro j
    have hM : totalMass (m n) ≤ 2 := by
      rw [totalMass_masses (ε n) (μ n) (hμ n)]
      linarith [hεone n]
    exact (normalized_position_norm_le (m n) (hm n) (x n) (hx n) j).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (totalMass_pos (m n) (hm n)).le hM (by norm_num)) (by norm_num))
  obtain ⟨xLimit,_,φ,hφ,hxt⟩ := (isCompact_closedBall (0 : Configuration) R).tendsto_subseq hbounded
  have hmφ : ∀ n, PositiveMasses ((m ∘ φ) n) := fun n => hm (φ n)
  have hxφ : ∀ n, NormalizedCentralConfiguration ((m ∘ φ) n) ((x ∘ φ) n) := fun n => hx (φ n)
  have hmtφ := hmt.comp hφ.tendsto_atTop
  have hx0 := normalized_primary_limit_zero (m ∘ φ) (x ∘ φ) hxφ hmtφ xLimit hxt
  have hgeom : Tendsto (fun n => pairDistance (x (φ n)) 0 i) atTop
      (nhds (pairDistance xLimit 0 i)) := by
    simpa [pairDistance,Function.comp_def] using
      (((continuous_apply (0 : Label)).tendsto xLimit |>.comp hxt).sub
        ((continuous_apply i).tendsto xLimit |>.comp hxt)).norm
  have hc : xLimit i ≠ 0 := by
    obtain ⟨b,hb,hbound⟩ := dominant_primary_separation_for_label 1 (by norm_num) i hi
    have hlo : b ≤ pairDistance xLimit 0 i := ge_of_tendsto hgeom
      (Filter.Eventually.of_forall (fun n => hbound (ε (φ n)) (μ (φ n)) (x (φ n))
        (hε (φ n)) (hεone (φ n)) (hμ (φ n)) (hx (φ n))))
    intro hzero
    simp [pairDistance,hx0,hzero] at hlo
    linarith
  let S : Finset Label := Finset.univ.filter (fun j => xLimit j = xLimit i)
  have hS : S.Nonempty := ⟨i,by simp [S]⟩
  have hC : CompleteLimitingCluster xLimit S (xLimit i) := by intro j; simp [S]
  have hunit := satellite_complete_cluster_limit_unit (m ∘ φ) (x ∘ φ) hmφ hxφ hmtφ
    xLimit hxt S hS (xLimit i) hc hC
  have hdistance : pairDistance xLimit 0 i = 1 := by simpa [pairDistance,hx0] using hunit
  have herr : Tendsto (fun n => |pairDistance (x (φ n)) 0 i-1|) atTop (nhds 0) := by
    simpa [hdistance] using (hgeom.sub_const 1).abs
  have hcontr : η ≤ 0 := ge_of_tendsto herr (Filter.Eventually.of_forall (fun n => hbad (φ n)))
  exact (not_le.mpr hη) hcontr

/-- Full uniform convergence of all four primary-relative radii in the
original Proposition 4.1. The `δ` comes before every positive ratio and root. -/
theorem dominant_primary_relative_radii_uniform (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ) (μ : MassRatio) (x : Configuration),
      0 < ε → ε < δ → PositiveRatio μ →
      NormalizedCentralConfiguration (masses ε μ) x →
      ∀ i : Satellite, |‖satellitesRelative x i‖-1| < η := by
  obtain ⟨d1,h1,hd1⟩ := dominant_radius_uniform_for_label 1 (by decide) η hη
  obtain ⟨d2,h2,hd2⟩ := dominant_radius_uniform_for_label 2 (by decide) η hη
  obtain ⟨d3,h3,hd3⟩ := dominant_radius_uniform_for_label 3 (by decide) η hη
  obtain ⟨d4,h4,hd4⟩ := dominant_radius_uniform_for_label 4 (by decide) η hη
  let δ := min d1 (min d2 (min d3 d4))
  have hδd1 : δ ≤ d1 := min_le_left _ _
  have hδd2 : δ ≤ d2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδd3 : δ ≤ d3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd4 : δ ≤ d4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ,lt_min h1 (lt_min h2 (lt_min h3 h4)),?_⟩
  intro ε μ x hε hεδ hμ hx i
  have hdist : pairDistance x 0 i.succ = ‖satellitesRelative x i‖ := by
    exact norm_sub_rev _ _
  rw [← hdist]
  fin_cases i
  · exact hd1 ε μ x hε (hεδ.trans_le hδd1) hμ hx
  · exact hd2 ε μ x hε (hεδ.trans_le hδd2) hμ hx
  · exact hd3 ε μ x hε (hεδ.trans_le hδd3) hμ hx
  · exact hd4 ε μ x hε (hεδ.trans_le hδd4) hμ hx

/-- The complete uniform span assertion `eq:span` for actual five-body
solutions, in every original directed hull order. Both constants precede
all positive mass ratios; the polar gauge is constructed geometrically. -/
theorem dominant_strictConvex_uniform_polar_span :
    ∃ (eta eps0 : ℝ),0<eta ∧ 0<eps0 ∧
      ∀ (eps : ℝ) (mu : MassRatio) (sigma : HullOrder) (x : Configuration),
      0<eps → eps<eps0 → PositiveRatio mu →
      NormalizedCentralConfiguration (masses eps mu) x → StrictConvexInOrder sigma x →
      ∃ (r theta : Satellite → ℝ) (phi : ℝ),
        (∀ i,0<r i) ∧ theta 0=0 ∧
        (∀ i j,i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi) ∧
        (∀ i,x (sigma.labels i.succ)-x 0=polarPoint (r i) (theta i+phi)) ∧
        (∀ i,angularResidual eps (mu ∘ hullSatellitePermutation sigma) r theta i=0) ∧
        eta≤theta 3 ∧ theta 3≤Real.pi-eta := by
  obtain ⟨eta,heta,hmargin⟩ := uniform_ordered_angular_margin_near_unit
  obtain ⟨delta,hdelta,hradii⟩ := dominant_primary_relative_radii_uniform eta heta
  refine ⟨eta,min eta delta,heta,lt_min heta hdelta,?_⟩
  intro eps mu sigma x heps hepssmall hm hx hconv
  obtain ⟨r,theta,phi,hr,hzero,horder,hpolar,hroot⟩ :=
    normalized_strictConvex_ordered_angular_rep eps mu sigma x heps hm hx hconv
  have hrclose (i : Satellite) : |r i-1|<eta := by
    have hi := hradii eps mu x heps (hepssmall.trans_le (min_le_right _ _)) hm hx
      (hullSatellitePermutation sigma i)
    have hq : satellitesRelative x (hullSatellitePermutation sigma i)=
        x (sigma.labels i.succ)-x 0 := by
      unfold satellitesRelative primaryRelative
      rw [hullSatellitePermutation_succ]
    rw [hq,hpolar i,polarPoint_norm,abs_of_pos (hr i)] at hi
    exact hi
  have hspan := hmargin eps (mu ∘ hullSatellitePermutation sigma) r theta heps
    (hepssmall.trans_le (min_le_left _ _)) (positiveRatio_hull_reindex mu sigma hm)
    hr hzero horder hroot hrclose
  exact ⟨r,theta,phi,hr,hzero,horder,hpolar,hroot,hspan⟩

/-- Uniform unit-radius control for any actual polar representation in the
original hull order. This transports the physical relative radii without
identifying them with the barycentric polar coordinates. -/
theorem dominant_given_polar_radii_uniform (eta : ℝ) (heta : 0<eta) :
    ∃ delta : ℝ,0<delta ∧
      ∀ (eps : ℝ) (mu : MassRatio) (sigma : HullOrder) (x : Configuration)
        (r theta : Satellite → ℝ) (phi : ℝ),
      0<eps → eps<delta → PositiveRatio mu →
      NormalizedCentralConfiguration (masses eps mu) x → (∀ i,0<r i) →
      (∀ i,x (sigma.labels i.succ)-x 0=polarPoint (r i) (theta i+phi)) →
      ∀ i,|r i-1|<eta := by
  obtain ⟨delta,hdelta,hradii⟩ := dominant_primary_relative_radii_uniform eta heta
  refine ⟨delta,hdelta,?_⟩
  intro eps mu sigma x r theta phi heps hepssmall hm hx hr hpolar i
  have hi := hradii eps mu x heps hepssmall hm hx (hullSatellitePermutation sigma i)
  have hq : satellitesRelative x (hullSatellitePermutation sigma i)=
      x (sigma.labels i.succ)-x 0 := by
    unfold satellitesRelative primaryRelative
    rw [hullSatellitePermutation_succ]
  rw [hq,hpolar i,polarPoint_norm,abs_of_pos (hr i)] at hi
  exact hi

/-- The actual sequence assertion in Proposition 4.1: each consecutive
angular gap has limsup at most h=pi/3. All current mass ratios and directed
hull orders may vary with n. No convergent positive mass fractions, chart
capture, or prior collision classification is assumed. -/
theorem dominant_ordered_polar_gap_limsup
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (sigma : ℕ → HullOrder)
    (x : ℕ → Configuration) (r theta : ℕ → Satellite → ℝ) (phi : ℕ → ℝ)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hr : ∀ n,∀ i,0<r n i) (hzero : ∀ n,theta n 0=0)
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (hpolar : ∀ n,∀ i,x n ((sigma n).labels i.succ)-x n 0=
      polarPoint (r n i) (theta n i+phi n)) (k : Fin 3) :
    Filter.limsup (fun n => theta n k.succ-theta n k.castSucc) atTop≤Real.pi/3 := by
  have hk : k.castSucc<k.succ := by simp
  have hlo : atTop.IsCoboundedUnder (·≤·) (fun n => theta n k.succ-theta n k.castSucc) :=
    Filter.isCoboundedUnder_le_of_le atTop (fun n : ℕ => (horder n _ _ hk).1.le)
  have hhi : atTop.IsBoundedUnder (·≤·) (fun n => theta n k.succ-theta n k.castSucc) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall (fun n : ℕ => (horder n _ _ hk).2.le))
  apply (Filter.limsup_le_iff hlo hhi).mpr
  intro y hy
  obtain ⟨delta,hdelta,hgap⟩ := uniform_ordered_consecutive_gaps_near_unit
    (y-Real.pi/3) (by linarith)
  obtain ⟨radDelta,hradDelta,hradii⟩ := dominant_given_polar_radii_uniform delta hdelta
  have hsmall := hepst.eventually (Iio_mem_nhds hdelta)
  have hrsmall := hepst.eventually (Iio_mem_nhds hradDelta)
  filter_upwards [hsmall,hrsmall] with n hn hrn
  have hroot := normalized_polar_gauge_angular_rows (eps n) (mu n) (sigma n) (x n)
    (heps n) (hm n) (hx n) (r n) (theta n) (phi n) (hr n) (hpolar n)
  have hclose := hradii (eps n) (mu n) (sigma n) (x n) (r n) (theta n) (phi n)
    (heps n) hrn (hm n) (hx n) (hr n) (hpolar n)
  have hbound := hgap (eps n) (mu n ∘ hullSatellitePermutation (sigma n)) (r n) (theta n)
    (heps n) hn (positiveRatio_hull_reindex (mu n) (sigma n) (hm n))
    (hr n) (hzero n) (horder n) hroot hclose k
  linarith

/-- Full Proposition 4.1, with the physical uniform estimates and the actual
sequence limsup assertion bundled without any extra research hypotheses.
The polar representation is constructed from all five-point strict convexity;
the last field applies to every such given gauge and every directed order. -/
theorem dominant_uniform_geometry_complete :
    (∀ (eps : ℝ) (mu : MassRatio),0<eps → PositiveRatio mu → ∀ x : Configuration,
      NormalizedCentralConfiguration (masses eps mu) x →
      Metric.diam (Set.range x)≤4*Real.rpow (1+eps) (1/3)) ∧
    (∀ E : ℝ,0<E → ∃ b : ℝ,0<b ∧ ∀ (eps : ℝ) (mu : MassRatio) (x : Configuration),
      0<eps → eps≤E → PositiveRatio mu →
      NormalizedCentralConfiguration (masses eps mu) x →
      ∀ i : Satellite,b≤‖satellitesRelative x i‖) ∧
    (∀ eta : ℝ,0<eta → ∃ delta : ℝ,0<delta ∧
      ∀ (eps : ℝ) (mu : MassRatio) (x : Configuration),
      0<eps → eps<delta → PositiveRatio mu →
      NormalizedCentralConfiguration (masses eps mu) x →
      ∀ i : Satellite,|‖satellitesRelative x i‖-1|<eta) ∧
    (∃ (eta eps0 : ℝ),0<eta ∧ 0<eps0 ∧
      ∀ (eps : ℝ) (mu : MassRatio) (sigma : HullOrder) (x : Configuration),
      0<eps → eps<eps0 → PositiveRatio mu →
      NormalizedCentralConfiguration (masses eps mu) x → StrictConvexInOrder sigma x →
      ∃ (r theta : Satellite → ℝ) (phi : ℝ),
        (∀ i,0<r i) ∧ theta 0=0 ∧
        (∀ i j,i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi) ∧
        (∀ i,x (sigma.labels i.succ)-x 0=polarPoint (r i) (theta i+phi)) ∧
        (∀ i,angularResidual eps (mu ∘ hullSatellitePermutation sigma) r theta i=0) ∧
        eta≤theta 3 ∧ theta 3≤Real.pi-eta) ∧
    (∀ (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (sigma : ℕ → HullOrder)
      (x : ℕ → Configuration) (r theta : ℕ → Satellite → ℝ) (phi : ℕ → ℝ),
      (∀ n,0<eps n) → Tendsto eps atTop (nhds 0) →
      (∀ n,PositiveRatio (mu n)) →
      (∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n)) →
      (∀ n,∀ i,0<r n i) → (∀ n,theta n 0=0) →
      (∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi) →
      (∀ n,∀ i,x n ((sigma n).labels i.succ)-x n 0=
        polarPoint (r n i) (theta n i+phi n)) →
      ∀ k : Fin 3,Filter.limsup (fun n => theta n k.succ-theta n k.castSucc) atTop≤Real.pi/3) := by
  exact ⟨dominant_normalized_diameter_le,dominant_primary_relative_radius_lower,
    dominant_primary_relative_radii_uniform,dominant_strictConvex_uniform_polar_span,
    dominant_ordered_polar_gap_limsup⟩

end DominantFiveBody
