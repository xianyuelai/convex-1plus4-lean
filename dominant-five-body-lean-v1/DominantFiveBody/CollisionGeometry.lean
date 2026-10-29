import DominantFiveBody.ForceBalance
import DominantFiveBody.ShapeDimension
import DominantFiveBody.Residuals
import DominantFiveBody.ResidualEquivalence
import DominantFiveBody.PolarCoordinates
import DominantFiveBody.HullOrderTransport
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

/-! Actual multiplier-one force identities and uniform geometry for §4,
Proposition `prop:uniform`. No lower bound on satellite mass fractions is used.
Cluster averages always use the current masses. -/

noncomputable section
open scoped BigOperators
open Filter Topology

namespace DominantFiveBody

def clusterMass (m : MassVector) (S : Finset Label) : ℝ := ∑ i ∈ S, m i

def clusterPosition (m : MassVector) (x : Configuration) (S : Finset Label) : Plane :=
  ∑ i ∈ S, m i • x i

def clusterCrossForce (m : MassVector) (x : Configuration) (S : Finset Label) : Plane :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, pairForce m x i j

theorem clusterMass_pos (m : MassVector) (hm : PositiveMasses m)
    (S : Finset Label) (hS : S.Nonempty) : 0 < clusterMass m S := by
  exact Finset.sum_pos (fun i _ => hm i) hS

theorem clusterMass_add_compl (m : MassVector) (S : Finset Label) :
    clusterMass m S + clusterMass m Sᶜ = totalMass m := by
  exact Finset.sum_add_sum_compl S (fun i => m i)

theorem clusterPosition_add_compl (m : MassVector) (x : Configuration)
    (S : Finset Label) :
    clusterPosition m x S + clusterPosition m x Sᶜ = weightedPosition m x := by
  exact Finset.sum_add_sum_compl S (fun i => m i • x i)

/-- §4: internal forces cancel in any current cluster, including arbitrarily
small masses. This is algebraic cancellation, not a collision regularization. -/
theorem cluster_internal_force_zero (m : MassVector) (x : Configuration)
    (S : Finset Label) : (∑ i ∈ S, ∑ j ∈ S, pairForce m x i j) = 0 := by
  have hn : (∑ i ∈ S, ∑ j ∈ S, pairForce m x i j) =
      -(∑ i ∈ S, ∑ j ∈ S, pairForce m x i j) := by
    calc
      _ = ∑ j ∈ S, ∑ i ∈ S, pairForce m x i j := Finset.sum_comm
      _ = -(∑ j ∈ S, ∑ i ∈ S, pairForce m x j i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact pairForce_reverse m x j i
  have ht : (2 : ℝ) • (∑ i ∈ S, ∑ j ∈ S, pairForce m x i j) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hn
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

theorem cluster_weighted_acceleration (m : MassVector) (x : Configuration)
    (S : Finset Label) :
    (∑ i ∈ S, m i • acceleration m x i) = clusterCrossForce m x S := by
  simp_rw [weighted_acceleration_as_pair_sum]
  have heq (i : Label) : (∑ j, pairForce m x i j) =
      (∑ j ∈ S, pairForce m x i j) + (∑ j ∈ Sᶜ, pairForce m x i j) :=
    (Finset.sum_add_sum_compl S (fun j => pairForce m x i j)).symm
  simp_rw [heq]
  rw [Finset.sum_add_distrib, cluster_internal_force_zero, zero_add]
  rfl

/-- §4 Proposition `prop:uniform`: exact cross-force identity at actual
centered multiplier-one solutions. -/
theorem normalized_cluster_cross_force (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) (S : Finset Label) :
    clusterCrossForce m x S = -clusterPosition m x S := by
  rw [← cluster_weighted_acceleration]
  simp only [hx.2.2, smul_neg, Finset.sum_neg_distrib, clusterPosition]

theorem pairDistance_reverse (x : Configuration) (i j : Label) :
    pairDistance x j i = pairDistance x i j := norm_sub_rev _ _

/-- A unit projection of a physical pair force is bounded by inverse-square
distance; positivity/nonzero distance are proved at the use site. -/
theorem projected_pairForce_le (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (e : Plane) (he : ‖e‖ = 1) (i j : Label)
    (g : ℝ) (hg : 0 < g) (hgap : g ≤ pairDistance x i j) :
    inner ℝ e (pairForce m x i j) ≤ m i * m j / g ^ 2 := by
  have hd : 0 < pairDistance x i j := lt_of_lt_of_le hg hgap
  have hmi := hm i
  have hmj := hm j
  have hcoef : 0 ≤ m i * m j / pairDistance x i j ^ 3 := by positivity
  have hp := real_inner_le_norm e (x j - x i)
  rw [he, one_mul, norm_sub_rev] at hp
  have hfirst : inner ℝ e (pairForce m x i j) ≤
      (m i * m j / pairDistance x i j ^ 3) * pairDistance x i j := by
    rw [pairForce, real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left hp hcoef
  have hsimp : (m i * m j / pairDistance x i j ^ 3) * pairDistance x i j =
      m i * m j / pairDistance x i j ^ 2 := by
    field_simp [ne_of_gt hd]
  rw [hsimp] at hfirst
  apply hfirst.trans
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

theorem weighted_projection_separation (m : MassVector) (p : Label → ℝ)
    (S : Finset Label) :
    (∑ i ∈ S, ∑ j ∈ Sᶜ, m i * m j * (p j - p i)) =
      clusterMass m S * (∑ j ∈ Sᶜ, m j * p j) -
        clusterMass m Sᶜ * (∑ i ∈ S, m i * p i) := by
  calc
    _ = ∑ i ∈ S, ∑ j ∈ Sᶜ,
        (m i * (m j * p j) - (m i * p i) * m j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i ∈ S, m i) * (∑ j ∈ Sᶜ, m j * p j) -
        (∑ i ∈ S, m i * p i) * (∑ j ∈ Sᶜ, m j) := by
      simp_rw [Finset.sum_sub_distrib]
      rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
    _ = _ := by unfold clusterMass; ring

/-- The projected center separation times both CURRENT cluster masses,
computed directly from the physical normalized equations. -/
theorem normalized_weighted_separation (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) (S : Finset Label) (e : Plane) :
    (∑ i ∈ S, ∑ j ∈ Sᶜ, m i * m j * inner ℝ e (x j - x i)) =
      totalMass m * inner ℝ e (clusterCrossForce m x S) := by
  have hz : (∑ i, m i * inner ℝ e (x i)) = 0 := by
    simpa [weightedPosition, inner_sum, real_inner_smul_right] using
      congrArg (fun v => inner ℝ e v) hx.2.1
  have hp : (∑ i ∈ S, m i * inner ℝ e (x i)) +
      (∑ i ∈ Sᶜ, m i * inner ℝ e (x i)) = 0 := by
    rw [Finset.sum_add_sum_compl]
    exact hz
  simp_rw [inner_sub_right]
  rw [weighted_projection_separation]
  rw [normalized_cluster_cross_force m x hx, inner_neg_right]
  simp only [clusterPosition, inner_sum, real_inner_smul_right]
  rw [← clusterMass_add_compl m S]
  have hPB : (∑ i ∈ Sᶜ, m i * inner ℝ e (x i)) =
      -(∑ i ∈ S, m i * inner ℝ e (x i)) := by linarith
  rw [hPB]
  ring

theorem projected_crossForce_le (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (e : Plane) (he : ‖e‖ = 1) (S : Finset Label)
    (g : ℝ) (hg : 0 < g)
    (hgap : ∀ i ∈ S, ∀ j ∈ Sᶜ, g ≤ inner ℝ e (x j - x i)) :
    inner ℝ e (clusterCrossForce m x S) ≤
      clusterMass m S * clusterMass m Sᶜ / g ^ 2 := by
  have hdist (i : Label) (hi : i ∈ S) (j : Label) (hj : j ∈ Sᶜ) :
      g ≤ pairDistance x i j := by
    have hproj := real_inner_le_norm e (x j - x i)
    rw [he, one_mul, norm_sub_rev] at hproj
    exact (hgap i hi j hj).trans hproj
  calc
    inner ℝ e (clusterCrossForce m x S) =
        ∑ i ∈ S, ∑ j ∈ Sᶜ, inner ℝ e (pairForce m x i j) := by
      simp [clusterCrossForce, inner_sum]
    _ ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, m i * m j / g ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact projected_pairForce_le m hm x e he i j g hg (hdist i hi j hj)
    _ = _ := by
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
      rw [← Finset.sum_mul_sum]
      rfl

/-- §4 Proposition `prop:uniform`: every nonempty separated projection cut
of an actual positive-mass multiplier-one configuration has `g³ ≤ M`.
No individual or cluster mass lower bound enters this inequality. -/
theorem normalized_projection_gap_cube_le (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x)
    (e : Plane) (he : ‖e‖ = 1) (S : Finset Label)
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (g : ℝ) (hg : 0 < g)
    (hgap : ∀ i ∈ S, ∀ j ∈ Sᶜ, g ≤ inner ℝ e (x j - x i)) :
    g ^ 3 ≤ totalMass m := by
  have hma := clusterMass_pos m hm S hS
  have hmb := clusterMass_pos m hm Sᶜ hSc
  have hM := totalMass_pos m hm
  have hsep : g * (clusterMass m S * clusterMass m Sᶜ) ≤
      ∑ i ∈ S, ∑ j ∈ Sᶜ, m i * m j * inner ℝ e (x j - x i) := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ Sᶜ, m i * m j * g := by
        unfold clusterMass
        rw [Finset.sum_mul_sum]
        simp_rw [← Finset.sum_mul]
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hgap i hi j hj) (mul_pos (hm i) (hm j)).le
  rw [normalized_weighted_separation m x hx S e] at hsep
  have hupper := projected_crossForce_le m hm x e he S g hg hgap
  have hc := hsep.trans (mul_le_mul_of_nonneg_left hupper hM.le)
  have hcancel : g ≤ totalMass m / g ^ 2 := by
    have hrew : totalMass m * (clusterMass m S * clusterMass m Sᶜ / g ^ 2) =
        (totalMass m / g ^ 2) * (clusterMass m S * clusterMass m Sᶜ) := by ring
    rw [hrew] at hc
    exact le_of_mul_le_mul_right hc (mul_pos hma hmb)
  have hmul := (le_div_iff₀ (show 0 < g ^ 2 by positivity)).mp hcancel
  nlinarith

/-- A five point projection has one of its four adjacent gaps at least one
quarter of the total span. This finite pigeonhole estimate is exact. -/
theorem five_projection_large_gap (v : Label → ℝ) :
    ∃ k : Satellite, (v 4 - v 0) / 4 ≤ v k.succ - v k.castSucc := by
  by_contra h
  push Not at h
  have h0 := h (0 : Satellite)
  have h1 := h (1 : Satellite)
  have h2 := h (2 : Satellite)
  have h3 := h (3 : Satellite)
  norm_num at h0 h1 h2 h3
  change v 3 - v 2 < (v 4 - v 0) / 4 at h2
  change v 4 - v 3 < (v 4 - v 0) / 4 at h3
  linarith

/-- §4 Proposition `prop:uniform`: the actual equations give the uniform
diameter-cube bound. Arbitrarily small positive satellite fractions are allowed. -/
theorem normalized_pairDistance_cube_le (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x) (a b : Label) :
    pairDistance x a b ^ 3 ≤ 64 * totalMass m := by
  have hM := totalMass_pos m hm
  by_cases hab : a = b
  · subst b
    simp only [pairDistance, sub_self, norm_zero, zero_pow (by decide : 3 ≠ 0)]
    positivity
  have hd : 0 < ‖x b - x a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hx.1 b a (Ne.symm hab)))
  let D := ‖x b - x a‖
  let e : Plane := D⁻¹ • (x b - x a)
  have he : ‖e‖ = 1 := by
    simp only [e, D, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd]
    exact inv_mul_cancel₀ (ne_of_gt hd)
  let p : Label → ℝ := fun i => inner ℝ e (x i)
  have hdiff : p b - p a = D := by
    rw [← inner_sub_right]
    simp only [e, real_inner_smul_left, real_inner_self_eq_norm_sq]
    dsimp [D]
    field_simp
  let σ := Tuple.sort p
  let v : Label → ℝ := p ∘ σ
  have hmono : Monotone v := Tuple.monotone_sort p
  have hmin : v 0 ≤ p a := by
    simpa [v] using hmono (show (0 : Label) ≤ σ.symm a from Fin.zero_le _)
  have hmax : p b ≤ v 4 := by
    have hfin : σ.symm b ≤ (4 : Label) := by omega
    simpa [v] using hmono hfin
  have hspan : D ≤ v 4 - v 0 := by linarith
  obtain ⟨k, hk⟩ := five_projection_large_gap v
  let g : ℝ := v k.succ - v k.castSucc
  have hDg : D ≤ 4 * g := by dsimp [g]; linarith
  have hg : 0 < g := by linarith
  let S : Finset Label := Finset.univ.filter (fun i => σ.symm i ≤ k.castSucc)
  have hS : S.Nonempty := by
    refine ⟨σ k.castSucc, ?_⟩
    simp [S]
  have hSc : Sᶜ.Nonempty := by
    refine ⟨σ k.succ, ?_⟩
    simp [S]
  have hgap : ∀ i ∈ S, ∀ j ∈ Sᶜ, g ≤ inner ℝ e (x j - x i) := by
    intro i hi j hj
    have hil : σ.symm i ≤ k.castSucc := by simpa [S] using hi
    have hjr : k.succ ≤ σ.symm j := by
      have hj' : ¬σ.symm j ≤ k.castSucc := by simpa [S] using hj
      change ¬(σ.symm j).val ≤ k.val at hj'
      change k.val + 1 ≤ (σ.symm j).val
      omega
    have hleft : p i ≤ v k.castSucc := by simpa [v] using hmono hil
    have hright : v k.succ ≤ p j := by simpa [v] using hmono hjr
    change g ≤ inner ℝ e (x j - x i)
    rw [inner_sub_right]
    change g ≤ p j - p i
    dsimp [g]
    linarith
  have hc := normalized_projection_gap_cube_le m hm x hx e he S hS hSc g hg hgap
  have hp := pow_le_pow_left₀ hd.le hDg 3
  have hrew : (4 * g) ^ 3 = 64 * g ^ 3 := by ring
  rw [hrew] at hp
  have hdist : pairDistance x a b = D := norm_sub_rev _ _
  rw [hdist]
  linarith

/-- Cube-root version of the full five-body uniform diameter estimate. -/
theorem normalized_pairDistance_le (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x) (a b : Label) :
    pairDistance x a b ≤ 4 * Real.rpow (totalMass m) (1 / 3) := by
  have hM := totalMass_pos m hm
  have hc := normalized_pairDistance_cube_le m hm x hx a b
  have hroot : (Real.rpow (totalMass m) (1 / 3)) ^ 3 = totalMass m := by
    simpa using Real.rpow_inv_natCast_pow hM.le (by decide : (3 : ℕ) ≠ 0)
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hM.le _))
  calc
    _ ≤ 64 * totalMass m := hc
    _ = (4 * Real.rpow (totalMass m) (1 / 3)) ^ 3 := by rw [mul_pow, hroot]; norm_num

/-- Proposition `prop:uniform`, with diameter taken over all five actual positions. -/
theorem normalized_diameter_le (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x) :
    Metric.diam (Set.range x) ≤ 4 * Real.rpow (totalMass m) (1 / 3) := by
  apply Metric.diam_le_of_forall_dist_le
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (totalMass_pos m hm).le _))
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  simpa [pairDistance, dist_eq_norm] using normalized_pairDistance_le m hm x hx a b

/-- The manuscript's diameter bound with primary mass one and total satellite
mass `ε`; its quantifiers include every positive ratio. -/
theorem dominant_normalized_diameter_le (ε : ℝ) (μ : MassRatio)
    (hε : 0 < ε) (hμ : PositiveRatio μ) (x : Configuration)
    (hx : NormalizedCentralConfiguration (masses ε μ) x) :
    Metric.diam (Set.range x) ≤ 4 * Real.rpow (1 + ε) (1 / 3) := by
  simpa [totalMass_masses ε μ hμ] using
    normalized_diameter_le (masses ε μ) (masses_positive ε μ hε hμ) x hx

/-- Centering converts the uniform pair bound into a bound on every actual
position. This supplies compactness without a lower bound on any mass ratio. -/
theorem normalized_position_norm_le (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x) (i : Label) :
    ‖x i‖ ≤ 4 * Real.rpow (totalMass m) (1 / 3) := by
  have hM := totalMass_pos m hm
  have hweighted : (∑ j, m j • (x i-x j)) = totalMass m • x i := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul]
    change totalMass m • x i - weightedPosition m x = _
    rw [hx.2.1, sub_zero]
  have hnorm : ‖totalMass m • x i‖ ≤
      ∑ j, m j * (4 * Real.rpow (totalMass m) (1 / 3)) := by
    rw [← hweighted]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hm j)]
    exact mul_le_mul_of_nonneg_left (normalized_pairDistance_le m hm x hx i j) (hm j).le
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hM, ← Finset.sum_mul] at hnorm
  exact le_of_mul_le_mul_left hnorm hM

theorem satelliteDistance_common_angle (r theta : Satellite → ℝ) (phi : ℝ)
    (i j : Satellite) :
    satelliteDistance (polarSatellites r (fun k => theta k+phi)) i j =
      satelliteDistance (polarSatellites r theta) i j := by
  unfold satelliteDistance polarSatellites
  have h1 := polar_distance_sq (r j) (r i) (theta j+phi) (theta i+phi)
  have h2 := polar_distance_sq (r j) (r i) (theta j) (theta i)
  have hangle : theta i+phi-(theta j+phi)=theta i-theta j := by ring
  rw [hangle] at h1
  nlinarith [norm_nonneg (polarPoint (r i) (theta i+phi)-polarPoint (r j) (theta j+phi)),
    norm_nonneg (polarPoint (r i) (theta i)-polarPoint (r j) (theta j))]

theorem angularResidual_common_angle (eps : ℝ) (mu r theta : Satellite → ℝ)
    (phi : ℝ) (i : Satellite) :
    angularResidual eps mu r (fun k => theta k+phi) i=angularResidual eps mu r theta i := by
  unfold angularResidual
  apply Finset.sum_congr rfl
  intro j _
  rw [satelliteDistance_common_angle]
  have he : theta j+phi-(theta i+phi)=theta j-theta i := by ring
  rw [he]

def fullAngularMatrix (ε : ℝ) (r θ : Satellite → ℝ) : Matrix Satellite Satellite ℝ :=
  fun i j => r i*r j*Real.sin (θ j-θ i)*
    ((satelliteDistance (polarSatellites r θ) i j^3)⁻¹-(1+ε)⁻¹)

theorem fullAngularMatrix_reverse (ε : ℝ) (r θ : Satellite → ℝ) (i j : Satellite) :
    fullAngularMatrix ε r θ j i = -fullAngularMatrix ε r θ i j := by
  have ht : θ i-θ j=-(θ j-θ i) := by ring
  have hd : satelliteDistance (polarSatellites r θ) j i =
      satelliteDistance (polarSatellites r θ) i j := norm_sub_rev _ _
  simp only [fullAngularMatrix,ht,Real.sin_neg,hd]
  ring

@[simp] theorem fullAngularMatrix_self (ε : ℝ) (r θ : Satellite → ℝ) (i : Satellite) :
    fullAngularMatrix ε r θ i i = 0 := by simp [fullAngularMatrix]

theorem angularResidual_eq_full_matrix_sum (ε : ℝ) (μ r θ : Satellite → ℝ) (i : Satellite) :
    angularResidual ε μ r θ i = ∑ j, μ j*fullAngularMatrix ε r θ i j := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [fullAngularMatrix_self,mul_zero,add_zero]
  unfold angularResidual
  apply Finset.sum_congr rfl
  intro j _
  unfold fullAngularMatrix
  ring

def fullAngularPair (ε : ℝ) (μ r θ : Satellite → ℝ) (i j : Satellite) : ℝ :=
  μ i*μ j*fullAngularMatrix ε r θ i j

theorem fullAngularPair_reverse (ε : ℝ) (μ r θ : Satellite → ℝ) (i j : Satellite) :
    fullAngularPair ε μ r θ j i = -fullAngularPair ε μ r θ i j := by
  unfold fullAngularPair
  rw [fullAngularMatrix_reverse]
  ring

/-- The source's full variational cut identity, for every subset and every
actual angular root, follows from pair cancellation before any mass division. -/
theorem full_angular_cut (ε : ℝ) (μ r θ : Satellite → ℝ)
    (hroot : ∀ i, angularResidual ε μ r θ i=0) (S : Finset Satellite) :
    (∑ i ∈ S, ∑ j ∈ Sᶜ, fullAngularPair ε μ r θ i j) = 0 := by
  have hin : (∑ i ∈ S, ∑ j ∈ S, fullAngularPair ε μ r θ i j)=0 := by
    have hn : (∑ i ∈ S, ∑ j ∈ S, fullAngularPair ε μ r θ i j)=
        -(∑ i ∈ S, ∑ j ∈ S, fullAngularPair ε μ r θ i j) := by
      calc
        _ = ∑ j ∈ S, ∑ i ∈ S, fullAngularPair ε μ r θ i j := Finset.sum_comm
        _ = -(∑ j ∈ S, ∑ i ∈ S, fullAngularPair ε μ r θ j i) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          exact fullAngularPair_reverse ε μ r θ j i
    linarith
  have hsum : (∑ i ∈ S, μ i*angularResidual ε μ r θ i)=
      (∑ i ∈ S, ∑ j ∈ S, fullAngularPair ε μ r θ i j)+
        (∑ i ∈ S, ∑ j ∈ Sᶜ, fullAngularPair ε μ r θ i j) := by
    simp_rw [angularResidual_eq_full_matrix_sum,Finset.mul_sum,← mul_assoc]
    change (∑ i ∈ S, ∑ j, fullAngularPair ε μ r θ i j)=_
    simp_rw [← Finset.sum_add_sum_compl S (fun j => fullAngularPair ε μ r θ _ j)]
    rw [Finset.sum_add_distrib]
  simp only [hroot,mul_zero,Finset.sum_const_zero,hin,zero_add] at hsum
  exact hsum.symm

/-- A separated ordered angular cut cannot have all its physical distances
above the sign-change distance. Positivity may be arbitrarily small. -/
theorem full_angular_cut_excludes_large_cross_distances
    (ε : ℝ) (hε : 0 < ε) (μ r θ : Satellite → ℝ)
    (hμ : ∀ i, 0 < μ i) (hr : ∀ i, 0 < r i)
    (hroot : ∀ i, angularResidual ε μ r θ i=0)
    (S : Finset Satellite) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (hangle : ∀ i ∈ S, ∀ j ∈ Sᶜ, 0 < θ j-θ i ∧ θ j-θ i < Real.pi)
    (hdist : ∀ i ∈ S, ∀ j ∈ Sᶜ,
      1+ε < satelliteDistance (polarSatellites r θ) i j^3) : False := by
  have hpair : ∀ i ∈ S, ∀ j ∈ Sᶜ, fullAngularPair ε μ r θ i j < 0 := by
    intro i hi j hj
    have hsin := Real.sin_pos_of_pos_of_lt_pi (hangle i hi j hj).1 (hangle i hi j hj).2
    have hdpos : 0 < satelliteDistance (polarSatellites r θ) i j^3 :=
      lt_trans (by linarith) (hdist i hi j hj)
    have hinv : (satelliteDistance (polarSatellites r θ) i j^3)⁻¹ < (1+ε)⁻¹ :=
      (inv_lt_inv₀ hdpos (by linarith)).mpr (hdist i hi j hj)
    unfold fullAngularPair fullAngularMatrix
    have hp : 0 < μ i*μ j*(r i*r j*Real.sin (θ j-θ i)) :=
      mul_pos (mul_pos (hμ i) (hμ j)) (mul_pos (mul_pos (hr i) (hr j)) hsin)
    have hn := mul_neg_of_pos_of_neg hp (sub_neg.mpr hinv)
    simpa only [mul_assoc] using hn
  have hsum : (∑ i ∈ S, ∑ j ∈ Sᶜ, fullAngularPair ε μ r θ i j) < 0 := by
    apply Finset.sum_neg _ hS
    intro i hi
    exact Finset.sum_neg (fun j hj => hpair i hi j hj) hSc
  rw [full_angular_cut ε μ r θ hroot S] at hsum
  exact (lt_irrefl 0) hsum

theorem polar_distance_pos (r s a b : ℝ) (hr : 0<r) (hs : 0<s)
    (hangle : 0<b-a ∧ b-a<Real.pi) :
    0<‖polarPoint s b-polarPoint r a‖ := by
  have hsin := Real.sin_pos_of_pos_of_lt_pi
    (show 0<(b-a)/2 by linarith) (show (b-a)/2<Real.pi by linarith [Real.pi_pos])
  have hsq := polar_distance_sq r s a b
  have hp : 0<4*r*s*Real.sin ((b-a)/2)^2 := by positivity
  nlinarith [norm_nonneg (polarPoint s b-polarPoint r a),sq_nonneg (s-r)]

/-- The complementary cut sign excludes angular collapse. Distances and
their cubes are proved strictly positive before comparing real inverses. -/
theorem full_angular_cut_excludes_small_cross_distances
    (ε : ℝ) (hε : 0<ε) (μ r θ : Satellite → ℝ)
    (hμ : ∀ i,0<μ i) (hr : ∀ i,0<r i)
    (hroot : ∀ i,angularResidual ε μ r θ i=0)
    (S : Finset Satellite) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (hangle : ∀ i∈S,∀ j∈Sᶜ,0<θ j-θ i ∧ θ j-θ i<Real.pi)
    (hdist : ∀ i∈S,∀ j∈Sᶜ,
      satelliteDistance (polarSatellites r θ) i j^3<1+ε) : False := by
  have hpair : ∀ i∈S,∀ j∈Sᶜ,0<fullAngularPair ε μ r θ i j := by
    intro i hi j hj
    have hsin := Real.sin_pos_of_pos_of_lt_pi (hangle i hi j hj).1 (hangle i hi j hj).2
    have hdpos : 0<satelliteDistance (polarSatellites r θ) i j^3 := by
      have hp := polar_distance_pos (r i) (r j) (θ i) (θ j) (hr i) (hr j) (hangle i hi j hj)
      rw [norm_sub_rev] at hp
      exact pow_pos hp _
    have hinv : (1+ε)⁻¹<(satelliteDistance (polarSatellites r θ) i j^3)⁻¹ :=
      (inv_lt_inv₀ (by linarith) hdpos).mpr (hdist i hi j hj)
    unfold fullAngularPair fullAngularMatrix
    have hp : 0<μ i*μ j*(r i*r j*Real.sin (θ j-θ i)) :=
      mul_pos (mul_pos (hμ i) (hμ j)) (mul_pos (mul_pos (hr i) (hr j)) hsin)
    have hn := mul_pos hp (sub_pos.mpr hinv)
    simpa only [mul_assoc] using hn
  have hsum : 0<(∑ i∈S,∑ j∈Sᶜ,fullAngularPair ε μ r θ i j) := by
    apply Finset.sum_pos _ hS
    intro i hi
    exact Finset.sum_pos (fun j hj => hpair i hi j hj) hSc
  rw [full_angular_cut ε μ r θ hroot S] at hsum
  exact (lt_irrefl 0) hsum

theorem polarPoint_continuous : Continuous (fun p : ℝ×ℝ => polarPoint p.1 p.2) := by
  unfold polarPoint point
  fun_prop

theorem unit_polar_distance_cube_gt_one (a b : ℝ)
    (hgap : Real.pi/3 < b-a) (hspan : b-a ≤ Real.pi) :
    1 < ‖polarPoint 1 b-polarPoint 1 a‖^3 := by
  have hsin := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (show -(Real.pi/2) ≤ Real.pi/6 by linarith [Real.pi_pos])
    (show (b-a)/2 ≤ Real.pi/2 by linarith)
    (show Real.pi/6 < (b-a)/2 by linarith)
  rw [Real.sin_pi_div_six] at hsin
  have hsq := polar_distance_sq 1 1 a b
  norm_num at hsq
  have hnorm : 1 < ‖polarPoint 1 b-polarPoint 1 a‖ := by
    nlinarith [norm_nonneg (polarPoint 1 b-polarPoint 1 a)]
  exact one_lt_pow₀ hnorm (by decide : (3 : ℕ) ≠ 0)

/-- The source's gap-limsup estimate at any selected convergent angle
subsequence. It comes from the genuine full angular equations and unit-radius
limits, with no positive lower bound on any satellite mass fraction. -/
theorem full_angular_cut_limit_gap_le
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεt : Tendsto ε atTop (nhds 0))
    (μ r θ : ℕ → Satellite → ℝ) (hμ : ∀ n i, 0 < μ n i) (hr : ∀ n i, 0 < r n i)
    (hroot : ∀ n i, angularResidual (ε n) (μ n) (r n) (θ n) i=0)
    (rLimit θLimit : Satellite → ℝ) (hrLimit : ∀ i, rLimit i=1)
    (hrt : Tendsto r atTop (nhds rLimit)) (hθt : Tendsto θ atTop (nhds θLimit))
    (S : Finset Satellite) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (hangle : ∀ n, ∀ i ∈ S, ∀ j ∈ Sᶜ, 0 < θ n j-θ n i ∧ θ n j-θ n i < Real.pi)
    (g : ℝ) (hgap : ∀ i ∈ S, ∀ j ∈ Sᶜ, g ≤ θLimit j-θLimit i) :
    g ≤ Real.pi/3 := by
  by_contra hbad
  have hg : Real.pi/3 < g := lt_of_not_ge hbad
  have hdist : ∀ᶠ n in atTop, ∀ i ∈ S, ∀ j ∈ Sᶜ,
      1+ε n < satelliteDistance (polarSatellites (r n) (θ n)) i j^3 := by
    apply (Finset.eventually_all S).mpr
    intro i hi
    apply (Finset.eventually_all Sᶜ).mpr
    intro j hj
    have htij : Tendsto (fun n => θ n j-θ n i) atTop (nhds (θLimit j-θLimit i)) :=
      ((continuous_apply j).tendsto θLimit |>.comp hθt).sub
        ((continuous_apply i).tendsto θLimit |>.comp hθt)
    have hpi : θLimit j-θLimit i ≤ Real.pi :=
      le_of_tendsto htij (Filter.Eventually.of_forall (fun n => (hangle n i hi j hj).2.le))
    have hcube : 1 < ‖polarPoint 1 (θLimit j)-polarPoint 1 (θLimit i)‖^3 :=
      unit_polar_distance_cube_gt_one _ _ (hg.trans_le (hgap i hi j hj)) hpi
    have hp (k : Satellite) : Tendsto (fun n => polarPoint (r n k) (θ n k)) atTop
        (nhds (polarPoint 1 (θLimit k))) := by
      have hpdata := ((continuous_apply k).tendsto rLimit |>.comp hrt).prodMk_nhds
        ((continuous_apply k).tendsto θLimit |>.comp hθt)
      simpa [Function.comp_def,hrLimit k] using polarPoint_continuous.tendsto (rLimit k,θLimit k) |>.comp hpdata
    have hpair : Tendsto (fun n => satelliteDistance (polarSatellites (r n) (θ n)) i j^3)
        atTop (nhds (‖polarPoint 1 (θLimit j)-polarPoint 1 (θLimit i)‖^3)) := by
      simpa [satelliteDistance,polarSatellites,norm_sub_rev] using ((hp j).sub (hp i)).norm.pow 3
    have hdiff := hpair.sub ((tendsto_const_nhds (x := (1 : ℝ))).add hεt)
    have hpositive := hdiff.eventually (isOpen_Ioi.mem_nhds
      (show 0 < ‖polarPoint 1 (θLimit j)-polarPoint 1 (θLimit i)‖^3-(1+0) by linarith))
    filter_upwards [hpositive] with n hn
    exact sub_pos.mp hn
  obtain ⟨n,hn⟩ := hdist.exists
  exact full_angular_cut_excludes_large_cross_distances (ε n) (hε n) (μ n) (r n) (θ n)
    (hμ n) (hr n) (hroot n) S hS hSc (hangle n) hn

/-- Complex coordinates used only to select the principal angle. The physical
plane remains the Euclidean plane from `Definitions`. -/
def planeComplex (v : Plane) : ℂ := ⟨v 0,v 1⟩

theorem planeComplex_norm (v : Plane) : ‖planeComplex v‖=‖v‖ := by
  have hc := Complex.sq_norm (planeComplex v)
  have hv := EuclideanSpace.real_norm_sq_eq v
  rw [Fin.sum_univ_two] at hv
  simp only [planeComplex,Complex.normSq_apply] at hc
  change ‖planeComplex v‖^2=v 0*v 0+v 1*v 1 at hc
  nlinarith [norm_nonneg (planeComplex v),norm_nonneg v]

theorem planeComplex_eq_zero_iff (v : Plane) : planeComplex v=0 ↔ v=0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    rw [← planeComplex_norm,h,norm_zero]
  · rintro rfl
    rfl

theorem planeComplex_det_im (u v : Plane) :
    (star (planeComplex u)*planeComplex v).im=det2 u v := by
  simp only [planeComplex,Complex.star_def,Complex.mul_im,Complex.conj_re,Complex.conj_im,det2]
  ring

theorem complex_quotient_det_im (z w a : ℂ) :
    (star (z/a)*(w/a)).im=(star z*w).im/Complex.normSq a := by
  have he : star (z/a)*(w/a)=(star z*w)/(Complex.normSq a : ℂ) := by
    simp only [Complex.star_def,map_div₀,div_mul_div_comm,Complex.normSq_eq_conj_mul_self]
  rw [he,Complex.div_ofReal_im]

theorem complex_arg_pos_of_im_pos (z : ℂ) (h : 0<z.im) :
    0<z.arg ∧ z.arg<Real.pi := by
  have hn : 0≤z.arg := Complex.arg_nonneg_iff.mpr h.le
  have hz : z.arg≠0 := by
    intro he
    exact h.ne' (Complex.arg_eq_zero_iff.mp he).2
  exact ⟨lt_of_le_of_ne hn (Ne.symm hz),Complex.arg_lt_pi_iff.mpr (Or.inr h.ne')⟩

theorem complex_det_im_arg (z w : ℂ) :
    (star z*w).im=‖z‖*‖w‖*Real.sin (w.arg-z.arg) := by
  rw [Real.sin_sub]
  calc
    _ = (‖z‖*Real.cos z.arg)*(‖w‖*Real.sin w.arg)-
      (‖z‖*Real.sin z.arg)*(‖w‖*Real.cos w.arg) := by
      simp only [Complex.star_def,Complex.mul_im,Complex.conj_re,Complex.conj_im,
        Complex.norm_mul_cos_arg,Complex.norm_mul_sin_arg]
      ring
    _ = _ := by ring

theorem complex_arg_lt_of_det_pos (z w : ℂ)
    (hz : 0≤z.arg ∧ z.arg<Real.pi) (hw : 0≤w.arg ∧ w.arg<Real.pi)
    (hdet : 0<(star z*w).im) : z.arg<w.arg := by
  by_contra hbad
  have hle : w.arg-z.arg≤0 := by linarith [le_of_not_gt hbad]
  have hpi : -Real.pi≤w.arg-z.arg := by linarith
  have hs := Real.sin_nonpos_of_nonpos_of_neg_pi_le hle hpi
  rw [complex_det_im_arg] at hdet
  have hn := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (norm_nonneg z) (norm_nonneg w)) hs
  linarith

theorem planeComplex_polar_product (v a : Plane) (ha : a≠0) :
    v=polarPoint ‖v‖ ((planeComplex v/planeComplex a).arg+(planeComplex a).arg) := by
  have hza : planeComplex a≠0 := mt (planeComplex_eq_zero_iff a).mp ha
  have hzprod : planeComplex v=(planeComplex v/planeComplex a)*planeComplex a :=
    (div_mul_cancel₀ _ hza).symm
  have hn : ‖planeComplex v‖=‖planeComplex v/planeComplex a‖*‖planeComplex a‖ := by
    conv_lhs => rw [hzprod]
    exact norm_mul _ _
  ext i
  fin_cases i
  · change v 0=‖v‖*Real.cos ((planeComplex v/planeComplex a).arg+(planeComplex a).arg)
    rw [Real.cos_add,← planeComplex_norm,hn]
    calc
      v 0=((planeComplex v/planeComplex a)*planeComplex a).re := congrArg Complex.re hzprod
      _ = _ := by
        rw [Complex.mul_re]
        simp only [← Complex.norm_mul_cos_arg,← Complex.norm_mul_sin_arg]
        ring
  · change v 1=‖v‖*Real.sin ((planeComplex v/planeComplex a).arg+(planeComplex a).arg)
    rw [Real.sin_add,← planeComplex_norm,hn]
    calc
      v 1=((planeComplex v/planeComplex a)*planeComplex a).im := congrArg Complex.im hzprod
      _ = _ := by
        rw [Complex.mul_im]
        simp only [← Complex.norm_mul_cos_arg,← Complex.norm_mul_sin_arg]
        ring

/-- The true geometric polar-order bridge in Proposition `prop:uniform`.
The hull includes the primary, and its original permutation is retained.
The common angle `phi` is a rotation gauge, never a reflection or a relabeling
of the physical configuration. -/
theorem strictConvexInOrder_exists_ordered_polar (σ : HullOrder) (x : Configuration)
    (hconv : StrictConvexInOrder σ x) (hcollision : CollisionFree x) :
    ∃ (r theta : Satellite → ℝ) (phi : ℝ),
      (∀ i,0<r i) ∧ theta 0=0 ∧
      (∀ i j, i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi) ∧
      (∀ i, x (σ.labels i.succ)-x 0=polarPoint (r i) (theta i+phi)) := by
  let q : Satellite → Plane := fun i => x (σ.labels i.succ)-x 0
  have hq (i : Satellite) : q i≠0 := by
    apply sub_ne_zero.mpr
    apply hcollision
    intro he
    have hh : σ.labels i.succ=σ.labels 0 := he.trans σ.primary_first.symm
    have hf := σ.labels.injective hh
    exact Fin.succ_ne_zero i hf
  have hfirst (i : Satellite) (hi : i≠0) : 0<det2 (q 0) (q i) := by
    have hside := hconv 0 i.succ (Fin.succ_ne_zero i) (by
      intro he
      have he' : i.succ=(0 : Satellite).succ := by
        simpa only [show (0 : Label)+1=(0 : Satellite).succ from rfl] using he
      have hv : i=0 := Fin.succ_injective _ he'
      exact hi hv)
    simpa only [orientedArea,σ.primary_first,q,
      show (0 : Label)+1=(0 : Satellite).succ from rfl] using hside
  have hnext (i : Fin 3) : 0<det2 (q i.castSucc) (q i.succ) := by
    have he : (i.castSucc.succ : Label)+1=i.succ.succ := by fin_cases i <;> rfl
    have hside := hconv i.castSucc.succ 0 (by fin_cases i <;> decide) (by
      rw [he]
      fin_cases i <;> decide)
    rw [he] at hside
    simp only [orientedArea,σ.primary_first,det2,PiLp.sub_apply] at hside
    dsimp only [q,det2]
    simp only [PiLp.sub_apply]
    nlinarith
  let z : Satellite → ℂ := fun i => planeComplex (q i)/planeComplex (q 0)
  let theta : Satellite → ℝ := fun i => (z i).arg
  have hzero : theta 0=0 := Complex.arg_div_self _
  have ha : planeComplex (q 0)≠0 := mt (planeComplex_eq_zero_iff _).mp (hq 0)
  have htheta (i : Satellite) : 0≤theta i ∧ theta i<Real.pi := by
    by_cases hi : i=0
    · subst i
      rw [hzero]
      exact ⟨le_rfl,Real.pi_pos⟩
    · have him : 0<(z i).im := by
        rw [show z i=planeComplex (q i)/planeComplex (q 0) from rfl,Complex.div_im]
        have hp := Complex.normSq_pos.mpr ha
        have heq : (planeComplex (q i)).im*(planeComplex (q 0)).re/Complex.normSq (planeComplex (q 0))-
          (planeComplex (q i)).re*(planeComplex (q 0)).im/Complex.normSq (planeComplex (q 0))=
          det2 (q 0) (q i)/Complex.normSq (planeComplex (q 0)) := by
          unfold planeComplex det2
          ring
        rw [heq]
        exact div_pos (hfirst i hi) hp
      exact ⟨(complex_arg_pos_of_im_pos _ him).1.le,(complex_arg_pos_of_im_pos _ him).2⟩
  have hmono : StrictMono theta := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    apply complex_arg_lt_of_det_pos _ _ (htheta _) (htheta _)
    dsimp only [z]
    rw [complex_quotient_det_im,planeComplex_det_im]
    exact div_pos (hnext i) (Complex.normSq_pos.mpr ha)
  refine ⟨fun i => ‖q i‖,theta,(planeComplex (q 0)).arg,
    fun i => norm_pos_iff.mpr (hq i),hzero,?_,?_⟩
  · intro i j hij
    exact ⟨sub_pos.mpr (hmono hij),by linarith [(htheta i).1,(htheta j).2]⟩
  · intro i
    exact planeComplex_polar_product (q i) (q 0) (hq 0)

theorem masses_hull_reindex (eps : ℝ) (mu : MassRatio) (σ : HullOrder) :
    masses eps (mu ∘ hullSatellitePermutation σ)=(masses eps mu) ∘ σ.labels := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [σ.primary_first,masses]
  · simp only [Function.comp_apply,← hullSatellitePermutation_succ σ j,
      masses_satellite]

theorem positiveRatio_hull_reindex (mu : MassRatio) (σ : HullOrder) (hm : PositiveRatio mu) :
    PositiveRatio (mu ∘ hullSatellitePermutation σ) := by
  exact ⟨fun i => hm.1 _,(Equiv.sum_comp _ mu).trans hm.2⟩

theorem acceleration_eq_full_sum (m : MassVector) (x : Configuration) (i : Label) :
    acceleration m x i=∑ j, (m j/pairDistance x i j^3) • (x j-x i) := by
  unfold acceleration
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp only [sub_self,smul_zero,sub_zero]

/-- Positions and masses are transported together. This is a change of
labels for proving the specified order, not part of similarity uniqueness. -/
theorem acceleration_reindex (m : MassVector) (x : Configuration)
    (e : Equiv.Perm Label) (i : Label) :
    acceleration (m ∘ e) (x ∘ e) i=acceleration m x (e i) := by
  rw [acceleration_eq_full_sum,acceleration_eq_full_sum]
  exact Equiv.sum_comp e (fun j => (m j/pairDistance x (e i) j^3) • (x j-x (e i)))

theorem normalized_reindex (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) (e : Equiv.Perm Label) :
    NormalizedCentralConfiguration (m ∘ e) (x ∘ e) := by
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    exact hx.1 (e i) (e j) (e.injective.ne hij)
  · unfold weightedPosition
    exact (Equiv.sum_comp e (fun j => m j • x j)).trans hx.2.1
  · intro i
    rw [acceleration_reindex]
    exact hx.2.2 (e i)

/-- Proposition `prop:uniform`: actual strictly convex normalized roots admit
the source's ordered polar gauge and satisfy every divided angular row in
that gauge. All four original mass fractions are transported explicitly. -/
theorem normalized_strictConvex_ordered_angular_rep (eps : ℝ) (mu : MassRatio)
    (σ : HullOrder) (x : Configuration) (heps : 0<eps) (hm : PositiveRatio mu)
    (hx : NormalizedCentralConfiguration (masses eps mu) x)
    (hconv : StrictConvexInOrder σ x) :
    ∃ (r theta : Satellite → ℝ) (phi : ℝ),
      (∀ i,0<r i) ∧ theta 0=0 ∧
      (∀ i j, i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi) ∧
      (∀ i, x (σ.labels i.succ)-x 0=polarPoint (r i) (theta i+phi)) ∧
      (∀ i, angularResidual eps (mu ∘ hullSatellitePermutation σ) r theta i=0) := by
  obtain ⟨r,theta,phi,hr,hzero,horder,hpolar⟩ :=
    strictConvexInOrder_exists_ordered_polar σ x hconv hx.1
  have hx' : NormalizedCentralConfiguration (masses eps (mu ∘ hullSatellitePermutation σ))
      (x ∘ σ.labels) := by
    rw [masses_hull_reindex]
    exact normalized_reindex _ _ hx _
  have hpolar' : satellitesRelative (x ∘ σ.labels)=polarSatellites r (fun i => theta i+phi) := by
    funext i
    simpa only [satellitesRelative,primaryRelative,Function.comp_apply,σ.primary_first,
      polarSatellites] using hpolar i
  have hroot := (polarResiduals_zero_of_normalized eps (mu ∘ hullSatellitePermutation σ)
    (x ∘ σ.labels) hx' (positiveRatio_hull_reindex mu σ hm) heps r
    (fun i => theta i+phi) hr hpolar').2
  refine ⟨r,theta,phi,hr,hzero,horder,hpolar,?_⟩
  intro i
  rw [← angularResidual_common_angle eps (mu ∘ hullSatellitePermutation σ) r theta phi i]
  exact hroot i

/-- The zero-span endpoint in Proposition `prop:uniform` is excluded by the
actual angular cut, even when all satellite mass fractions can tend to zero.
There is no inverse-distance limit at the collision. -/
theorem full_angular_cut_limit_angles_not_constant
    (eps : ℕ → ℝ) (heps : ∀ n,0<eps n)
    (mu r theta : ℕ → Satellite → ℝ) (hm : ∀ n i,0<mu n i) (hr : ∀ n i,0<r n i)
    (hroot : ∀ n i,angularResidual (eps n) (mu n) (r n) (theta n) i=0)
    (rLimit thetaLimit : Satellite → ℝ) (hrLimit : ∀ i,rLimit i=1)
    (hrt : Tendsto r atTop (nhds rLimit)) (htt : Tendsto theta atTop (nhds thetaLimit))
    (S : Finset Satellite) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (hangle : ∀ n,∀ i∈S,∀ j∈Sᶜ,0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (c : ℝ) (hconstant : ∀ i,thetaLimit i=c) : False := by
  have hdist : ∀ᶠ n in atTop,∀ i∈S,∀ j∈Sᶜ,
      satelliteDistance (polarSatellites (r n) (theta n)) i j^3<1+eps n := by
    apply (Finset.eventually_all S).mpr
    intro i hi
    apply (Finset.eventually_all Sᶜ).mpr
    intro j hj
    have hp (k : Satellite) : Tendsto (fun n => polarPoint (r n k) (theta n k))
        atTop (nhds (polarPoint 1 c)) := by
      have hd := ((continuous_apply k).tendsto rLimit |>.comp hrt).prodMk_nhds
        ((continuous_apply k).tendsto thetaLimit |>.comp htt)
      simpa only [Function.comp_def,hrLimit k,hconstant k] using
        polarPoint_continuous.tendsto (rLimit k,thetaLimit k) |>.comp hd
    have hd : Tendsto (fun n => satelliteDistance (polarSatellites (r n) (theta n)) i j^3)
        atTop (nhds 0) := by
      simpa [satelliteDistance,polarSatellites]
        using ((hp i).sub (hp j)).norm.pow 3
    have hsmall := hd.eventually (isOpen_Iio.mem_nhds (show (0:ℝ)<1 by norm_num))
    filter_upwards [hsmall] with n hn
    exact hn.trans (by linarith [heps n])
  obtain ⟨n,hn⟩ := hdist.exists
  exact full_angular_cut_excludes_small_cross_distances (eps n) (heps n)
    (mu n) (r n) (theta n) (hm n) (hr n) (hroot n) S hS hSc (hangle n) hn

theorem ordered_angle_limits_monotone (theta : ℕ → Satellite → ℝ)
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (thetaLimit : Satellite → ℝ) (htt : Tendsto theta atTop (nhds thetaLimit)) :
    Monotone thetaLimit := by
  intro i j hij
  rcases hij.eq_or_lt with he|hlt
  · exact he ▸ le_rfl
  · have ht := ((continuous_apply j).tendsto thetaLimit |>.comp htt).sub
      ((continuous_apply i).tendsto thetaLimit |>.comp htt)
    exact sub_nonneg.mp (ge_of_tendsto ht (Filter.Eventually.of_forall
      (fun n => (horder n i j hlt).1.le)))

theorem ordered_full_angular_limit_span_pos
    (eps : ℕ → ℝ) (heps : ∀ n,0<eps n)
    (mu r theta : ℕ → Satellite → ℝ) (hm : ∀ n i,0<mu n i) (hr : ∀ n i,0<r n i)
    (hroot : ∀ n i,angularResidual (eps n) (mu n) (r n) (theta n) i=0)
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (rLimit thetaLimit : Satellite → ℝ) (hrLimit : ∀ i,rLimit i=1)
    (hrt : Tendsto r atTop (nhds rLimit)) (htt : Tendsto theta atTop (nhds thetaLimit)) :
    0<thetaLimit 3-thetaLimit 0 := by
  have hmono := ordered_angle_limits_monotone theta horder thetaLimit htt
  by_contra hbad
  have hsame : thetaLimit 3=thetaLimit 0 := by
    linarith [hmono (show (0 : Satellite)≤3 by decide),le_of_not_gt hbad]
  have hc (i : Satellite) : thetaLimit i=thetaLimit 0 := by
    have hlo := hmono (Fin.zero_le i)
    have hhi := hmono (Fin.le_last i)
    change thetaLimit i≤thetaLimit 3 at hhi
    linarith
  apply full_angular_cut_limit_angles_not_constant eps heps mu r theta hm hr hroot
    rLimit thetaLimit hrLimit hrt htt ({0} : Finset Satellite)
    (by simp) (by exact ⟨1,by decide⟩) ?_ (thetaLimit 0) hc
  intro n i hi j hj
  have hi0 : i=0 := Finset.mem_singleton.mp hi
  subst i
  have hj0 : j≠0 := by simpa only [Finset.mem_compl,Finset.mem_singleton] using hj
  exact horder n 0 j (lt_of_le_of_ne (Fin.zero_le j) (Ne.symm hj0))

/-- Each original consecutive gap satisfies the manuscript's bound on every
selected convergent subsequence of actual angular roots. -/
theorem ordered_full_angular_limit_consecutive_gap_le
    (eps : ℕ → ℝ) (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (mu r theta : ℕ → Satellite → ℝ) (hm : ∀ n i,0<mu n i) (hr : ∀ n i,0<r n i)
    (hroot : ∀ n i,angularResidual (eps n) (mu n) (r n) (theta n) i=0)
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (rLimit thetaLimit : Satellite → ℝ) (hrLimit : ∀ i,rLimit i=1)
    (hrt : Tendsto r atTop (nhds rLimit)) (htt : Tendsto theta atTop (nhds thetaLimit)) :
    ∀ k : Fin 3, thetaLimit k.succ-thetaLimit k.castSucc≤Real.pi/3 := by
  have hmono := ordered_angle_limits_monotone theta horder thetaLimit htt
  intro k
  let S : Finset Satellite := Finset.univ.filter (fun i => i≤k.castSucc)
  have hS : S.Nonempty := ⟨0,by simp [S]⟩
  have hSc : Sᶜ.Nonempty := by
    refine ⟨3,?_⟩
    simp only [Finset.mem_compl,S,Finset.mem_filter,Finset.mem_univ,true_and]
    change ¬(3 : ℕ)≤k.val
    have hk := k.isLt
    omega
  apply full_angular_cut_limit_gap_le eps heps hepst mu r theta hm hr hroot
    rLimit thetaLimit hrLimit hrt htt S hS hSc ?_
    (thetaLimit k.succ-thetaLimit k.castSucc) ?_
  · intro n i hi j hj
    have hi' : i≤k.castSucc := (Finset.mem_filter.mp hi).2
    have hj' : k.castSucc<j := by
      apply lt_of_not_ge
      intro hle
      exact (Finset.mem_compl.mp hj) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hle⟩)
    exact horder n i j (lt_of_le_of_lt hi' hj')
  · intro i hi j hj
    have hi' : i≤k.castSucc := (Finset.mem_filter.mp hi).2
    have hj' : k.succ≤j := by
      have hbad : ¬j≤k.castSucc := by
        intro hle
        exact (Finset.mem_compl.mp hj) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hle⟩)
      change ¬j.val≤k.val at hbad
      change k.val+1≤j.val
      omega
    linarith [hmono hi',hmono hj']

theorem unit_polar_chord_closed (a b : ℝ) (hangle : 0≤b-a ∧ b-a≤Real.pi) :
    ‖polarPoint 1 b-polarPoint 1 a‖=2*Real.sin ((b-a)/2) := by
  have hs : 0≤Real.sin ((b-a)/2) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith) (by linarith [Real.pi_pos])
  have hsq := polar_distance_sq 1 1 a b
  norm_num at hsq
  nlinarith [norm_nonneg (polarPoint 1 b-polarPoint 1 a)]

theorem fullAngularMatrix_unit_positive_gap (theta : Satellite → ℝ) (i j : Satellite)
    (hangle : 0≤theta j-theta i ∧ theta j-theta i≤Real.pi) :
    fullAngularMatrix 0 (fun _ => 1) theta i j=Coorbital.kernelF (theta j-theta i) := by
  have hd : satelliteDistance (polarSatellites (fun _ => 1) theta) i j=
      2*Real.sin ((theta j-theta i)/2) := by
    rw [satelliteDistance,polarSatellites,norm_sub_rev]
    exact unit_polar_chord_closed _ _ hangle
  simp only [fullAngularMatrix,hd,Coorbital.kernelF,one_mul,mul_one,add_zero,inv_one,inv_pow]

/-- The span-pi boundary matrix has trivial kernel even for signed masses.
In particular, zero limiting satellite masses do not invalidate the source's
boundary contradiction. The proof uses all four actual unweighted rows. -/
theorem no_full_angular_unit_root_at_pi (mu theta : Satellite → ℝ)
    (hsum : ∑ i,mu i=1)
    (hgaps : theta 1-theta 0≤Real.pi/3 ∧ theta 2-theta 1≤Real.pi/3 ∧
      theta 3-theta 2≤Real.pi/3)
    (hspan : theta 3-theta 0=Real.pi)
    (hroot : ∀ i,angularResidual 0 mu (fun _ => 1) theta i=0) : False := by
  let h : ℝ := Real.pi/3
  have hh : 0<h := by dsimp [h]; positivity
  have hthree : 3*h=Real.pi := by dsimp [h]; ring
  have h01 : theta 1-theta 0=h := by dsimp [h] at *; linarith [hgaps.1,hgaps.2.1,hgaps.2.2]
  have h12 : theta 2-theta 1=h := by dsimp [h] at *; linarith [hgaps.1,hgaps.2.1,hgaps.2.2]
  have h23 : theta 3-theta 2=h := by dsimp [h] at *; linarith [hgaps.1,hgaps.2.1,hgaps.2.2]
  have h02 : theta 2-theta 0=2*h := by linarith
  have h13 : theta 3-theta 1=2*h := by linarith
  let M := fullAngularMatrix 0 (fun _ => 1) theta
  have hdiag (i : Satellite) : M i i=0 := fullAngularMatrix_self _ _ _ _
  have hreverse (i j : Satellite) : M j i= -M i j := fullAngularMatrix_reverse _ _ _ _ _
  have hz01 : M 0 1=0 := by
    rw [show M 0 1=Coorbital.kernelF (theta 1-theta 0) from
      fullAngularMatrix_unit_positive_gap theta 0 1 ⟨by linarith,by linarith⟩,h01]
    exact Coorbital.kernelF_h
  have hz12 : M 1 2=0 := by
    rw [show M 1 2=Coorbital.kernelF (theta 2-theta 1) from
      fullAngularMatrix_unit_positive_gap theta 1 2 ⟨by linarith,by linarith⟩,h12]
    exact Coorbital.kernelF_h
  have hz23 : M 2 3=0 := by
    rw [show M 2 3=Coorbital.kernelF (theta 3-theta 2) from
      fullAngularMatrix_unit_positive_gap theta 2 3 ⟨by linarith,by linarith⟩,h23]
    exact Coorbital.kernelF_h
  have hz03 : M 0 3=0 := by
    rw [show M 0 3=Coorbital.kernelF (theta 3-theta 0) from
      fullAngularMatrix_unit_positive_gap theta 0 3 ⟨by linarith,by linarith⟩,hspan]
    exact Coorbital.kernelF_pi
  have hn02 : M 0 2≠0 := by
    rw [show M 0 2=Coorbital.kernelF (theta 2-theta 0) from
      fullAngularMatrix_unit_positive_gap theta 0 2 ⟨by linarith,by linarith⟩,h02]
    exact ne_of_lt (Coorbital.kernelF_neg_on_long_arc (by change Real.pi/3<2*h; linarith)
      (by linarith))
  have hn13 : M 1 3≠0 := by
    rw [show M 1 3=Coorbital.kernelF (theta 3-theta 1) from
      fullAngularMatrix_unit_positive_gap theta 1 3 ⟨by linarith,by linarith⟩,h13]
    exact ne_of_lt (Coorbital.kernelF_neg_on_long_arc (by change Real.pi/3<2*h; linarith)
      (by linarith))
  have hz10 : M 1 0=0 := by rw [hreverse,hz01,neg_zero]
  have hz21 : M 2 1=0 := by rw [hreverse,hz12,neg_zero]
  have hz32 : M 3 2=0 := by rw [hreverse,hz23,neg_zero]
  have hz30 : M 3 0=0 := by rw [hreverse,hz03,neg_zero]
  have hn20 : M 2 0≠0 := by rw [hreverse]; exact neg_ne_zero.mpr hn02
  have hn31 : M 3 1≠0 := by rw [hreverse]; exact neg_ne_zero.mpr hn13
  have hrows (i : Satellite) : ∑ j,mu j*M i j=0 := by
    exact (angularResidual_eq_full_matrix_sum 0 mu (fun _ => 1) theta i).symm.trans (hroot i)
  have hmu2 : mu 2=0 := by
    have he := hrows 0
    rw [Fin.sum_univ_four] at he
    simp only [hdiag,hz01,hz03,mul_zero,zero_add,add_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hn02
  have hmu3 : mu 3=0 := by
    have he := hrows 1
    rw [Fin.sum_univ_four] at he
    simp only [hz10,hdiag,hz12,mul_zero,zero_add] at he
    exact (mul_eq_zero.mp he).resolve_right hn13
  have hmu0 : mu 0=0 := by
    have he := hrows 2
    rw [Fin.sum_univ_four] at he
    simp only [hz21,hdiag,hz23,mul_zero,add_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hn20
  have hmu1 : mu 1=0 := by
    have he := hrows 3
    rw [Fin.sum_univ_four] at he
    simp only [hz30,hz32,hdiag,mul_zero,zero_add,add_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hn31
  rw [Fin.sum_univ_four,hmu0,hmu1,hmu2,hmu3] at hsum
  norm_num at hsum

theorem fullAngularMatrix_tendsto
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (nhds 0))
    (r theta : ℕ → Satellite → ℝ) (rLimit thetaLimit : Satellite → ℝ)
    (hrt : Tendsto r atTop (nhds rLimit)) (htt : Tendsto theta atTop (nhds thetaLimit))
    (hsep : ∀ i j,i≠j → satelliteDistance (polarSatellites rLimit thetaLimit) i j≠0)
    (i j : Satellite) :
    Tendsto (fun n => fullAngularMatrix (eps n) (r n) (theta n) i j)
      atTop (nhds (fullAngularMatrix 0 rLimit thetaLimit i j)) := by
  by_cases hij : i=j
  · subst j
    simpa only [fullAngularMatrix_self] using (tendsto_const_nhds (x := (0 : ℝ)))
  · have hp (k : Satellite) : Tendsto (fun n => polarPoint (r n k) (theta n k))
        atTop (nhds (polarPoint (rLimit k) (thetaLimit k))) := by
      exact polarPoint_continuous.tendsto (rLimit k,thetaLimit k) |>.comp
        (((continuous_apply k).tendsto rLimit |>.comp hrt).prodMk_nhds
          ((continuous_apply k).tendsto thetaLimit |>.comp htt))
    have hd : Tendsto (fun n => satelliteDistance (polarSatellites (r n) (theta n)) i j^3)
        atTop (nhds (satelliteDistance (polarSatellites rLimit thetaLimit) i j^3)) := by
      exact ((hp i).sub (hp j)).norm.pow 3
    have hc : Tendsto (fun n => (1+eps n)⁻¹) atTop (nhds ((1+0 : ℝ)⁻¹)) :=
      ((tendsto_const_nhds (x := (1 : ℝ))).add heps).inv₀ (by norm_num)
    have hs := Real.continuous_sin.tendsto (thetaLimit j-thetaLimit i) |>.comp
      (((continuous_apply j).tendsto thetaLimit |>.comp htt).sub
        ((continuous_apply i).tendsto thetaLimit |>.comp htt))
    exact (((continuous_apply i).tendsto rLimit |>.comp hrt).mul
      ((continuous_apply j).tendsto rLimit |>.comp hrt)).mul hs |>.mul
      ((hd.inv₀ (pow_ne_zero _ (hsep i j hij))).sub hc)

/-- Taking limits of the genuine unweighted angular rows is valid whenever
all limiting physical distances are nonzero. Zero mass fractions are only
coefficients; no division by a limiting mass is performed. -/
theorem full_angular_roots_limit_separated
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (nhds 0))
    (mu r theta : ℕ → Satellite → ℝ) (muLimit rLimit thetaLimit : Satellite → ℝ)
    (hmt : Tendsto mu atTop (nhds muLimit)) (hrt : Tendsto r atTop (nhds rLimit))
    (htt : Tendsto theta atTop (nhds thetaLimit))
    (hroot : ∀ n i,angularResidual (eps n) (mu n) (r n) (theta n) i=0)
    (hsep : ∀ i j,i≠j → satelliteDistance (polarSatellites rLimit thetaLimit) i j≠0) :
    ∀ i,angularResidual 0 muLimit rLimit thetaLimit i=0 := by
  intro i
  rw [angularResidual_eq_full_matrix_sum]
  have hsum := tendsto_finsetSum Finset.univ (fun j _ =>
    ((continuous_apply j).tendsto muLimit |>.comp hmt).mul
      (fullAngularMatrix_tendsto eps heps r theta rLimit thetaLimit hrt htt hsep i j))
  have hzero : Tendsto (fun n => ∑ j,mu n j*fullAngularMatrix (eps n) (r n) (theta n) i j)
      atTop (nhds 0) := by
    have he n : (∑ j,mu n j*fullAngularMatrix (eps n) (r n) (theta n) i j)=0 := by
      rw [← angularResidual_eq_full_matrix_sum]
      exact hroot n i
    simpa only [he] using (tendsto_const_nhds (x := (0 : ℝ)))
  exact tendsto_nhds_unique hsum hzero

theorem unit_polar_distance_pos_closed (a b : ℝ) (hangle : 0<b-a ∧ b-a≤Real.pi) :
    0<‖polarPoint 1 b-polarPoint 1 a‖ := by
  rw [unit_polar_chord_closed a b ⟨hangle.1.le,hangle.2⟩]
  apply mul_pos (by norm_num)
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- The span-pi limit contradiction uses current roots, unit-radius limits,
and all four unweighted rows; no positive lower bound on the limiting mass
vector is introduced. This is the other endpoint of `eq:span`. -/
theorem ordered_full_angular_limit_span_lt_pi
    (eps : ℕ → ℝ) (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (mu r theta : ℕ → Satellite → ℝ) (hm : ∀ n i,0<mu n i) (hsum : ∀ n,∑ i,mu n i=1)
    (hr : ∀ n i,0<r n i)
    (hroot : ∀ n i,angularResidual (eps n) (mu n) (r n) (theta n) i=0)
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit rLimit thetaLimit : Satellite → ℝ) (hrLimit : ∀ i,rLimit i=1)
    (hmt : Tendsto mu atTop (nhds muLimit)) (hrt : Tendsto r atTop (nhds rLimit))
    (htt : Tendsto theta atTop (nhds thetaLimit)) :
    thetaLimit 3-thetaLimit 0<Real.pi := by
  have hspanle : thetaLimit 3-thetaLimit 0≤Real.pi := by
    have ht := ((continuous_apply 3).tendsto thetaLimit |>.comp htt).sub
      ((continuous_apply 0).tendsto thetaLimit |>.comp htt)
    exact le_of_tendsto ht (Filter.Eventually.of_forall
      (fun n => (horder n 0 3 (by decide)).2.le))
  by_contra hbad
  have hspan : thetaLimit 3-thetaLimit 0=Real.pi := le_antisymm hspanle (le_of_not_gt hbad)
  have hgap := ordered_full_angular_limit_consecutive_gap_le eps heps hepst mu r theta hm hr
    hroot horder rLimit thetaLimit hrLimit hrt htt
  have hgaps : thetaLimit 1-thetaLimit 0≤Real.pi/3 ∧ thetaLimit 2-thetaLimit 1≤Real.pi/3 ∧
      thetaLimit 3-thetaLimit 2≤Real.pi/3 := ⟨hgap 0,hgap 1,hgap 2⟩
  have hstrict : StrictMono thetaLimit := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro k
    fin_cases k
    · change thetaLimit 0<thetaLimit 1
      linarith [hgaps.1,hgaps.2.1,hgaps.2.2,Real.pi_pos]
    · change thetaLimit 1<thetaLimit 2
      linarith [hgaps.1,hgaps.2.1,hgaps.2.2,Real.pi_pos]
    · change thetaLimit 2<thetaLimit 3
      linarith [hgaps.1,hgaps.2.1,hgaps.2.2,Real.pi_pos]
  have hsep : ∀ i j,i≠j → satelliteDistance (polarSatellites rLimit thetaLimit) i j≠0 := by
    intro i j hij
    have hp (a b : Satellite) (hab : a<b) :
        0<satelliteDistance (polarSatellites rLimit thetaLimit) a b := by
      have hgapab : 0<thetaLimit b-thetaLimit a := sub_pos.mpr (hstrict hab)
      have hspab : thetaLimit b-thetaLimit a≤Real.pi := by
        have hlo := hstrict.monotone (Fin.zero_le a)
        have hhi := hstrict.monotone (Fin.le_last b)
        change thetaLimit b≤thetaLimit 3 at hhi
        linarith
      simpa only [satelliteDistance,polarSatellites,hrLimit,norm_sub_rev] using
        unit_polar_distance_pos_closed (thetaLimit a) (thetaLimit b) ⟨hgapab,hspab⟩
    rcases lt_or_gt_of_ne hij with hij'|hji'
    · exact ne_of_gt (hp i j hij')
    · have he : satelliteDistance (polarSatellites rLimit thetaLimit) i j=
          satelliteDistance (polarSatellites rLimit thetaLimit) j i := norm_sub_rev _ _
      rw [he]
      exact ne_of_gt (hp j i hji')
  have hrootLimit := full_angular_roots_limit_separated eps hepst mu r theta muLimit
    rLimit thetaLimit hmt hrt htt hroot hsep
  have hrone : rLimit=fun _ => 1 := funext hrLimit
  rw [hrone] at hrootLimit
  have hsumLimit : ∑ i,muLimit i=1 := by
    have ht := tendsto_finsetSum Finset.univ (fun i _ =>
      (continuous_apply i).tendsto muLimit |>.comp hmt)
    have hz : Tendsto (fun n => ∑ i,mu n i) atTop (nhds (1 : ℝ)) := by
      simpa only [hsum] using (tendsto_const_nhds (x := (1 : ℝ)))
    exact tendsto_nhds_unique ht hz
  exact no_full_angular_unit_root_at_pi muLimit thetaLimit hsumLimit hgaps hspan hrootLimit

/-- A genuine uniform angular margin near the unit-radius set. The one
constant precedes every positive mass vector; compactness includes the
closed mass simplex and its zero-mass faces. Proposition `prop:uniform`
uses the already proved physical uniform radius convergence to enter this
neighborhood, rather than assuming chart capture. -/
theorem uniform_ordered_angular_margin_near_unit :
    ∃ delta : ℝ, 0<delta ∧ ∀ (eps : ℝ) (mu r theta : Satellite → ℝ),
      0<eps → eps<delta → PositiveRatio mu → (∀ i,0<r i) → theta 0=0 →
      (∀ i j,i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi) →
      (∀ i,angularResidual eps mu r theta i=0) → (∀ i,|r i-1|<delta) →
      delta≤theta 3 ∧ theta 3≤Real.pi-delta := by
  by_contra h
  push Not at h
  have hw (n : ℕ) : ∃ (eps : ℝ) (mu r theta : Satellite → ℝ),
      0<eps ∧ eps<1/((n : ℝ)+1) ∧ PositiveRatio mu ∧ (∀ i,0<r i) ∧ theta 0=0 ∧
      (∀ i j,i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi) ∧
      (∀ i,angularResidual eps mu r theta i=0) ∧ (∀ i,|r i-1|<1/((n : ℝ)+1)) ∧
      (1/((n : ℝ)+1)≤theta 3 → Real.pi-1/((n : ℝ)+1)<theta 3) :=
    h (1/((n : ℝ)+1)) (by positivity)
  choose eps mu r theta heps hepssmall hm hr hzero horder hroot hrclose hbad using hw
  have hbound (n : ℕ) (i : Satellite) : 0≤theta n i ∧ theta n i≤Real.pi := by
    by_cases hi : i=0
    · subst i
      rw [hzero n]
      exact ⟨le_rfl,Real.pi_pos.le⟩
    · have ho := horder n 0 i (lt_of_le_of_ne (Fin.zero_le i) (Ne.symm hi))
      rw [hzero n,sub_zero] at ho
      exact ⟨ho.1.le,ho.2.le⟩
  let R : ℝ := Real.pi+1
  have hR : 0≤R := by dsimp [R]; linarith [Real.pi_pos]
  have hbounded : ∀ n,(mu n,theta n)∈Metric.closedBall (0 : MassRatio×MassRatio) R := by
    intro n
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def]
    apply max_le
    · apply (pi_norm_le_iff_of_nonneg hR).mpr
      intro i
      rw [Real.norm_eq_abs,abs_of_pos ((hm n).1 i)]
      have hi : mu n i≤1 := by
        rw [← (hm n).2]
        exact Finset.single_le_sum (fun j _ => ((hm n).1 j).le) (Finset.mem_univ i)
      exact hi.trans (by dsimp [R]; linarith [Real.pi_pos])
    · apply (pi_norm_le_iff_of_nonneg hR).mpr
      intro i
      rw [Real.norm_eq_abs,abs_of_nonneg (hbound n i).1]
      exact (hbound n i).2.trans (by dsimp [R]; linarith)
  obtain ⟨lim,_,phi,hphi,ht⟩ := (isCompact_closedBall (0 : MassRatio×MassRatio) R).tendsto_subseq hbounded
  have hmt : Tendsto (mu ∘ phi) atTop (nhds lim.1) := by
    simpa only [Function.comp_def] using continuous_fst.tendsto lim |>.comp ht
  have htt : Tendsto (theta ∘ phi) atTop (nhds lim.2) := by
    simpa only [Function.comp_def] using continuous_snd.tendsto lim |>.comp ht
  have hepst : Tendsto eps atTop (nhds 0) := squeeze_zero (fun n => (heps n).le)
    (fun n => (hepssmall n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hrt : Tendsto r atTop (nhds (fun _ : Satellite => (1 : ℝ))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply Metric.tendsto_nhds.mpr
    intro eta heta
    have hsmall := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds heta)
    filter_upwards [hsmall] with n hn
    rw [Real.dist_eq]
    exact (hrclose n i).trans hn
  have hlimzero : lim.2 0=0 := by
    have hz : Tendsto (fun n => theta (phi n) 0) atTop (nhds 0) := by
      simpa only [hzero] using (tendsto_const_nhds (x := (0 : ℝ)))
    exact tendsto_nhds_unique ((continuous_apply 0).tendsto lim.2 |>.comp htt) hz
  have hspanpos := ordered_full_angular_limit_span_pos (eps ∘ phi) (fun n => heps (phi n))
    (mu ∘ phi) (r ∘ phi) (theta ∘ phi) (fun n => (hm (phi n)).1) (fun n => hr (phi n))
    (fun n => hroot (phi n)) (fun n => horder (phi n)) (fun _ => 1) lim.2
    (fun _ => rfl) (hrt.comp hphi.tendsto_atTop) htt
  have hspanpi := ordered_full_angular_limit_span_lt_pi (eps ∘ phi) (fun n => heps (phi n))
    (hepst.comp hphi.tendsto_atTop) (mu ∘ phi) (r ∘ phi) (theta ∘ phi)
    (fun n => (hm (phi n)).1) (fun n => (hm (phi n)).2) (fun n => hr (phi n))
    (fun n => hroot (phi n)) (fun n => horder (phi n)) lim.1 (fun _ => 1) lim.2
    (fun _ => rfl) hmt (hrt.comp hphi.tendsto_atTop) htt
  rw [hlimzero,sub_zero] at hspanpos hspanpi
  have hmargin0 : Tendsto (fun n => min (theta n 3) (Real.pi-theta n 3)) atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact le_min (hbound n 3).1 (sub_nonneg.mpr (hbound n 3).2)
    · intro n
      by_cases hlo : theta n 3<1/((n : ℝ)+1)
      · exact ((min_le_left _ _).trans_lt hlo).le
      · have hhi := hbad n (le_of_not_gt hlo)
        exact ((min_le_right _ _).trans_lt (by linarith)).le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have ht3 := (continuous_apply 3).tendsto lim.2 |>.comp htt
  have hmarginLimit : min (lim.2 3) (Real.pi-lim.2 3)=0 :=
    tendsto_nhds_unique (ht3.min ((tendsto_const_nhds (x := Real.pi)).sub ht3))
      (hmargin0.comp hphi.tendsto_atTop)
  have hpositive : 0<min (lim.2 3) (Real.pi-lim.2 3) := lt_min hspanpos (sub_pos.mpr hspanpi)
  rw [hmarginLimit] at hpositive
  exact (lt_irrefl 0) hpositive

theorem ordered_angles_compact_subsequence (theta : ℕ → Satellite → ℝ)
    (hzero : ∀ n,theta n 0=0)
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi) :
    ∃ (thetaLimit : Satellite → ℝ) (phi : ℕ → ℕ),StrictMono phi ∧
      Tendsto (theta ∘ phi) atTop (nhds thetaLimit) := by
  have hb : ∀ n,theta n∈Metric.closedBall (0 : MassRatio) Real.pi := by
    intro n
    rw [Metric.mem_closedBall,dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr
    intro i
    by_cases hi : i=0
    · subst i
      rw [Real.norm_eq_abs,hzero n,abs_zero]
      exact Real.pi_pos.le
    · have ho := horder n 0 i (lt_of_le_of_ne (Fin.zero_le i) (Ne.symm hi))
      rw [hzero n,sub_zero] at ho
      rw [Real.norm_eq_abs,abs_of_pos ho.1]
      exact ho.2.le
  obtain ⟨limit,_,phi,hphi,ht⟩ := (isCompact_closedBall (0 : MassRatio) Real.pi).tendsto_subseq hb
  exact ⟨limit,phi,hphi,ht⟩

/-- Uniform consecutive-gap control near unit radii. It is proved from
actual angular roots, with arbitrarily small positive satellite fractions. -/
theorem uniform_ordered_gap_bound_near_unit (k : Fin 3) (eta : ℝ) (heta : 0<eta) :
    ∃ delta : ℝ,0<delta ∧ ∀ (eps : ℝ) (mu r theta : Satellite → ℝ),
      0<eps → eps<delta → PositiveRatio mu → (∀ i,0<r i) → theta 0=0 →
      (∀ i j,i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi) →
      (∀ i,angularResidual eps mu r theta i=0) → (∀ i,|r i-1|<delta) →
      theta k.succ-theta k.castSucc<Real.pi/3+eta := by
  by_contra h
  push Not at h
  have hw (n : ℕ) : ∃ (eps : ℝ) (mu r theta : Satellite → ℝ),
      0<eps ∧ eps<1/((n : ℝ)+1) ∧ PositiveRatio mu ∧ (∀ i,0<r i) ∧ theta 0=0 ∧
      (∀ i j,i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi) ∧
      (∀ i,angularResidual eps mu r theta i=0) ∧ (∀ i,|r i-1|<1/((n : ℝ)+1)) ∧
      Real.pi/3+eta≤theta k.succ-theta k.castSucc :=
    h (1/((n : ℝ)+1)) (by positivity)
  choose eps mu r theta heps hepssmall hm hr hzero horder hroot hrclose hbad using hw
  obtain ⟨thetaLimit,phi,hphi,htt⟩ := ordered_angles_compact_subsequence theta hzero horder
  have hepst : Tendsto eps atTop (nhds 0) := squeeze_zero (fun n => (heps n).le)
    (fun n => (hepssmall n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hrt : Tendsto r atTop (nhds (fun _ : Satellite => (1 : ℝ))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply Metric.tendsto_nhds.mpr
    intro e he
    have hsmall := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds he)
    filter_upwards [hsmall] with n hn
    rw [Real.dist_eq]
    exact (hrclose n i).trans hn
  have hgap := ordered_full_angular_limit_consecutive_gap_le (eps ∘ phi) (fun n => heps (phi n))
    (hepst.comp hphi.tendsto_atTop) (mu ∘ phi) (r ∘ phi) (theta ∘ phi)
    (fun n => (hm (phi n)).1) (fun n => hr (phi n)) (fun n => hroot (phi n))
    (fun n => horder (phi n)) (fun _ => 1) thetaLimit (fun _ => rfl)
    (hrt.comp hphi.tendsto_atTop) htt k
  have hdiff := ((continuous_apply k.succ).tendsto thetaLimit |>.comp htt).sub
    ((continuous_apply k.castSucc).tendsto thetaLimit |>.comp htt)
  have hlo : Real.pi/3+eta≤thetaLimit k.succ-thetaLimit k.castSucc :=
    ge_of_tendsto hdiff (Filter.Eventually.of_forall (fun n => hbad (phi n)))
  linarith

theorem uniform_ordered_consecutive_gaps_near_unit (eta : ℝ) (heta : 0<eta) :
    ∃ delta : ℝ,0<delta ∧ ∀ (eps : ℝ) (mu r theta : Satellite → ℝ),
      0<eps → eps<delta → PositiveRatio mu → (∀ i,0<r i) → theta 0=0 →
      (∀ i j,i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi) →
      (∀ i,angularResidual eps mu r theta i=0) → (∀ i,|r i-1|<delta) →
      ∀ k : Fin 3,theta k.succ-theta k.castSucc<Real.pi/3+eta := by
  obtain ⟨d0,hd0,h0⟩ := uniform_ordered_gap_bound_near_unit 0 eta heta
  obtain ⟨d1,hd1,h1⟩ := uniform_ordered_gap_bound_near_unit 1 eta heta
  obtain ⟨d2,hd2,h2⟩ := uniform_ordered_gap_bound_near_unit 2 eta heta
  let delta := min d0 (min d1 d2)
  have hdelta0 : delta≤d0 := min_le_left _ _
  have hdelta1 : delta≤d1 := (min_le_right _ _).trans (min_le_left _ _)
  have hdelta2 : delta≤d2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨delta,lt_min hd0 (lt_min hd1 hd2),?_⟩
  intro eps mu r theta heps hepssmall hm hr hzero horder hroot hrclose k
  fin_cases k
  · exact h0 eps mu r theta heps (hepssmall.trans_le hdelta0) hm hr hzero horder hroot
      (fun i => (hrclose i).trans_le hdelta0)
  · exact h1 eps mu r theta heps (hepssmall.trans_le hdelta1) hm hr hzero horder hroot
      (fun i => (hrclose i).trans_le hdelta1)
  · exact h2 eps mu r theta heps (hepssmall.trans_le hdelta2) hm hr hzero horder hroot
      (fun i => (hrclose i).trans_le hdelta2)

/-- Every given ordered polar representation of a normalized configuration
satisfies the original angular rows; the masses follow the specified hull
permutation. The polar coordinates are never assumed to lie in a chart. -/
theorem normalized_polar_gauge_angular_rows (eps : ℝ) (mu : MassRatio)
    (sigma : HullOrder) (x : Configuration) (heps : 0<eps) (hm : PositiveRatio mu)
    (hx : NormalizedCentralConfiguration (masses eps mu) x)
    (r theta : Satellite → ℝ) (phi : ℝ) (hr : ∀ i,0<r i)
    (hpolar : ∀ i,x (sigma.labels i.succ)-x 0=polarPoint (r i) (theta i+phi)) :
    ∀ i,angularResidual eps (mu ∘ hullSatellitePermutation sigma) r theta i=0 := by
  have hx' : NormalizedCentralConfiguration (masses eps (mu ∘ hullSatellitePermutation sigma))
      (x ∘ sigma.labels) := by
    rw [masses_hull_reindex]
    exact normalized_reindex _ _ hx _
  have hpolar' : satellitesRelative (x ∘ sigma.labels)=polarSatellites r (fun i => theta i+phi) := by
    funext i
    simpa only [satellitesRelative,primaryRelative,Function.comp_apply,sigma.primary_first,
      polarSatellites] using hpolar i
  have hroot := (polarResiduals_zero_of_normalized eps (mu ∘ hullSatellitePermutation sigma)
    (x ∘ sigma.labels) hx' (positiveRatio_hull_reindex mu sigma hm) heps r
    (fun i => theta i+phi) hr hpolar').2
  intro i
  rw [← angularResidual_common_angle eps (mu ∘ hullSatellitePermutation sigma) r theta phi i]
  exact hroot i

end DominantFiveBody
