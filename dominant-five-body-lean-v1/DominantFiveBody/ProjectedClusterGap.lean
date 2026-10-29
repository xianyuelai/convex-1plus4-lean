import DominantFiveBody.CollisionGeometry

/-! Original projected-center identity in Section 4, with current masses. -/
noncomputable section
open scoped BigOperators
namespace DominantFiveBody

def projectedClusterGap (m : MassVector) (x : Configuration) (S : Finset Label) (e : Plane) : ℝ :=
  inner ℝ e ((clusterMass m Sᶜ)⁻¹ • clusterPosition m x Sᶜ-
    (clusterMass m S)⁻¹ • clusterPosition m x S)

theorem projectedClusterGap_mass_product (m : MassVector) (x : Configuration)
    (S : Finset Label) (e : Plane) (hA : clusterMass m S≠0) (hB : clusterMass m Sᶜ≠0) :
    projectedClusterGap m x S e*(clusterMass m S*clusterMass m Sᶜ)=
      ∑ i∈S,∑ j∈Sᶜ,m i*m j*inner ℝ e (x j-x i) := by
  simp only [inner_sub_right,weighted_projection_separation]
  simp only [projectedClusterGap,inner_sub_right,real_inner_smul_right,
    clusterPosition,inner_sum,real_inner_smul_right]
  field_simp

theorem projectedClusterGap_force_identity (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) (S : Finset Label) (e : Plane) :
    projectedClusterGap m x S e=
      ((clusterMass m S)⁻¹+(clusterMass m Sᶜ)⁻¹)*inner ℝ e (clusterCrossForce m x S) := by
  have hsum := clusterPosition_add_compl m x S
  rw [hx.2.1] at hsum
  have hB : clusterPosition m x Sᶜ = -clusterPosition m x S := eq_neg_of_add_eq_zero_right hsum
  rw [projectedClusterGap,hB,normalized_cluster_cross_force m x hx S]
  simp only [inner_sub_right,real_inner_smul_right,inner_neg_right]
  ring

theorem projectedClusterGap_explicit_force (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) (S : Finset Label) (e : Plane) :
    projectedClusterGap m x S e=
      ((clusterMass m S)⁻¹+(clusterMass m Sᶜ)⁻¹)*
        ∑ i∈S,∑ j∈Sᶜ,m i*m j*inner ℝ e (x j-x i)/‖x j-x i‖^3 := by
  rw [projectedClusterGap_force_identity m x hx]
  congr 1
  simp only [clusterCrossForce,inner_sum,pairForce,real_inner_smul_right,pairDistance]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_sub_rev (x j)]
  ring

theorem normalized_projectedClusterGap_bounds (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x)
    (S : Finset Label) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (e : Plane) (he : ‖e‖=1) (g : ℝ) (hg : 0<g)
    (hgap : ∀ i∈S,∀ j∈Sᶜ,g ≤ inner ℝ e (x j-x i)) :
    g≤projectedClusterGap m x S e ∧ projectedClusterGap m x S e≤totalMass m/g^2 := by
  have hA := clusterMass_pos m hm S hS
  have hB := clusterMass_pos m hm Sᶜ hSc
  constructor
  · apply (mul_le_mul_iff_left₀ (mul_pos hA hB)).mp
    rw [projectedClusterGap_mass_product m x S e hA.ne' hB.ne']
    calc
      _ = ∑ i∈S,∑ j∈Sᶜ,m i*m j*g := by
        rw [mul_comm g]
        unfold clusterMass
        rw [Finset.sum_mul_sum]
        simp only [Finset.sum_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hgap i hi j hj) (mul_pos (hm i) (hm j)).le
  · rw [projectedClusterGap_force_identity m x hx]
    have hcoef : 0≤(clusterMass m S)⁻¹+(clusterMass m Sᶜ)⁻¹ := by positivity
    have hle := mul_le_mul_of_nonneg_left (projected_crossForce_le m hm x e he S g hg hgap) hcoef
    apply hle.trans_eq
    rw [← clusterMass_add_compl m S]
    field_simp
    ring

theorem dominant_projectedClusterGap_source (eps : ℝ) (mu : MassRatio)
    (heps : 0<eps) (hmu : PositiveRatio mu) (x : Configuration)
    (hx : NormalizedCentralConfiguration (masses eps mu) x)
    (S : Finset Label) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (e : Plane) (he : ‖e‖=1) (g : ℝ) (hg : 0<g)
    (hgap : ∀ i∈S,∀ j∈Sᶜ,g ≤ inner ℝ e (x j-x i)) :
    g≤projectedClusterGap (masses eps mu) x S e ∧
    projectedClusterGap (masses eps mu) x S e=
      ((clusterMass (masses eps mu) S)⁻¹+(clusterMass (masses eps mu) Sᶜ)⁻¹)*
        ∑ i∈S,∑ j∈Sᶜ,(masses eps mu) i*(masses eps mu) j*
          inner ℝ e (x j-x i)/‖x j-x i‖^3 ∧
    projectedClusterGap (masses eps mu) x S e≤(1+eps)/g^2 := by
  obtain ⟨hl,hu⟩ := normalized_projectedClusterGap_bounds (masses eps mu)
    (masses_positive eps mu heps hmu) x hx S hS hSc e he g hg hgap
  rw [totalMass_masses eps mu hmu] at hu
  exact ⟨hl,projectedClusterGap_explicit_force _ x hx S e,hu⟩

end DominantFiveBody
