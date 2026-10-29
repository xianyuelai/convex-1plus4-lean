import DominantFiveBody.HessianCorrespondence

/-! Physical Hessian and shape-space transport under actual labels. -/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

def configurationReindexLinear (e : Equiv.Perm Label) : Configuration →L[ℝ] Configuration :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (e i))

@[simp] theorem configurationReindexLinear_apply (e : Equiv.Perm Label) (x : Configuration) :
    configurationReindexLinear e x = x ∘ e := rfl

theorem totalMass_permutation (m : MassVector) (e : Equiv.Perm Label) :
    totalMass (m ∘ e) = totalMass m := Equiv.sum_comp e m

theorem weightedPosition_permutation (m : MassVector) (x : Configuration) (e : Equiv.Perm Label) :
    weightedPosition (m ∘ e) (x ∘ e) = weightedPosition m x :=
  Equiv.sum_comp e (fun i => m i • x i)

theorem massInner_permutation (m : MassVector) (v w : Configuration) (e : Equiv.Perm Label) :
    massInner (m ∘ e) (v ∘ e) (w ∘ e) = massInner m v w :=
  Equiv.sum_comp e (fun i => m i * inner ℝ (v i) (w i))

theorem massCenter_permutation (m : MassVector) (x : Configuration) (e : Equiv.Perm Label) :
    massCenter (m ∘ e) (x ∘ e) = massCenter m x := by
  rw [massCenter, totalMass_permutation, weightedPosition_permutation]
  rfl

theorem centered_permutation (m : MassVector) (x : Configuration) (e : Equiv.Perm Label) :
    centered (m ∘ e) (x ∘ e) = centered m x ∘ e := by
  unfold centered
  rw [massCenter_permutation]
  rfl

theorem potential_full_sum (m : MassVector) (x : Configuration) :
    (∑ i, ∑ j, m i * m j / pairDistance x i j) = 2 * potential m x := by
  rw [sum_orderedPairs_eq_unordered (fun i j => m i * m j / pairDistance x i j)
    (by intro i; simp [pairDistance])]
  have hsym (i j : Label) : m j * m i / pairDistance x j i = m i * m j / pairDistance x i j := by
    simp only [pairDistance, norm_sub_rev, mul_comm]
  simp_rw [hsym]
  rw [Finset.sum_add_distrib]
  change potential m x + potential m x = _
  ring

theorem potential_permutation (m : MassVector) (x : Configuration) (e : Equiv.Perm Label) :
    potential (m ∘ e) (x ∘ e) = potential m x := by
  have hdouble : (∑ i, ∑ j, (m ∘ e) i * (m ∘ e) j / pairDistance (x ∘ e) i j) =
      ∑ i, ∑ j, m i * m j / pairDistance x i j := by
    change (∑ i, ∑ j, m (e i) * m (e j) / pairDistance x (e i) (e j)) = _
    calc
      _ = ∑ i, ∑ j, m (e i) * m j / pairDistance x (e i) j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp e (fun j => m (e i) * m j / pairDistance x (e i) j)
      _ = _ := Equiv.sum_comp e (fun i => ∑ j, m i * m j / pairDistance x i j)
  rw [potential_full_sum, potential_full_sum] at hdouble
  linarith

theorem inertia_permutation (m : MassVector) (x : Configuration) (e : Equiv.Perm Label) :
    inertia (m ∘ e) (x ∘ e) = inertia m x := Equiv.sum_comp e (fun i => m i * ‖x i‖ ^ 2)

theorem augmentedPotential_permutation (m : MassVector) (lam : ℝ) (x : Configuration)
    (e : Equiv.Perm Label) :
    augmentedPotential (m ∘ e) lam (x ∘ e) = augmentedPotential m lam x := by
  rw [augmentedPotential, potential_permutation, inertia_permutation]
  rfl

theorem acceleration_full_sum (m : MassVector) (x : Configuration) (i : Label) :
    acceleration m x i = ∑ j, (m j / pairDistance x i j ^ 3) • (x j - x i) := by
  unfold acceleration
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp only [sub_self, smul_zero, sub_zero]

theorem acceleration_permutation (m : MassVector) (x : Configuration) (e : Equiv.Perm Label)
    (i : Label) : acceleration (m ∘ e) (x ∘ e) i = acceleration m x (e i) := by
  rw [acceleration_full_sum, acceleration_full_sum]
  exact Equiv.sum_comp e (fun j => (m j / pairDistance x (e i) j ^ 3) • (x j - x (e i)))

theorem normalizedCC_permutation (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) (e : Equiv.Perm Label) :
    NormalizedCentralConfiguration (m ∘ e) (x ∘ e) := by
  refine ⟨fun i j hij => hx.1 (e i) (e j) (e.injective.ne hij), ?_, ?_⟩
  · rw [weightedPosition_permutation]; exact hx.2.1
  · intro i; rw [acceleration_permutation]; exact hx.2.2 (e i)

/-- The actual nested second derivative transforms by the actual label
linear map. The proof differentiates the original augmented potential. -/
theorem physicalHessian_permutation (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) (e : Equiv.Perm Label) (v w : Configuration) :
    physicalHessian (m ∘ e) 1 (x ∘ e) (v ∘ e) (w ∘ e) = physicalHessian m 1 x v w := by
  let L := configurationReindexLinear e
  have heq : augmentedPotential (m ∘ e) 1 ∘ L = augmentedPotential m 1 := by
    funext z
    exact augmentedPotential_permutation m 1 z e
  have h := physicalHessian_comp_at_normalizedCC (m ∘ e) L x L.contDiff.contDiffAt
    (normalizedCC_permutation m x hx e) v w
  rw [heq, L.fderiv] at h
  exact h.symm

theorem shapeSpace_permutation_mem_iff (m : MassVector) (x v : Configuration)
    (e : Equiv.Perm Label) :
    v ∘ e ∈ shapeSpace (m ∘ e) (x ∘ e) ↔ v ∈ shapeSpace m x := by
  rw [mem_shapeSpace_iff, mem_shapeSpace_iff, centered_permutation]
  have hr : rotationDirection (centered m x ∘ e) = rotationDirection (centered m x) ∘ e := rfl
  rw [hr, weightedPosition_permutation, massInner_permutation, massInner_permutation]

theorem shapeHessianNondegenerate_permutation_forward (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) (e : Equiv.Perm Label)
    (hn : ShapeHessianNondegenerate m 1 x) :
    ShapeHessianNondegenerate (m ∘ e) 1 (x ∘ e) := by
  intro v hv hk
  let u : Configuration := v ∘ e.symm
  have hu : u ∈ shapeSpace m x := by
    apply (shapeSpace_permutation_mem_iff m x u e).mp
    simpa only [u, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using hv
  have hz : u = 0 := hn u hu (by
    intro w hw
    have h := hk (w ∘ e) ((shapeSpace_permutation_mem_iff m x w e).mpr hw)
    have hveq : v = u ∘ e := by ext i; simp [u]
    rw [hveq, physicalHessian_permutation m x hx e u w] at h
    exact h)
  funext i
  have h := congrFun hz (e i)
  simpa [u] using h

/-- Actual geometric shape nondegeneracy is unchanged by transporting
masses and labels together. Relabeling is not added to similarity. -/
theorem shapeHessianNondegenerate_permutation_iff (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) (e : Equiv.Perm Label) :
    ShapeHessianNondegenerate (m ∘ e) 1 (x ∘ e) ↔ ShapeHessianNondegenerate m 1 x := by
  constructor
  · intro hn
    have h := shapeHessianNondegenerate_permutation_forward (m ∘ e) (x ∘ e)
      (normalizedCC_permutation m x hx e) e.symm hn
    simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using h
  · exact shapeHessianNondegenerate_permutation_forward m x hx e

end DominantFiveBody
