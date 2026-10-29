import DominantFiveBody.ShapeDimension
import DominantFiveBody.ForceBalance
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Derivatives of the actual five-body potential

Sources: §3 `eq:UI`, `eq:action`, and `lem:hessian`.  All derivatives below
refer to `potential`, `inertia`, and `augmentedPotential` from the physical
definitions.  Noncollision denominators are explicitly justified.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

/-- Difference of the two actual labeled positions, as a continuous linear map. -/
def pairDifference (i j : Label) : Configuration →L[ℝ] Plane :=
  (ContinuousLinearMap.proj i : Configuration →L[ℝ] Plane) -
    (ContinuousLinearMap.proj j : Configuration →L[ℝ] Plane)

@[simp] theorem pairDifference_apply (i j : Label) (x : Configuration) :
    pairDifference i j x = x i - x j := rfl

/-- The bilinear pair metric `(v,w) ↦ ⟨vᵢ-vⱼ,wᵢ-wⱼ⟩`. -/
def pairMetric (i j : Label) : Configuration →L[ℝ] Configuration →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ Configuration Plane ℝ).flip (pairDifference i j)).comp
    ((innerSL ℝ).comp (pairDifference i j))

@[simp] theorem pairMetric_apply (i j : Label) (v w : Configuration) :
    pairMetric i j v w = inner ℝ (v i - v j) (w i - w j) := rfl

/-- The mass metric packaged continuously; it is the original `massInner`. -/
def massMetric (m : MassVector) : Configuration →L[ℝ] Configuration →L[ℝ] ℝ :=
  ∑ i, m i • ((ContinuousLinearMap.compL ℝ Configuration Plane ℝ).flip
    (ContinuousLinearMap.proj i)).comp ((innerSL ℝ).comp (ContinuousLinearMap.proj i))

@[simp] theorem massMetric_apply (m : MassVector) (v w : Configuration) :
    massMetric m v w = massInner m v w := by
  simp [massMetric, massInner]

/-- Norm differentiation in the physical plane, proved through squared
norm and square root. The singular point is excluded explicitly. -/
theorem norm_hasFDerivAt (q : Plane) (hq : q ≠ 0) :
    HasFDerivAt (fun z : Plane => ‖z‖) (‖q‖⁻¹ • innerSL ℝ q) q := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have h := (hasStrictFDerivAt_norm_sq q).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  have hnorm := h.congr_of_eventuallyEq
    (Eventually.of_forall fun z => (Real.sqrt_sq (norm_nonneg z)).symm)
  apply hnorm.congr_fderiv
  ext v
  simp only [smul_apply, smul_eq_mul, Real.sqrt_sq (norm_nonneg q)]
  field_simp
  ring

theorem pairDistance_hasFDerivAt (x : Configuration) (i j : Label)
    (hij : x i ≠ x j) :
    HasFDerivAt (fun y => pairDistance y i j)
      (‖x i - x j‖⁻¹ • pairMetric i j x) x := by
  convert! (norm_hasFDerivAt (x i - x j) (sub_ne_zero.mpr hij)).comp x
      (pairDifference i j).hasFDerivAt using 1

/-- The exact first differential of the Newtonian potential. -/
def potentialDerivative (m : MassVector) (x : Configuration) : Configuration →L[ℝ] ℝ :=
  ∑ p ∈ pairs, (-(m p.1 * m p.2) / pairDistance x p.1 p.2 ^ 3) • pairMetric p.1 p.2 x

/-- §3 `eq:UI`: the physical Newtonian potential is differentiable at every
collision-free configuration, with its complete ten-interaction derivative. -/
theorem potential_hasFDerivAt (m : MassVector) (x : Configuration) (hx : CollisionFree x) :
    HasFDerivAt (potential m) (potentialDerivative m x) x := by
  unfold potential potentialDerivative
  apply HasFDerivAt.fun_sum
  intro p hp
  have hij : p.1 ≠ p.2 := ne_of_lt ((Finset.mem_filter.mp hp).2)
  have hn := ne_of_gt (collision_distance_pos x hx p.1 p.2 hij)
  have hd := pairDistance_hasFDerivAt x p.1 p.2 (hx p.1 p.2 hij)
  have h := ((hasDerivAt_inv hn).comp_hasFDerivAt x hd).const_mul (m p.1 * m p.2)
  have hf := h.congr_of_eventuallyEq
    (Eventually.of_forall fun y => div_eq_mul_inv (m p.1 * m p.2) (pairDistance y p.1 p.2))
  apply hf.congr_fderiv
  ext v
  simp only [smul_apply, smul_eq_mul, pairDistance]
  field_simp

theorem inertia_hasFDerivAt (m : MassVector) (x : Configuration) :
    HasFDerivAt (inertia m) (2 • massMetric m x) x := by
  have h : HasFDerivAt (inertia m)
      (∑ i, m i • (2 • (innerSL ℝ (x i)).comp (ContinuousLinearMap.proj i))) x := by
    unfold inertia
    apply HasFDerivAt.fun_sum
    intro i _
    exact ((ContinuousLinearMap.proj i : Configuration →L[ℝ] Plane).hasFDerivAt.norm_sq).const_mul (m i)
  apply h.congr_fderiv
  ext v
  simp [massMetric, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The complete first derivative of `G = U + lam I/2`. -/
def augmentedPotentialDerivative (m : MassVector) (lam : ℝ) (x : Configuration) :
    Configuration →L[ℝ] ℝ := potentialDerivative m x + lam • massMetric m x

theorem augmentedPotential_hasFDerivAt (m : MassVector) (lam : ℝ)
    (x : Configuration) (hx : CollisionFree x) :
    HasFDerivAt (augmentedPotential m lam) (augmentedPotentialDerivative m lam x) x := by
  have h := (potential_hasFDerivAt m x hx).add ((inertia_hasFDerivAt m x).const_mul (lam / 2))
  apply h.congr_fderiv
  ext v
  simp [augmentedPotentialDerivative]
  ring

theorem fderiv_potential (m : MassVector) (x : Configuration) (hx : CollisionFree x) :
    fderiv ℝ (potential m) x = potentialDerivative m x :=
  (potential_hasFDerivAt m x hx).fderiv

theorem fderiv_inertia (m : MassVector) (x : Configuration) :
    fderiv ℝ (inertia m) x = 2 • massMetric m x :=
  (inertia_hasFDerivAt m x).fderiv

theorem fderiv_augmentedPotential (m : MassVector) (lam : ℝ)
    (x : Configuration) (hx : CollisionFree x) :
    fderiv ℝ (augmentedPotential m lam) x = augmentedPotentialDerivative m lam x :=
  (augmentedPotential_hasFDerivAt m lam x hx).fderiv

/-- Collision freedom is an open condition in the actual ten-dimensional
configuration space. It justifies differentiating the nearby first-derivative formula. -/
theorem isOpen_collisionFree : IsOpen {x : Configuration | CollisionFree x} := by
  simp only [CollisionFree, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _
  have hi : Continuous (fun x : Configuration => x i) := continuous_apply i
  have hj : Continuous (fun x : Configuration => x j) := continuous_apply j
  exact (isClosed_eq hi hj).isOpen_compl

theorem eventually_collisionFree (x : Configuration) (hx : CollisionFree x) :
    ∀ᶠ y in 𝓝 x, CollisionFree y := isOpen_collisionFree.mem_nhds hx

/-- Differentiation of the genuine inverse-cube distance. -/
theorem inverseCubeDistance_hasFDerivAt (x : Configuration) (i j : Label)
    (hij : x i ≠ x j) :
    HasFDerivAt (fun y => (pairDistance y i j ^ 3)⁻¹)
      ((-3 / pairDistance x i j ^ 5) • pairMetric i j x) x := by
  have hn : pairDistance x i j ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hij)
  have hd := pairDistance_hasFDerivAt x i j hij
  have h := (hasDerivAt_inv (pow_ne_zero 3 hn)).comp_hasFDerivAt x (hd.pow 3)
  apply h.congr_fderiv
  ext v
  have hn' : ‖x i - x j‖ ≠ 0 := hn
  norm_num only [smul_apply, smul_eq_mul, pairDistance, nsmul_eq_mul, Nat.cast_ofNat]
  field_simp [hn']

theorem pairGradientCoefficient_hasFDerivAt (m : MassVector) (x : Configuration)
    (i j : Label) (hij : x i ≠ x j) :
    HasFDerivAt (fun y => -(m i * m j) / pairDistance y i j ^ 3)
      ((3 * (m i * m j) / pairDistance x i j ^ 5) • pairMetric i j x) x := by
  have h := (inverseCubeDistance_hasFDerivAt x i j hij).const_mul (-(m i * m j))
  have hf := h.congr_of_eventuallyEq (Eventually.of_forall fun y =>
    div_eq_mul_inv (-(m i * m j)) (pairDistance y i j ^ 3))
  apply hf.congr_fderiv
  ext v
  simp only [smul_apply, smul_eq_mul]
  ring

/-- The continuous bilinear Newtonian Hessian, with all pair terms retained. -/
def potentialHessianMap (m : MassVector) (x : Configuration) :
    Configuration →L[ℝ] Configuration →L[ℝ] ℝ :=
  ∑ p ∈ pairs,
    ((-(m p.1 * m p.2) / pairDistance x p.1 p.2 ^ 3) • pairMetric p.1 p.2 +
    ((3 * (m p.1 * m p.2) / pairDistance x p.1 p.2 ^ 5) • pairMetric p.1 p.2 x).smulRight
      (pairMetric p.1 p.2 x))

theorem potentialDerivative_hasFDerivAt (m : MassVector) (x : Configuration)
    (hx : CollisionFree x) :
    HasFDerivAt (potentialDerivative m) (potentialHessianMap m x) x := by
  unfold potentialDerivative potentialHessianMap
  apply HasFDerivAt.fun_sum
  intro p hp
  have hij : p.1 ≠ p.2 := ne_of_lt ((Finset.mem_filter.mp hp).2)
  exact (pairGradientCoefficient_hasFDerivAt m x p.1 p.2 (hx p.1 p.2 hij)).smul
    (pairMetric p.1 p.2).hasFDerivAt

/-- The true Hessian of `G`, including the inertia contribution. -/
def augmentedPotentialHessianMap (m : MassVector) (lam : ℝ) (x : Configuration) :
    Configuration →L[ℝ] Configuration →L[ℝ] ℝ :=
  potentialHessianMap m x + lam • massMetric m

theorem augmentedPotentialDerivative_hasFDerivAt (m : MassVector) (lam : ℝ)
    (x : Configuration) (hx : CollisionFree x) :
    HasFDerivAt (augmentedPotentialDerivative m lam)
      (augmentedPotentialHessianMap m lam x) x := by
  exact (potentialDerivative_hasFDerivAt m x hx).add ((massMetric m).hasFDerivAt.const_smul lam)

/-- §3 `lem:hessian`: the explicit expression is proved equal to the actual
second Fréchet derivative; it is not installed as its definition. -/
theorem physicalHessian_eq_map (m : MassVector) (lam : ℝ) (x : Configuration)
    (hx : CollisionFree x) (v w : Configuration) :
    physicalHessian m lam x v w = augmentedPotentialHessianMap m lam x v w := by
  have hnear : fderiv ℝ (augmentedPotential m lam) =ᶠ[𝓝 x]
      augmentedPotentialDerivative m lam :=
    (eventually_collisionFree x hx).mono fun y hy => fderiv_augmentedPotential m lam y hy
  exact congrArg (fun A : Configuration →L[ℝ] Configuration →L[ℝ] ℝ => A v w)
    ((augmentedPotentialDerivative_hasFDerivAt m lam x hx).congr_of_eventuallyEq hnear).fderiv

/-- The entrywise bilinear formula of the actual `D²G`; every distance is
nonzero under the explicitly stated collision-freedom hypothesis. -/
theorem physicalHessian_explicit (m : MassVector) (lam : ℝ) (x : Configuration)
    (hx : CollisionFree x) (v w : Configuration) :
    physicalHessian m lam x v w =
      (∑ p ∈ pairs, m p.1 * m p.2 *
        (3 * inner ℝ (x p.1 - x p.2) (v p.1 - v p.2) *
            inner ℝ (x p.1 - x p.2) (w p.1 - w p.2) / pairDistance x p.1 p.2 ^ 5 -
          inner ℝ (v p.1 - v p.2) (w p.1 - w p.2) / pairDistance x p.1 p.2 ^ 3)) +
      lam * massInner m v w := by
  rw [physicalHessian_eq_map m lam x hx]
  simp only [augmentedPotentialHessianMap, potentialHessianMap, sum_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, pairMetric_apply, massMetric_apply,
    smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Symmetry is proved from the true second derivative and its pair formula. -/
theorem physicalHessian_comm (m : MassVector) (lam : ℝ) (x : Configuration)
    (hx : CollisionFree x) (v w : Configuration) :
    physicalHessian m lam x v w = physicalHessian m lam x w v := by
  rw [physicalHessian_explicit m lam x hx, physicalHessian_explicit m lam x hx,
    massInner_comm m v w]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [real_inner_comm (v p.1 - v p.2) (w p.1 - w p.2)]
  ring

/-- The genuine potential is smooth throughout the collision-free locus. -/
theorem potential_contDiffAt (n : ℕ∞ω) (m : MassVector) (x : Configuration)
    (hx : CollisionFree x) : ContDiffAt ℝ n (potential m) x := by
  unfold potential
  apply ContDiffAt.sum
  intro p hp
  have hij : p.1 ≠ p.2 := ne_of_lt ((Finset.mem_filter.mp hp).2)
  exact contDiffAt_const.div
    ((pairDifference p.1 p.2).contDiff.contDiffAt.norm ℝ (sub_ne_zero.mpr (hx p.1 p.2 hij)))
    (ne_of_gt (collision_distance_pos x hx p.1 p.2 hij))

theorem inertia_contDiff (n : ℕ∞ω) (m : MassVector) : ContDiff ℝ n (inertia m) := by
  unfold inertia
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul ((ContinuousLinearMap.proj i : Configuration →L[ℝ] Plane).contDiff.norm_sq ℝ)

theorem augmentedPotential_contDiffAt (n : ℕ∞ω) (m : MassVector) (lam : ℝ)
    (x : Configuration) (hx : CollisionFree x) :
    ContDiffAt ℝ n (augmentedPotential m lam) x :=
  (potential_contDiffAt n m x hx).add (contDiffAt_const.mul (inertia_contDiff n m).contDiffAt)

/-- Joint smoothness of the physical action in masses and positions.
This uses no strictly positive lower bound on any varying mass. -/
theorem potential_joint_contDiffAt (n : ℕ∞ω) (m : MassVector) (x : Configuration)
    (hx : CollisionFree x) :
    ContDiffAt ℝ n (fun z : MassVector × Configuration => potential z.1 z.2) (m, x) := by
  unfold potential
  apply ContDiffAt.sum
  intro p hp
  have hij : p.1 ≠ p.2 := ne_of_lt ((Finset.mem_filter.mp hp).2)
  have hc : ContDiffAt ℝ n (fun z : MassVector × Configuration => z.1 p.1 * z.1 p.2) (m, x) := by
    fun_prop
  have hd : ContDiffAt ℝ n (fun z : MassVector × Configuration => z.2 p.1 - z.2 p.2) (m, x) := by
    fun_prop
  exact hc.div (hd.norm ℝ (sub_ne_zero.mpr (hx p.1 p.2 hij)))
    (ne_of_gt (collision_distance_pos x hx p.1 p.2 hij))

theorem inertia_joint_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun z : MassVector × Configuration => inertia z.1 z.2) := by
  unfold inertia
  apply ContDiff.sum
  intro i _
  exact (by fun_prop : ContDiff ℝ n (fun z : MassVector × Configuration => z.1 i)).mul
    ((by fun_prop : ContDiff ℝ n (fun z : MassVector × Configuration => z.2 i)).norm_sq ℝ)

/-- Exact finite decomposition into the ten unordered five-body pairs.
This is a kernel-checked finite identity; no numerical evidence is used. -/
theorem sum_orderedPairs_eq_unordered (f : Label → Label → ℝ) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = ∑ p ∈ pairs, (f p.1 p.2 + f p.2 p.1) := by
  simp [pairs, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ, hdiag]
  ring

/-- §3 `eq:cc`, `eq:UI`: the Newtonian gradient is the physical
mass-weighted acceleration, proved by exact pair cancellation. -/
theorem potentialDerivative_eq_acceleration (m : MassVector) (x v : Configuration) :
    potentialDerivative m x v = massInner m (acceleration m x) v := by
  have hsum := sum_orderedPairs_eq_unordered
    (fun i j => inner ℝ (pairForce m x i j) (v i)) (by intro i; simp)
  have hacc : massInner m (acceleration m x) v =
      ∑ i, ∑ j, inner ℝ (pairForce m x i j) (v i) := by
    unfold massInner
    simp_rw [← real_inner_smul_left, weighted_acceleration_as_pair_sum, sum_inner]
  rw [hacc, hsum]
  simp only [potentialDerivative, sum_apply, smul_apply, pairMetric_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [pairForce_reverse m x p.1 p.2, inner_neg_left]
  simp only [pairForce, real_inner_smul_left, inner_sub_left, inner_sub_right]
  ring

/-- A genuine multiplier-one central configuration is a critical point of
the actual augmented potential, without a gradient interface assumption. -/
theorem normalizedCC_fderiv_augmentedPotential_zero (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) :
    fderiv ℝ (augmentedPotential m 1) x = 0 := by
  rw [fderiv_augmentedPotential m 1 x hx.1]
  ext v
  simp only [augmentedPotentialDerivative, add_apply, massMetric_apply,
    potentialDerivative_eq_acceleration, one_smul, zero_apply]
  unfold massInner
  simp_rw [hx.2.2, inner_neg_left]
  simp [Finset.sum_neg_distrib]

end DominantFiveBody
