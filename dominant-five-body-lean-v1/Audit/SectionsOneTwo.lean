import DominantFiveBody.CoorbitalSourceCalculus
import DominantFiveBody.CoorbitalSourceBounds
import DominantFiveBody.CoorbitalSemicircleGeometry
import DominantFiveBody.ProbeOriginalDerivatives
import DominantFiveBody.BoundarySourceCalculus
import DominantFiveBody.CycleDecomposition
import DominantFiveBody.MassRescaling
open scoped BigOperators ContDiff Matrix.Norms.Operator Topology
universe u_1 u_2 u_3 u_4
set_option linter.unusedVariables false

example : ∀ {n : ℕ} (mass theta : Fin n → ℝ),
  (∀ (i : Fin n), DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
    ∀ (i : Fin n), ∑ j : Fin n, DominantFiveBody.Coorbital.angularFlow mass theta i j = 0 := @DominantFiveBody.Coorbital.angularFlow_balanced
#print axioms DominantFiveBody.Coorbital.angularFlow_balanced

example : ∀ {n : ℕ} (mass theta : Fin n → ℝ),
  (∀ (i : Fin n), 0 < mass i) →
    ∀ (i j : Fin n),
      0 < theta j - theta i →
        theta j - theta i < Real.pi →
          (DominantFiveBody.Coorbital.angularFlow mass theta i j < 0 ↔ DominantFiveBody.Coorbital.h < theta j - theta i) := @DominantFiveBody.Coorbital.angularFlow_neg_iff
#print axioms DominantFiveBody.Coorbital.angularFlow_neg_iff

example : ∀ {n : ℕ} (mass theta : Fin n → ℝ),
  (∀ (i : Fin n), 0 < mass i) →
    ∀ (i j : Fin n),
      0 < theta j - theta i →
        theta j - theta i < Real.pi →
          (0 < DominantFiveBody.Coorbital.angularFlow mass theta i j ↔ theta j - theta i < DominantFiveBody.Coorbital.h) := @DominantFiveBody.Coorbital.angularFlow_pos_iff
#print axioms DominantFiveBody.Coorbital.angularFlow_pos_iff

example : ∀ {n : ℕ},
  2 ≤ n →
    n ≤ 4 →
      ∀ (mass theta u : Fin n → ℝ),
        (∀ (i : Fin n), 0 < mass i) →
          (∀ (i j : Fin n), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
            (∀ (i : Fin n), DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
              DominantFiveBody.Coorbital.coorbitalRemainderForm mass theta u ≤
                DominantFiveBody.Coorbital.coorbitalKappaForm mass theta u := @DominantFiveBody.Coorbital.coorbital_cycle_bound
#print axioms DominantFiveBody.Coorbital.coorbital_cycle_bound

example : ∀ (mass theta : Fin 4 → ℝ),
  (∀ (i : Fin 4), 0 < mass i) →
    (∀ (i j : Fin 4), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
      (∀ (i : Fin 4), DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
        ∃ (p : ℝ) (q : ℝ) (r : ℝ) (s : ℝ) (t : ℝ),
          0 ≤ p ∧
            0 ≤ q ∧
              0 ≤ r ∧
                0 ≤ s ∧
                  0 ≤ t ∧
                    DominantFiveBody.Coorbital.angularFlow mass theta 0 1 = p + s + t ∧
                      DominantFiveBody.Coorbital.angularFlow mass theta 1 2 = p + q + t ∧
                        DominantFiveBody.Coorbital.angularFlow mass theta 2 3 = q + r + t ∧
                          DominantFiveBody.Coorbital.angularFlow mass theta 0 2 = r - p ∧
                            DominantFiveBody.Coorbital.angularFlow mass theta 1 3 = s - q ∧
                              DominantFiveBody.Coorbital.angularFlow mass theta 0 3 = -(r + s + t) ∧
                                (0 < p → DominantFiveBody.Coorbital.angularFlow mass theta 0 2 < 0) ∧
                                  (0 < q → DominantFiveBody.Coorbital.angularFlow mass theta 1 3 < 0) ∧
                                    (0 < r → 0 < DominantFiveBody.Coorbital.angularFlow mass theta 0 2) ∧
                                      (0 < s → 0 < DominantFiveBody.Coorbital.angularFlow mass theta 1 3) := @DominantFiveBody.Coorbital.four_angular_cycle_decomposition
#print axioms DominantFiveBody.Coorbital.four_angular_cycle_decomposition

example : ∀ (mass theta : Fin 4 → ℝ),
  (∀ (i : Fin 4), 0 < mass i) →
    (∀ (i j : Fin 4), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
      (∀ (i : Fin 4), DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
        theta 1 - theta 0 < DominantFiveBody.Coorbital.h ∧
          theta 2 - theta 1 < DominantFiveBody.Coorbital.h ∧
            theta 3 - theta 2 < DominantFiveBody.Coorbital.h ∧ DominantFiveBody.Coorbital.h < theta 3 - theta 0 := @DominantFiveBody.Coorbital.four_root_gaps
#print axioms DominantFiveBody.Coorbital.four_root_gaps

example : DominantFiveBody.Coorbital.kappa DominantFiveBody.Coorbital.h = 9 / 4 := @DominantFiveBody.Coorbital.kappa_h
#print axioms DominantFiveBody.Coorbital.kappa_h

example : ∀ {a b : ℝ},
  0 < a →
    a ≤ b → b ≤ Real.pi → IntervalIntegrable DominantFiveBody.Coorbital.kappa MeasureTheory.MeasureSpace.volume a b := @DominantFiveBody.Coorbital.kappa_intervalIntegrable
#print axioms DominantFiveBody.Coorbital.kappa_intervalIntegrable

example : ∀ {t : ℝ}, 0 < t → t < Real.pi → -1 ≤ DominantFiveBody.Coorbital.kernelF t := @DominantFiveBody.Coorbital.kernelF_ge_neg_one
#print axioms DominantFiveBody.Coorbital.kernelF_ge_neg_one

example : DominantFiveBody.Coorbital.kernelF DominantFiveBody.Coorbital.h = 0 := @DominantFiveBody.Coorbital.kernelF_h
#print axioms DominantFiveBody.Coorbital.kernelF_h

example : ∀ {t : ℝ}, DominantFiveBody.Coorbital.h < t → t < Real.pi → DominantFiveBody.Coorbital.kernelF t < 0 := @DominantFiveBody.Coorbital.kernelF_neg_on_long_arc
#print axioms DominantFiveBody.Coorbital.kernelF_neg_on_long_arc

example : DominantFiveBody.Coorbital.kernelF Real.pi = 0 := @DominantFiveBody.Coorbital.kernelF_pi
#print axioms DominantFiveBody.Coorbital.kernelF_pi

example : ∀ {t : ℝ}, 0 < t → t < DominantFiveBody.Coorbital.h → 0 < DominantFiveBody.Coorbital.kernelF t := @DominantFiveBody.Coorbital.kernelF_pos_on_short_arc
#print axioms DominantFiveBody.Coorbital.kernelF_pos_on_short_arc

example : ∀ {t : ℝ}, 0 < t → t < Real.pi → 0 < DominantFiveBody.Coorbital.positiveRemainder t := @DominantFiveBody.Coorbital.positiveRemainder_pos
#print axioms DominantFiveBody.Coorbital.positiveRemainder_pos

example : StrictAntiOn DominantFiveBody.Coorbital.kappa (Set.Ioo 0 Real.pi) := @DominantFiveBody.Coorbital.strictAntiOn_kappa
#print axioms DominantFiveBody.Coorbital.strictAntiOn_kappa

example : ∀ (s t r u v w : ℝ),
  s < DominantFiveBody.Coorbital.h →
    t < DominantFiveBody.Coorbital.h →
      r < DominantFiveBody.Coorbital.h →
        (u + v + w) ^ 2 / (3 * DominantFiveBody.Coorbital.h - (s + t + r)) - (u + v + w) ^ 2 / (Real.pi - (s + t + r)) ≤
            u ^ 2 / (DominantFiveBody.Coorbital.h - s) + v ^ 2 / (DominantFiveBody.Coorbital.h - t) +
                w ^ 2 / (DominantFiveBody.Coorbital.h - r) -
              (u + v + w) ^ 2 / (Real.pi - (s + t + r)) ∧
          0 ≤
            (u + v + w) ^ 2 / (3 * DominantFiveBody.Coorbital.h - (s + t + r)) -
              (u + v + w) ^ 2 / (Real.pi - (s + t + r)) := @DominantFiveBody.Coorbital.three_cycle_display
#print axioms DominantFiveBody.Coorbital.three_cycle_display

example : ∀ (s t r u v w : ℝ),
  s < DominantFiveBody.Coorbital.h →
    t < DominantFiveBody.Coorbital.h →
      r < DominantFiveBody.Coorbital.h →
        (u ^ 2 / (DominantFiveBody.Coorbital.h - s) + v ^ 2 / (DominantFiveBody.Coorbital.h - t) +
                w ^ 2 / (DominantFiveBody.Coorbital.h - r) -
              (u + v + w) ^ 2 / (Real.pi - (s + t + r)) =
            0 ↔
          (DominantFiveBody.Coorbital.h - t) * u = (DominantFiveBody.Coorbital.h - s) * v ∧
            (DominantFiveBody.Coorbital.h - r) * (u + v) =
              (DominantFiveBody.Coorbital.h - s + (DominantFiveBody.Coorbital.h - t)) * w) := @DominantFiveBody.Coorbital.three_edge_cycle_eq_zero_iff
#print axioms DominantFiveBody.Coorbital.three_edge_cycle_eq_zero_iff

example : ∀ (mass theta : Fin 3 → ℝ),
  (∀ (i : Fin 3), 0 < mass i) →
    (∀ (i j : Fin 3), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
      (∀ (i : Fin 3), DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
        theta 1 - theta 0 < DominantFiveBody.Coorbital.h ∧
          theta 2 - theta 1 < DominantFiveBody.Coorbital.h ∧ DominantFiveBody.Coorbital.h < theta 2 - theta 0 := @DominantFiveBody.Coorbital.three_root_gaps
#print axioms DominantFiveBody.Coorbital.three_root_gaps

example : ∀ (s t u v : ℝ),
  s < DominantFiveBody.Coorbital.h →
    t < DominantFiveBody.Coorbital.h →
      s + t < Real.pi →
        (u + v) ^ 2 / (2 * DominantFiveBody.Coorbital.h - (s + t)) - (u + v) ^ 2 / (Real.pi - (s + t)) ≤
            u ^ 2 / (DominantFiveBody.Coorbital.h - s) + v ^ 2 / (DominantFiveBody.Coorbital.h - t) -
              (u + v) ^ 2 / (Real.pi - (s + t)) ∧
          0 ≤ (u + v) ^ 2 / (2 * DominantFiveBody.Coorbital.h - (s + t)) - (u + v) ^ 2 / (Real.pi - (s + t)) := @DominantFiveBody.Coorbital.two_cycle_display
#print axioms DominantFiveBody.Coorbital.two_cycle_display

example : ∀ (a b u v : ℝ), 0 < a → 0 < b → ((u + v) ^ 2 / (a + b) = u ^ 2 / a + v ^ 2 / b ↔ b * u = a * v) := @DominantFiveBody.Coorbital.two_denominator_cauchy_eq_iff
#print axioms DominantFiveBody.Coorbital.two_denominator_cauchy_eq_iff

example : ∀ (s t u v : ℝ),
  s < DominantFiveBody.Coorbital.h →
    t < DominantFiveBody.Coorbital.h →
      s + t < Real.pi →
        (u ^ 2 / (DominantFiveBody.Coorbital.h - s) + v ^ 2 / (DominantFiveBody.Coorbital.h - t) -
              (u + v) ^ 2 / (Real.pi - (s + t)) =
            0 ↔
          u = 0 ∧ v = 0) := @DominantFiveBody.Coorbital.two_edge_cycle_eq_zero_iff
#print axioms DominantFiveBody.Coorbital.two_edge_cycle_eq_zero_iff

example : ∀ (mass theta : Fin 2 → ℝ),
  (∀ (i : Fin 2), 0 < mass i) →
    (∀ (i j : Fin 2), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
      (∀ (i : Fin 2), DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
        theta 1 - theta 0 = DominantFiveBody.Coorbital.h := @DominantFiveBody.Coorbital.two_root_separation
#print axioms DominantFiveBody.Coorbital.two_root_separation

example : ∀ {n : ℕ},
  2 ≤ n →
    n ≤ 4 →
      ∀ (mass theta u : Fin n → ℝ),
        (∀ (i : Fin n), 0 < mass i) →
          DominantFiveBody.OrderedSemicircle theta →
            (∀ (i : Fin n), DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
              ((∀ (v : Fin n → ℝ), DominantFiveBody.angularChordHessian mass theta u v = 0) ↔
                ∀ (i j : Fin n), u i = u j) := @DominantFiveBody.angularChordHessian_kernel_iff
#print axioms DominantFiveBody.angularChordHessian_kernel_iff

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (c : ℝ),
  ((DominantFiveBody.angularDifferential mass theta : (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
      fun (x : DominantFiveBody.Satellite) => c) =
    0 := @DominantFiveBody.angularDifferential_constant
#print axioms DominantFiveBody.angularDifferential_constant

example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ),
  (∀ (i : DominantFiveBody.Satellite), 0 ≤ mass i) →
    ∑ i : DominantFiveBody.Satellite, mass i = 1 →
      DominantFiveBody.SeparatedSemicircle theta →
        (∀ (i j : DominantFiveBody.Satellite), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
          (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = 0) →
            ((DominantFiveBody.angularDifferential mass theta :
                    (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
                  u =
                0 ↔
              ∀ (i j : DominantFiveBody.Satellite), u i = u j) := @DominantFiveBody.angularDifferential_kernel_iff_nonnegative
#print axioms DominantFiveBody.angularDifferential_kernel_iff_nonnegative

example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ) (p : DominantFiveBody.Satellite),
  0 < mass p →
    (∀ (i : DominantFiveBody.Satellite),
        i ≠ p →
          (DominantFiveBody.angularDifferential mass theta :
                (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
              u i =
            0) →
      (DominantFiveBody.angularDifferential mass theta :
            (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
          u p =
        0 := @DominantFiveBody.angularDifferential_recover_row
#print axioms DominantFiveBody.angularDifferential_recover_row

example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ),
  ∑ i : DominantFiveBody.Satellite,
      mass i *
        (DominantFiveBody.angularDifferential mass theta :
            (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
          u i =
    0 := @DominantFiveBody.angularDifferential_weighted_zero
#print axioms DominantFiveBody.angularDifferential_weighted_zero

example : ∀ {n : ℕ} (mass theta u : Fin n → ℝ) (c : ℝ),
  (((DominantFiveBody.angularHessianMap mass theta : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) u : (Fin n → ℝ) → ℝ)
      fun (x : Fin n) => c) =
    0 := @DominantFiveBody.angularHessianMap_constant_right
#print axioms DominantFiveBody.angularHessianMap_constant_right

example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ),
  (DominantFiveBody.angularJacobian mass theta).mulVec u =
    (DominantFiveBody.angularDifferential mass theta :
        (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
      u := @DominantFiveBody.angularJacobian_mulVec
#print axioms DominantFiveBody.angularJacobian_mulVec

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite),
  i ≠ j → mass j = 0 → DominantFiveBody.angularJacobian mass theta i j = 0 := @DominantFiveBody.angularJacobian_zero_mass_column
#print axioms DominantFiveBody.angularJacobian_zero_mass_column

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (k : DominantFiveBody.Satellite),
  mass k = 0 →
    DominantFiveBody.angularJacobian mass theta k k =
      ∑ j : DominantFiveBody.Satellite with mass j ≠ 0, mass j * DominantFiveBody.Coorbital.kappa |theta j - theta k| := @DominantFiveBody.angularJacobian_zero_support_diagonal
#print axioms DominantFiveBody.angularJacobian_zero_support_diagonal

example : ∀ {n : ℕ},
  2 ≤ n →
    n ≤ 4 →
      ∀ (mass theta : Fin n → ℝ),
        (∀ (i : Fin n), 0 < mass i) →
          DominantFiveBody.OrderedSemicircle theta →
            (∀ (i : Fin n), DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
              (∀ (i j : Fin n), i < j → 0 < DominantFiveBody.Coorbital.positiveRemainder (theta j - theta i)) ∧
                (∀ (u : Fin n → ℝ),
                    DominantFiveBody.angularChordHessian mass theta u u =
                        DominantFiveBody.Coorbital.coorbitalKappaForm mass theta u ∧
                      DominantFiveBody.Coorbital.coorbitalRemainderForm mass theta u ≤
                        DominantFiveBody.angularChordHessian mass theta u u) ∧
                  ∀ (u : Fin n → ℝ),
                    (∀ (v : Fin n → ℝ), DominantFiveBody.angularChordHessian mass theta u v = 0) ↔
                      ∀ (i j : Fin n), u i = u j := @DominantFiveBody.angular_hessian_estimate
#print axioms DominantFiveBody.angular_hessian_estimate

example : ∀ (K : Set (DominantFiveBody.Satellite → ℝ)),
  IsCompact K →
    (∀ m ∈ K, ∀ (i : DominantFiveBody.Satellite), 0 < m i) →
      ∃ (alpha : ℝ), 0 < alpha ∧ ∀ m ∈ K, ∀ (i : DominantFiveBody.Satellite), alpha ≤ m i := @DominantFiveBody.compact_positive_mass_floor
#print axioms DominantFiveBody.compact_positive_mass_floor

example : ∀ (t : ℝ), DominantFiveBody.coorbitalKernel (-t) = -DominantFiveBody.coorbitalKernel t := @DominantFiveBody.coorbitalKernel_neg
#print axioms DominantFiveBody.coorbitalKernel_neg

example : ∀ (m : DominantFiveBody.CoorbitalMassSpace), (DominantFiveBody.coorbitalMassProjection ⁻¹' {m}).Finite := @DominantFiveBody.coorbitalMassProjection_fiber_finite
#print axioms DominantFiveBody.coorbitalMassProjection_fiber_finite

example : IsCoveringMapOn DominantFiveBody.coorbitalMassProjection Set.univ := @DominantFiveBody.coorbitalMassProjection_isCoveringMapOn
#print axioms DominantFiveBody.coorbitalMassProjection_isCoveringMapOn

example : IsLocalHomeomorphOn DominantFiveBody.coorbitalMassProjection Set.univ := @DominantFiveBody.coorbitalMassProjection_isLocalHomeomorphOn
#print axioms DominantFiveBody.coorbitalMassProjection_isLocalHomeomorphOn

example : IsProperMap DominantFiveBody.coorbitalMassProjection := @DominantFiveBody.coorbitalMassProjection_isProperMap
#print axioms DominantFiveBody.coorbitalMassProjection_isProperMap

example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    DominantFiveBody.coorbitalPhysicalHessian mass theta u u =
      DominantFiveBody.Coorbital.coorbitalKappaForm mass theta u := @DominantFiveBody.coorbitalPhysicalHessian_self
#print axioms DominantFiveBody.coorbitalPhysicalHessian_self

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    ∀ (k : DominantFiveBody.Satellite),
      (fderiv ℝ (DominantFiveBody.coorbitalPotential mass) theta : (DominantFiveBody.Satellite → ℝ) → ℝ)
          (Pi.single k 1) =
        mass k * DominantFiveBody.coorbitalResidual mass theta k := @DominantFiveBody.coorbitalPotential_coordinate_derivative
#print axioms DominantFiveBody.coorbitalPotential_coordinate_derivative

example : ∀ (μ θ : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite),
  DominantFiveBody.coorbitalResidual μ θ i =
    ∑ j : DominantFiveBody.Satellite, μ j * DominantFiveBody.coorbitalMatrix θ i j := @DominantFiveBody.coorbitalResidual_eq_matrix_sum
#print axioms DominantFiveBody.coorbitalResidual_eq_matrix_sum

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.SeparatedSemicircle theta →
    HasFDerivAt
      (fun (angles : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) =>
        DominantFiveBody.coorbitalResidual mass angles i)
      (DominantFiveBody.angularDifferential mass theta) theta := @DominantFiveBody.coorbitalResidual_hasFDerivAt
#print axioms DominantFiveBody.coorbitalResidual_hasFDerivAt

example : ∀ (alpha : ℝ),
  0 < alpha →
    ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
      DominantFiveBody.PositiveRatio mass →
        (∀ (i : DominantFiveBody.Satellite), alpha ≤ mass i) →
          DominantFiveBody.OrderedSemicircle theta →
            (∀ (i : Fin 4), DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
              ∀ (i j : DominantFiveBody.Satellite),
                i < j →
                  theta j - theta i < DominantFiveBody.Coorbital.h →
                    alpha ^ 2 * ((theta j - theta i) * DominantFiveBody.Coorbital.kernelF (theta j - theta i)) ≤
                      Real.pi / 2 := @DominantFiveBody.coorbitalVirial_pair_with_mass_floor
#print axioms DominantFiveBody.coorbitalVirial_pair_with_mass_floor

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    (∀ (i : Fin 4), DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
      DominantFiveBody.coorbitalVirial mass theta = 0 := @DominantFiveBody.coorbitalVirial_zero
#print axioms DominantFiveBody.coorbitalVirial_zero

example : (∀ (mass theta : DominantFiveBody.Satellite → ℝ),
    (∀ (i : DominantFiveBody.Satellite), 0 ≤ mass i) →
      ∑ i : DominantFiveBody.Satellite, mass i = 1 →
        DominantFiveBody.SeparatedSemicircle theta →
          (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = 0) →
            HasFDerivAt
                (fun (angles : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) =>
                  DominantFiveBody.coorbitalResidual mass angles i)
                (DominantFiveBody.angularDifferential mass theta) theta ∧
              (∀ (u : DominantFiveBody.Satellite → ℝ),
                  (DominantFiveBody.angularDifferential mass theta :
                          (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
                        u =
                      0 ↔
                    ∀ (i j : DominantFiveBody.Satellite), u i = u j) ∧
                ∀ (p q : DominantFiveBody.Satellite),
                  0 < mass p → IsUnit (DominantFiveBody.deletedAngularJacobian mass theta p q)) ∧
  ∀ (K : Set ((DominantFiveBody.Satellite → ℝ) × (DominantFiveBody.Satellite → ℝ))) (delta eta : ℝ)
    (p q : DominantFiveBody.Satellite),
    IsClosed K →
      0 < delta →
        0 < eta →
          (∀ z ∈ K,
              (∀ (i : DominantFiveBody.Satellite), 0 ≤ z.1 i) ∧
                ∑ i : DominantFiveBody.Satellite, z.1 i = 1 ∧
                  z.2 0 = 0 ∧
                    (∀ (i : Fin 3), delta ≤ z.2 i.succ - z.2 i.castSucc) ∧
                      z.2 3 - z.2 0 ≤ Real.pi - eta ∧
                        1 / 4 ≤ z.1 p ∧
                          ∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual z.1 z.2 i = 0) →
            ∃ (C : ℝ), 0 < C ∧ ∀ z ∈ K, ‖(DominantFiveBody.deletedAngularJacobian z.1 z.2 p q)⁻¹‖ ≤ C := @DominantFiveBody.coorbital_closed_mass_jacobian_complete
#print axioms DominantFiveBody.coorbital_closed_mass_jacobian_complete

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    (∀ (i : Fin 4), DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
      ∀ (k : Fin 3),
        (∑ i : DominantFiveBody.Satellite,
            ∑ j : DominantFiveBody.Satellite,
              if (↑i : ℕ) ≤ (↑k : ℕ) ∧ (↑k : ℕ) < (↑j : ℕ) then
                mass i * mass j * DominantFiveBody.Coorbital.kernelF (theta j - theta i)
              else 0) =
          0 := @DominantFiveBody.coorbital_cut
#print axioms DominantFiveBody.coorbital_cut

example : (∀ (m : DominantFiveBody.MassRatio),
    DominantFiveBody.PositiveRatio m →
      ∃! theta : DominantFiveBody.Satellite → ℝ,
        DominantFiveBody.CoorbitalAngleDomain theta ∧
          ∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual m theta i = 0) ∧
  ContDiffOn ℝ ∞ DominantFiveBody.coorbitalRootAngles
      {m : DominantFiveBody.MassRatio | DominantFiveBody.PositiveRatio m} ∧
    (∀ (m : DominantFiveBody.MassRatio),
        DominantFiveBody.PositiveRatio m →
          ∀ (u : DominantFiveBody.Satellite → ℝ),
            u 0 = 0 →
              u ≠ 0 → 0 < DominantFiveBody.coorbitalPhysicalHessian m (DominantFiveBody.coorbitalRootAngles m) u u) ∧
      IsProperMap DominantFiveBody.coorbitalMassProjection ∧
        IsCoveringMapOn DominantFiveBody.coorbitalMassProjection Set.univ := @DominantFiveBody.coorbital_global_complete
#print axioms DominantFiveBody.coorbital_global_complete

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.PositiveRatio mass →
    DominantFiveBody.OrderedSemicircle theta →
      -Real.pi / 2 ≤
        ∑ i : DominantFiveBody.Satellite,
          ∑ j : DominantFiveBody.Satellite,
            if i < j then
              Min.min (mass i * mass j * (theta j - theta i) * DominantFiveBody.Coorbital.kernelF (theta j - theta i)) 0
            else 0 := @DominantFiveBody.coorbital_negative_terms_lower_bound
#print axioms DominantFiveBody.coorbital_negative_terms_lower_bound

example : ∀ (μ θ : DominantFiveBody.Satellite → ℝ) (p : DominantFiveBody.Satellite),
  0 < μ p →
    (∀ (i : DominantFiveBody.Satellite), i ≠ p → DominantFiveBody.coorbitalResidual μ θ i = 0) →
      DominantFiveBody.coorbitalResidual μ θ p = 0 := @DominantFiveBody.coorbital_recover_positive_mass_row
#print axioms DominantFiveBody.coorbital_recover_positive_mass_row

example : ∀ (alpha : ℝ),
  0 < alpha →
    ∃ (d : ℝ),
      0 < d ∧
        ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
          DominantFiveBody.PositiveRatio mass →
            (∀ (i : DominantFiveBody.Satellite), alpha ≤ mass i) →
              DominantFiveBody.OrderedSemicircle theta →
                (∀ (i : Fin 4), DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
                  ∀ (i j : DominantFiveBody.Satellite), i < j → d ≤ theta j - theta i := @DominantFiveBody.coorbital_roots_uniform_pair_separation
#print axioms DominantFiveBody.coorbital_roots_uniform_pair_separation

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (k : DominantFiveBody.Satellite),
  mass k = 0 →
    (∀ (i : DominantFiveBody.Satellite), i ≠ k → 0 < mass i) →
      (∀ (i j : DominantFiveBody.Satellite), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
        (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = 0) →
          ∃ v ∈ (DominantFiveBody.coorbitalMatrix theta).mulVecLin.ker, v k ≠ 0 := @DominantFiveBody.coorbital_three_source_kernel_not_all_zero_at_missing_source
#print axioms DominantFiveBody.coorbital_three_source_kernel_not_all_zero_at_missing_source

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (k : DominantFiveBody.Satellite),
  mass k = 0 →
    (∀ (i : DominantFiveBody.Satellite), i ≠ k → 0 < mass i) →
      (∀ (i j : DominantFiveBody.Satellite), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
        (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = 0) →
          ∃ (nu : DominantFiveBody.Satellite → ℝ),
            nu k = 1 ∧ ∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual nu theta i = 0 := @DominantFiveBody.coorbital_three_source_kernel_vector_by_rank
#print axioms DominantFiveBody.coorbital_three_source_kernel_vector_by_rank

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (k : DominantFiveBody.Satellite),
  mass k = 0 →
    (∀ (i : DominantFiveBody.Satellite), i ≠ k → 0 < mass i) →
      (∀ (i j : DominantFiveBody.Satellite), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
        (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = 0) →
          (DominantFiveBody.coorbitalSupportMatrix theta k).rank = 2 ∧
            (DominantFiveBody.coorbitalMatrix theta).rank = 2 ∧
              Module.finrank ℝ ↥(DominantFiveBody.coorbitalMatrix theta).mulVecLin.ker = 2 ∧
                Module.finrank ℝ ↥(DominantFiveBody.coorbitalSupportMatrix theta k).mulVecLin.ker = 1 := @DominantFiveBody.coorbital_three_source_ranks_and_kernel_dimensions
#print axioms DominantFiveBody.coorbital_three_source_ranks_and_kernel_dimensions

example : ∀ (μ θ : DominantFiveBody.Satellite → ℝ),
  ∑ i : DominantFiveBody.Satellite, μ i * DominantFiveBody.coorbitalResidual μ θ i = 0 := @DominantFiveBody.coorbital_weightedResidual_zero
#print axioms DominantFiveBody.coorbital_weightedResidual_zero

example : ∀ (K : Set ((DominantFiveBody.Satellite → ℝ) × (DominantFiveBody.Satellite → ℝ))) (delta eta : ℝ)
  (p q : DominantFiveBody.Satellite),
  IsClosed K →
    0 < delta →
      0 < eta →
        (∀ z ∈ K,
            (∀ (i : DominantFiveBody.Satellite), 0 ≤ z.1 i) ∧
              ∑ i : DominantFiveBody.Satellite, z.1 i = 1 ∧
                z.2 0 = 0 ∧
                  (∀ (i : Fin 3), delta ≤ z.2 i.succ - z.2 i.castSucc) ∧
                    z.2 3 - z.2 0 ≤ Real.pi - eta ∧
                      1 / 4 ≤ z.1 p ∧
                        ∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual z.1 z.2 i = 0) →
          ∃ (C : ℝ), 0 < C ∧ ∀ z ∈ K, ‖(DominantFiveBody.deletedAngularJacobian z.1 z.2 p q)⁻¹‖ ≤ C := @DominantFiveBody.deletedAngularJacobian_inverse_uniform_on_closed_roots
#print axioms DominantFiveBody.deletedAngularJacobian_inverse_uniform_on_closed_roots

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (p q : DominantFiveBody.Satellite),
  (∀ (i : DominantFiveBody.Satellite), 0 ≤ mass i) →
    ∑ i : DominantFiveBody.Satellite, mass i = 1 →
      0 < mass p →
        DominantFiveBody.SeparatedSemicircle theta →
          (∀ (i j : DominantFiveBody.Satellite), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
            (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = 0) →
              IsUnit (DominantFiveBody.deletedAngularJacobian mass theta p q) := @DominantFiveBody.deletedAngularJacobian_isUnit_nonnegative
#print axioms DominantFiveBody.deletedAngularJacobian_isUnit_nonnegative

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (p q : DominantFiveBody.Satellite),
  (∀ (i : DominantFiveBody.Satellite), 0 < mass i) →
    (∀ (i j : DominantFiveBody.Satellite), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
      (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = 0) →
        IsUnit (DominantFiveBody.deletedAngularJacobian mass theta p q) := @DominantFiveBody.deletedAngularJacobian_isUnit_positive
#print axioms DominantFiveBody.deletedAngularJacobian_isUnit_positive

example : ∃! theta : DominantFiveBody.Satellite → ℝ,
  DominantFiveBody.CoorbitalAngleDomain theta ∧
    ∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual DominantFiveBody.equalMassRatio theta i = 0 := @DominantFiveBody.equalMass_coorbital_existsUnique
#print axioms DominantFiveBody.equalMass_coorbital_existsUnique

example : ∀ (theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.CoorbitalAngleDomain theta →
    (∀ (i : DominantFiveBody.Satellite),
        DominantFiveBody.coorbitalResidual DominantFiveBody.equalMassRatio theta i = 0) →
      theta 1 - theta 0 = theta 3 - theta 2 := @DominantFiveBody.equalMass_root_reversal_symmetry
#print axioms DominantFiveBody.equalMass_root_reversal_symmetry

example : Filter.Tendsto (fun (t : ℝ) => t * DominantFiveBody.Coorbital.kernelF t) (𝓝[>] 0) Filter.atTop := @DominantFiveBody.kernelF_angle_mul_tendsto_atTop
#print axioms DominantFiveBody.kernelF_angle_mul_tendsto_atTop

example : DominantFiveBody.MainUniformStatement := @DominantFiveBody.main_uniform
#print axioms DominantFiveBody.main_uniform

example : ∃ (δ : ℝ),
  0 < δ ∧
    ∀ (m : DominantFiveBody.MassVector),
      DominantFiveBody.PositiveMasses m →
        (∑ i : DominantFiveBody.Satellite, m (Fin.succ i)) / m 0 < δ →
          ∀ (σ : DominantFiveBody.HullOrder),
            ∃ (x : DominantFiveBody.Configuration),
              DominantFiveBody.StrictConvexCentralConfiguration m σ x ∧
                (∀ (y : DominantFiveBody.Configuration),
                    DominantFiveBody.StrictConvexCentralConfiguration m σ y → DominantFiveBody.OrientedSimilar x y) ∧
                  ∀ (y : DominantFiveBody.Configuration),
                    DominantFiveBody.StrictConvexCentralConfiguration m σ y →
                      DominantFiveBody.NondegenerateCentralConfiguration m y := @DominantFiveBody.main_uniform_unnormalized
#print axioms DominantFiveBody.main_uniform_unnormalized

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  (∀ (i : DominantFiveBody.Satellite), 0 < mass i) →
    theta 1 - theta 0 ≤ DominantFiveBody.Coorbital.h ∧
        theta 2 - theta 1 ≤ DominantFiveBody.Coorbital.h ∧ theta 3 - theta 2 ≤ DominantFiveBody.Coorbital.h →
      theta 3 - theta 0 = Real.pi → (∀ (i : Fin 4), DominantFiveBody.Coorbital.angularEquation mass theta i = 0) → False := @DominantFiveBody.no_coorbital_root_at_semicircle_boundary
#print axioms DominantFiveBody.no_coorbital_root_at_semicircle_boundary

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (p : DominantFiveBody.Satellite),
  0 < mass p →
    (∀ (i : DominantFiveBody.Satellite), i ≠ p → mass i = 0) →
      DominantFiveBody.SeparatedSemicircle theta →
        (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = 0) → False := @DominantFiveBody.no_one_source_coorbital_root
#print axioms DominantFiveBody.no_one_source_coorbital_root

example : ∀ {p q x : ℝ},
  x ≠ 0 →
    x ≠ DominantFiveBody.Coorbital.h →
      DominantFiveBody.twoSourceSpan x < Real.pi →
        HasDerivAt
          (fun (t : ℝ) =>
            p * DominantFiveBody.coorbitalKernel t +
              q * DominantFiveBody.coorbitalKernel (t - DominantFiveBody.Coorbital.h))
          (-(p * DominantFiveBody.Coorbital.kappa |x| +
              q * DominantFiveBody.Coorbital.kappa |x - DominantFiveBody.Coorbital.h|))
          x := @DominantFiveBody.signedProbe_hasDerivAt
#print axioms DominantFiveBody.signedProbe_hasDerivAt

example : ∀ {p q x : ℝ},
  0 ≤ p →
    0 < q →
      0 < x →
        x < DominantFiveBody.Coorbital.h →
          deriv
              (fun (t : ℝ) =>
                p * DominantFiveBody.coorbitalKernel t +
                  q * DominantFiveBody.coorbitalKernel (t - DominantFiveBody.Coorbital.h))
              x <
            0 := @DominantFiveBody.signedProbe_inner_deriv_neg
#print axioms DominantFiveBody.signedProbe_inner_deriv_neg

example : ∀ (p q x : ℝ),
  q * DominantFiveBody.coorbitalKernel (DominantFiveBody.Coorbital.h - x) +
      p * DominantFiveBody.coorbitalKernel (DominantFiveBody.Coorbital.h - x - DominantFiveBody.Coorbital.h) =
    -(p * DominantFiveBody.coorbitalKernel x + q * DominantFiveBody.coorbitalKernel (x - DominantFiveBody.Coorbital.h)) := @DominantFiveBody.signedProbe_reflection
#print axioms DominantFiveBody.signedProbe_reflection

example : ∀ (θ : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.CoorbitalAngleDomain θ ↔ θ 0 = 0 ∧ 0 < θ 1 ∧ θ 1 < θ 2 ∧ θ 2 < θ 3 ∧ θ 3 < Real.pi := @DominantFiveBody.source_angle_domain
#print axioms DominantFiveBody.source_angle_domain

example : (∀ (t : ℝ),
    0 < t →
      t < DominantFiveBody.Coorbital.h →
        DominantFiveBody.Coorbital.kernelF t =
            ∫ (s : ℝ) in t..DominantFiveBody.Coorbital.h, DominantFiveBody.Coorbital.kappa s ∧
          ∫ (s : ℝ) in t..DominantFiveBody.Coorbital.h, DominantFiveBody.Coorbital.kappa s <
            (DominantFiveBody.Coorbital.h - t) * DominantFiveBody.Coorbital.kappa t) ∧
  ∀ (t : ℝ),
    DominantFiveBody.Coorbital.h < t →
      t < Real.pi →
        DominantFiveBody.Coorbital.kernelF t = ∫ (s : ℝ) in t..Real.pi, DominantFiveBody.Coorbital.kappa s ∧
          ∫ (s : ℝ) in t..Real.pi, DominantFiveBody.Coorbital.kappa s <
            (Real.pi - t) * DominantFiveBody.Coorbital.kappa t := @DominantFiveBody.source_integral_comparisons
#print axioms DominantFiveBody.source_integral_comparisons

example : ∀ (ε : ℝ) (μ : DominantFiveBody.MassRatio),
  DominantFiveBody.masses ε μ 0 = 1 ∧
    (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.masses ε μ (Fin.succ i) = ε * μ i) ∧
      (DominantFiveBody.PositiveRatio μ ↔
        (∀ (i : DominantFiveBody.Satellite), 0 < μ i) ∧ ∑ i : DominantFiveBody.Satellite, μ i = 1) := @DominantFiveBody.source_masses
#print axioms DominantFiveBody.source_masses

example : ∀ {t : ℝ},
  0 < t →
    t < Real.pi →
      deriv DominantFiveBody.Coorbital.pairPotential t = -DominantFiveBody.Coorbital.kernelF t ∧
        deriv DominantFiveBody.Coorbital.kernelF t = -DominantFiveBody.Coorbital.kappa t ∧
          deriv (deriv DominantFiveBody.Coorbital.pairPotential) t = DominantFiveBody.Coorbital.kappa t ∧
            deriv DominantFiveBody.Coorbital.kappa t = DominantFiveBody.Coorbital.kappaPrime t ∧
              DominantFiveBody.Coorbital.kappaPrime t < 0 := @DominantFiveBody.source_scalar_derivatives
#print axioms DominantFiveBody.source_scalar_derivatives

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (k : DominantFiveBody.Satellite),
  mass k = 0 →
    (∀ (i : DominantFiveBody.Satellite), i ≠ k → 0 < mass i) →
      DominantFiveBody.SeparatedSemicircle theta →
        (∀ (i j : DominantFiveBody.Satellite), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
          (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = 0) →
            ∑ j ∈ Finset.univ.erase k, mass j * DominantFiveBody.Coorbital.positiveRemainder |theta j - theta k| ≤
                DominantFiveBody.angularJacobian mass theta k k ∧
              0 < ∑ j ∈ Finset.univ.erase k, mass j * DominantFiveBody.Coorbital.positiveRemainder |theta j - theta k| := @DominantFiveBody.three_source_probe_remainder_lower_bound
#print axioms DominantFiveBody.three_source_probe_remainder_lower_bound

example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ) (k : DominantFiveBody.Satellite),
  mass k = 0 →
    (∀ (i : DominantFiveBody.Satellite), i ≠ k → 0 < mass i) →
      (∀ (i j : DominantFiveBody.Satellite), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
        (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = 0) →
          (DominantFiveBody.angularDifferential mass theta :
                  (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
                u =
              0 →
            ∀ (i j : Fin 3), u (Fin.succAbove k i) = u (Fin.succAbove k j) := @DominantFiveBody.three_source_support_kernel
#print axioms DominantFiveBody.three_source_support_kernel

example : ∀ (p q : ℝ),
  DominantFiveBody.twoSourceFunction p q Real.pi =
    q * DominantFiveBody.Coorbital.kernelF (Real.pi - DominantFiveBody.Coorbital.h) := @DominantFiveBody.twoSourceFunction_endpoint
#print axioms DominantFiveBody.twoSourceFunction_endpoint

example : ∀ {p q x : ℝ},
  0 ≤ p →
    0 < q →
      DominantFiveBody.Coorbital.h < x →
        x < Real.pi →
          DominantFiveBody.twoSourceFunction p q x = 0 →
            deriv (DominantFiveBody.twoSourceFunction p q) x <
                DominantFiveBody.twoSourceFunction p q Real.pi / (Real.pi - x) ∧
              DominantFiveBody.twoSourceFunction p q Real.pi / (Real.pi - x) < 0 := @DominantFiveBody.twoSourceFunction_root_strict_secant
#print axioms DominantFiveBody.twoSourceFunction_root_strict_secant

example : ∀ {p q x : ℝ},
  0 ≤ p →
    0 < q →
      DominantFiveBody.Coorbital.h < x → x < Real.pi → 0 < deriv (deriv (DominantFiveBody.twoSourceFunction p q)) x := @DominantFiveBody.twoSourceFunction_second_deriv_pos
#print axioms DominantFiveBody.twoSourceFunction_second_deriv_pos

example : ∀ {p q x : ℝ},
  0 ≤ p →
    0 ≤ q →
      p + q = 1 →
        x ≠ 0 →
          x ≠ DominantFiveBody.Coorbital.h →
            DominantFiveBody.twoSourceSpan x < Real.pi →
              p * DominantFiveBody.coorbitalKernel x +
                    q * DominantFiveBody.coorbitalKernel (x - DominantFiveBody.Coorbital.h) =
                  0 →
                0 <
                  p * DominantFiveBody.Coorbital.kappa |x| +
                    q * DominantFiveBody.Coorbital.kappa |x - DominantFiveBody.Coorbital.h| := @DominantFiveBody.twoSourceProbe
#print axioms DominantFiveBody.twoSourceProbe

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (a b k : DominantFiveBody.Satellite),
  a < b →
    0 < mass a →
      0 < mass b →
        (∀ (j : DominantFiveBody.Satellite), j ≠ a → j ≠ b → mass j = 0) →
          ∑ j : DominantFiveBody.Satellite, mass j = 1 →
            DominantFiveBody.SeparatedSemicircle theta →
              (∀ (i j : DominantFiveBody.Satellite), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
                (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = 0) →
                  k ≠ a → k ≠ b → 0 < DominantFiveBody.angularJacobian mass theta k k := @DominantFiveBody.two_source_probe_diagonal_pos
#print axioms DominantFiveBody.two_source_probe_diagonal_pos

example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (a b : DominantFiveBody.Satellite),
  a < b →
    0 < mass a →
      0 < mass b →
        (∀ (j : DominantFiveBody.Satellite), j ≠ a → j ≠ b → mass j = 0) →
          (∀ (i j : DominantFiveBody.Satellite), i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) →
            (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = 0) →
              theta b - theta a = DominantFiveBody.Coorbital.h := @DominantFiveBody.two_source_separation
#print axioms DominantFiveBody.two_source_separation

example : ∀ (x : DominantFiveBody.Configuration),
  DominantFiveBody.CollisionFree x →
    (∀ (i : DominantFiveBody.Satellite), ‖x (Fin.succ i) - x 0‖ = 1) →
      (DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder x ↔
        ∃ (theta : DominantFiveBody.Satellite → ℝ),
          DominantFiveBody.OrderedSemicircle theta ∧
            ∀ (i : DominantFiveBody.Satellite), x (Fin.succ i) - x 0 = DominantFiveBody.polarPoint 1 (theta i)) := @DominantFiveBody.unit_satellites_strictConvex_iff_open_semicircle
#print axioms DominantFiveBody.unit_satellites_strictConvex_iff_open_semicircle
