import DominantFiveBody
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Operator Topology
universe u_1 u_2 u_3 u_4 u_5 u_6 u v w
set_option linter.unusedVariables false
set_option linter.auxLemma false

-- Source binding: eq:masses
example : ∀ (ε : ℝ) (μ : DominantFiveBody.MassRatio),
  DominantFiveBody.masses ε μ (0 : DominantFiveBody.Label) = (1 : ℝ) ∧
    (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.masses ε μ (Fin.succ i) = ε * μ i) ∧
      (DominantFiveBody.PositiveRatio μ ↔
        (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < μ i) ∧ ∑ i : DominantFiveBody.Satellite, μ i = (1 : ℝ)) := @DominantFiveBody.source_masses

-- Source binding: thm:main
example : DominantFiveBody.MainUniformStatement := @DominantFiveBody.main_uniform

-- Source binding: prose:76
example : ∃ (δ : ℝ),
  (0 : ℝ) < δ ∧
    ∀ (m : DominantFiveBody.MassVector),
      DominantFiveBody.PositiveMasses m →
        (∑ i : DominantFiveBody.Satellite, m (Fin.succ i)) / m (0 : DominantFiveBody.Label) < δ →
          ∀ (σ : DominantFiveBody.HullOrder),
            ∃ (x : DominantFiveBody.Configuration),
              DominantFiveBody.StrictConvexCentralConfiguration m σ x ∧
                (∀ (y : DominantFiveBody.Configuration),
                    DominantFiveBody.StrictConvexCentralConfiguration m σ y → DominantFiveBody.OrientedSimilar x y) ∧
                  ∀ (y : DominantFiveBody.Configuration),
                    DominantFiveBody.StrictConvexCentralConfiguration m σ y →
                      DominantFiveBody.NondegenerateCentralConfiguration m y := @DominantFiveBody.main_uniform_unnormalized

-- Source binding: eq:angle-domain
example : ∀ (θ : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.CoorbitalAngleDomain θ ↔
    θ (0 : DominantFiveBody.Satellite) = (0 : ℝ) ∧
      (0 : ℝ) < θ (1 : DominantFiveBody.Satellite) ∧
        θ (1 : DominantFiveBody.Satellite) < θ (2 : DominantFiveBody.Satellite) ∧
          θ (2 : DominantFiveBody.Satellite) < θ (3 : DominantFiveBody.Satellite) ∧
            θ (3 : DominantFiveBody.Satellite) < Real.pi := @DominantFiveBody.source_angle_domain

-- Source binding: prose:88
example : ∀ (x : DominantFiveBody.Configuration),
  DominantFiveBody.CollisionFree x →
    (∀ (i : DominantFiveBody.Satellite), ‖x (Fin.succ i) - x (0 : DominantFiveBody.Label)‖ = (1 : ℝ)) →
      (DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder x ↔
        ∃ (theta : DominantFiveBody.Satellite → ℝ),
          DominantFiveBody.OrderedSemicircle theta ∧
            ∀ (i : DominantFiveBody.Satellite),
              x (Fin.succ i) - x (0 : DominantFiveBody.Label) = DominantFiveBody.polarPoint (1 : ℝ) (theta i)) := @DominantFiveBody.unit_satellites_strictConvex_iff_open_semicircle

-- Source binding: eq:kernel
example : ∀ {t : ℝ},
  (0 : ℝ) < t →
    t < Real.pi →
      deriv DominantFiveBody.Coorbital.pairPotential t = -DominantFiveBody.Coorbital.kernelF t ∧
        deriv DominantFiveBody.Coorbital.kernelF t = -DominantFiveBody.Coorbital.kappa t ∧
          deriv (deriv DominantFiveBody.Coorbital.pairPotential) t = DominantFiveBody.Coorbital.kappa t ∧
            deriv DominantFiveBody.Coorbital.kappa t = DominantFiveBody.Coorbital.kappaPrime t ∧
              DominantFiveBody.Coorbital.kappaPrime t < (0 : ℝ) := @DominantFiveBody.source_scalar_derivatives

-- Source binding: prose:95
example : ∀ (t : ℝ), DominantFiveBody.coorbitalKernel (-t) = -DominantFiveBody.coorbitalKernel t := @DominantFiveBody.coorbitalKernel_neg

-- Source binding: eq:co-equations
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    DominantFiveBody.coorbitalPotential mass theta = DominantFiveBody.angularPotential mass theta := @DominantFiveBody.coorbitalPotential_eq_angularPotential

-- Source binding: prose:101
example : ∀ (μ θ : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite),
  DominantFiveBody.coorbitalResidual μ θ i =
    ∑ j : DominantFiveBody.Satellite, μ j * DominantFiveBody.coorbitalMatrix θ i j := @DominantFiveBody.coorbitalResidual_eq_matrix_sum

-- Source binding: prose:101
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    ∀ (k : DominantFiveBody.Satellite),
      (fderiv ℝ (DominantFiveBody.coorbitalPotential mass) theta : (DominantFiveBody.Satellite → ℝ) → ℝ)
          (Pi.single k (1 : ℝ)) =
        mass k * DominantFiveBody.coorbitalResidual mass theta k := @DominantFiveBody.coorbitalPotential_coordinate_derivative

-- Source binding: prose:111
example : DominantFiveBody.Coorbital.kernelF DominantFiveBody.Coorbital.h = (0 : ℝ) := @DominantFiveBody.Coorbital.kernelF_h

-- Source binding: prose:111
example : DominantFiveBody.Coorbital.kernelF Real.pi = (0 : ℝ) := @DominantFiveBody.Coorbital.kernelF_pi

-- Source binding: prose:111
example : ∀ {t : ℝ}, (0 : ℝ) < t → t < DominantFiveBody.Coorbital.h → (0 : ℝ) < DominantFiveBody.Coorbital.kernelF t := @DominantFiveBody.Coorbital.kernelF_pos_on_short_arc

-- Source binding: prose:111
example : ∀ {t : ℝ}, DominantFiveBody.Coorbital.h < t → t < Real.pi → DominantFiveBody.Coorbital.kernelF t < (0 : ℝ) := @DominantFiveBody.Coorbital.kernelF_neg_on_long_arc

-- Source binding: prose:111
example : DominantFiveBody.Coorbital.kappa DominantFiveBody.Coorbital.h = (9 / 4 : ℝ) := @DominantFiveBody.Coorbital.kappa_h

-- Source binding: prose:111
example : ∀ {t : ℝ}, (0 : ℝ) < t → t < Real.pi → (-1 : ℝ) ≤ DominantFiveBody.Coorbital.kernelF t := @DominantFiveBody.Coorbital.kernelF_ge_neg_one

-- Source binding: prose:111
example : Filter.Tendsto (fun (t : ℝ) => t * DominantFiveBody.Coorbital.kernelF t) (𝓝[>] (0 : ℝ)) Filter.atTop := @DominantFiveBody.kernelF_angle_mul_tendsto_atTop

-- Source binding: v1:hessian.coordinates
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite),
  i < j →
    DominantFiveBody.coorbitalHessianCoefficient mass theta i j =
      mass i * mass j * DominantFiveBody.Coorbital.kappa (theta j - theta i) := @DominantFiveBody.coorbitalHessianCoefficient_of_lt

-- Source binding: v1:hessian.coordinates
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite),
  DominantFiveBody.coorbitalHessianCoefficient mass theta i j =
    DominantFiveBody.coorbitalHessianCoefficient mass theta j i := @DominantFiveBody.coorbitalHessianCoefficient_symmetric

-- Source binding: v1:hessian.coordinates
example : ∀ (mass theta u v : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    DominantFiveBody.coorbitalPhysicalHessian mass theta u v =
      ∑ i : DominantFiveBody.Satellite,
        ∑ j : DominantFiveBody.Satellite,
          if i < j then
            mass i * mass j * DominantFiveBody.Coorbital.kappa (theta j - theta i) * (u j - u i) * (v j - v i)
          else (0 : ℝ) := @DominantFiveBody.coorbitalPhysicalHessian_pair_formula

-- Source binding: v1:hessian.entries
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    ∀ (i : DominantFiveBody.Satellite),
      DominantFiveBody.coorbitalHessianMatrix mass theta i i =
        ∑ j ∈ Finset.univ.erase i, DominantFiveBody.coorbitalHessianCoefficient mass theta i j := @DominantFiveBody.coorbitalHessianMatrix_diagonal

-- Source binding: v1:hessian.entries
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    ∀ (i j : DominantFiveBody.Satellite),
      i ≠ j →
        DominantFiveBody.coorbitalHessianMatrix mass theta i j =
          -DominantFiveBody.coorbitalHessianCoefficient mass theta i j := @DominantFiveBody.coorbitalHessianMatrix_offDiagonal

-- Source binding: v1:hessian.quadratic
example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    u ⬝ᵥ (DominantFiveBody.coorbitalHessianMatrix mass theta).mulVec u =
      ∑ i : DominantFiveBody.Satellite,
        ∑ j : DominantFiveBody.Satellite,
          if i < j then mass i * mass j * DominantFiveBody.Coorbital.kappa (theta j - theta i) * (u j - u i) ^ (2 : ℕ)
          else (0 : ℝ) := @DominantFiveBody.coorbitalHessianMatrix_quadratic

-- Source binding: v1:hessian.quadratic
example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    u ⬝ᵥ (DominantFiveBody.coorbitalHessianMatrix mass theta).mulVec u =
      ∑ i : DominantFiveBody.Satellite,
        ∑ j : DominantFiveBody.Satellite,
          if i < j then
            DominantFiveBody.coorbitalHessianCoefficient mass theta i j *
              (u i ^ (2 : ℕ) + u j ^ (2 : ℕ) - (2 : ℝ) * u i * u j)
          else (0 : ℝ) := @DominantFiveBody.coorbitalHessianMatrix_quadratic_expanded

-- Source binding: v1:hessian.slice
example : ∀ (mass : DominantFiveBody.Satellite → ℝ) (z u v : Fin (3 : ℕ) → ℝ),
  DominantFiveBody.OrderedSemicircle
      ((DominantFiveBody.coorbitalFirstAngleInsertion : (Fin (3 : ℕ) → ℝ) → DominantFiveBody.Satellite → ℝ) z) →
    ((fderiv ℝ (fderiv ℝ (DominantFiveBody.coorbitalSlicePotential mass)) z :
              (Fin (3 : ℕ) → ℝ) → (Fin (3 : ℕ) → ℝ) →L[ℝ] ℝ)
            u :
          (Fin (3 : ℕ) → ℝ) → ℝ)
        v =
      DominantFiveBody.coorbitalPhysicalHessian mass
        ((DominantFiveBody.coorbitalFirstAngleInsertion : (Fin (3 : ℕ) → ℝ) → DominantFiveBody.Satellite → ℝ) z)
        ((DominantFiveBody.coorbitalFirstAngleInsertion : (Fin (3 : ℕ) → ℝ) → DominantFiveBody.Satellite → ℝ) u)
        ((DominantFiveBody.coorbitalFirstAngleInsertion : (Fin (3 : ℕ) → ℝ) → DominantFiveBody.Satellite → ℝ) v) := @DominantFiveBody.coorbitalSlicePotential_hessian_pullback

-- Source binding: v1:hessian.slice
example : ∀ (mass : DominantFiveBody.Satellite → ℝ) (z : Fin (3 : ℕ) → ℝ),
  DominantFiveBody.OrderedSemicircle
      ((DominantFiveBody.coorbitalFirstAngleInsertion : (Fin (3 : ℕ) → ℝ) → DominantFiveBody.Satellite → ℝ) z) →
    DominantFiveBody.coorbitalSliceHessianMatrix mass z =
      (DominantFiveBody.coorbitalHessianMatrix mass
            ((DominantFiveBody.coorbitalFirstAngleInsertion : (Fin (3 : ℕ) → ℝ) → DominantFiveBody.Satellite → ℝ)
              z)).submatrix
        Fin.succ Fin.succ := @DominantFiveBody.coorbitalSliceHessianMatrix_eq_submatrix

-- Source binding: v1:hessian.slice
example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    theta (0 : DominantFiveBody.Satellite) = (0 : ℝ) →
      u (0 : DominantFiveBody.Satellite) = (0 : ℝ) →
        (((fderiv ℝ (fderiv ℝ (DominantFiveBody.coorbitalSlicePotential mass)) fun (i : Fin (3 : ℕ)) => theta i.succ :
                  (Fin (3 : ℕ) → ℝ) → (Fin (3 : ℕ) → ℝ) →L[ℝ] ℝ)
                fun (i : Fin (3 : ℕ)) => u i.succ :
              (Fin (3 : ℕ) → ℝ) → ℝ)
            fun (i : Fin (3 : ℕ)) => u i.succ) =
          DominantFiveBody.Coorbital.coorbitalKappaForm mass theta u := @DominantFiveBody.coorbitalSliceHessian_quadratic_zero_first

-- Source binding: lem:cycle
example : ∀ {n : ℕ},
  (2 : ℕ) ≤ n →
    n ≤ (4 : ℕ) →
      ∀ (mass theta : Fin n → ℝ),
        (∀ (i : Fin n), (0 : ℝ) < mass i) →
          DominantFiveBody.OrderedSemicircle theta →
            (∀ (i : Fin n), DominantFiveBody.Coorbital.angularEquation mass theta i = (0 : ℝ)) →
              (∀ (i j : Fin n), i < j → (0 : ℝ) < DominantFiveBody.Coorbital.positiveRemainder (theta j - theta i)) ∧
                (∀ (u : Fin n → ℝ),
                    DominantFiveBody.angularChordHessian mass theta u u =
                        DominantFiveBody.Coorbital.coorbitalKappaForm mass theta u ∧
                      DominantFiveBody.Coorbital.coorbitalRemainderForm mass theta u ≤
                        DominantFiveBody.angularChordHessian mass theta u u) ∧
                  ∀ (u : Fin n → ℝ),
                    (∀ (v : Fin n → ℝ), DominantFiveBody.angularChordHessian mass theta u v = (0 : ℝ)) ↔
                      ∀ (i j : Fin n), u i = u j := @DominantFiveBody.angular_hessian_estimate

-- Source binding: prose:127
example : ∀ {t : ℝ}, (0 : ℝ) < t → t < Real.pi → (0 : ℝ) < DominantFiveBody.Coorbital.positiveRemainder t := @DominantFiveBody.Coorbital.positiveRemainder_pos

-- Source binding: eq:cycle-bound
example : ∀ {n : ℕ},
  (2 : ℕ) ≤ n →
    n ≤ (4 : ℕ) →
      ∀ (mass theta u : Fin n → ℝ),
        (∀ (i : Fin n), (0 : ℝ) < mass i) →
          (∀ (i j : Fin n), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
            (∀ (i : Fin n), DominantFiveBody.Coorbital.angularEquation mass theta i = (0 : ℝ)) →
              DominantFiveBody.Coorbital.coorbitalRemainderForm mass theta u ≤
                DominantFiveBody.Coorbital.coorbitalKappaForm mass theta u := @DominantFiveBody.Coorbital.coorbital_cycle_bound

-- Source binding: prose:132
example : ∀ {n : ℕ},
  (2 : ℕ) ≤ n →
    n ≤ (4 : ℕ) →
      ∀ (mass theta u : Fin n → ℝ),
        (∀ (i : Fin n), (0 : ℝ) < mass i) →
          DominantFiveBody.OrderedSemicircle theta →
            (∀ (i : Fin n), DominantFiveBody.Coorbital.angularEquation mass theta i = (0 : ℝ)) →
              ((∀ (v : Fin n → ℝ), DominantFiveBody.angularChordHessian mass theta u v = (0 : ℝ)) ↔
                ∀ (i j : Fin n), u i = u j) := @DominantFiveBody.angularChordHessian_kernel_iff

-- Source binding: prose:132
example : StrictAntiOn DominantFiveBody.Coorbital.kappa (Set.Ioo (0 : ℝ) Real.pi) := @DominantFiveBody.Coorbital.strictAntiOn_kappa

-- Source binding: display:136
example : (∀ (t : ℝ),
    (0 : ℝ) < t →
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

-- Source binding: display:136
example : ∀ {a b : ℝ},
  (0 : ℝ) < a →
    a ≤ b → b ≤ Real.pi → IntervalIntegrable DominantFiveBody.Coorbital.kappa MeasureTheory.MeasureSpace.volume a b := @DominantFiveBody.Coorbital.kappa_intervalIntegrable

-- Source binding: prose:142
example : ∀ {n : ℕ} (mass theta : Fin n → ℝ),
  (∀ (i : Fin n), DominantFiveBody.Coorbital.angularEquation mass theta i = (0 : ℝ)) →
    ∀ (i : Fin n), ∑ j : Fin n, DominantFiveBody.Coorbital.angularFlow mass theta i j = (0 : ℝ) := @DominantFiveBody.Coorbital.angularFlow_balanced

-- Source binding: prose:142
example : ∀ (mass theta : Fin (4 : ℕ) → ℝ),
  (∀ (i : Fin (4 : ℕ)), (0 : ℝ) < mass i) →
    (∀ (i j : Fin (4 : ℕ)), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
      (∀ (i : Fin (4 : ℕ)), DominantFiveBody.Coorbital.angularEquation mass theta i = (0 : ℝ)) →
        ∃ (p : ℝ) (q : ℝ) (r : ℝ) (s : ℝ) (t : ℝ),
          (0 : ℝ) ≤ p ∧
            (0 : ℝ) ≤ q ∧
              (0 : ℝ) ≤ r ∧
                (0 : ℝ) ≤ s ∧
                  (0 : ℝ) ≤ t ∧
                    DominantFiveBody.Coorbital.angularFlow mass theta (0 : Fin (4 : ℕ)) (1 : Fin (4 : ℕ)) = p + s + t ∧
                      DominantFiveBody.Coorbital.angularFlow mass theta (1 : Fin (4 : ℕ)) (2 : Fin (4 : ℕ)) =
                          p + q + t ∧
                        DominantFiveBody.Coorbital.angularFlow mass theta (2 : Fin (4 : ℕ)) (3 : Fin (4 : ℕ)) =
                            q + r + t ∧
                          DominantFiveBody.Coorbital.angularFlow mass theta (0 : Fin (4 : ℕ)) (2 : Fin (4 : ℕ)) =
                              r - p ∧
                            DominantFiveBody.Coorbital.angularFlow mass theta (1 : Fin (4 : ℕ)) (3 : Fin (4 : ℕ)) =
                                s - q ∧
                              DominantFiveBody.Coorbital.angularFlow mass theta (0 : Fin (4 : ℕ)) (3 : Fin (4 : ℕ)) =
                                  -(r + s + t) ∧
                                ((0 : ℝ) < p →
                                    DominantFiveBody.Coorbital.angularFlow mass theta (0 : Fin (4 : ℕ))
                                        (2 : Fin (4 : ℕ)) <
                                      (0 : ℝ)) ∧
                                  ((0 : ℝ) < q →
                                      DominantFiveBody.Coorbital.angularFlow mass theta (1 : Fin (4 : ℕ))
                                          (3 : Fin (4 : ℕ)) <
                                        (0 : ℝ)) ∧
                                    ((0 : ℝ) < r →
                                        (0 : ℝ) <
                                          DominantFiveBody.Coorbital.angularFlow mass theta (0 : Fin (4 : ℕ))
                                            (2 : Fin (4 : ℕ))) ∧
                                      ((0 : ℝ) < s →
                                        (0 : ℝ) <
                                          DominantFiveBody.Coorbital.angularFlow mass theta (1 : Fin (4 : ℕ))
                                            (3 : Fin (4 : ℕ))) := @DominantFiveBody.Coorbital.four_angular_cycle_decomposition

-- Source binding: prose:142
example : ∀ {n : ℕ} (mass theta : Fin n → ℝ),
  (∀ (i : Fin n), (0 : ℝ) < mass i) →
    ∀ (i j : Fin n),
      (0 : ℝ) < theta j - theta i →
        theta j - theta i < Real.pi →
          ((0 : ℝ) < DominantFiveBody.Coorbital.angularFlow mass theta i j ↔
            theta j - theta i < DominantFiveBody.Coorbital.h) := @DominantFiveBody.Coorbital.angularFlow_pos_iff

-- Source binding: prose:142
example : ∀ {n : ℕ} (mass theta : Fin n → ℝ),
  (∀ (i : Fin n), (0 : ℝ) < mass i) →
    ∀ (i j : Fin n),
      (0 : ℝ) < theta j - theta i →
        theta j - theta i < Real.pi →
          (DominantFiveBody.Coorbital.angularFlow mass theta i j < (0 : ℝ) ↔
            DominantFiveBody.Coorbital.h < theta j - theta i) := @DominantFiveBody.Coorbital.angularFlow_neg_iff

-- Source binding: prose:142
example : ∀ (mass theta : Fin (3 : ℕ) → ℝ),
  (∀ (i : Fin (3 : ℕ)), (0 : ℝ) < mass i) →
    (∀ (i j : Fin (3 : ℕ)), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
      (∀ (i : Fin (3 : ℕ)), DominantFiveBody.Coorbital.angularEquation mass theta i = (0 : ℝ)) →
        theta (1 : Fin (3 : ℕ)) - theta (0 : Fin (3 : ℕ)) < DominantFiveBody.Coorbital.h ∧
          theta (2 : Fin (3 : ℕ)) - theta (1 : Fin (3 : ℕ)) < DominantFiveBody.Coorbital.h ∧
            DominantFiveBody.Coorbital.h < theta (2 : Fin (3 : ℕ)) - theta (0 : Fin (3 : ℕ)) := @DominantFiveBody.Coorbital.three_root_gaps

-- Source binding: prose:142
example : ∀ (mass theta : Fin (2 : ℕ) → ℝ),
  (∀ (i : Fin (2 : ℕ)), (0 : ℝ) < mass i) →
    (∀ (i j : Fin (2 : ℕ)), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
      (∀ (i : Fin (2 : ℕ)), DominantFiveBody.Coorbital.angularEquation mass theta i = (0 : ℝ)) →
        theta (1 : Fin (2 : ℕ)) - theta (0 : Fin (2 : ℕ)) = DominantFiveBody.Coorbital.h := @DominantFiveBody.Coorbital.two_root_separation

-- Source binding: display:146
example : ∀ (s t u v : ℝ),
  s < DominantFiveBody.Coorbital.h →
    t < DominantFiveBody.Coorbital.h →
      s + t < Real.pi →
        (u + v) ^ (2 : ℕ) / ((2 : ℝ) * DominantFiveBody.Coorbital.h - (s + t)) -
              (u + v) ^ (2 : ℕ) / (Real.pi - (s + t)) ≤
            u ^ (2 : ℕ) / (DominantFiveBody.Coorbital.h - s) + v ^ (2 : ℕ) / (DominantFiveBody.Coorbital.h - t) -
              (u + v) ^ (2 : ℕ) / (Real.pi - (s + t)) ∧
          (0 : ℝ) ≤
            (u + v) ^ (2 : ℕ) / ((2 : ℝ) * DominantFiveBody.Coorbital.h - (s + t)) -
              (u + v) ^ (2 : ℕ) / (Real.pi - (s + t)) := @DominantFiveBody.Coorbital.two_cycle_display

-- Source binding: display:146
example : ∀ (s t r u v w : ℝ),
  s < DominantFiveBody.Coorbital.h →
    t < DominantFiveBody.Coorbital.h →
      r < DominantFiveBody.Coorbital.h →
        (u + v + w) ^ (2 : ℕ) / ((3 : ℝ) * DominantFiveBody.Coorbital.h - (s + t + r)) -
              (u + v + w) ^ (2 : ℕ) / (Real.pi - (s + t + r)) ≤
            u ^ (2 : ℕ) / (DominantFiveBody.Coorbital.h - s) + v ^ (2 : ℕ) / (DominantFiveBody.Coorbital.h - t) +
                w ^ (2 : ℕ) / (DominantFiveBody.Coorbital.h - r) -
              (u + v + w) ^ (2 : ℕ) / (Real.pi - (s + t + r)) ∧
          (0 : ℝ) ≤
            (u + v + w) ^ (2 : ℕ) / ((3 : ℝ) * DominantFiveBody.Coorbital.h - (s + t + r)) -
              (u + v + w) ^ (2 : ℕ) / (Real.pi - (s + t + r)) := @DominantFiveBody.Coorbital.three_cycle_display

-- Source binding: display:146
example : ∀ (a b u v : ℝ),
  (0 : ℝ) < a → (0 : ℝ) < b → ((u + v) ^ (2 : ℕ) / (a + b) = u ^ (2 : ℕ) / a + v ^ (2 : ℕ) / b ↔ b * u = a * v) := @DominantFiveBody.Coorbital.two_denominator_cauchy_eq_iff

-- Source binding: display:146
example : ∀ (s t u v : ℝ),
  s < DominantFiveBody.Coorbital.h →
    t < DominantFiveBody.Coorbital.h →
      s + t < Real.pi →
        (u ^ (2 : ℕ) / (DominantFiveBody.Coorbital.h - s) + v ^ (2 : ℕ) / (DominantFiveBody.Coorbital.h - t) -
              (u + v) ^ (2 : ℕ) / (Real.pi - (s + t)) =
            (0 : ℝ) ↔
          u = (0 : ℝ) ∧ v = (0 : ℝ)) := @DominantFiveBody.Coorbital.two_edge_cycle_eq_zero_iff

-- Source binding: display:146
example : ∀ (s t r u v w : ℝ),
  s < DominantFiveBody.Coorbital.h →
    t < DominantFiveBody.Coorbital.h →
      r < DominantFiveBody.Coorbital.h →
        (u ^ (2 : ℕ) / (DominantFiveBody.Coorbital.h - s) + v ^ (2 : ℕ) / (DominantFiveBody.Coorbital.h - t) +
                w ^ (2 : ℕ) / (DominantFiveBody.Coorbital.h - r) -
              (u + v + w) ^ (2 : ℕ) / (Real.pi - (s + t + r)) =
            (0 : ℝ) ↔
          (DominantFiveBody.Coorbital.h - t) * u = (DominantFiveBody.Coorbital.h - s) * v ∧
            (DominantFiveBody.Coorbital.h - r) * (u + v) =
              (DominantFiveBody.Coorbital.h - s + (DominantFiveBody.Coorbital.h - t)) * w) := @DominantFiveBody.Coorbital.three_edge_cycle_eq_zero_iff

-- Source binding: prose:152
example : ∀ {n : ℕ} (mass theta u : Fin n → ℝ) (c : ℝ),
  (((DominantFiveBody.angularHessianMap mass theta : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) u : (Fin n → ℝ) → ℝ)
      fun (x : Fin n) => c) =
    (0 : ℝ) := @DominantFiveBody.angularHessianMap_constant_right

-- Source binding: prose:155
example : (∀ (m : DominantFiveBody.MassRatio),
    DominantFiveBody.PositiveRatio m →
      ∃! theta : DominantFiveBody.Satellite → ℝ,
        DominantFiveBody.CoorbitalAngleDomain theta ∧
          ∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual m theta i = (0 : ℝ)) ∧
  ContDiffOn ℝ ∞ DominantFiveBody.coorbitalRootAngles
      {m : DominantFiveBody.MassRatio | DominantFiveBody.PositiveRatio m} ∧
    (∀ (m : DominantFiveBody.MassRatio),
        DominantFiveBody.PositiveRatio m →
          ∀ (u : DominantFiveBody.Satellite → ℝ),
            u (0 : DominantFiveBody.Satellite) = (0 : ℝ) →
              u ≠ (0 : DominantFiveBody.Satellite → ℝ) →
                (0 : ℝ) < DominantFiveBody.coorbitalPhysicalHessian m (DominantFiveBody.coorbitalRootAngles m) u u) ∧
      IsProperMap DominantFiveBody.coorbitalMassProjection ∧
        IsCoveringMapOn DominantFiveBody.coorbitalMassProjection Set.univ := @DominantFiveBody.coorbital_global_complete

-- Source binding: prose:155
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    (∀ (i : Fin (4 : ℕ)), DominantFiveBody.Coorbital.angularEquation mass theta i = (0 : ℝ)) →
      ∀ (k : Fin (3 : ℕ)),
        (∑ i : DominantFiveBody.Satellite,
            ∑ j : DominantFiveBody.Satellite,
              if (↑i : ℕ) ≤ (↑k : ℕ) ∧ (↑k : ℕ) < (↑j : ℕ) then
                mass i * mass j * DominantFiveBody.Coorbital.kernelF (theta j - theta i)
              else (0 : ℝ)) =
          (0 : ℝ) := @DominantFiveBody.coorbital_cut

-- Source binding: prose:155
example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    DominantFiveBody.coorbitalPhysicalHessian mass theta u u =
      DominantFiveBody.Coorbital.coorbitalKappaForm mass theta u := @DominantFiveBody.coorbitalPhysicalHessian_self

-- Source binding: prose:163
example : ∀ (mass theta : Fin (4 : ℕ) → ℝ),
  (∀ (i : Fin (4 : ℕ)), (0 : ℝ) < mass i) →
    (∀ (i j : Fin (4 : ℕ)), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
      (∀ (i : Fin (4 : ℕ)), DominantFiveBody.Coorbital.angularEquation mass theta i = (0 : ℝ)) →
        theta (1 : Fin (4 : ℕ)) - theta (0 : Fin (4 : ℕ)) < DominantFiveBody.Coorbital.h ∧
          theta (2 : Fin (4 : ℕ)) - theta (1 : Fin (4 : ℕ)) < DominantFiveBody.Coorbital.h ∧
            theta (3 : Fin (4 : ℕ)) - theta (2 : Fin (4 : ℕ)) < DominantFiveBody.Coorbital.h ∧
              DominantFiveBody.Coorbital.h < theta (3 : Fin (4 : ℕ)) - theta (0 : Fin (4 : ℕ)) := @DominantFiveBody.Coorbital.four_root_gaps

-- Source binding: prose:163
example : ∀ (K : Set (DominantFiveBody.Satellite → ℝ)),
  IsCompact K →
    (∀ m ∈ K, ∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < m i) →
      ∃ (alpha : ℝ), (0 : ℝ) < alpha ∧ ∀ m ∈ K, ∀ (i : DominantFiveBody.Satellite), alpha ≤ m i := @DominantFiveBody.compact_positive_mass_floor

-- Source binding: prose:163
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.OrderedSemicircle theta →
    (∀ (i : Fin (4 : ℕ)), DominantFiveBody.Coorbital.angularEquation mass theta i = (0 : ℝ)) →
      DominantFiveBody.coorbitalVirial mass theta = (0 : ℝ) := @DominantFiveBody.coorbitalVirial_zero

-- Source binding: prose:167
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.PositiveRatio mass →
    DominantFiveBody.OrderedSemicircle theta →
      -Real.pi / (2 : ℝ) ≤
        ∑ i : DominantFiveBody.Satellite,
          ∑ j : DominantFiveBody.Satellite,
            if i < j then
              Min.min (mass i * mass j * (theta j - theta i) * DominantFiveBody.Coorbital.kernelF (theta j - theta i))
                (0 : ℝ)
            else (0 : ℝ) := @DominantFiveBody.coorbital_negative_terms_lower_bound

-- Source binding: prose:167
example : ∀ (alpha : ℝ),
  (0 : ℝ) < alpha →
    ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
      DominantFiveBody.PositiveRatio mass →
        (∀ (i : DominantFiveBody.Satellite), alpha ≤ mass i) →
          DominantFiveBody.OrderedSemicircle theta →
            (∀ (i : Fin (4 : ℕ)), DominantFiveBody.Coorbital.angularEquation mass theta i = (0 : ℝ)) →
              ∀ (i j : DominantFiveBody.Satellite),
                i < j →
                  theta j - theta i < DominantFiveBody.Coorbital.h →
                    alpha ^ (2 : ℕ) * ((theta j - theta i) * DominantFiveBody.Coorbital.kernelF (theta j - theta i)) ≤
                      Real.pi / (2 : ℝ) := @DominantFiveBody.coorbitalVirial_pair_with_mass_floor

-- Source binding: prose:167
example : ∀ (alpha : ℝ),
  (0 : ℝ) < alpha →
    ∃ (d : ℝ),
      (0 : ℝ) < d ∧
        ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
          DominantFiveBody.PositiveRatio mass →
            (∀ (i : DominantFiveBody.Satellite), alpha ≤ mass i) →
              DominantFiveBody.OrderedSemicircle theta →
                (∀ (i : Fin (4 : ℕ)), DominantFiveBody.Coorbital.angularEquation mass theta i = (0 : ℝ)) →
                  ∀ (i j : DominantFiveBody.Satellite), i < j → d ≤ theta j - theta i := @DominantFiveBody.coorbital_roots_uniform_pair_separation

-- Source binding: prose:167
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < mass i) →
    theta (1 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite) ≤ DominantFiveBody.Coorbital.h ∧
        theta (2 : DominantFiveBody.Satellite) - theta (1 : DominantFiveBody.Satellite) ≤ DominantFiveBody.Coorbital.h ∧
          theta (3 : DominantFiveBody.Satellite) - theta (2 : DominantFiveBody.Satellite) ≤
            DominantFiveBody.Coorbital.h →
      theta (3 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite) = Real.pi →
        (∀ (i : Fin (4 : ℕ)), DominantFiveBody.Coorbital.angularEquation mass theta i = (0 : ℝ)) → False := @DominantFiveBody.no_coorbital_root_at_semicircle_boundary

-- Source binding: prose:167
example : IsProperMap DominantFiveBody.coorbitalMassProjection := @DominantFiveBody.coorbitalMassProjection_isProperMap

-- Source binding: prose:169
example : ∀ (μ θ : DominantFiveBody.Satellite → ℝ),
  ∑ i : DominantFiveBody.Satellite, μ i * DominantFiveBody.coorbitalResidual μ θ i = (0 : ℝ) := @DominantFiveBody.coorbital_weightedResidual_zero

-- Source binding: prose:169
example : ∀ (μ θ : DominantFiveBody.Satellite → ℝ) (p : DominantFiveBody.Satellite),
  (0 : ℝ) < μ p →
    (∀ (i : DominantFiveBody.Satellite), i ≠ p → DominantFiveBody.coorbitalResidual μ θ i = (0 : ℝ)) →
      DominantFiveBody.coorbitalResidual μ θ p = (0 : ℝ) := @DominantFiveBody.coorbital_recover_positive_mass_row

-- Source binding: prose:169
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (p q : DominantFiveBody.Satellite),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < mass i) →
    (∀ (i j : DominantFiveBody.Satellite), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
      (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = (0 : ℝ)) →
        IsUnit (DominantFiveBody.deletedAngularJacobian mass theta p q) := @DominantFiveBody.deletedAngularJacobian_isUnit_positive

-- Source binding: prose:169
example : IsLocalHomeomorphOn DominantFiveBody.coorbitalMassProjection Set.univ := @DominantFiveBody.coorbitalMassProjection_isLocalHomeomorphOn

-- Source binding: prose:169
example : ∀ (m : DominantFiveBody.CoorbitalMassSpace), (DominantFiveBody.coorbitalMassProjection ⁻¹' {m}).Finite := @DominantFiveBody.coorbitalMassProjection_fiber_finite

-- Source binding: prose:169
example : IsCoveringMapOn DominantFiveBody.coorbitalMassProjection Set.univ := @DominantFiveBody.coorbitalMassProjection_isCoveringMapOn

-- Source binding: prose:169
example : ∃! theta : DominantFiveBody.Satellite → ℝ,
  DominantFiveBody.CoorbitalAngleDomain theta ∧
    ∀ (i : DominantFiveBody.Satellite),
      DominantFiveBody.coorbitalResidual DominantFiveBody.equalMassRatio theta i = (0 : ℝ) := @DominantFiveBody.equalMass_coorbital_existsUnique

-- Source binding: prose:169
example : ∀ (theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.CoorbitalAngleDomain theta →
    (∀ (i : DominantFiveBody.Satellite),
        DominantFiveBody.coorbitalResidual DominantFiveBody.equalMassRatio theta i = (0 : ℝ)) →
      theta (1 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite) =
        theta (3 : DominantFiveBody.Satellite) - theta (2 : DominantFiveBody.Satellite) := @DominantFiveBody.equalMass_root_reversal_symmetry

-- Source binding: lem:probe
example : ∀ {p q x : ℝ},
  (0 : ℝ) ≤ p →
    (0 : ℝ) ≤ q →
      p + q = (1 : ℝ) →
        x ≠ (0 : ℝ) →
          x ≠ DominantFiveBody.Coorbital.h →
            DominantFiveBody.twoSourceSpan x < Real.pi →
              p * DominantFiveBody.coorbitalKernel x +
                    q * DominantFiveBody.coorbitalKernel (x - DominantFiveBody.Coorbital.h) =
                  (0 : ℝ) →
                (0 : ℝ) <
                  p * DominantFiveBody.Coorbital.kappa |x| +
                    q * DominantFiveBody.Coorbital.kappa |x - DominantFiveBody.Coorbital.h| := @DominantFiveBody.twoSourceProbe

-- Source binding: prose:184
example : ∀ {p q x : ℝ},
  x ≠ (0 : ℝ) →
    x ≠ DominantFiveBody.Coorbital.h →
      DominantFiveBody.twoSourceSpan x < Real.pi →
        HasDerivAt
          (fun (t : ℝ) =>
            p * DominantFiveBody.coorbitalKernel t +
              q * DominantFiveBody.coorbitalKernel (t - DominantFiveBody.Coorbital.h))
          (-(p * DominantFiveBody.Coorbital.kappa |x| +
              q * DominantFiveBody.Coorbital.kappa |x - DominantFiveBody.Coorbital.h|))
          x := @DominantFiveBody.signedProbe_hasDerivAt

-- Source binding: prose:184
example : ∀ {p q x : ℝ},
  (0 : ℝ) ≤ p →
    (0 : ℝ) < q →
      (0 : ℝ) < x →
        x < DominantFiveBody.Coorbital.h →
          deriv
              (fun (t : ℝ) =>
                p * DominantFiveBody.coorbitalKernel t +
                  q * DominantFiveBody.coorbitalKernel (t - DominantFiveBody.Coorbital.h))
              x <
            (0 : ℝ) := @DominantFiveBody.signedProbe_inner_deriv_neg

-- Source binding: prose:184
example : ∀ {p q x : ℝ},
  (0 : ℝ) ≤ p →
    (0 : ℝ) < q →
      DominantFiveBody.Coorbital.h < x →
        x < Real.pi → (0 : ℝ) < deriv (deriv (DominantFiveBody.twoSourceFunction p q)) x := @DominantFiveBody.twoSourceFunction_second_deriv_pos

-- Source binding: prose:184
example : ∀ (p q : ℝ),
  DominantFiveBody.twoSourceFunction p q Real.pi =
    q * DominantFiveBody.Coorbital.kernelF (Real.pi - DominantFiveBody.Coorbital.h) := @DominantFiveBody.twoSourceFunction_endpoint

-- Source binding: prose:184
example : ∀ {p q x : ℝ},
  (0 : ℝ) ≤ p →
    (0 : ℝ) < q →
      DominantFiveBody.Coorbital.h < x →
        x < Real.pi →
          DominantFiveBody.twoSourceFunction p q x = (0 : ℝ) →
            deriv (DominantFiveBody.twoSourceFunction p q) x <
                DominantFiveBody.twoSourceFunction p q Real.pi / (Real.pi - x) ∧
              DominantFiveBody.twoSourceFunction p q Real.pi / (Real.pi - x) < (0 : ℝ) := @DominantFiveBody.twoSourceFunction_root_strict_secant

-- Source binding: prose:184
example : ∀ (p q x : ℝ),
  q * DominantFiveBody.coorbitalKernel (DominantFiveBody.Coorbital.h - x) +
      p * DominantFiveBody.coorbitalKernel (DominantFiveBody.Coorbital.h - x - DominantFiveBody.Coorbital.h) =
    -(p * DominantFiveBody.coorbitalKernel x + q * DominantFiveBody.coorbitalKernel (x - DominantFiveBody.Coorbital.h)) := @DominantFiveBody.signedProbe_reflection

-- Source binding: prop:closed
example : (∀ (mass theta : DominantFiveBody.Satellite → ℝ),
    (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) ≤ mass i) →
      ∑ i : DominantFiveBody.Satellite, mass i = (1 : ℝ) →
        DominantFiveBody.SeparatedSemicircle theta →
          (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = (0 : ℝ)) →
            HasFDerivAt
                (fun (angles : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) =>
                  DominantFiveBody.coorbitalResidual mass angles i)
                (DominantFiveBody.angularDifferential mass theta) theta ∧
              (∀ (u : DominantFiveBody.Satellite → ℝ),
                  (DominantFiveBody.angularDifferential mass theta :
                          (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
                        u =
                      (0 : DominantFiveBody.Satellite → ℝ) ↔
                    ∀ (i j : DominantFiveBody.Satellite), u i = u j) ∧
                ∀ (p q : DominantFiveBody.Satellite),
                  (0 : ℝ) < mass p → IsUnit (DominantFiveBody.deletedAngularJacobian mass theta p q)) ∧
  ∀ (K : Set ((DominantFiveBody.Satellite → ℝ) × (DominantFiveBody.Satellite → ℝ))) (delta eta : ℝ)
    (p q : DominantFiveBody.Satellite),
    IsClosed K →
      (0 : ℝ) < delta →
        (0 : ℝ) < eta →
          (∀ z ∈ K,
              (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) ≤ z.1 i) ∧
                ∑ i : DominantFiveBody.Satellite, z.1 i = (1 : ℝ) ∧
                  z.2 (0 : DominantFiveBody.Satellite) = (0 : ℝ) ∧
                    (∀ (i : Fin (3 : ℕ)), delta ≤ z.2 i.succ - z.2 i.castSucc) ∧
                      z.2 (3 : DominantFiveBody.Satellite) - z.2 (0 : DominantFiveBody.Satellite) ≤ Real.pi - eta ∧
                        (1 / 4 : ℝ) ≤ z.1 p ∧
                          ∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual z.1 z.2 i = (0 : ℝ)) →
            ∃ (C : ℝ), (0 : ℝ) < C ∧ ∀ z ∈ K, ‖(DominantFiveBody.deletedAngularJacobian z.1 z.2 p q)⁻¹‖ ≤ C := @DominantFiveBody.coorbital_closed_mass_jacobian_complete

-- Source binding: prose:191
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (p : DominantFiveBody.Satellite),
  (0 : ℝ) < mass p →
    (∀ (i : DominantFiveBody.Satellite), i ≠ p → mass i = (0 : ℝ)) →
      DominantFiveBody.SeparatedSemicircle theta →
        (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = (0 : ℝ)) → False := @DominantFiveBody.no_one_source_coorbital_root

-- Source binding: prose:191
example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ) (k : DominantFiveBody.Satellite),
  mass k = (0 : ℝ) →
    (∀ (i : DominantFiveBody.Satellite), i ≠ k → (0 : ℝ) < mass i) →
      (∀ (i j : DominantFiveBody.Satellite), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
        (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = (0 : ℝ)) →
          (DominantFiveBody.angularDifferential mass theta :
                  (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
                u =
              (0 : DominantFiveBody.Satellite → ℝ) →
            ∀ (i j : Fin (3 : ℕ)), u (Fin.succAbove k i) = u (Fin.succAbove k j) := @DominantFiveBody.three_source_support_kernel

-- Source binding: prose:191
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (a b : DominantFiveBody.Satellite),
  a < b →
    (0 : ℝ) < mass a →
      (0 : ℝ) < mass b →
        (∀ (j : DominantFiveBody.Satellite), j ≠ a → j ≠ b → mass j = (0 : ℝ)) →
          (∀ (i j : DominantFiveBody.Satellite), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
            (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = (0 : ℝ)) →
              theta b - theta a = DominantFiveBody.Coorbital.h := @DominantFiveBody.two_source_separation

-- Source binding: prose:191
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (a b k : DominantFiveBody.Satellite),
  a < b →
    (0 : ℝ) < mass a →
      (0 : ℝ) < mass b →
        (∀ (j : DominantFiveBody.Satellite), j ≠ a → j ≠ b → mass j = (0 : ℝ)) →
          ∑ j : DominantFiveBody.Satellite, mass j = (1 : ℝ) →
            DominantFiveBody.SeparatedSemicircle theta →
              (∀ (i j : DominantFiveBody.Satellite),
                  i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
                (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = (0 : ℝ)) →
                  k ≠ a → k ≠ b → (0 : ℝ) < DominantFiveBody.angularJacobian mass theta k k := @DominantFiveBody.two_source_probe_diagonal_pos

-- Source binding: prose:200
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (k : DominantFiveBody.Satellite),
  mass k = (0 : ℝ) →
    (∀ (i : DominantFiveBody.Satellite), i ≠ k → (0 : ℝ) < mass i) →
      (∀ (i j : DominantFiveBody.Satellite), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
        (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = (0 : ℝ)) →
          (DominantFiveBody.coorbitalSupportMatrix theta k).rank = (2 : ℕ) ∧
            (DominantFiveBody.coorbitalMatrix theta).rank = (2 : ℕ) ∧
              Module.finrank ℝ ↥(DominantFiveBody.coorbitalMatrix theta).mulVecLin.ker = (2 : ℕ) ∧
                Module.finrank ℝ ↥(DominantFiveBody.coorbitalSupportMatrix theta k).mulVecLin.ker = (1 : ℕ) := @DominantFiveBody.coorbital_three_source_ranks_and_kernel_dimensions

-- Source binding: prose:200
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (k : DominantFiveBody.Satellite),
  mass k = (0 : ℝ) →
    (∀ (i : DominantFiveBody.Satellite), i ≠ k → (0 : ℝ) < mass i) →
      (∀ (i j : DominantFiveBody.Satellite), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
        (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = (0 : ℝ)) →
          ∃ v ∈ (DominantFiveBody.coorbitalMatrix theta).mulVecLin.ker, v k ≠ (0 : ℝ) := @DominantFiveBody.coorbital_three_source_kernel_not_all_zero_at_missing_source

-- Source binding: prose:200
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (k : DominantFiveBody.Satellite),
  mass k = (0 : ℝ) →
    (∀ (i : DominantFiveBody.Satellite), i ≠ k → (0 : ℝ) < mass i) →
      (∀ (i j : DominantFiveBody.Satellite), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
        (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = (0 : ℝ)) →
          ∃ (nu : DominantFiveBody.Satellite → ℝ),
            nu k = (1 : ℝ) ∧ ∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual nu theta i = (0 : ℝ) := @DominantFiveBody.coorbital_three_source_kernel_vector_by_rank

-- Source binding: prose:200
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (k : DominantFiveBody.Satellite),
  mass k = (0 : ℝ) →
    (∀ (i : DominantFiveBody.Satellite), i ≠ k → (0 : ℝ) < mass i) →
      DominantFiveBody.SeparatedSemicircle theta →
        (∀ (i j : DominantFiveBody.Satellite), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
          (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = (0 : ℝ)) →
            ∑ j ∈ Finset.univ.erase k, mass j * DominantFiveBody.Coorbital.positiveRemainder |theta j - theta k| ≤
                DominantFiveBody.angularJacobian mass theta k k ∧
              (0 : ℝ) <
                ∑ j ∈ Finset.univ.erase k, mass j * DominantFiveBody.Coorbital.positiveRemainder |theta j - theta k| := @DominantFiveBody.three_source_probe_remainder_lower_bound

-- Source binding: display:205
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.SeparatedSemicircle theta →
    HasFDerivAt
      (fun (angles : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) =>
        DominantFiveBody.coorbitalResidual mass angles i)
      (DominantFiveBody.angularDifferential mass theta) theta := @DominantFiveBody.coorbitalResidual_hasFDerivAt

-- Source binding: display:205
example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ),
  (DominantFiveBody.angularJacobian mass theta).mulVec u =
    (DominantFiveBody.angularDifferential mass theta :
        (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
      u := @DominantFiveBody.angularJacobian_mulVec

-- Source binding: display:205
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite),
  i ≠ j → mass j = (0 : ℝ) → DominantFiveBody.angularJacobian mass theta i j = (0 : ℝ) := @DominantFiveBody.angularJacobian_zero_mass_column

-- Source binding: display:205
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (k : DominantFiveBody.Satellite),
  mass k = (0 : ℝ) →
    DominantFiveBody.angularJacobian mass theta k k =
      ∑ j : DominantFiveBody.Satellite with mass j ≠ (0 : ℝ),
        mass j * DominantFiveBody.Coorbital.kappa |theta j - theta k| := @DominantFiveBody.angularJacobian_zero_support_diagonal

-- Source binding: prose:208
example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) ≤ mass i) →
    ∑ i : DominantFiveBody.Satellite, mass i = (1 : ℝ) →
      DominantFiveBody.SeparatedSemicircle theta →
        (∀ (i j : DominantFiveBody.Satellite), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
          (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = (0 : ℝ)) →
            ((DominantFiveBody.angularDifferential mass theta :
                    (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
                  u =
                (0 : DominantFiveBody.Satellite → ℝ) ↔
              ∀ (i j : DominantFiveBody.Satellite), u i = u j) := @DominantFiveBody.angularDifferential_kernel_iff_nonnegative

-- Source binding: prose:208
example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ),
  ∑ i : DominantFiveBody.Satellite,
      mass i *
        (DominantFiveBody.angularDifferential mass theta :
            (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
          u i =
    (0 : ℝ) := @DominantFiveBody.angularDifferential_weighted_zero

-- Source binding: prose:208
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (c : ℝ),
  ((DominantFiveBody.angularDifferential mass theta : (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
      fun (x : DominantFiveBody.Satellite) => c) =
    (0 : DominantFiveBody.Satellite → ℝ) := @DominantFiveBody.angularDifferential_constant

-- Source binding: prose:208
example : ∀ (mass theta u : DominantFiveBody.Satellite → ℝ) (p : DominantFiveBody.Satellite),
  (0 : ℝ) < mass p →
    (∀ (i : DominantFiveBody.Satellite),
        i ≠ p →
          (DominantFiveBody.angularDifferential mass theta :
                (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
              u i =
            (0 : ℝ)) →
      (DominantFiveBody.angularDifferential mass theta :
            (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ)
          u p =
        (0 : ℝ) := @DominantFiveBody.angularDifferential_recover_row

-- Source binding: prose:208
example : ∀ (mass theta : DominantFiveBody.Satellite → ℝ) (p q : DominantFiveBody.Satellite),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) ≤ mass i) →
    ∑ i : DominantFiveBody.Satellite, mass i = (1 : ℝ) →
      (0 : ℝ) < mass p →
        DominantFiveBody.SeparatedSemicircle theta →
          (∀ (i j : DominantFiveBody.Satellite), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) →
            (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mass theta i = (0 : ℝ)) →
              IsUnit (DominantFiveBody.deletedAngularJacobian mass theta p q) := @DominantFiveBody.deletedAngularJacobian_isUnit_nonnegative

-- Source binding: prose:208
example : ∀ (K : Set ((DominantFiveBody.Satellite → ℝ) × (DominantFiveBody.Satellite → ℝ))) (delta eta : ℝ)
  (p q : DominantFiveBody.Satellite),
  IsClosed K →
    (0 : ℝ) < delta →
      (0 : ℝ) < eta →
        (∀ z ∈ K,
            (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) ≤ z.1 i) ∧
              ∑ i : DominantFiveBody.Satellite, z.1 i = (1 : ℝ) ∧
                z.2 (0 : DominantFiveBody.Satellite) = (0 : ℝ) ∧
                  (∀ (i : Fin (3 : ℕ)), delta ≤ z.2 i.succ - z.2 i.castSucc) ∧
                    z.2 (3 : DominantFiveBody.Satellite) - z.2 (0 : DominantFiveBody.Satellite) ≤ Real.pi - eta ∧
                      (1 / 4 : ℝ) ≤ z.1 p ∧
                        ∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual z.1 z.2 i = (0 : ℝ)) →
          ∃ (C : ℝ), (0 : ℝ) < C ∧ ∀ z ∈ K, ‖(DominantFiveBody.deletedAngularJacobian z.1 z.2 p q)⁻¹‖ ≤ C := @DominantFiveBody.deletedAngularJacobian_inverse_uniform_on_closed_roots

-- Source binding: prose:230
example : ∀ (ε : ℝ) (μ : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration),
  DominantFiveBody.liftRelative q (0 : DominantFiveBody.Label) = (0 : DominantFiveBody.Plane) ∧
    DominantFiveBody.centeredFromRelative ε μ q (0 : DominantFiveBody.Label) =
        -(ε / ((1 : ℝ) + ε)) • DominantFiveBody.relativeAverage μ q ∧
      (∀ (i : DominantFiveBody.Satellite),
          DominantFiveBody.centeredFromRelative ε μ q (Fin.succ i) =
            q i - (ε / ((1 : ℝ) + ε)) • DominantFiveBody.relativeAverage μ q) ∧
        DominantFiveBody.centeredFromRelative (0 : ℝ) μ q = DominantFiveBody.liftRelative q ∧
          ∀ (i j : DominantFiveBody.Label),
            DominantFiveBody.pairDistance (DominantFiveBody.centeredFromRelative ε μ q) i j =
              DominantFiveBody.pairDistance (DominantFiveBody.liftRelative q) i j := @DominantFiveBody.centeredFromRelative_source_formulas

-- Source binding: eq:G
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio),
  (-1 : ℝ) < eps →
    DominantFiveBody.PositiveRatio mu →
      ∀ (q : DominantFiveBody.SatelliteConfiguration),
        DominantFiveBody.RelativeCollisionFree q →
          (DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu)
              (DominantFiveBody.centeredFromRelative eps mu q) ↔
            ∀ (i : DominantFiveBody.Satellite),
              DominantFiveBody.vectorResidual eps mu q i = (0 : DominantFiveBody.Plane)) := @DominantFiveBody.normalized_centeredFromRelative_iff_vectorRoot

-- Source binding: prose:238
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio),
  (-1 : ℝ) < eps →
    DominantFiveBody.PositiveRatio mu →
      ∀ (q : DominantFiveBody.SatelliteConfiguration),
        DominantFiveBody.RelativeCollisionFree q →
          (∀ (i : DominantFiveBody.Satellite),
              DominantFiveBody.vectorResidual eps mu q i = (0 : DominantFiveBody.Plane)) →
            DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu)
              (DominantFiveBody.centeredFromRelative eps mu q) := @DominantFiveBody.normalized_of_vectorResidual_zero

-- Source binding: eq:action
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio),
  ∑ i : DominantFiveBody.Satellite, mu i = (1 : ℝ) →
    eps ≠ (0 : ℝ) →
      (1 : ℝ) + eps ≠ (0 : ℝ) →
        ∀ (q : DominantFiveBody.SatelliteConfiguration),
          DominantFiveBody.relativeAction eps mu q =
            DominantFiveBody.augmentedPotential (DominantFiveBody.masses eps mu) (1 : ℝ)
                (DominantFiveBody.centeredFromRelative eps mu q) /
              eps := @DominantFiveBody.relativeAction_eq_augmentedPotential_div

-- Source binding: eq:action.inertia_reduction
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio),
  ∑ i : DominantFiveBody.Satellite, mu i = (1 : ℝ) →
    (1 : ℝ) + eps ≠ (0 : ℝ) →
      ∀ (q : DominantFiveBody.SatelliteConfiguration),
        DominantFiveBody.inertia (DominantFiveBody.masses eps mu) (DominantFiveBody.centeredFromRelative eps mu q) =
          eps * ∑ i : DominantFiveBody.Satellite, mu i * ‖q i‖ ^ (2 : ℕ) -
            eps ^ (2 : ℕ) / ((1 : ℝ) + eps) * ‖DominantFiveBody.relativeAverage mu q‖ ^ (2 : ℕ) := @DominantFiveBody.inertia_centeredFromRelative

-- Source binding: prose:245
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio),
  ∑ i : DominantFiveBody.Satellite, mu i = (1 : ℝ) →
    (1 : ℝ) + eps ≠ (0 : ℝ) →
      ∀ (q : DominantFiveBody.SatelliteConfiguration) (i : DominantFiveBody.Satellite),
        DominantFiveBody.relativeActionVectorGradient eps mu q i =
          ∑ j : DominantFiveBody.Satellite,
            DominantFiveBody.relativeMassMatrix eps mu i j • DominantFiveBody.vectorResidual eps mu q j := @DominantFiveBody.relativeActionVectorGradient_eq_CF

-- Source binding: prose:245
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio),
  (-1 : ℝ) < eps →
    (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < mu i) →
      ∑ i : DominantFiveBody.Satellite, mu i = (1 : ℝ) → (DominantFiveBody.relativeMassMatrix eps mu).PosDef := @DominantFiveBody.relativeMassMatrix_posDef

-- Source binding: prose:245
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio),
  (-1 : ℝ) < eps →
    DominantFiveBody.PositiveRatio mu →
      ∀ (q : DominantFiveBody.SatelliteConfiguration),
        DominantFiveBody.RelativeCollisionFree q →
          (fderiv ℝ (DominantFiveBody.relativeAction eps mu) q = (0 : DominantFiveBody.SatelliteConfiguration →L[ℝ] ℝ) ↔
            ∀ (i : DominantFiveBody.Satellite),
              DominantFiveBody.vectorResidual eps mu q i = (0 : DominantFiveBody.Plane)) := @DominantFiveBody.relativeAction_critical_iff_vectorRoot

-- Source binding: eq:R
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (p v : DominantFiveBody.PolarCoordinates),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < p.1 i) →
    DominantFiveBody.RelativeCollisionFree (DominantFiveBody.polarCoordinateMap p) →
      (fderiv ℝ (DominantFiveBody.polarAction eps mu) p : DominantFiveBody.PolarCoordinates → ℝ) v =
        ∑ i : DominantFiveBody.Satellite, mu i * DominantFiveBody.radialResidual eps mu p.1 p.2 i * v.1 i +
          ∑ i : DominantFiveBody.Satellite, eps * mu i * DominantFiveBody.angularResidual eps mu p.1 p.2 i * v.2 i := @DominantFiveBody.polarAction_fderiv_apply

-- Source binding: eq:polar-gradient
example : ∀ (eps : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ),
  ∑ i : DominantFiveBody.Satellite, mu i * DominantFiveBody.angularResidual eps mu r theta i = (0 : ℝ) := @DominantFiveBody.weighted_angularResidual_zero

-- Source binding: prose:265
example : ∀ (eps : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ) (p : DominantFiveBody.Satellite),
  mu p ≠ (0 : ℝ) →
    (∀ (i : DominantFiveBody.Satellite), i ≠ p → DominantFiveBody.angularResidual eps mu r theta i = (0 : ℝ)) →
      DominantFiveBody.angularResidual eps mu r theta p = (0 : ℝ) := @DominantFiveBody.angularResidual_omitted_row

-- Source binding: prose:265
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (p : DominantFiveBody.PolarCoordinates),
  (0 : ℝ) < eps →
    DominantFiveBody.PositiveRatio mu →
      (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < p.1 i) →
        ∀ (omitted : DominantFiveBody.Satellite),
          ((∀ (i : DominantFiveBody.Satellite), DominantFiveBody.radialResidual eps mu p.1 p.2 i = (0 : ℝ)) ∧
              ∀ (i : DominantFiveBody.Satellite),
                i ≠ omitted → DominantFiveBody.angularResidual eps mu p.1 p.2 i = (0 : ℝ)) ↔
            ∀ (i : DominantFiveBody.Satellite),
              DominantFiveBody.vectorResidual eps mu (DominantFiveBody.polarCoordinateMap p) i =
                (0 : DominantFiveBody.Plane) := @DominantFiveBody.reducedPolarResiduals_zero_iff_vectorRoot

-- Source binding: prose:265
example : ∀ (p : DominantFiveBody.ContinuationParameter) (y : DominantFiveBody.SliceCoordinates),
  DominantFiveBody.SliceRegular p y →
    (0 : ℝ) < p.1 →
      DominantFiveBody.PositiveRatio p.2 →
        DominantFiveBody.reducedResidual p y = (0 : DominantFiveBody.SliceCoordinates) →
          DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses p.1 p.2)
            (DominantFiveBody.slicePhysicalConfiguration p y) := @DominantFiveBody.normalizedCC_of_reducedResidual_zero

-- Source binding: prose:267
example : ∀ (eps : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) →
    ∀ (i : DominantFiveBody.Satellite),
      Inner.inner ℝ (DominantFiveBody.vectorResidual eps mu (DominantFiveBody.polarSatellites r theta) i)
          (DominantFiveBody.quarterTurn (DominantFiveBody.polarSatellites r theta i)) =
        eps * r i * DominantFiveBody.tangentialResidual mu r theta i := @DominantFiveBody.vectorResidual_tangential

-- Source binding: prose:267
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
  DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
    eps ≠ (0 : ℝ) →
      ∀ (r theta : DominantFiveBody.Satellite → ℝ),
        (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) →
          DominantFiveBody.satellitesRelative x = DominantFiveBody.polarSatellites r theta →
            ∀ (i : DominantFiveBody.Satellite), DominantFiveBody.tangentialResidual mu r theta i = (0 : ℝ) := @DominantFiveBody.tangentialResidual_zero_of_normalized

-- Source binding: prose:272
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio),
  ∑ i : DominantFiveBody.Satellite, mu i = (1 : ℝ) →
    (1 : ℝ) + eps ≠ (0 : ℝ) →
      ∀ (q : DominantFiveBody.SatelliteConfiguration),
        (∀ (i : DominantFiveBody.Satellite),
            DominantFiveBody.vectorResidual eps mu q i = (0 : DominantFiveBody.Plane)) →
          DominantFiveBody.relativeField mu q = ((1 : ℝ) + eps)⁻¹ • DominantFiveBody.relativeAverage mu q := @DominantFiveBody.relativeField_eq_scaledAverage_of_vectorRoot

-- Source binding: prose:272
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
  DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
    DominantFiveBody.PositiveRatio mu →
      (0 : ℝ) < eps →
        ∀ (r theta : DominantFiveBody.Satellite → ℝ),
          (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) →
            DominantFiveBody.satellitesRelative x = DominantFiveBody.polarSatellites r theta →
              DominantFiveBody.relativeField mu (DominantFiveBody.polarSatellites r theta) =
                  ((1 : ℝ) + eps)⁻¹ • DominantFiveBody.relativeAverage mu (DominantFiveBody.polarSatellites r theta) ∧
                ∀ (i : DominantFiveBody.Satellite),
                  DominantFiveBody.angularResidual eps mu r theta i =
                    r i * DominantFiveBody.tangentialResidual mu r theta i := @DominantFiveBody.sectionThree_solution_field_and_tangential_identity

-- Source binding: lem:hessian
example : ∀ (p : DominantFiveBody.ContinuationParameter) (fixed omitted : DominantFiveBody.Satellite)
  (y : DominantFiveBody.SliceCoordinates),
  DominantFiveBody.SliceRegular
      (p.1,
        p.2 ∘
          (⇑(DominantFiveBody.fixedAnglePermutation fixed) : DominantFiveBody.Satellite → DominantFiveBody.Satellite))
      y →
    (0 : ℝ) < p.1 →
      DominantFiveBody.PositiveRatio p.2 →
        DominantFiveBody.fixedAngleDeletedResidual p fixed omitted y = (0 : DominantFiveBody.SliceCoordinates) →
          ((fderiv ℝ (DominantFiveBody.fixedAngleDeletedResidual p fixed omitted) y).IsInvertible ↔
            DominantFiveBody.ShapeHessianNondegenerate (DominantFiveBody.masses p.1 p.2) (1 : ℝ)
              (DominantFiveBody.fixedAnglePhysicalConfiguration p fixed y)) := @DominantFiveBody.fixedAngleDeletedJacobian_isInvertible_iff_shape

-- Source binding: lem:hessian
example : ∀ {E : Type u_1} {F : Type u_2} {G : Type u_3} {H : Type u_4} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
  [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace ℝ F] [inst_4 : NormedAddCommGroup G] [inst_5 : NormedSpace ℝ G]
  [inst_6 : NormedAddCommGroup H] [inst_7 : NormedSpace ℝ H] (f : E → F) (L : E → F →L[ℝ] G) (psi : H → E) (z : H),
  DifferentiableAt ℝ f (psi z) →
    DifferentiableAt ℝ L (psi z) →
      DifferentiableAt ℝ psi z →
        f (psi z) = (0 : F) →
          (L (psi z)).IsInvertible →
            (fderiv ℝ psi z).IsInvertible →
              ((fderiv ℝ (fun (y : H) => (L (psi y) : F → G) (f (psi y))) z).IsInvertible ↔
                (fderiv ℝ f (psi z)).IsInvertible) := @DominantFiveBody.coordinate_row_transform_isInvertible_iff

-- Source binding: prose:275
example : ∀ {E : Type u_1} {F : Type u_2} {G : Type u_3} {H : Type u_4} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
  [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace ℝ F] [inst_4 : NormedAddCommGroup G] [inst_5 : NormedSpace ℝ G]
  [inst_6 : NormedAddCommGroup H] [inst_7 : NormedSpace ℝ H] (f : E → F) (L : E → F →L[ℝ] G) (psi : H → E) (z : H),
  DifferentiableAt ℝ f (psi z) →
    DifferentiableAt ℝ L (psi z) →
      DifferentiableAt ℝ psi z →
        f (psi z) = (0 : F) →
          fderiv ℝ (fun (y : H) => (L (psi y) : F → G) (f (psi y))) z =
            (L (psi z) ∘SL fderiv ℝ f (psi z)) ∘SL fderiv ℝ psi z := @DominantFiveBody.coordinate_row_transform_fderiv_at_root

-- Source binding: prose:275
example : ∀ (p : DominantFiveBody.ContinuationParameter) (u v : DominantFiveBody.SliceCoordinates),
  ((DominantFiveBody.sliceWeightedMetric p :
            DominantFiveBody.SliceCoordinates → DominantFiveBody.SliceCoordinates →L[ℝ] ℝ)
          u :
        DominantFiveBody.SliceCoordinates → ℝ)
      v =
    ∑ i : Fin (7 : ℕ), DominantFiveBody.sliceMassWeights p i * u i * v i := @DominantFiveBody.sliceWeightedMetric_apply

-- Source binding: prose:275
example : ∀ (p : DominantFiveBody.ContinuationParameter),
  (0 : ℝ) < p.1 →
    (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < p.2 i) →
      ∀ (k : Fin (7 : ℕ)), (0 : ℝ) < DominantFiveBody.sliceMassWeights p k := @DominantFiveBody.sliceMassWeights_pos

-- Source binding: prose:275
example : ∀ (p : DominantFiveBody.ContinuationParameter) (y : DominantFiveBody.SliceCoordinates),
  DominantFiveBody.SliceRegular p y →
    fderiv ℝ (fderiv ℝ (DominantFiveBody.sliceAction p)) y =
      DominantFiveBody.sliceWeightedMetric p ∘SL DominantFiveBody.reducedJacobian p y := @DominantFiveBody.sliceAction_second_fderiv

-- Source binding: prose:275
example : ∀ (p : DominantFiveBody.ContinuationParameter) (y : DominantFiveBody.SliceCoordinates),
  DominantFiveBody.SliceRegular p y →
    (0 : ℝ) < p.1 →
      (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < p.2 i) →
        ((fderiv ℝ (fderiv ℝ (DominantFiveBody.sliceAction p)) y).IsInvertible ↔
          (DominantFiveBody.reducedJacobian p y).IsInvertible) := @DominantFiveBody.sliceAction_second_fderiv_isInvertible_iff_reducedJacobian

-- Source binding: display:285
example : ∀ (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration),
  DominantFiveBody.NormalizedCentralConfiguration m x →
    ∀ (w : DominantFiveBody.Configuration),
      DominantFiveBody.physicalHessian m (1 : ℝ) x x w = (3 : ℝ) * DominantFiveBody.massInner m x w := @DominantFiveBody.physicalHessian_radial_of_normalizedCC

-- Source binding: display:285
example : ∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m →
    ∀ (x : DominantFiveBody.Configuration),
      DominantFiveBody.NormalizedCentralConfiguration m x →
        (DominantFiveBody.RotationSliceHessianNondegenerate m (1 : ℝ) x ↔
          DominantFiveBody.ShapeHessianNondegenerate m (1 : ℝ) x) := @DominantFiveBody.rotationSliceHessian_nondegenerate_iff_shape

-- Source binding: display:285
example : ∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m →
    ∀ (x : DominantFiveBody.Configuration),
      DominantFiveBody.NormalizedCentralConfiguration m x →
        ℝ ∙ x ⊔ DominantFiveBody.inertiaTangentSpace m x = DominantFiveBody.centeredVariationSpace m ∧
          Disjoint (ℝ ∙ x) (DominantFiveBody.inertiaTangentSpace m x) := @DominantFiveBody.centered_radial_tangent_direct_sum

-- Source binding: prose:288
example : (ε : ℝ) →
  (μ : DominantFiveBody.MassRatio) →
    ∑ i : DominantFiveBody.Satellite, μ i = (1 : ℝ) →
      (1 : ℝ) + ε ≠ (0 : ℝ) →
        DominantFiveBody.SatelliteConfiguration ≃L[ℝ]
          ↥(DominantFiveBody.centeredVariationSpace (DominantFiveBody.masses ε μ)) := @DominantFiveBody.relativeCenteredEquiv

-- Source binding: prose:288
example : ∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m →
    ∀ (x : DominantFiveBody.Configuration),
      DominantFiveBody.CollisionFree x → Module.finrank ℝ ↥(DominantFiveBody.shapeSpace m x) = (6 : ℕ) := @DominantFiveBody.finrank_shapeSpace

-- Source binding: prose:288
example : ∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m →
    ∀ (x : DominantFiveBody.Configuration),
      DominantFiveBody.NormalizedCentralConfiguration m x →
        (∀ v ∈ ℝ ∙ x,
            ∀ w ∈ DominantFiveBody.inertiaTangentSpace m x,
              DominantFiveBody.physicalHessian m (1 : ℝ) x v w = (0 : ℝ)) ∧
          DominantFiveBody.physicalHessian m (1 : ℝ) x x x = (3 : ℝ) * DominantFiveBody.inertia m x ∧
            (0 : ℝ) < (3 : ℝ) * DominantFiveBody.inertia m x := @DominantFiveBody.centered_radial_tangent_hessian_orthogonal

-- Source binding: lem:product
example : ∀ {P : Type u_1} [inst : NormedAddCommGroup P] [inst_1 : NormedSpace ℝ P] [CompleteSpace P] {n : ℕ}
  (F : P → DominantFiveBody.CompactImplicit.Unknown n → DominantFiveBody.CompactImplicit.Unknown n)
  (D K : Set (P × DominantFiveBody.CompactImplicit.Unknown n)),
  IsOpen D →
    ContDiffOn ℝ ∞ (Function.uncurry F) D →
      IsCompact K →
        (∀ a ∈ K,
            a ∈ D ∧
              F a.1 a.2 = (0 : DominantFiveBody.CompactImplicit.Unknown n) ∧
                (DominantFiveBody.CompactImplicit.jacobian F a.1 a.2).IsInvertible) →
          ∀ (τ : ℝ),
            (0 : ℝ) < τ →
              ∃ (η : ℝ) (r : ℝ) (C : ℝ),
                (0 : ℝ) < η ∧
                  (0 : ℝ) < r ∧
                    (0 : ℝ) < C ∧
                      r ≤ τ ∧
                        η ≤ r ∧
                          ∀ a ∈ K,
                            ∃ (ψ : P → DominantFiveBody.CompactImplicit.Unknown n),
                              ψ a.1 = a.2 ∧
                                ContDiffOn ℝ ∞ ψ (Metric.ball a.1 η) ∧
                                  ∀ (q : P),
                                    Dist.dist q a.1 < η →
                                      Dist.dist (ψ q) a.2 < r / (2 : ℝ) ∧
                                        (q, ψ q) ∈ D ∧
                                          (DominantFiveBody.CompactImplicit.jacobian F q (ψ q)).IsInvertible ∧
                                            ‖(DominantFiveBody.CompactImplicit.jacobian F q (ψ q)).inverse‖ ≤ C ∧
                                              F q (ψ q) = (0 : DominantFiveBody.CompactImplicit.Unknown n) ∧
                                                ∀ (z : DominantFiveBody.CompactImplicit.Unknown n),
                                                  Dist.dist z a.2 < r →
                                                    (F q z = (0 : DominantFiveBody.CompactImplicit.Unknown n) ↔ ψ q = z) := @DominantFiveBody.CompactImplicit.compact_product

-- Source binding: prop:local
example : ∀ (K : Set DominantFiveBody.MassRatio),
  IsCompact K →
    (∀ μ ∈ K, DominantFiveBody.PositiveRatio μ) →
      ∃ (η : ℝ) (r : ℝ) (C : ℝ),
        (0 : ℝ) < η ∧
          (0 : ℝ) < r ∧
            (0 : ℝ) < C ∧
              ∀ μ ∈ K,
                ∃ (ψ : DominantFiveBody.ContinuationParameter → DominantFiveBody.SliceCoordinates),
                  ψ ((0 : ℝ), μ) = DominantFiveBody.coorbitalBaseSlice μ ∧
                    ContDiffOn ℝ ∞ ψ (Metric.ball ((0 : ℝ), μ) η) ∧
                      ∀ (ε : ℝ) (ν : DominantFiveBody.MassRatio),
                        |ε| < η →
                          Dist.dist ν μ < η →
                            DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder
                                (DominantFiveBody.slicePhysicalConfiguration (ε, ν) (ψ (ε, ν))) ∧
                              Dist.dist (ψ (ε, ν)) (DominantFiveBody.coorbitalBaseSlice μ) < r / (2 : ℝ) ∧
                                DominantFiveBody.SliceRegular (ε, ν) (ψ (ε, ν)) ∧
                                  (DominantFiveBody.reducedJacobian (ε, ν) (ψ (ε, ν))).IsInvertible ∧
                                    ‖(DominantFiveBody.reducedJacobian (ε, ν) (ψ (ε, ν))).inverse‖ ≤ C ∧
                                      DominantFiveBody.reducedResidual (ε, ν) (ψ (ε, ν)) =
                                          (0 : DominantFiveBody.SliceCoordinates) ∧
                                        (∀ (z : DominantFiveBody.SliceCoordinates),
                                            Dist.dist z (DominantFiveBody.coorbitalBaseSlice μ) < r →
                                              (DominantFiveBody.reducedResidual (ε, ν) z =
                                                  (0 : DominantFiveBody.SliceCoordinates) ↔
                                                ψ (ε, ν) = z)) ∧
                                          ((0 : ℝ) < ε →
                                            DominantFiveBody.PositiveRatio ν →
                                              DominantFiveBody.NormalizedCentralConfiguration
                                                  (DominantFiveBody.masses ε ν)
                                                  (DominantFiveBody.slicePhysicalConfiguration (ε, ν) (ψ (ε, ν))) ∧
                                                DominantFiveBody.StrictConvexCentralConfiguration
                                                    (DominantFiveBody.masses ε ν) DominantFiveBody.standardHullOrder
                                                    (DominantFiveBody.slicePhysicalConfiguration (ε, ν) (ψ (ε, ν))) ∧
                                                  DominantFiveBody.ShapeHessianNondegenerate
                                                    (DominantFiveBody.masses ε ν) (1 : ℝ)
                                                    (DominantFiveBody.slicePhysicalConfiguration (ε, ν) (ψ (ε, ν)))) := @DominantFiveBody.coorbital_compact_physical_continuation

-- Source binding: prose:305
example : ∀ (μ : DominantFiveBody.MassRatio) (y : DominantFiveBody.SliceCoordinates),
  DominantFiveBody.SliceRegular ((0 : ℝ), μ) y →
    (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.sliceRadii y i = (1 : ℝ)) →
      ∀ (v : DominantFiveBody.SliceCoordinates) (i : DominantFiveBody.Satellite),
        (DominantFiveBody.reducedJacobian ((0 : ℝ), μ) y :
              DominantFiveBody.SliceCoordinates → DominantFiveBody.SliceCoordinates)
            v (Fin.castAdd (3 : ℕ) i) =
          (3 : ℝ) * DominantFiveBody.sliceRadii v i := @DominantFiveBody.reducedJacobian_zero_radial_block

-- Source binding: prose:305
example : ∀ (μ : DominantFiveBody.MassRatio),
  DominantFiveBody.PositiveRatio μ →
    DominantFiveBody.SliceRegular ((0 : ℝ), μ) (DominantFiveBody.coorbitalBaseSlice μ) ∧
      DominantFiveBody.reducedResidual ((0 : ℝ), μ) (DominantFiveBody.coorbitalBaseSlice μ) =
          (0 : DominantFiveBody.SliceCoordinates) ∧
        (DominantFiveBody.reducedJacobian ((0 : ℝ), μ) (DominantFiveBody.coorbitalBaseSlice μ)).IsInvertible := @DominantFiveBody.coorbitalBaseSlice_actual_data

-- Source binding: prose:305
example : ∀ (μ : DominantFiveBody.MassRatio) (y : DominantFiveBody.SliceCoordinates),
  DominantFiveBody.SliceRegular ((0 : ℝ), μ) y →
    (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.sliceRadii y i = (1 : ℝ)) →
      DominantFiveBody.OrderedSemicircle (DominantFiveBody.sliceAngles y) →
        DominantFiveBody.reducedAngularJacobian ((0 : ℝ), μ) y =
          DominantFiveBody.coorbitalFreeRows ∘SL
            DominantFiveBody.angularDifferential μ (DominantFiveBody.sliceAngles y) ∘SL
              DominantFiveBody.coorbitalAngleInjection := @DominantFiveBody.reducedAngularJacobian_zero_eq

-- Source binding: prose:305
example : ∀ (μ : DominantFiveBody.MassRatio) (y : DominantFiveBody.SliceCoordinates),
  DominantFiveBody.SliceRegular ((0 : ℝ), μ) y →
    (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.sliceRadii y i = (1 : ℝ)) →
      (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < μ i) →
        DominantFiveBody.OrderedSemicircle (DominantFiveBody.sliceAngles y) →
          (∀ (i : DominantFiveBody.Satellite),
              DominantFiveBody.coorbitalResidual μ (DominantFiveBody.sliceAngles y) i = (0 : ℝ)) →
            (DominantFiveBody.reducedAngularJacobian ((0 : ℝ), μ) y).IsInvertible := @DominantFiveBody.reducedAngularJacobian_zero_isInvertible

-- Source binding: prose:305
example : ∀ (μ : DominantFiveBody.MassRatio) (y : DominantFiveBody.SliceCoordinates),
  (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.sliceRadii y i = (1 : ℝ)) →
    (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < μ i) →
      DominantFiveBody.OrderedSemicircle (DominantFiveBody.sliceAngles y) →
        (∀ (i : DominantFiveBody.Satellite),
            DominantFiveBody.coorbitalResidual μ (DominantFiveBody.sliceAngles y) i = (0 : ℝ)) →
          (DominantFiveBody.reducedJacobian ((0 : ℝ), μ) y).IsInvertible := @DominantFiveBody.reducedJacobian_at_coorbital_root_isInvertible

-- Source binding: prose:315
example : Real.sinc (0 : ℝ) = (1 : ℝ) ∧ (∀ (t : ℝ), t ≠ (0 : ℝ) → Real.sinc t = Real.sin t / t) ∧ ContDiff ℝ ∞ Real.sinc := @DominantFiveBody.sinc_source_extension

-- Source binding: prop:uniform
example : (∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio),
    (0 : ℝ) < eps →
      DominantFiveBody.PositiveRatio mu →
        ∀ (x : DominantFiveBody.Configuration),
          DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
            Metric.diam (Set.range x) ≤ (4 : ℝ) * ((1 : ℝ) + eps).rpow (1 / 3 : ℝ)) ∧
  (∀ (E : ℝ),
      (0 : ℝ) < E →
        ∃ (b : ℝ),
          (0 : ℝ) < b ∧
            ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
              (0 : ℝ) < eps →
                eps ≤ E →
                  DominantFiveBody.PositiveRatio mu →
                    DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
                      ∀ (i : DominantFiveBody.Satellite), b ≤ ‖DominantFiveBody.satellitesRelative x i‖) ∧
    (∀ (eta : ℝ),
        (0 : ℝ) < eta →
          ∃ (delta : ℝ),
            (0 : ℝ) < delta ∧
              ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
                (0 : ℝ) < eps →
                  eps < delta →
                    DominantFiveBody.PositiveRatio mu →
                      DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
                        ∀ (i : DominantFiveBody.Satellite),
                          |‖DominantFiveBody.satellitesRelative x i‖ - (1 : ℝ)| < eta) ∧
      (∃ (eta : ℝ) (eps0 : ℝ),
          (0 : ℝ) < eta ∧
            (0 : ℝ) < eps0 ∧
              ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (sigma : DominantFiveBody.HullOrder)
                (x : DominantFiveBody.Configuration),
                (0 : ℝ) < eps →
                  eps < eps0 →
                    DominantFiveBody.PositiveRatio mu →
                      DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
                        DominantFiveBody.StrictConvexInOrder sigma x →
                          ∃ (r : DominantFiveBody.Satellite → ℝ) (theta : DominantFiveBody.Satellite → ℝ) (phi : ℝ),
                            (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) ∧
                              theta (0 : DominantFiveBody.Satellite) = (0 : ℝ) ∧
                                (∀ (i j : DominantFiveBody.Satellite),
                                    i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) ∧
                                  (∀ (i : DominantFiveBody.Satellite),
                                      x
                                            ((sigma.labels : DominantFiveBody.Label → DominantFiveBody.Label)
                                              (Fin.succ i)) -
                                          x (0 : DominantFiveBody.Label) =
                                        DominantFiveBody.polarPoint (r i) (theta i + phi)) ∧
                                    (∀ (i : DominantFiveBody.Satellite),
                                        DominantFiveBody.angularResidual eps
                                            (mu ∘
                                              (⇑(DominantFiveBody.hullSatellitePermutation sigma) :
                                                DominantFiveBody.Satellite → DominantFiveBody.Satellite))
                                            r theta i =
                                          (0 : ℝ)) ∧
                                      eta ≤ theta (3 : DominantFiveBody.Satellite) ∧
                                        theta (3 : DominantFiveBody.Satellite) ≤ Real.pi - eta) ∧
        ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (sigma : ℕ → DominantFiveBody.HullOrder)
          (x : ℕ → DominantFiveBody.Configuration) (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (phi : ℕ → ℝ),
          (∀ (n : ℕ), (0 : ℝ) < eps n) →
            Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
              (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
                (∀ (n : ℕ),
                    DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
                  (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                    (∀ (n : ℕ), theta n (0 : DominantFiveBody.Satellite) = (0 : ℝ)) →
                      (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                          i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                        (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
                            x n (((sigma n).labels : DominantFiveBody.Label → DominantFiveBody.Label) (Fin.succ i)) -
                                x n (0 : DominantFiveBody.Label) =
                              DominantFiveBody.polarPoint (r n i) (theta n i + phi n)) →
                          ∀ (k : Fin (3 : ℕ)),
                            Filter.limsup (fun (n : ℕ) => theta n k.succ - theta n k.castSucc) Filter.atTop ≤
                              Real.pi / (3 : ℝ) := @DominantFiveBody.dominant_uniform_geometry_complete

-- Source binding: prop:uniform.diameter
example : ∀ (ε : ℝ) (μ : DominantFiveBody.MassRatio),
  (0 : ℝ) < ε →
    DominantFiveBody.PositiveRatio μ →
      ∀ (x : DominantFiveBody.Configuration),
        DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses ε μ) x →
          Metric.diam (Set.range x) ≤ (4 : ℝ) * ((1 : ℝ) + ε).rpow (1 / 3 : ℝ) := @DominantFiveBody.dominant_normalized_diameter_le

-- Source binding: prop:uniform.lower_radius
example : ∀ (E : ℝ),
  (0 : ℝ) < E →
    ∃ (b : ℝ),
      (0 : ℝ) < b ∧
        ∀ (ε : ℝ) (μ : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
          (0 : ℝ) < ε →
            ε ≤ E →
              DominantFiveBody.PositiveRatio μ →
                DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses ε μ) x →
                  ∀ (i : DominantFiveBody.Satellite), b ≤ ‖DominantFiveBody.satellitesRelative x i‖ := @DominantFiveBody.dominant_primary_relative_radius_lower

-- Source binding: prop:uniform.uniform_radius_to_one
example : ∀ (η : ℝ),
  (0 : ℝ) < η →
    ∃ (δ : ℝ),
      (0 : ℝ) < δ ∧
        ∀ (ε : ℝ) (μ : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
          (0 : ℝ) < ε →
            ε < δ →
              DominantFiveBody.PositiveRatio μ →
                DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses ε μ) x →
                  ∀ (i : DominantFiveBody.Satellite), |‖DominantFiveBody.satellitesRelative x i‖ - (1 : ℝ)| < η := @DominantFiveBody.dominant_primary_relative_radii_uniform

-- Source binding: eq:span
example : ∃ (eta : ℝ) (eps0 : ℝ),
  (0 : ℝ) < eta ∧
    (0 : ℝ) < eps0 ∧
      ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (sigma : DominantFiveBody.HullOrder)
        (x : DominantFiveBody.Configuration),
        (0 : ℝ) < eps →
          eps < eps0 →
            DominantFiveBody.PositiveRatio mu →
              DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
                DominantFiveBody.StrictConvexInOrder sigma x →
                  ∃ (r : DominantFiveBody.Satellite → ℝ) (theta : DominantFiveBody.Satellite → ℝ) (phi : ℝ),
                    (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) ∧
                      theta (0 : DominantFiveBody.Satellite) = (0 : ℝ) ∧
                        (∀ (i j : DominantFiveBody.Satellite),
                            i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) ∧
                          (∀ (i : DominantFiveBody.Satellite),
                              x ((sigma.labels : DominantFiveBody.Label → DominantFiveBody.Label) (Fin.succ i)) -
                                  x (0 : DominantFiveBody.Label) =
                                DominantFiveBody.polarPoint (r i) (theta i + phi)) ∧
                            (∀ (i : DominantFiveBody.Satellite),
                                DominantFiveBody.angularResidual eps
                                    (mu ∘
                                      (⇑(DominantFiveBody.hullSatellitePermutation sigma) :
                                        DominantFiveBody.Satellite → DominantFiveBody.Satellite))
                                    r theta i =
                                  (0 : ℝ)) ∧
                              eta ≤ theta (3 : DominantFiveBody.Satellite) ∧
                                theta (3 : DominantFiveBody.Satellite) ≤ Real.pi - eta := @DominantFiveBody.dominant_strictConvex_uniform_polar_span

-- Source binding: prose:330
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (sigma : ℕ → DominantFiveBody.HullOrder)
  (x : ℕ → DominantFiveBody.Configuration) (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (phi : ℕ → ℝ),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
            (∀ (n : ℕ), theta n (0 : DominantFiveBody.Satellite) = (0 : ℝ)) →
              (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                  i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
                    x n (((sigma n).labels : DominantFiveBody.Label → DominantFiveBody.Label) (Fin.succ i)) -
                        x n (0 : DominantFiveBody.Label) =
                      DominantFiveBody.polarPoint (r n i) (theta n i + phi n)) →
                  ∀ (k : Fin (3 : ℕ)),
                    Filter.limsup (fun (n : ℕ) => theta n k.succ - theta n k.castSucc) Filter.atTop ≤ Real.pi / (3 : ℝ) := @DominantFiveBody.dominant_ordered_polar_gap_limsup

-- Source binding: prose:330
example : ∀ (v : DominantFiveBody.Label → ℝ),
  ∃ (k : DominantFiveBody.Satellite),
    (v (4 : DominantFiveBody.Label) - v (0 : DominantFiveBody.Label)) / (4 : ℝ) ≤ v (Fin.succ k) - v (Fin.castSucc k) := @DominantFiveBody.five_projection_large_gap

-- Source binding: prose:330
example : ∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m →
    ∀ (x : DominantFiveBody.Configuration),
      DominantFiveBody.NormalizedCentralConfiguration m x →
        ∀ (a b : DominantFiveBody.Label),
          DominantFiveBody.pairDistance x a b ^ (3 : ℕ) ≤ (64 : ℝ) * DominantFiveBody.totalMass m := @DominantFiveBody.normalized_pairDistance_cube_le

-- Source binding: display:334
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio),
  (0 : ℝ) < eps →
    DominantFiveBody.PositiveRatio mu →
      ∀ (x : DominantFiveBody.Configuration),
        DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
          ∀ (S : Finset DominantFiveBody.Label),
            S.Nonempty →
              Sᶜ.Nonempty →
                ∀ (e : DominantFiveBody.Plane),
                  ‖e‖ = (1 : ℝ) →
                    ∀ (g : ℝ),
                      (0 : ℝ) < g →
                        (∀ i ∈ S, ∀ j ∈ Sᶜ, g ≤ Inner.inner ℝ e (x j - x i)) →
                          g ≤ DominantFiveBody.projectedClusterGap (DominantFiveBody.masses eps mu) x S e ∧
                            DominantFiveBody.projectedClusterGap (DominantFiveBody.masses eps mu) x S e =
                                ((DominantFiveBody.clusterMass (DominantFiveBody.masses eps mu) S)⁻¹ +
                                    (DominantFiveBody.clusterMass (DominantFiveBody.masses eps mu) Sᶜ)⁻¹) *
                                  ∑ i ∈ S,
                                    ∑ j ∈ Sᶜ,
                                      DominantFiveBody.masses eps mu i * DominantFiveBody.masses eps mu j *
                                          Inner.inner ℝ e (x j - x i) /
                                        ‖x j - x i‖ ^ (3 : ℕ) ∧
                              DominantFiveBody.projectedClusterGap (DominantFiveBody.masses eps mu) x S e ≤
                                ((1 : ℝ) + eps) / g ^ (2 : ℕ) := @DominantFiveBody.dominant_projectedClusterGap_source

-- Source binding: display:334
example : ∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m →
    ∀ (x : DominantFiveBody.Configuration),
      DominantFiveBody.NormalizedCentralConfiguration m x →
        ∀ (e : DominantFiveBody.Plane),
          ‖e‖ = (1 : ℝ) →
            ∀ (S : Finset DominantFiveBody.Label),
              S.Nonempty →
                Sᶜ.Nonempty →
                  ∀ (g : ℝ),
                    (0 : ℝ) < g →
                      (∀ i ∈ S, ∀ j ∈ Sᶜ, g ≤ Inner.inner ℝ e (x j - x i)) → g ^ (3 : ℕ) ≤ DominantFiveBody.totalMass m := @DominantFiveBody.normalized_projection_gap_cube_le

-- Source binding: prop:uniform.current_cluster_force_cancellation
example : ∀ (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) (S : Finset DominantFiveBody.Label),
  ∑ i ∈ S, ∑ j ∈ S, DominantFiveBody.pairForce m x i j = (0 : DominantFiveBody.Plane) := @DominantFiveBody.cluster_internal_force_zero

-- Source binding: prose:341
example : ∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m →
    ∀ (x : DominantFiveBody.Configuration),
      DominantFiveBody.CollisionFree x →
        ∀ (S : Finset DominantFiveBody.Label),
          (0 : DominantFiveBody.Label) ∈ S →
            ∀ (d : ℝ),
              (0 : ℝ) < d →
                (∀ i ∈ S, DominantFiveBody.pairDistance x (0 : DominantFiveBody.Label) i ≤ d) →
                  m (0 : DominantFiveBody.Label) *
                        DominantFiveBody.clusterMass m (S.erase (0 : DominantFiveBody.Label)) /
                      d ≤
                    DominantFiveBody.clusterPotential m x S := @DominantFiveBody.primary_cluster_potential_lower

-- Source binding: prose:341
example : ∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m →
    ∀ (x : DominantFiveBody.Configuration) (S : Finset DominantFiveBody.Label),
      (0 : DominantFiveBody.Label) ∈ S →
        ∀ (d : ℝ),
          (0 : ℝ) < d →
            (∀ i ∈ S, DominantFiveBody.pairDistance x (0 : DominantFiveBody.Label) i ≤ d) →
              DominantFiveBody.clusterInertia m x S ≤
                DominantFiveBody.clusterMass m (S.erase (0 : DominantFiveBody.Label)) * d ^ (2 : ℕ) := @DominantFiveBody.primary_cluster_inertia_upper

-- Source binding: prose:341
example : ∀ (m : ℕ → DominantFiveBody.MassVector) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), DominantFiveBody.PositiveMasses (m n)) →
    ∀ (mLimit : DominantFiveBody.MassVector) (xLimit : DominantFiveBody.Configuration),
      Filter.Tendsto m Filter.atTop (𝓝 mLimit) →
        Filter.Tendsto x Filter.atTop (𝓝 xLimit) →
          ∀ (S : Finset DominantFiveBody.Label),
            S.Nonempty →
              ∀ (c : DominantFiveBody.Plane),
                DominantFiveBody.CompleteLimitingCluster xLimit S c →
                  ∃ (L : ℝ),
                    (0 : ℝ) < L ∧
                      ∃ (V : Set DominantFiveBody.ExteriorData),
                        IsOpen V ∧
                          V ∈ 𝓝 ((mLimit, xLimit), c) ∧
                            (∀ d ∈ V,
                                DifferentiableAt ℝ (DominantFiveBody.exteriorField S) d ∧
                                  ‖fderiv ℝ (DominantFiveBody.exteriorField S) d‖ ≤ L) ∧
                              ∀ᶠ (n : ℕ) in Filter.atTop,
                                ((m n, x n), DominantFiveBody.clusterCenter (m n) (x n) S) ∈ V ∧
                                  ∀ i ∈ S,
                                    ((m n, x n), x n i) ∈ V ∧
                                      ‖DominantFiveBody.exteriorAcceleration (m n) (x n) S i -
                                            DominantFiveBody.exteriorField S
                                              ((m n, x n), DominantFiveBody.clusterCenter (m n) (x n) S)‖ ≤
                                        L * ‖x n i - DominantFiveBody.clusterCenter (m n) (x n) S‖ := @DominantFiveBody.complete_cluster_current_center_exterior_bound

-- Source binding: prose:341
example : ∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m →
    ∀ (x : DominantFiveBody.Configuration),
      DominantFiveBody.NormalizedCentralConfiguration m x →
        ∀ (S : Finset DominantFiveBody.Label),
          S.Nonempty →
            ∀ (Acenter : DominantFiveBody.Plane),
              DominantFiveBody.clusterPotential m x S =
                DominantFiveBody.clusterInertia m x S +
                  ∑ i ∈ S,
                    m i *
                      Inner.inner ℝ (x i - DominantFiveBody.clusterCenter m x S)
                        (DominantFiveBody.exteriorAcceleration m x S i - Acenter) := @DominantFiveBody.normalized_cluster_virial

-- Source binding: display:342
example : ∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m →
    ∀ (x : DominantFiveBody.Configuration),
      DominantFiveBody.NormalizedCentralConfiguration m x →
        ∀ (S : Finset DominantFiveBody.Label),
          S.Nonempty →
            ∀ (Acenter : DominantFiveBody.Plane) (L : ℝ),
              (∀ i ∈ S,
                  ‖DominantFiveBody.exteriorAcceleration m x S i - Acenter‖ ≤
                    L * ‖x i - DominantFiveBody.clusterCenter m x S‖) →
                DominantFiveBody.clusterPotential m x S ≤ ((1 : ℝ) + L) * DominantFiveBody.clusterInertia m x S := @DominantFiveBody.normalized_cluster_virial_le

-- Source binding: prose:345
example : ∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m →
    ∀ (x : DominantFiveBody.Configuration),
      DominantFiveBody.NormalizedCentralConfiguration m x →
        ∀ (S : Finset DominantFiveBody.Label),
          (0 : DominantFiveBody.Label) ∈ S →
            (S.erase (0 : DominantFiveBody.Label)).Nonempty →
              ∀ (d : ℝ),
                (0 : ℝ) < d →
                  (∀ i ∈ S, DominantFiveBody.pairDistance x (0 : DominantFiveBody.Label) i ≤ d) →
                    ∀ (Acenter : DominantFiveBody.Plane) (L : ℝ),
                      (0 : ℝ) ≤ L →
                        (∀ i ∈ S,
                            ‖DominantFiveBody.exteriorAcceleration m x S i - Acenter‖ ≤
                              L * ‖x i - DominantFiveBody.clusterCenter m x S‖) →
                          m (0 : DominantFiveBody.Label) ≤ ((1 : ℝ) + L) * d ^ (3 : ℕ) := @DominantFiveBody.primary_cluster_cube_lower

-- Source binding: prose:345
example : ∀ (m : ℕ → DominantFiveBody.MassVector) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), DominantFiveBody.PositiveMasses (m n)) →
    (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (m n) (x n)) →
      (∀ (n : ℕ), m n (0 : DominantFiveBody.Label) = (1 : ℝ)) →
        ∀ (mLimit : DominantFiveBody.MassVector) (xLimit : DominantFiveBody.Configuration),
          Filter.Tendsto m Filter.atTop (𝓝 mLimit) →
            Filter.Tendsto x Filter.atTop (𝓝 xLimit) →
              ∀ (S : Finset DominantFiveBody.Label),
                (0 : DominantFiveBody.Label) ∈ S →
                  (S.erase (0 : DominantFiveBody.Label)).Nonempty →
                    DominantFiveBody.CompleteLimitingCluster xLimit S (xLimit (0 : DominantFiveBody.Label)) → False := @DominantFiveBody.no_primary_complete_collision

-- Source binding: prose:347
example : ∀ (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration),
  DominantFiveBody.NormalizedCentralConfiguration m x →
    ∀ (S : Finset DominantFiveBody.Label),
      DominantFiveBody.clusterCenter m
          (fun (i : DominantFiveBody.Label) => DominantFiveBody.exteriorAcceleration m x S i) S =
        -DominantFiveBody.clusterCenter m x S := @DominantFiveBody.normalized_cluster_exterior_average

-- Source binding: prose:347
example : ∀ (m : ℕ → DominantFiveBody.MassVector),
  (∀ (n : ℕ), DominantFiveBody.PositiveMasses (m n)) →
    ∀ (x : ℕ → DominantFiveBody.Configuration) (S : Finset DominantFiveBody.Label),
      S.Nonempty →
        ∀ (c : DominantFiveBody.Plane),
          (∀ i ∈ S, Filter.Tendsto (fun (n : ℕ) => x n i) Filter.atTop (𝓝 c)) →
            Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.clusterCenter (m n) (x n) S) Filter.atTop (𝓝 c) := @DominantFiveBody.clusterCenter_tendsto_current_weights

-- Source binding: prose:347
example : ∀ (m : ℕ → DominantFiveBody.MassVector) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), DominantFiveBody.PositiveMasses (m n)) →
    (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (m n) (x n)) →
      Filter.Tendsto m Filter.atTop (𝓝 DominantFiveBody.primaryOnlyMass) →
        ∀ (xLimit : DominantFiveBody.Configuration),
          Filter.Tendsto x Filter.atTop (𝓝 xLimit) →
            ∀ (S : Finset DominantFiveBody.Label),
              S.Nonempty →
                ∀ (c : DominantFiveBody.Plane),
                  c ≠ (0 : DominantFiveBody.Plane) → DominantFiveBody.CompleteLimitingCluster xLimit S c → ‖c‖ = (1 : ℝ) := @DominantFiveBody.satellite_complete_cluster_limit_unit

-- Source binding: prose:349
example : ∀ (σ : DominantFiveBody.HullOrder) (x : DominantFiveBody.Configuration),
  DominantFiveBody.StrictConvexInOrder σ x →
    DominantFiveBody.CollisionFree x →
      ∃ (r : DominantFiveBody.Satellite → ℝ) (theta : DominantFiveBody.Satellite → ℝ) (phi : ℝ),
        (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) ∧
          theta (0 : DominantFiveBody.Satellite) = (0 : ℝ) ∧
            (∀ (i j : DominantFiveBody.Satellite), i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) ∧
              ∀ (i : DominantFiveBody.Satellite),
                x ((σ.labels : DominantFiveBody.Label → DominantFiveBody.Label) (Fin.succ i)) -
                    x (0 : DominantFiveBody.Label) =
                  DominantFiveBody.polarPoint (r i) (theta i + phi) := @DominantFiveBody.strictConvexInOrder_exists_ordered_polar

-- Source binding: prose:349
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (sigma : DominantFiveBody.HullOrder) (x : DominantFiveBody.Configuration),
  (0 : ℝ) < eps →
    DominantFiveBody.PositiveRatio mu →
      DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
        ∀ (r theta : DominantFiveBody.Satellite → ℝ) (phi : ℝ),
          (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) →
            (∀ (i : DominantFiveBody.Satellite),
                x ((sigma.labels : DominantFiveBody.Label → DominantFiveBody.Label) (Fin.succ i)) -
                    x (0 : DominantFiveBody.Label) =
                  DominantFiveBody.polarPoint (r i) (theta i + phi)) →
              ∀ (i : DominantFiveBody.Satellite),
                DominantFiveBody.angularResidual eps
                    (mu ∘
                      (⇑(DominantFiveBody.hullSatellitePermutation sigma) :
                        DominantFiveBody.Satellite → DominantFiveBody.Satellite))
                    r theta i =
                  (0 : ℝ) := @DominantFiveBody.normalized_polar_gauge_angular_rows

-- Source binding: prose:349
example : ∀ (ε : ℝ) (μ r θ : DominantFiveBody.Satellite → ℝ),
  (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.angularResidual ε μ r θ i = (0 : ℝ)) →
    ∀ (S : Finset DominantFiveBody.Satellite), ∑ i ∈ S, ∑ j ∈ Sᶜ, DominantFiveBody.fullAngularPair ε μ r θ i j = (0 : ℝ) := @DominantFiveBody.full_angular_cut

-- Source binding: prop:uniform.actual_ordered_polar_bridge
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (σ : DominantFiveBody.HullOrder) (x : DominantFiveBody.Configuration),
  (0 : ℝ) < eps →
    DominantFiveBody.PositiveRatio mu →
      DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
        DominantFiveBody.StrictConvexInOrder σ x →
          ∃ (r : DominantFiveBody.Satellite → ℝ) (theta : DominantFiveBody.Satellite → ℝ) (phi : ℝ),
            (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) ∧
              theta (0 : DominantFiveBody.Satellite) = (0 : ℝ) ∧
                (∀ (i j : DominantFiveBody.Satellite),
                    i < j → (0 : ℝ) < theta j - theta i ∧ theta j - theta i < Real.pi) ∧
                  (∀ (i : DominantFiveBody.Satellite),
                      x ((σ.labels : DominantFiveBody.Label → DominantFiveBody.Label) (Fin.succ i)) -
                          x (0 : DominantFiveBody.Label) =
                        DominantFiveBody.polarPoint (r i) (theta i + phi)) ∧
                    ∀ (i : DominantFiveBody.Satellite),
                      DominantFiveBody.angularResidual eps
                          (mu ∘
                            (⇑(DominantFiveBody.hullSatellitePermutation σ) :
                              DominantFiveBody.Satellite → DominantFiveBody.Satellite))
                          r theta i =
                        (0 : ℝ) := @DominantFiveBody.normalized_strictConvex_ordered_angular_rep

-- Source binding: prop:uniform.selected_consecutive_gap_limit
example : ∀ (eps : ℕ → ℝ),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ),
        (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < mu n i) →
          (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
                DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = (0 : ℝ)) →
              (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                  i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                ∀ (rLimit thetaLimit : DominantFiveBody.Satellite → ℝ),
                  (∀ (i : DominantFiveBody.Satellite), rLimit i = (1 : ℝ)) →
                    Filter.Tendsto r Filter.atTop (𝓝 rLimit) →
                      Filter.Tendsto theta Filter.atTop (𝓝 thetaLimit) →
                        ∀ (k : Fin (3 : ℕ)), thetaLimit k.succ - thetaLimit k.castSucc ≤ Real.pi / (3 : ℝ) := @DominantFiveBody.ordered_full_angular_limit_consecutive_gap_le

-- Source binding: prop:uniform.selected_cut_gap_limit
example : ∀ (ε : ℕ → ℝ),
  (∀ (n : ℕ), (0 : ℝ) < ε n) →
    Filter.Tendsto ε Filter.atTop (𝓝 (0 : ℝ)) →
      ∀ (μ r θ : ℕ → DominantFiveBody.Satellite → ℝ),
        (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < μ n i) →
          (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
                DominantFiveBody.angularResidual (ε n) (μ n) (r n) (θ n) i = (0 : ℝ)) →
              ∀ (rLimit θLimit : DominantFiveBody.Satellite → ℝ),
                (∀ (i : DominantFiveBody.Satellite), rLimit i = (1 : ℝ)) →
                  Filter.Tendsto r Filter.atTop (𝓝 rLimit) →
                    Filter.Tendsto θ Filter.atTop (𝓝 θLimit) →
                      ∀ (S : Finset DominantFiveBody.Satellite),
                        S.Nonempty →
                          Sᶜ.Nonempty →
                            (∀ (n : ℕ), ∀ i ∈ S, ∀ j ∈ Sᶜ, (0 : ℝ) < θ n j - θ n i ∧ θ n j - θ n i < Real.pi) →
                              ∀ (g : ℝ), (∀ i ∈ S, ∀ j ∈ Sᶜ, g ≤ θLimit j - θLimit i) → g ≤ Real.pi / (3 : ℝ) := @DominantFiveBody.full_angular_cut_limit_gap_le

-- Source binding: prose:353
example : ∀ (mu theta : DominantFiveBody.Satellite → ℝ),
  ∑ i : DominantFiveBody.Satellite, mu i = (1 : ℝ) →
    theta (1 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite) ≤ Real.pi / (3 : ℝ) ∧
        theta (2 : DominantFiveBody.Satellite) - theta (1 : DominantFiveBody.Satellite) ≤ Real.pi / (3 : ℝ) ∧
          theta (3 : DominantFiveBody.Satellite) - theta (2 : DominantFiveBody.Satellite) ≤ Real.pi / (3 : ℝ) →
      theta (3 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite) = Real.pi →
        (∀ (i : DominantFiveBody.Satellite),
            DominantFiveBody.angularResidual (0 : ℝ) mu (fun (x : DominantFiveBody.Satellite) => (1 : ℝ)) theta i =
              (0 : ℝ)) →
          False := @DominantFiveBody.no_full_angular_unit_root_at_pi

-- Source binding: display:354
example : ∀ (eps : ℝ) (r theta : DominantFiveBody.Satellite → ℝ),
  (∀ (i j : DominantFiveBody.Satellite),
      DominantFiveBody.fullAngularMatrix eps r theta i j =
        r i * r j * Real.sin (theta j - theta i) *
          (DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r theta) i j ^ (-3 : ℤ) -
            ((1 : ℝ) + eps)⁻¹)) ∧
    ∀ (i : DominantFiveBody.Satellite), DominantFiveBody.fullAngularMatrix eps r theta i i = (0 : ℝ) := @DominantFiveBody.fullAngularMatrix_source_entries

-- Source binding: prop:uniform.selected_limit_span_pi_exclusion
example : ∀ (eps : ℕ → ℝ),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ),
        (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < mu n i) →
          (∀ (n : ℕ), ∑ i : DominantFiveBody.Satellite, mu n i = (1 : ℝ)) →
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
                  DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = (0 : ℝ)) →
                (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                    i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                  ∀ (muLimit rLimit thetaLimit : DominantFiveBody.Satellite → ℝ),
                    (∀ (i : DominantFiveBody.Satellite), rLimit i = (1 : ℝ)) →
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        Filter.Tendsto r Filter.atTop (𝓝 rLimit) →
                          Filter.Tendsto theta Filter.atTop (𝓝 thetaLimit) →
                            thetaLimit (3 : DominantFiveBody.Satellite) - thetaLimit (0 : DominantFiveBody.Satellite) <
                              Real.pi := @DominantFiveBody.ordered_full_angular_limit_span_lt_pi

-- Source binding: prose:357
example : ∀ (theta : DominantFiveBody.Satellite → ℝ),
  theta (1 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite) ≤ DominantFiveBody.Coorbital.h ∧
      theta (2 : DominantFiveBody.Satellite) - theta (1 : DominantFiveBody.Satellite) ≤ DominantFiveBody.Coorbital.h ∧
        theta (3 : DominantFiveBody.Satellite) - theta (2 : DominantFiveBody.Satellite) ≤ DominantFiveBody.Coorbital.h →
    theta (3 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite) = Real.pi →
      DominantFiveBody.fullAngularMatrix (0 : ℝ) (fun (x : DominantFiveBody.Satellite) => (1 : ℝ)) theta =
        ![![(0 : ℝ), (0 : ℝ), DominantFiveBody.Coorbital.kernelF ((2 : ℝ) * DominantFiveBody.Coorbital.h), (0 : ℝ)],
          ![(0 : ℝ), (0 : ℝ), (0 : ℝ), DominantFiveBody.Coorbital.kernelF ((2 : ℝ) * DominantFiveBody.Coorbital.h)],
          ![-DominantFiveBody.Coorbital.kernelF ((2 : ℝ) * DominantFiveBody.Coorbital.h), (0 : ℝ), (0 : ℝ), (0 : ℝ)],
          ![(0 : ℝ), -DominantFiveBody.Coorbital.kernelF ((2 : ℝ) * DominantFiveBody.Coorbital.h), (0 : ℝ), (0 : ℝ)]] := @DominantFiveBody.fullAngularMatrix_pi_entries

-- Source binding: prose:357
example : ∀ (theta : DominantFiveBody.Satellite → ℝ),
  theta (1 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite) ≤ DominantFiveBody.Coorbital.h ∧
      theta (2 : DominantFiveBody.Satellite) - theta (1 : DominantFiveBody.Satellite) ≤ DominantFiveBody.Coorbital.h ∧
        theta (3 : DominantFiveBody.Satellite) - theta (2 : DominantFiveBody.Satellite) ≤ DominantFiveBody.Coorbital.h →
    theta (3 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite) = Real.pi →
      (DominantFiveBody.fullAngularMatrix (0 : ℝ) (fun (x : DominantFiveBody.Satellite) => (1 : ℝ)) theta).det =
          DominantFiveBody.Coorbital.kernelF ((2 : ℝ) * DominantFiveBody.Coorbital.h) ^ (4 : ℕ) ∧
        (0 : ℝ) < DominantFiveBody.Coorbital.kernelF ((2 : ℝ) * DominantFiveBody.Coorbital.h) ^ (4 : ℕ) := @DominantFiveBody.fullAngularMatrix_pi_det

-- Source binding: prose:357
example : ∀ (eps : ℕ → ℝ),
  Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
    ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (thetaLimit : DominantFiveBody.Satellite → ℝ),
      Filter.Tendsto r Filter.atTop (𝓝 fun (x : DominantFiveBody.Satellite) => (1 : ℝ)) →
        Filter.Tendsto theta Filter.atTop (𝓝 thetaLimit) →
          (∀ (i j : DominantFiveBody.Satellite),
              i ≠ j →
                DominantFiveBody.satelliteDistance
                    (DominantFiveBody.polarSatellites (fun (x : DominantFiveBody.Satellite) => (1 : ℝ)) thetaLimit) i
                    j ≠
                  (0 : ℝ)) →
            thetaLimit (1 : DominantFiveBody.Satellite) - thetaLimit (0 : DominantFiveBody.Satellite) ≤
                  DominantFiveBody.Coorbital.h ∧
                thetaLimit (2 : DominantFiveBody.Satellite) - thetaLimit (1 : DominantFiveBody.Satellite) ≤
                    DominantFiveBody.Coorbital.h ∧
                  thetaLimit (3 : DominantFiveBody.Satellite) - thetaLimit (2 : DominantFiveBody.Satellite) ≤
                    DominantFiveBody.Coorbital.h →
              thetaLimit (3 : DominantFiveBody.Satellite) - thetaLimit (0 : DominantFiveBody.Satellite) = Real.pi →
                Filter.Tendsto (fun (n : ℕ) => (DominantFiveBody.fullAngularMatrix (eps n) (r n) (theta n)).det)
                    Filter.atTop
                    (𝓝 (DominantFiveBody.Coorbital.kernelF ((2 : ℝ) * DominantFiveBody.Coorbital.h) ^ (4 : ℕ))) ∧
                  (0 : ℝ) < DominantFiveBody.Coorbital.kernelF ((2 : ℝ) * DominantFiveBody.Coorbital.h) ^ (4 : ℕ) := @DominantFiveBody.fullAngularMatrix_pi_determinant_limit

-- Source binding: prose:357
example : ∀ (eps : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ),
  ∑ i : DominantFiveBody.Satellite, mu i = (1 : ℝ) →
    (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.angularResidual eps mu r theta i = (0 : ℝ)) →
      (DominantFiveBody.fullAngularMatrix eps r theta).det = (0 : ℝ) := @DominantFiveBody.fullAngularMatrix_det_zero_of_root

-- Source binding: prose:357
example : ∀ (eps : ℕ → ℝ),
  Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
    ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ) (thetaLimit : DominantFiveBody.Satellite → ℝ),
      (∀ (n : ℕ), ∑ i : DominantFiveBody.Satellite, mu n i = (1 : ℝ)) →
        (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
            DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = (0 : ℝ)) →
          Filter.Tendsto r Filter.atTop (𝓝 fun (x : DominantFiveBody.Satellite) => (1 : ℝ)) →
            Filter.Tendsto theta Filter.atTop (𝓝 thetaLimit) →
              thetaLimit (1 : DominantFiveBody.Satellite) - thetaLimit (0 : DominantFiveBody.Satellite) ≤
                    DominantFiveBody.Coorbital.h ∧
                  thetaLimit (2 : DominantFiveBody.Satellite) - thetaLimit (1 : DominantFiveBody.Satellite) ≤
                      DominantFiveBody.Coorbital.h ∧
                    thetaLimit (3 : DominantFiveBody.Satellite) - thetaLimit (2 : DominantFiveBody.Satellite) ≤
                      DominantFiveBody.Coorbital.h →
                thetaLimit (3 : DominantFiveBody.Satellite) - thetaLimit (0 : DominantFiveBody.Satellite) = Real.pi →
                  False := @DominantFiveBody.no_full_angular_sequence_at_pi_by_determinant

-- Source binding: prose:357
example : ∀ (eps : ℕ → ℝ),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ),
      (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < mu n i) →
        (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
          (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
              DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = (0 : ℝ)) →
            (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
              ∀ (rLimit thetaLimit : DominantFiveBody.Satellite → ℝ),
                (∀ (i : DominantFiveBody.Satellite), rLimit i = (1 : ℝ)) →
                  Filter.Tendsto r Filter.atTop (𝓝 rLimit) →
                    Filter.Tendsto theta Filter.atTop (𝓝 thetaLimit) →
                      (0 : ℝ) <
                        thetaLimit (3 : DominantFiveBody.Satellite) - thetaLimit (0 : DominantFiveBody.Satellite) := @DominantFiveBody.ordered_full_angular_limit_span_pos

-- Source binding: eq:distance
example : ∀ (r s a b : ℝ),
  ‖DominantFiveBody.polarPoint s b - DominantFiveBody.polarPoint r a‖ ^ (2 : ℕ) =
    (s - r) ^ (2 : ℕ) + (4 : ℝ) * r * s * Real.sin ((b - a) / (2 : ℝ)) ^ (2 : ℕ) := @DominantFiveBody.polar_distance_sq

-- Source binding: prose:364
example : ∀ (x : DominantFiveBody.Configuration) (sigma : DominantFiveBody.HullOrder),
  DominantFiveBody.StrictConvexInOrder sigma x →
    ∀ (k j : DominantFiveBody.Label),
      j ≠ k →
        j ≠ k + (1 : DominantFiveBody.Label) →
          (0 : ℝ) <
            DominantFiveBody.det2
              (DominantFiveBody.primaryRelative x
                  ((sigma.labels : DominantFiveBody.Label → DominantFiveBody.Label)
                    (k + (1 : DominantFiveBody.Label))) -
                DominantFiveBody.primaryRelative x ((sigma.labels : DominantFiveBody.Label → DominantFiveBody.Label) k))
              (DominantFiveBody.primaryRelative x ((sigma.labels : DominantFiveBody.Label → DominantFiveBody.Label) j) -
                DominantFiveBody.primaryRelative x ((sigma.labels : DominantFiveBody.Label → DominantFiveBody.Label) k)) := @DominantFiveBody.strictConvex_primaryRelative_all_edges

-- Source binding: prop:pair-scale
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ),
              DominantFiveBody.StrictConvexInOrder { labels := Equiv.refl DominantFiveBody.Label, primary_first := rfl }
                (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                      i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (a b : DominantFiveBody.Satellite),
                              a < b →
                                ∀ (c : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c →
                                    ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                                      Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                        ∀ (u w : DominantFiveBody.Satellite),
                                          u < w →
                                            u ∈ DominantFiveBody.pairExteriorLabels a b →
                                              w ∈ DominantFiveBody.pairExteriorLabels a b →
                                                (↑b : ℕ) = (↑a : ℕ) + (1 : ℕ) ∧
                                                  Filter.Tendsto (fun (n : ℕ) => mu n a + mu n b) Filter.atTop
                                                      (𝓝 (0 : ℝ)) ∧
                                                    Filter.Tendsto
                                                        (fun (n : ℕ) =>
                                                          (theta n b - theta n a) /
                                                            DominantFiveBody.satelliteDistance
                                                              (DominantFiveBody.satellitesRelative (x n)) a b)
                                                        Filter.atTop (𝓝 (1 : ℝ)) ∧
                                                      (∃ (C : ℝ),
                                                          (0 : ℝ) < C ∧
                                                            ∀ᶠ (n : ℕ) in Filter.atTop,
                                                              |r n b - r n a| ≤
                                                                C * eps n * ((1 : ℝ) - (mu n a + mu n b)) *
                                                                  DominantFiveBody.satelliteDistance
                                                                    (DominantFiveBody.satellitesRelative (x n)) a b) ∧
                                                        qLimit u ≠ qLimit w ∧
                                                          theta0 w - theta0 u = DominantFiveBody.Coorbital.h ∧
                                                            (0 : ℝ) ≤ muLimit u ∧
                                                              muLimit u ≤ (1 : ℝ) ∧
                                                                muLimit u *
                                                                        DominantFiveBody.coorbitalKernel
                                                                          (theta0 a - theta0 u) +
                                                                      ((1 : ℝ) - muLimit u) *
                                                                        DominantFiveBody.coorbitalKernel
                                                                          (theta0 a - theta0 u -
                                                                            DominantFiveBody.Coorbital.h) =
                                                                    (0 : ℝ) ∧
                                                                  (0 : ℝ) <
                                                                      muLimit u *
                                                                          DominantFiveBody.Coorbital.kappa
                                                                            |theta0 a - theta0 u| +
                                                                        ((1 : ℝ) - muLimit u) *
                                                                          DominantFiveBody.Coorbital.kappa
                                                                            |theta0 a - theta0 u -
                                                                                DominantFiveBody.Coorbital.h| ∧
                                                                    Filter.Tendsto
                                                                        (fun (n : ℕ) =>
                                                                          (mu n a + mu n b) /
                                                                            DominantFiveBody.satelliteDistance
                                                                                (DominantFiveBody.satellitesRelative
                                                                                  (x n))
                                                                                a b ^
                                                                              (3 : ℕ))
                                                                        Filter.atTop
                                                                        (𝓝
                                                                          (muLimit u *
                                                                              DominantFiveBody.Coorbital.kappa
                                                                                |theta0 a - theta0 u| +
                                                                            ((1 : ℝ) - muLimit u) *
                                                                              DominantFiveBody.Coorbital.kappa
                                                                                |theta0 a - theta0 u -
                                                                                    DominantFiveBody.Coorbital.h|)) ∧
                                                                      ∀ (u' w' : DominantFiveBody.Satellite),
                                                                        u' < w' →
                                                                          ∀ (d : DominantFiveBody.Plane),
                                                                            c ≠ d →
                                                                              DominantFiveBody.CompleteLimitingSatellitePair
                                                                                  qLimit u' w' d →
                                                                                False := @DominantFiveBody.normalized_complete_pair_scale_complete

-- Source binding: prop:pair-scale.actual_two_pair_exclusion
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ),
              DominantFiveBody.StrictConvexInOrder { labels := Equiv.refl DominantFiveBody.Label, primary_first := rfl }
                (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                      i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (a b u w : DominantFiveBody.Satellite),
                              a < b →
                                u < w →
                                  ∀ (c d : DominantFiveBody.Plane),
                                    c ≠ d →
                                      DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c →
                                        DominantFiveBody.CompleteLimitingSatellitePair qLimit u w d →
                                          ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                                            Filter.Tendsto theta Filter.atTop (𝓝 theta0) → False := @DominantFiveBody.normalized_complete_pairs_cannot_coexist

-- Source binding: prose:381
example : ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
  Monotone theta0 →
    theta0 (3 : DominantFiveBody.Satellite) - theta0 (0 : DominantFiveBody.Satellite) < Real.pi →
      ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
        (∀ (i : DominantFiveBody.Satellite), qLimit i = DominantFiveBody.polarPoint (1 : ℝ) (theta0 i)) →
          ∀ (a b : DominantFiveBody.Satellite),
            a < b →
              ∀ (c : DominantFiveBody.Plane),
                DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c →
                  (↑b : ℕ) = (↑a : ℕ) + (1 : ℕ) ∧ theta0 b = theta0 a := @DominantFiveBody.complete_pair_ordered_angles_adjacent

-- Source binding: display:385
example : ∀ (mu r theta : DominantFiveBody.Satellite → ℝ) (q : DominantFiveBody.SatelliteConfiguration)
  (a b : DominantFiveBody.Satellite) (x : DominantFiveBody.Plane) (rho v : ℝ),
  DominantFiveBody.pairExteriorField mu q a b x =
      ∑ j ∈ DominantFiveBody.pairExteriorLabels a b, (mu j / ‖q j - x‖ ^ (3 : ℕ)) • (q j - x) ∧
    DominantFiveBody.physicalPairExteriorAngularField mu r theta a b rho v =
      ∑ j ∈ DominantFiveBody.pairExteriorLabels a b,
        mu j * r j * Real.sin (theta j - v) *
          ((‖DominantFiveBody.polarPoint rho v - DominantFiveBody.polarPoint (r j) (theta j)‖ ^ (3 : ℕ))⁻¹ -
            (r j ^ (3 : ℕ))⁻¹) := @DominantFiveBody.pairExteriorFields_source_formulas

-- Source binding: prop:pair-scale.current_exterior_error_bound
example : ∀ (mu : ℕ → DominantFiveBody.MassRatio) (q : ℕ → DominantFiveBody.SatelliteConfiguration),
  (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
    ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
      Filter.Tendsto q Filter.atTop (𝓝 qLimit) →
        ∀ (a b : DominantFiveBody.Satellite),
          a ≠ b →
            ∀ (c : DominantFiveBody.Plane),
              DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c →
                ∃ (C : ℝ),
                  (0 : ℝ) < C ∧
                    ∀ᶠ (n : ℕ) in Filter.atTop,
                      ‖DominantFiveBody.pairExteriorField (mu n) (q n) a b (q n b) -
                            DominantFiveBody.pairExteriorField (mu n) (q n) a b (q n a)‖ ≤
                        C * ((1 : ℝ) - (mu n a + mu n b)) * DominantFiveBody.satelliteDistance (q n) a b := @DominantFiveBody.complete_pair_exterior_error_bound

-- Source binding: prose:390
example : ∀ (a b : DominantFiveBody.Satellite)
  (d : (DominantFiveBody.MassRatio × DominantFiveBody.SatelliteConfiguration) × DominantFiveBody.Plane),
  (∀ j ∈ DominantFiveBody.pairExteriorLabels a b, d.2 ≠ d.1.2 j) →
    ContDiffAt ℝ ∞
      (fun (z : (DominantFiveBody.MassRatio × DominantFiveBody.SatelliteConfiguration) × DominantFiveBody.Plane) =>
        DominantFiveBody.pairExteriorField z.1.1 z.1.2 a b z.2)
      d := @DominantFiveBody.pairExteriorField_joint_contDiffAt

-- Source binding: prose:390
example : ∀ (d : (ℝ × ℝ) × ℝ × ℝ),
  d.1.1 ≠ (0 : ℝ) →
    DominantFiveBody.polarPoint d.1.1 d.1.2 ≠ DominantFiveBody.polarPoint d.2.1 d.2.2 →
      ContDiffAt ℝ ∞ (fun (z : (ℝ × ℝ) × ℝ × ℝ) => DominantFiveBody.physicalSourceAngularField z.1.1 z.1.2 z.2.1 z.2.2)
        d := @DominantFiveBody.physicalSourceAngularField_joint_contDiffAt

-- Source binding: prose:390
example : ∀ (a b : DominantFiveBody.Satellite) (z0 : DominantFiveBody.PairExteriorBoundsData),
  (∀ (j : DominantFiveBody.Satellite), (0 : ℝ) < z0.1.1 j) →
    (∀ j ∈ DominantFiveBody.pairExteriorLabels a b,
        DominantFiveBody.polarPoint (z0.1.1 j) (z0.1.2 j) ≠ DominantFiveBody.polarPoint z0.2.1 z0.2.2) →
      ∃ (C : ℝ),
        (0 : ℝ) < C ∧
          ∃ U ∈ 𝓝 z0,
            ∀ z ∈ U,
              ∀ (mu : DominantFiveBody.MassRatio),
                (∀ (j : DominantFiveBody.Satellite), (0 : ℝ) ≤ mu j) →
                  ‖fderiv ℝ (DominantFiveBody.pairExteriorField mu (DominantFiveBody.polarSatellites z.1.1 z.1.2) a b)
                          (DominantFiveBody.polarPoint z.2.1 z.2.2)‖ ≤
                      C * ∑ j ∈ DominantFiveBody.pairExteriorLabels a b, mu j ∧
                    |deriv
                            (fun (rho : ℝ) =>
                              DominantFiveBody.physicalPairExteriorAngularField mu z.1.1 z.1.2 a b rho z.2.2)
                            z.2.1| ≤
                        C * ∑ j ∈ DominantFiveBody.pairExteriorLabels a b, mu j ∧
                      |deriv
                            (fun (v : ℝ) =>
                              DominantFiveBody.physicalPairExteriorAngularField mu z.1.1 z.1.2 a b z.2.1 v)
                            z.2.2| ≤
                        C * ∑ j ∈ DominantFiveBody.pairExteriorLabels a b, mu j := @DominantFiveBody.pairExterior_joint_neighborhood_derivative_bounds

-- Source binding: prose:390
example : ∀ (a b : DominantFiveBody.Satellite) (r theta : ℕ → DominantFiveBody.Satellite → ℝ)
  (r0 theta0 : DominantFiveBody.Satellite → ℝ),
  Filter.Tendsto r Filter.atTop (𝓝 r0) →
    Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
      ∀ (rho0 v0 : ℝ),
        (∀ (j : DominantFiveBody.Satellite), (0 : ℝ) < r0 j) →
          (∀ j ∈ DominantFiveBody.pairExteriorLabels a b,
              DominantFiveBody.polarPoint (r0 j) (theta0 j) ≠ DominantFiveBody.polarPoint rho0 v0) →
            ∃ (C : ℝ),
              (0 : ℝ) < C ∧
                ∃ U ∈ 𝓝 (rho0, v0),
                  ∀ᶠ (n : ℕ) in Filter.atTop,
                    ∀ q ∈ U,
                      ∀ (mu : DominantFiveBody.MassRatio),
                        (∀ (j : DominantFiveBody.Satellite), (0 : ℝ) ≤ mu j) →
                          ‖fderiv ℝ
                                  (DominantFiveBody.pairExteriorField mu
                                    (DominantFiveBody.polarSatellites (r n) (theta n)) a b)
                                  (DominantFiveBody.polarPoint q.1 q.2)‖ ≤
                              C * ∑ j ∈ DominantFiveBody.pairExteriorLabels a b, mu j ∧
                            |deriv
                                    (fun (rho : ℝ) =>
                                      DominantFiveBody.physicalPairExteriorAngularField mu (r n) (theta n) a b rho q.2)
                                    q.1| ≤
                                C * ∑ j ∈ DominantFiveBody.pairExteriorLabels a b, mu j ∧
                              |deriv
                                    (fun (v : ℝ) =>
                                      DominantFiveBody.physicalPairExteriorAngularField mu (r n) (theta n) a b q.1 v)
                                    q.2| ≤
                                C * ∑ j ∈ DominantFiveBody.pairExteriorLabels a b, mu j := @DominantFiveBody.pairExterior_moving_neighborhood_derivative_bounds

-- Source binding: prose:390
example : ∀ (mu : ℕ → DominantFiveBody.MassRatio),
  (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
    ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
      (∀ (i : DominantFiveBody.Satellite), Filter.Tendsto (fun (n : ℕ) => r n i) Filter.atTop (𝓝 (1 : ℝ))) →
        ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
          Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
            ∀ (a b : DominantFiveBody.Satellite),
              a ≠ b →
                theta0 b = theta0 a →
                  (∀ j ∈ DominantFiveBody.pairExteriorLabels a b,
                      DominantFiveBody.polarPoint (1 : ℝ) (theta0 j) ≠ DominantFiveBody.polarPoint (1 : ℝ) (theta0 a)) →
                    ∃ (C : ℝ),
                      (0 : ℝ) < C ∧
                        ∀ᶠ (n : ℕ) in Filter.atTop,
                          |DominantFiveBody.physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b)
                                  (theta n b) -
                                DominantFiveBody.physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a)
                                  (theta n a)| ≤
                            C * ((1 : ℝ) - (mu n a + mu n b)) * Max.max |r n b - r n a| |theta n b - theta n a| := @DominantFiveBody.complete_pair_exterior_angular_error_bound

-- Source binding: eq:pair-qdiff
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
              (∀ (n : ℕ),
                  DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                    i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                  ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                    Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (𝓝 qLimit) →
                      ∀ (a b : DominantFiveBody.Satellite),
                        a < b →
                          ∀ (c : DominantFiveBody.Plane),
                            DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c →
                              ∀ᶠ (n : ℕ) in Filter.atTop,
                                DominantFiveBody.physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b)
                                        (theta n b) -
                                      DominantFiveBody.physicalPairExteriorAngularField (mu n) (r n) (theta n) a b
                                        (r n a) (theta n a) =
                                    Real.sin (theta n b - theta n a) *
                                      ((mu n a * r n a + mu n b * r n b) /
                                            DominantFiveBody.satelliteDistance
                                                (DominantFiveBody.polarSatellites (r n) (theta n)) a b ^
                                              (3 : ℕ) -
                                          mu n a / r n a ^ (2 : ℕ) -
                                        mu n b / r n b ^ (2 : ℕ)) ∧
                                  (0 : ℝ) <
                                    DominantFiveBody.physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b)
                                        (theta n b) -
                                      DominantFiveBody.physicalPairExteriorAngularField (mu n) (r n) (theta n) a b
                                        (r n a) (theta n a) := @DominantFiveBody.normalized_complete_pair_tangential_difference_positive

-- Source binding: prose:396
example : ∀ (mu r theta : DominantFiveBody.Satellite → ℝ) (a b : DominantFiveBody.Satellite),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < mu i) →
    (1 / 2 : ℝ) ≤ r a →
      (1 / 2 : ℝ) ≤ r b →
        (0 : ℝ) < DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r theta) a b →
          DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r theta) a b ≤ (1 / 4 : ℝ) →
            (mu a + mu b) /
                ((4 : ℝ) *
                  DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r theta) a b ^ (3 : ℕ)) ≤
              (mu a * r a + mu b * r b) /
                    DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r theta) a b ^ (3 : ℕ) -
                  mu a / r a ^ (2 : ℕ) -
                mu b / r b ^ (2 : ℕ) := @DominantFiveBody.pair_tangential_coefficient_lower

-- Source binding: prose:396
example : ∀ (mu : ℕ → DominantFiveBody.MassRatio),
  (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
    ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
      (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
        (∀ (i : DominantFiveBody.Satellite), Filter.Tendsto (fun (n : ℕ) => r n i) Filter.atTop (𝓝 (1 : ℝ))) →
          ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
            Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
              ∀ (a b : DominantFiveBody.Satellite),
                a ≠ b →
                  theta0 b = theta0 a →
                    (∀ (n : ℕ), theta n a < theta n b) →
                      (∀ j ∈ DominantFiveBody.pairExteriorLabels a b,
                          DominantFiveBody.polarPoint (1 : ℝ) (theta0 j) ≠
                            DominantFiveBody.polarPoint (1 : ℝ) (theta0 a)) →
                        (∀ (n : ℕ),
                            (0 : ℝ) <
                              DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a
                                b) →
                          (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
                              DominantFiveBody.tangentialResidual (mu n) (r n) (theta n) i = (0 : ℝ)) →
                            ∃ (C : ℝ),
                              (0 : ℝ) < C ∧
                                ∀ᶠ (n : ℕ) in Filter.atTop,
                                  theta n b - theta n a ≤
                                      (4 : ℝ) *
                                        DominantFiveBody.satelliteDistance
                                          (DominantFiveBody.polarSatellites (r n) (theta n)) a b ∧
                                    (1 / 2 : ℝ) ≤ Real.sinc (theta n b - theta n a) ∧
                                      (theta n b - theta n a) * (mu n a + mu n b) /
                                          DominantFiveBody.satelliteDistance
                                              (DominantFiveBody.polarSatellites (r n) (theta n)) a b ^
                                            (3 : ℕ) ≤
                                        C * ((1 : ℝ) - (mu n a + mu n b)) *
                                          DominantFiveBody.satelliteDistance
                                            (DominantFiveBody.polarSatellites (r n) (theta n)) a b := @DominantFiveBody.complete_pair_angular_prebound_before_radial_exclusion

-- Source binding: eq:pair-vdiff
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
  DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
    ∀ (a b : DominantFiveBody.Satellite),
      a ≠ b →
        DominantFiveBody.primaryRadialField (DominantFiveBody.satellitesRelative x b) -
              DominantFiveBody.primaryRadialField (DominantFiveBody.satellitesRelative x a) +
            eps •
              (DominantFiveBody.pairExteriorField mu (DominantFiveBody.satellitesRelative x) a b
                  (DominantFiveBody.satellitesRelative x b) -
                DominantFiveBody.pairExteriorField mu (DominantFiveBody.satellitesRelative x) a b
                  (DominantFiveBody.satellitesRelative x a)) =
          (eps * (mu a + mu b) /
              DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative x) a b ^ (3 : ℕ)) •
            (DominantFiveBody.satellitesRelative x b - DominantFiveBody.satellitesRelative x a) := @DominantFiveBody.normalized_pair_vector_difference

-- Source binding: prop:pair-scale.actual_direction_alternative
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          ∀ (muLimit : DominantFiveBody.MassRatio),
            Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
              ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (𝓝 qLimit) →
                  ∀ (a b : DominantFiveBody.Satellite),
                    a ≠ b →
                      ∀ (c : DominantFiveBody.Plane),
                        DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c →
                          ∀ (v : DominantFiveBody.Plane),
                            Filter.Tendsto
                                (fun (n : ℕ) =>
                                  DominantFiveBody.physicalPairDirection (DominantFiveBody.satellitesRelative (x n)) a
                                    b)
                                Filter.atTop (𝓝 v) →
                              Filter.Tendsto
                                    (fun (n : ℕ) =>
                                      eps n * (mu n a + mu n b) /
                                        DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a
                                            b ^
                                          (3 : ℕ))
                                    Filter.atTop (𝓝 (0 : ℝ)) ∧
                                  Inner.inner ℝ v c = (0 : ℝ) ∨
                                Filter.Tendsto
                                    (fun (n : ℕ) =>
                                      eps n * (mu n a + mu n b) /
                                        DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a
                                            b ^
                                          (3 : ℕ))
                                    Filter.atTop (𝓝 (3 : ℝ)) ∧
                                  (v = c ∨ v = -c) := @DominantFiveBody.normalized_complete_pair_direction_alternative

-- Source binding: prose:405
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ),
              DominantFiveBody.StrictConvexInOrder { labels := Equiv.refl DominantFiveBody.Label, primary_first := rfl }
                (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                      i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (a b : DominantFiveBody.Satellite),
                              a < b →
                                ∀ (c : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c →
                                    ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                                      Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                        ∀ (v : DominantFiveBody.Plane),
                                          Filter.Tendsto
                                              (fun (n : ℕ) =>
                                                DominantFiveBody.physicalPairDirection
                                                  (DominantFiveBody.satellitesRelative (x n)) a b)
                                              Filter.atTop (𝓝 v) →
                                            (↑b : ℕ) = (↑a : ℕ) + (1 : ℕ) ∧
                                              v =
                                                  DominantFiveBody.quarterTurn
                                                    (DominantFiveBody.polarPoint (1 : ℝ) (theta0 a)) ∧
                                                Filter.Tendsto
                                                    (fun (n : ℕ) =>
                                                      eps n * (mu n a + mu n b) /
                                                        DominantFiveBody.satelliteDistance
                                                            (DominantFiveBody.satellitesRelative (x n)) a b ^
                                                          (3 : ℕ))
                                                    Filter.atTop (𝓝 (0 : ℝ)) ∧
                                                  Filter.Tendsto
                                                      (fun (n : ℕ) =>
                                                        (theta n b - theta n a) /
                                                          DominantFiveBody.satelliteDistance
                                                            (DominantFiveBody.satellitesRelative (x n)) a b)
                                                      Filter.atTop (𝓝 (1 : ℝ)) ∧
                                                    Filter.Tendsto
                                                      (fun (n : ℕ) =>
                                                        (r n b - r n a) /
                                                          DominantFiveBody.satelliteDistance
                                                            (DominantFiveBody.satellitesRelative (x n)) a b)
                                                      Filter.atTop (𝓝 (0 : ℝ)) := @DominantFiveBody.normalized_complete_pair_selected_tangential

-- Source binding: prose:407
example : ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (a b : DominantFiveBody.Satellite) (psi : ℝ),
  (∀ (n : ℕ), (0 : ℝ) < r n b) →
    (∀ (n : ℕ), (0 : ℝ) < DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a b) →
      Filter.Tendsto (fun (n : ℕ) => r n b) Filter.atTop (𝓝 (1 : ℝ)) →
        Filter.Tendsto (fun (n : ℕ) => theta n a) Filter.atTop (𝓝 psi) →
          Filter.Tendsto (fun (n : ℕ) => theta n b) Filter.atTop (𝓝 psi) →
            ∀ (v : DominantFiveBody.Plane),
              Filter.Tendsto
                  (fun (n : ℕ) =>
                    DominantFiveBody.physicalPairDirection (DominantFiveBody.polarSatellites (r n) (theta n)) a b)
                  Filter.atTop (𝓝 v) →
                Filter.Tendsto
                    (fun (n : ℕ) =>
                      (theta n b - theta n a) /
                        DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a b)
                    Filter.atTop
                    (𝓝 (Inner.inner ℝ v (DominantFiveBody.quarterTurn (DominantFiveBody.polarPoint (1 : ℝ) psi)))) ∧
                  Filter.Tendsto
                    (fun (n : ℕ) =>
                      (r n b - r n a) /
                        DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a b)
                    Filter.atTop (𝓝 (Inner.inner ℝ v (DominantFiveBody.polarPoint (1 : ℝ) psi))) := @DominantFiveBody.physical_pair_direction_polar_ratio_limits

-- Source binding: prose:407
example : ∀ (q : ℕ → DominantFiveBody.SatelliteConfiguration) (qLimit : DominantFiveBody.SatelliteConfiguration),
  Filter.Tendsto q Filter.atTop (𝓝 qLimit) →
    ∀ (a b : DominantFiveBody.Satellite),
      (∀ (n : ℕ), q n a ≠ q n b) →
        ∀ (c v : DominantFiveBody.Plane),
          qLimit a = c →
            Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.physicalPairDirection (q n) a b) Filter.atTop (𝓝 v) →
              ∀ (j : DominantFiveBody.Satellite),
                (∀ᶠ (n : ℕ) in Filter.atTop, (0 : ℝ) < DominantFiveBody.det2 (q n b - q n a) (q n j - q n a)) →
                  (0 : ℝ) ≤ DominantFiveBody.det2 v (qLimit j - c) := @DominantFiveBody.complete_pair_direction_support_nonneg

-- Source binding: prose:407
example : ∀ (ra rb rj va vb vj : ℝ),
  DominantFiveBody.det2 (DominantFiveBody.polarPoint rb vb - DominantFiveBody.polarPoint ra va)
        (DominantFiveBody.polarPoint rj vj - DominantFiveBody.polarPoint ra va) -
      (rb - ra) * rj * Real.sin (vj - va) =
    rb * rj * (Real.sin (vj - vb) - Real.sin (vj - va)) + ra * rb * Real.sin (vb - va) := @DominantFiveBody.polar_support_radial_expansion_exact

-- Source binding: prose:407
example : ∀ (ra rb rj va vb vj : ℝ),
  |DominantFiveBody.det2 (DominantFiveBody.polarPoint rb vb - DominantFiveBody.polarPoint ra va)
          (DominantFiveBody.polarPoint rj vj - DominantFiveBody.polarPoint ra va) -
        (rb - ra) * rj * Real.sin (vj - va)| ≤
    (|rb * rj| + |ra * rb|) * |vb - va| := @DominantFiveBody.polar_support_radial_expansion_remainder_bound

-- Source binding: prose:407
example : ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (a b j : DominantFiveBody.Satellite),
  (∀ (i : DominantFiveBody.Satellite), Filter.Tendsto (fun (n : ℕ) => r n i) Filter.atTop (𝓝 (1 : ℝ))) →
    (∀ (n : ℕ), (0 : ℝ) < DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a b) →
      Filter.Tendsto
          (fun (n : ℕ) =>
            (theta n b - theta n a) /
              DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a b)
          Filter.atTop (𝓝 (0 : ℝ)) →
        (fun (n : ℕ) =>
            DominantFiveBody.det2
                (DominantFiveBody.polarSatellites (r n) (theta n) b -
                  DominantFiveBody.polarSatellites (r n) (theta n) a)
                (DominantFiveBody.polarSatellites (r n) (theta n) j -
                  DominantFiveBody.polarSatellites (r n) (theta n) a) -
              (r n b - r n a) * r n j * Real.sin (theta n j - theta n a)) =o[Filter.atTop]
          fun (n : ℕ) => DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a b := @DominantFiveBody.complete_pair_support_radial_expansion_littleO

-- Source binding: prose:407
example : ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (a b j : DominantFiveBody.Satellite) (psi : ℝ),
  (∀ (n : ℕ), (0 : ℝ) < r n b) →
    (∀ (i : DominantFiveBody.Satellite), Filter.Tendsto (fun (n : ℕ) => r n i) Filter.atTop (𝓝 (1 : ℝ))) →
      (∀ (n : ℕ), (0 : ℝ) < DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a b) →
        Filter.Tendsto (fun (n : ℕ) => theta n a) Filter.atTop (𝓝 psi) →
          Filter.Tendsto (fun (n : ℕ) => theta n b) Filter.atTop (𝓝 psi) →
            ∀ (v : DominantFiveBody.Plane),
              v = DominantFiveBody.polarPoint (1 : ℝ) psi ∨ v = -DominantFiveBody.polarPoint (1 : ℝ) psi →
                Filter.Tendsto
                    (fun (n : ℕ) =>
                      DominantFiveBody.physicalPairDirection (DominantFiveBody.polarSatellites (r n) (theta n)) a b)
                    Filter.atTop (𝓝 v) →
                  ((fun (n : ℕ) => theta n b - theta n a) =o[Filter.atTop] fun (n : ℕ) =>
                      DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a b) ∧
                    Filter.Tendsto
                        (fun (n : ℕ) =>
                          |r n b - r n a| /
                            DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a b)
                        Filter.atTop (𝓝 (1 : ℝ)) ∧
                      (fun (n : ℕ) =>
                          DominantFiveBody.det2
                              (DominantFiveBody.polarSatellites (r n) (theta n) b -
                                DominantFiveBody.polarSatellites (r n) (theta n) a)
                              (DominantFiveBody.polarSatellites (r n) (theta n) j -
                                DominantFiveBody.polarSatellites (r n) (theta n) a) -
                            (r n b - r n a) * r n j * Real.sin (theta n j - theta n a)) =o[Filter.atTop]
                        fun (n : ℕ) =>
                        DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a b := @DominantFiveBody.physical_pair_radial_subsequence_source_package

-- Source binding: prose:411
example : ∀ (theta0 : DominantFiveBody.Satellite → ℝ) (a b : DominantFiveBody.Satellite),
  a ≠ b →
    ∀ (psi : ℝ),
      (∀ j ∈ DominantFiveBody.pairExteriorLabels a b, (0 : ℝ) < theta0 j - psi ∧ theta0 j - psi < Real.pi) →
        ∃ (eta : ℝ) (k : ℝ) (C : ℝ),
          (0 : ℝ) < eta ∧
            (0 : ℝ) < k ∧
              (0 : ℝ) < C ∧
                ∀ (mu r theta : DominantFiveBody.Satellite → ℝ),
                  DominantFiveBody.PositiveRatio mu →
                    (∀ j ∈ DominantFiveBody.pairExteriorLabels a b,
                        Dist.dist (r j, theta j) ((1 : ℝ), theta0 j) < eta) →
                      (∀ (rho w : ℝ),
                          Dist.dist (rho, w) ((1 : ℝ), psi) < eta →
                            (∀ j ∈ DominantFiveBody.pairExteriorLabels a b,
                                (0 : ℝ) < r j ∧
                                  DominantFiveBody.polarPoint (r j) (theta j) ≠ DominantFiveBody.polarPoint rho w) ∧
                              ∑ j ∈ DominantFiveBody.pairExteriorLabels a b,
                                  mu j * DominantFiveBody.physicalSourceAngularRadialDerivative (r j) (theta j) rho w ≤
                                -k * ((1 : ℝ) - (mu a + mu b))) ∧
                        ∀ (rho va vb : ℝ),
                          Dist.dist (rho, va) ((1 : ℝ), psi) < eta →
                            Dist.dist (rho, vb) ((1 : ℝ), psi) < eta →
                              |DominantFiveBody.physicalPairExteriorAngularField mu r theta a b rho vb -
                                    DominantFiveBody.physicalPairExteriorAngularField mu r theta a b rho va| ≤
                                C * ((1 : ℝ) - (mu a + mu b)) * |vb - va| := @DominantFiveBody.physical_pair_left_endpoint_rectangular_controls

-- Source binding: display:412
example : ∀ (mu r theta : DominantFiveBody.Satellite → ℝ) (a b : DominantFiveBody.Satellite) (rho v : ℝ),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) →
    (∀ j ∈ DominantFiveBody.pairExteriorLabels a b,
        DominantFiveBody.polarPoint (r j) (theta j) ≠ DominantFiveBody.polarPoint rho v) →
      deriv (fun (s : ℝ) => DominantFiveBody.physicalPairExteriorAngularField mu r theta a b s v) rho =
          (-3 : ℝ) *
            ∑ j ∈ DominantFiveBody.pairExteriorLabels a b,
              mu j * r j * Real.sin (theta j - v) * (rho - r j * Real.cos (theta j - v)) *
                (‖DominantFiveBody.polarPoint rho v - DominantFiveBody.polarPoint (r j) (theta j)‖ ^ (5 : ℕ))⁻¹ ∧
        deriv (fun (w : ℝ) => DominantFiveBody.physicalPairExteriorAngularField mu r theta a b rho w) v =
          ∑ j ∈ DominantFiveBody.pairExteriorLabels a b,
            mu j * r j *
              (-Real.cos (theta j - v) *
                  ((‖DominantFiveBody.polarPoint rho v - DominantFiveBody.polarPoint (r j) (theta j)‖ ^ (3 : ℕ))⁻¹ -
                    (r j ^ (3 : ℕ))⁻¹) +
                (3 : ℝ) * rho * r j * Real.sin (theta j - v) ^ (2 : ℕ) *
                  (‖DominantFiveBody.polarPoint rho v - DominantFiveBody.polarPoint (r j) (theta j)‖ ^ (5 : ℕ))⁻¹) := @DominantFiveBody.pairExteriorAngular_source_derivatives

-- Source binding: prose:416
example : ∀ (theta0 : DominantFiveBody.Satellite → ℝ) (a b : DominantFiveBody.Satellite),
  a ≠ b →
    ∀ (psi : ℝ),
      (∀ j ∈ DominantFiveBody.pairExteriorLabels a b, (0 : ℝ) < theta0 j - psi ∧ theta0 j - psi < Real.pi) →
        ∃ (eta : ℝ) (k : ℝ) (C : ℝ),
          (0 : ℝ) < eta ∧
            (0 : ℝ) < k ∧
              (0 : ℝ) < C ∧
                ∀ (mu r theta : DominantFiveBody.Satellite → ℝ),
                  DominantFiveBody.PositiveRatio mu →
                    (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) →
                      (∀ j ∈ DominantFiveBody.pairExteriorLabels a b,
                          Dist.dist (r j, theta j) ((1 : ℝ), theta0 j) < eta) →
                        ∀ (ra rb va vb : ℝ),
                          ra ≤ rb →
                            Dist.dist (ra, va) ((1 : ℝ), psi) < eta →
                              Dist.dist (rb, va) ((1 : ℝ), psi) < eta →
                                Dist.dist (rb, vb) ((1 : ℝ), psi) < eta →
                                  DominantFiveBody.physicalPairExteriorAngularField mu r theta a b rb vb -
                                      DominantFiveBody.physicalPairExteriorAngularField mu r theta a b ra va ≤
                                    -k * ((1 : ℝ) - (mu a + mu b)) * (rb - ra) +
                                      C * ((1 : ℝ) - (mu a + mu b)) * |vb - va| := @DominantFiveBody.physical_pair_left_endpoint_difference_control

-- Source binding: prose:416
example : ∀ (theta0 : DominantFiveBody.Satellite → ℝ) (a b : DominantFiveBody.Satellite),
  a ≠ b →
    ∀ (psi : ℝ),
      (∀ j ∈ DominantFiveBody.pairExteriorLabels a b, -Real.pi < theta0 j - psi ∧ theta0 j - psi < (0 : ℝ)) →
        ∃ (eta : ℝ) (k : ℝ) (C : ℝ),
          (0 : ℝ) < eta ∧
            (0 : ℝ) < k ∧
              (0 : ℝ) < C ∧
                ∀ (mu r theta : DominantFiveBody.Satellite → ℝ),
                  DominantFiveBody.PositiveRatio mu →
                    (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) →
                      (∀ j ∈ DominantFiveBody.pairExteriorLabels a b,
                          Dist.dist (r j, theta j) ((1 : ℝ), theta0 j) < eta) →
                        ∀ (ra rb va vb : ℝ),
                          rb ≤ ra →
                            Dist.dist (rb, vb) ((1 : ℝ), psi) < eta →
                              Dist.dist (ra, vb) ((1 : ℝ), psi) < eta →
                                Dist.dist (ra, va) ((1 : ℝ), psi) < eta →
                                  DominantFiveBody.physicalPairExteriorAngularField mu r theta a b rb vb -
                                      DominantFiveBody.physicalPairExteriorAngularField mu r theta a b ra va ≤
                                    -k * ((1 : ℝ) - (mu a + mu b)) * (ra - rb) +
                                      C * ((1 : ℝ) - (mu a + mu b)) * |vb - va| := @DominantFiveBody.physical_pair_right_endpoint_difference_control

-- Source binding: prose:416
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
              (∀ (n : ℕ),
                  DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                    i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                  ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                    Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (𝓝 qLimit) →
                      ∀ (a b : DominantFiveBody.Satellite),
                        a < b →
                          ∀ (psi : ℝ),
                            DominantFiveBody.CompleteLimitingSatellitePair qLimit a b
                                (DominantFiveBody.polarPoint (1 : ℝ) psi) →
                              ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                                Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                  theta0 a = psi →
                                    theta0 b = psi →
                                      (∀ j ∈ DominantFiveBody.pairExteriorLabels a b,
                                          (0 : ℝ) < theta0 j - psi ∧ theta0 j - psi < Real.pi) →
                                        Filter.Tendsto
                                            (fun (n : ℕ) =>
                                              DominantFiveBody.physicalPairDirection
                                                (DominantFiveBody.satellitesRelative (x n)) a b)
                                            Filter.atTop (𝓝 (DominantFiveBody.polarPoint (1 : ℝ) psi)) →
                                          False := @DominantFiveBody.normalized_complete_pair_left_outward_radial_impossible

-- Source binding: prose:416
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
              (∀ (n : ℕ),
                  DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                    i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                  ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                    Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (𝓝 qLimit) →
                      ∀ (a b : DominantFiveBody.Satellite),
                        a < b →
                          ∀ (psi : ℝ),
                            DominantFiveBody.CompleteLimitingSatellitePair qLimit a b
                                (DominantFiveBody.polarPoint (1 : ℝ) psi) →
                              ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                                Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                  theta0 a = psi →
                                    theta0 b = psi →
                                      (∀ j ∈ DominantFiveBody.pairExteriorLabels a b,
                                          -Real.pi < theta0 j - psi ∧ theta0 j - psi < (0 : ℝ)) →
                                        Filter.Tendsto
                                            (fun (n : ℕ) =>
                                              DominantFiveBody.physicalPairDirection
                                                (DominantFiveBody.satellitesRelative (x n)) a b)
                                            Filter.atTop (𝓝 (-DominantFiveBody.polarPoint (1 : ℝ) psi)) →
                                          False := @DominantFiveBody.normalized_complete_pair_right_inward_radial_impossible

-- Source binding: prop:pair-scale.actual_first_stage
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ),
              DominantFiveBody.StrictConvexInOrder { labels := Equiv.refl DominantFiveBody.Label, primary_first := rfl }
                (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                      i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (a b : DominantFiveBody.Satellite),
                              a < b →
                                ∀ (c : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c →
                                    ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                                      Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                        (↑b : ℕ) = (↑a : ℕ) + (1 : ℕ) ∧
                                          Filter.Tendsto
                                              (fun (n : ℕ) =>
                                                (theta n b - theta n a) /
                                                  DominantFiveBody.satelliteDistance
                                                    (DominantFiveBody.satellitesRelative (x n)) a b)
                                              Filter.atTop (𝓝 (1 : ℝ)) ∧
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  (r n b - r n a) /
                                                    DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) a b)
                                                Filter.atTop (𝓝 (0 : ℝ)) ∧
                                              (∃ (C : ℝ),
                                                  (0 : ℝ) < C ∧
                                                    ∀ᶠ (n : ℕ) in Filter.atTop,
                                                      (mu n a + mu n b) /
                                                          DominantFiveBody.satelliteDistance
                                                              (DominantFiveBody.satellitesRelative (x n)) a b ^
                                                            (3 : ℕ) ≤
                                                        C * ((1 : ℝ) - (mu n a + mu n b))) ∧
                                                Filter.Tendsto (fun (n : ℕ) => mu n a + mu n b) Filter.atTop
                                                    (𝓝 (0 : ℝ)) ∧
                                                  ∃ (C : ℝ),
                                                    (0 : ℝ) < C ∧
                                                      ∀ᶠ (n : ℕ) in Filter.atTop,
                                                        |r n b - r n a| ≤
                                                          C * eps n * ((1 : ℝ) - (mu n a + mu n b)) *
                                                            DominantFiveBody.satelliteDistance
                                                              (DominantFiveBody.satellitesRelative (x n)) a b := @DominantFiveBody.normalized_complete_pair_tangential_mass_scale

-- Source binding: prose:418
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
  DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
    ∀ (r theta : DominantFiveBody.Satellite → ℝ),
      (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) →
        DominantFiveBody.satellitesRelative x = DominantFiveBody.polarSatellites r theta →
          ∀ (a b : DominantFiveBody.Satellite),
            a ≠ b →
              (DominantFiveBody.primaryRadialScalar (r b) - DominantFiveBody.primaryRadialScalar (r a) -
                    eps * (mu a + mu b) /
                        DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r theta) a b ^ (3 : ℕ) *
                      (r b - r a)) *
                  Real.cos ((theta b - theta a) / (2 : ℝ)) =
                -eps *
                  Inner.inner ℝ
                    (DominantFiveBody.pairExteriorField mu (DominantFiveBody.polarSatellites r theta) a b
                        (DominantFiveBody.polarPoint (r b) (theta b)) -
                      DominantFiveBody.pairExteriorField mu (DominantFiveBody.polarSatellites r theta) a b
                        (DominantFiveBody.polarPoint (r a) (theta a)))
                    (DominantFiveBody.polarPoint (1 : ℝ) ((theta a + theta b) / (2 : ℝ))) := @DominantFiveBody.normalized_pair_midpoint_identity

-- Source binding: prop:pair-scale.radial_bound_on_tangential_branch
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
      (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
        ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
          (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
            (∀ (n : ℕ), DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
              ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (𝓝 qLimit) →
                  ∀ (a b : DominantFiveBody.Satellite),
                    a ≠ b →
                      ∀ (c : DominantFiveBody.Plane),
                        DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c →
                          Filter.Tendsto
                              (fun (n : ℕ) =>
                                eps n * (mu n a + mu n b) /
                                  DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b ^
                                    (3 : ℕ))
                              Filter.atTop (𝓝 (0 : ℝ)) →
                            Filter.Tendsto (fun (n : ℕ) => theta n b - theta n a) Filter.atTop (𝓝 (0 : ℝ)) →
                              ∃ (C : ℝ),
                                (0 : ℝ) < C ∧
                                  ∀ᶠ (n : ℕ) in Filter.atTop,
                                    |r n b - r n a| ≤
                                      C * eps n * ((1 : ℝ) - (mu n a + mu n b)) *
                                        DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a
                                          b := @DominantFiveBody.normalized_complete_pair_radial_bound_of_tangential

-- Source binding: prop:pair-scale.actual_positive_cube_limit
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ),
              DominantFiveBody.StrictConvexInOrder { labels := Equiv.refl DominantFiveBody.Label, primary_first := rfl }
                (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                      i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (a b : DominantFiveBody.Satellite),
                              a < b →
                                ∀ (c : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c →
                                    ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                                      Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                        ∀ (u w : DominantFiveBody.Satellite),
                                          u < w →
                                            u ∈ DominantFiveBody.pairExteriorLabels a b →
                                              w ∈ DominantFiveBody.pairExteriorLabels a b →
                                                (0 : ℝ) <
                                                    muLimit u * DominantFiveBody.Coorbital.kappa |theta0 a - theta0 u| +
                                                      muLimit w *
                                                        DominantFiveBody.Coorbital.kappa |theta0 a - theta0 w| ∧
                                                  Filter.Tendsto
                                                    (fun (n : ℕ) =>
                                                      (mu n a + mu n b) /
                                                        DominantFiveBody.satelliteDistance
                                                            (DominantFiveBody.satellitesRelative (x n)) a b ^
                                                          (3 : ℕ))
                                                    Filter.atTop
                                                    (𝓝
                                                      (muLimit u *
                                                          DominantFiveBody.Coorbital.kappa |theta0 a - theta0 u| +
                                                        muLimit w *
                                                          DominantFiveBody.Coorbital.kappa |theta0 a - theta0 w|)) := @DominantFiveBody.normalized_complete_pair_mass_cube_limit

-- Source binding: prose:425
example : ∀ (eps : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ) (a b : DominantFiveBody.Satellite),
  a ≠ b →
    (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.angularResidual eps mu r theta i = (0 : ℝ)) →
      mu a * DominantFiveBody.physicalPairExteriorFullAngularField eps mu r theta a b (r a) (theta a) +
          mu b * DominantFiveBody.physicalPairExteriorFullAngularField eps mu r theta a b (r b) (theta b) =
        (0 : ℝ) := @DominantFiveBody.physical_pair_weighted_full_angular_average

-- Source binding: prose:425
example : ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ) (muLimit theta0 : DominantFiveBody.Satellite → ℝ),
  Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
    (∀ (i : DominantFiveBody.Satellite), Filter.Tendsto (fun (n : ℕ) => r n i) Filter.atTop (𝓝 (1 : ℝ))) →
      Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
        ∀ (a b : DominantFiveBody.Satellite) (psi : ℝ),
          theta0 a = psi →
            theta0 b = psi →
              ∀ (d : ℕ → ℝ),
                (∀ (n : ℕ), (0 : ℝ) < d n) →
                  Filter.Tendsto (fun (n : ℕ) => (r n b - r n a) / d n) Filter.atTop (𝓝 (0 : ℝ)) →
                    Filter.Tendsto (fun (n : ℕ) => (theta n b - theta n a) / d n) Filter.atTop (𝓝 (1 : ℝ)) →
                      (∀ j ∈ DominantFiveBody.pairExteriorLabels a b, theta0 j ≠ psi) →
                        (∀ j ∈ DominantFiveBody.pairExteriorLabels a b, |theta0 j - psi| < Real.pi) →
                          Filter.Tendsto
                            (fun (n : ℕ) =>
                              (DominantFiveBody.physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b)
                                    (theta n b) -
                                  DominantFiveBody.physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a)
                                    (theta n a)) /
                                d n)
                            Filter.atTop
                            (𝓝
                              (∑ j ∈ DominantFiveBody.pairExteriorLabels a b,
                                muLimit j * DominantFiveBody.Coorbital.kappa |psi - theta0 j|)) := @DominantFiveBody.complete_pair_exterior_difference_quotient_limit

-- Source binding: prop:triple-scale
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
              (∀ (n : ℕ),
                  DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                    i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                  ∀ (muLimit : DominantFiveBody.MassRatio),
                    Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                      ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                        Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                            (𝓝 qLimit) →
                          ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                            Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                              ∀ (p : DominantFiveBody.Satellite) (c : DominantFiveBody.Plane),
                                DominantFiveBody.CompleteLimitingSatelliteTriple qLimit p c →
                                  (p = (0 : DominantFiveBody.Satellite) ∨ p = (3 : DominantFiveBody.Satellite)) ∧
                                    ∀ (i : DominantFiveBody.Satellite),
                                      i ≠ p → |theta0 p - theta0 i| = DominantFiveBody.Coorbital.h := @DominantFiveBody.normalized_complete_triple_limiting_exterior

-- Source binding: prop:triple-scale
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ),
              DominantFiveBody.StrictConvexInOrder { labels := Equiv.refl DominantFiveBody.Label, primary_first := rfl }
                (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                      i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (c : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) c →
                                    ∃ (K : ℝ) (C : ℝ),
                                      (0 : ℝ) < K ∧
                                        (0 : ℝ) < C ∧
                                          ∀ᶠ (n : ℕ) in Filter.atTop,
                                            (∀ (i j : DominantFiveBody.TripleLabel),
                                                |r n (Fin.castSucc j) - r n (Fin.castSucc i)| ≤
                                                  K *
                                                    (theta n (2 : DominantFiveBody.Satellite) -
                                                      theta n (0 : DominantFiveBody.Satellite))) ∧
                                              DominantFiveBody.tripleLowDiameter
                                                    (DominantFiveBody.satellitesRelative (x n)) ≤
                                                  (K + (2 : ℝ)) *
                                                    (theta n (2 : DominantFiveBody.Satellite) -
                                                      theta n (0 : DominantFiveBody.Satellite)) ∧
                                                (mu n (0 : DominantFiveBody.Satellite) +
                                                        mu n (1 : DominantFiveBody.Satellite) +
                                                      mu n (2 : DominantFiveBody.Satellite)) /
                                                    DominantFiveBody.tripleLowDiameter
                                                        (DominantFiveBody.satellitesRelative (x n)) ^
                                                      (3 : ℕ) ≤
                                                  C * mu n (3 : DominantFiveBody.Satellite) := @DominantFiveBody.normalized_complete_lower_triple_initial_scales

-- Source binding: prop:triple-scale
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (c : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (0 : DominantFiveBody.Satellite) c →
                                    ∃ (K : ℝ) (C : ℝ),
                                      (0 : ℝ) < K ∧
                                        (0 : ℝ) < C ∧
                                          ∀ᶠ (n : ℕ) in Filter.atTop,
                                            (∀ (i j : DominantFiveBody.TripleLabel),
                                                |r n (Fin.succ j) - r n (Fin.succ i)| ≤
                                                  K *
                                                    (theta n (3 : DominantFiveBody.Satellite) -
                                                      theta n (1 : DominantFiveBody.Satellite))) ∧
                                              DominantFiveBody.tripleHighDiameter
                                                    (DominantFiveBody.satellitesRelative (x n)) ≤
                                                  (K + (2 : ℝ)) *
                                                    (theta n (3 : DominantFiveBody.Satellite) -
                                                      theta n (1 : DominantFiveBody.Satellite)) ∧
                                                (mu n (1 : DominantFiveBody.Satellite) +
                                                        mu n (2 : DominantFiveBody.Satellite) +
                                                      mu n (3 : DominantFiveBody.Satellite)) /
                                                    DominantFiveBody.tripleHighDiameter
                                                        (DominantFiveBody.satellitesRelative (x n)) ^
                                                      (3 : ℕ) ≤
                                                  C * mu n (0 : DominantFiveBody.Satellite) := @DominantFiveBody.normalized_complete_upper_triple_initial_scales

-- Source binding: prop:triple-scale
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ),
              DominantFiveBody.StrictConvexInOrder { labels := Equiv.refl DominantFiveBody.Label, primary_first := rfl }
                (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                      i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (c : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) c →
                                    Filter.Tendsto
                                        (fun (n : ℕ) =>
                                          mu n (0 : DominantFiveBody.Satellite) +
                                              mu n (1 : DominantFiveBody.Satellite) +
                                            mu n (2 : DominantFiveBody.Satellite))
                                        Filter.atTop (𝓝 (0 : ℝ)) ∧
                                      Filter.Tendsto (fun (n : ℕ) => mu n (3 : DominantFiveBody.Satellite)) Filter.atTop
                                        (𝓝 (1 : ℝ)) := @DominantFiveBody.normalized_complete_lower_triple_mass_vanishes

-- Source binding: prop:triple-scale
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (0 : DominantFiveBody.Satellite) center →
                                    Filter.Tendsto
                                        (fun (n : ℕ) =>
                                          mu n (1 : DominantFiveBody.Satellite) +
                                              mu n (2 : DominantFiveBody.Satellite) +
                                            mu n (3 : DominantFiveBody.Satellite))
                                        Filter.atTop (𝓝 (0 : ℝ)) ∧
                                      Filter.Tendsto (fun (n : ℕ) => mu n (0 : DominantFiveBody.Satellite)) Filter.atTop
                                        (𝓝 (1 : ℝ)) := @DominantFiveBody.normalized_complete_upper_triple_mass_vanishes

-- Source binding: prop:triple-scale
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    (∀ (i j : DominantFiveBody.TripleLabel),
                                        Filter.Tendsto
                                          (fun (n : ℕ) =>
                                            (r n (Fin.castSucc j) - r n (Fin.castSucc i)) /
                                              DominantFiveBody.tripleLowDiameter
                                                (DominantFiveBody.satellitesRelative (x n)))
                                          Filter.atTop (𝓝 (0 : ℝ))) ∧
                                      Filter.Tendsto
                                        (fun (n : ℕ) =>
                                          (theta n (2 : DominantFiveBody.Satellite) -
                                              theta n (0 : DominantFiveBody.Satellite)) /
                                            DominantFiveBody.tripleLowDiameter
                                              (DominantFiveBody.satellitesRelative (x n)))
                                        Filter.atTop (𝓝 (1 : ℝ)) := @DominantFiveBody.normalized_complete_lower_triple_original_group_geometry

-- Source binding: prop:triple-scale
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∃ (k : ℝ),
                                      (0 : ℝ) < k ∧
                                        ∀ᶠ (n : ℕ) in Filter.atTop,
                                          k ≤
                                            (mu n (0 : DominantFiveBody.Satellite) +
                                                  mu n (1 : DominantFiveBody.Satellite) +
                                                mu n (2 : DominantFiveBody.Satellite)) /
                                              DominantFiveBody.tripleLowDiameter
                                                  (DominantFiveBody.satellitesRelative (x n)) ^
                                                (3 : ℕ) := @DominantFiveBody.normalized_complete_lower_triple_original_group_mass_lower

-- Source binding: prop:triple-scale
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (0 : DominantFiveBody.Satellite) center →
                                    (∀ (i j : DominantFiveBody.TripleLabel),
                                        Filter.Tendsto
                                          (fun (n : ℕ) =>
                                            (r n (Fin.succ j) - r n (Fin.succ i)) /
                                              DominantFiveBody.tripleHighDiameter
                                                (DominantFiveBody.satellitesRelative (x n)))
                                          Filter.atTop (𝓝 (0 : ℝ))) ∧
                                      Filter.Tendsto
                                          (fun (n : ℕ) =>
                                            (theta n (3 : DominantFiveBody.Satellite) -
                                                theta n (1 : DominantFiveBody.Satellite)) /
                                              DominantFiveBody.tripleHighDiameter
                                                (DominantFiveBody.satellitesRelative (x n)))
                                          Filter.atTop (𝓝 (1 : ℝ)) ∧
                                        ∃ (k : ℝ),
                                          (0 : ℝ) < k ∧
                                            ∀ᶠ (n : ℕ) in Filter.atTop,
                                              k ≤
                                                (mu n (1 : DominantFiveBody.Satellite) +
                                                      mu n (2 : DominantFiveBody.Satellite) +
                                                    mu n (3 : DominantFiveBody.Satellite)) /
                                                  DominantFiveBody.tripleHighDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)) ^
                                                    (3 : ℕ) := @DominantFiveBody.normalized_complete_upper_triple_original_group_complete_geometry

-- Source binding: display:441
example : ∀ (eps s angle rho v : ℝ),
  DominantFiveBody.physicalSourceFullAngularField eps s angle rho v =
    rho * s * Real.sin (angle - v) *
      ((‖DominantFiveBody.polarPoint rho v - DominantFiveBody.polarPoint s angle‖ ^ (3 : ℕ))⁻¹ - ((1 : ℝ) + eps)⁻¹) := @DominantFiveBody.tripleExteriorJ_source_formula

-- Source binding: prose:445
example : ∀ (eps : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ) (p : DominantFiveBody.Satellite),
  (0 : ℝ) < mu p →
    (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.angularResidual eps mu r theta i = (0 : ℝ)) →
      ∑ i ∈ DominantFiveBody.tripleClusterLabels p,
          mu i * DominantFiveBody.physicalSourceFullAngularField eps (r p) (theta p) (r i) (theta i) =
        (0 : ℝ) := @DominantFiveBody.physical_triple_weighted_full_angular_average

-- Source binding: prose:445
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
              (∀ (n : ℕ),
                  DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                  ∀ (muLimit : DominantFiveBody.MassRatio),
                    Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                      ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                        Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                            (𝓝 qLimit) →
                          ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                            Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                              ∀ (center : DominantFiveBody.Plane),
                                DominantFiveBody.CompleteLimitingSatelliteTriple qLimit (3 : DominantFiveBody.Satellite)
                                    center →
                                  ∀ (eta : ℝ),
                                    (0 : ℝ) < eta →
                                      ∀ᶠ (n : ℕ) in Filter.atTop,
                                        ∀
                                          rho ∈
                                            Set.uIcc
                                              (Min.min (r n (0 : DominantFiveBody.Satellite))
                                                (Min.min (r n (1 : DominantFiveBody.Satellite))
                                                  (r n (2 : DominantFiveBody.Satellite))))
                                              (Max.max (r n (0 : DominantFiveBody.Satellite))
                                                (Max.max (r n (1 : DominantFiveBody.Satellite))
                                                  (r n (2 : DominantFiveBody.Satellite)))),
                                          ∀
                                            v ∈
                                              Set.uIcc (theta n (0 : DominantFiveBody.Satellite))
                                                (theta n (2 : DominantFiveBody.Satellite)),
                                            |DominantFiveBody.physicalSourceFullAngularRadialDerivative (eps n)
                                                      (r n (3 : DominantFiveBody.Satellite))
                                                      (theta n (3 : DominantFiveBody.Satellite)) rho v +
                                                    (3 : ℝ) * √(3 : ℝ) / (4 : ℝ)| <
                                                eta ∧
                                              |DominantFiveBody.physicalSourceFullAngularAngularDerivative (eps n)
                                                      (r n (3 : DominantFiveBody.Satellite))
                                                      (theta n (3 : DominantFiveBody.Satellite)) rho v -
                                                    (9 / 4 : ℝ)| <
                                                eta := @DominantFiveBody.normalized_complete_lower_triple_full_rectangle_derivatives_uniform

-- Source binding: eq:triple-J
example : ∀ (eps s angle rho v : ℝ),
  (0 : ℝ) < s →
    DominantFiveBody.polarPoint s angle ≠ DominantFiveBody.polarPoint rho v →
      HasDerivAt (fun (r : ℝ) => DominantFiveBody.physicalSourceFullAngularField eps s angle r v)
        (DominantFiveBody.physicalSourceFullAngularRadialDerivative eps s angle rho v) rho := @DominantFiveBody.physicalSourceFullAngularField_hasDerivAt_radius

-- Source binding: eq:triple-J
example : ∀ (eps s angle rho v : ℝ),
  (0 : ℝ) < s →
    DominantFiveBody.polarPoint s angle ≠ DominantFiveBody.polarPoint rho v →
      HasDerivAt (fun (w : ℝ) => DominantFiveBody.physicalSourceFullAngularField eps s angle rho w)
        (DominantFiveBody.physicalSourceFullAngularAngularDerivative eps s angle rho v) v := @DominantFiveBody.physicalSourceFullAngularField_hasDerivAt_angle

-- Source binding: prose:449
example : ∀ (ra rb rp va vb vp : ℝ),
  (1 / 2 : ℝ) ≤ ra →
    (1 / 2 : ℝ) ≤ rb →
      (1 / 2 : ℝ) ≤ rp →
        ra ≤ (2 : ℝ) →
          rb ≤ (2 : ℝ) →
            rp ≤ (2 : ℝ) →
              (0 : ℝ) < vb - va →
                (1 / 2 : ℝ) ≤ Real.sin (vp - vb) →
                  (0 : ℝ) <
                      DominantFiveBody.det2 (DominantFiveBody.polarPoint rb vb - DominantFiveBody.polarPoint ra va)
                        (DominantFiveBody.polarPoint rp vp - DominantFiveBody.polarPoint ra va) →
                    ra - rb ≤ (32 : ℝ) * (vb - va) := @DominantFiveBody.polar_support_radial_drop_le

-- Source binding: prose:449
example : ∀ (eps : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.PositiveRatio mu →
    (0 : ℝ) < theta (1 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite) →
      (0 : ℝ) < theta (2 : DominantFiveBody.Satellite) - theta (1 : DominantFiveBody.Satellite) →
        (0 : ℝ) <
            DominantFiveBody.tripleAngularCoefficient eps r theta (0 : DominantFiveBody.Satellite)
              (1 : DominantFiveBody.Satellite) →
          (0 : ℝ) <
              DominantFiveBody.tripleAngularCoefficient eps r theta (0 : DominantFiveBody.Satellite)
                (2 : DominantFiveBody.Satellite) →
            (0 : ℝ) <
                DominantFiveBody.tripleAngularCoefficient eps r theta (1 : DominantFiveBody.Satellite)
                  (2 : DominantFiveBody.Satellite) →
              (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.angularResidual eps mu r theta i = (0 : ℝ)) →
                DominantFiveBody.physicalSourceFullAngularField eps (r (3 : DominantFiveBody.Satellite))
                      (theta (3 : DominantFiveBody.Satellite)) (r (0 : DominantFiveBody.Satellite))
                      (theta (0 : DominantFiveBody.Satellite)) <
                    (0 : ℝ) ∧
                  (0 : ℝ) <
                    DominantFiveBody.physicalSourceFullAngularField eps (r (3 : DominantFiveBody.Satellite))
                      (theta (3 : DominantFiveBody.Satellite)) (r (2 : DominantFiveBody.Satellite))
                      (theta (2 : DominantFiveBody.Satellite)) := @DominantFiveBody.physical_triple_extreme_source_signs

-- Source binding: prose:449
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ),
              DominantFiveBody.StrictConvexInOrder { labels := Equiv.refl DominantFiveBody.Label, primary_first := rfl }
                (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                      i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (c : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) c →
                                    ∃ (k : ℝ) (A : ℝ) (C : ℝ),
                                      (0 : ℝ) < k ∧
                                        (0 : ℝ) < A ∧
                                          (0 : ℝ) < C ∧
                                            ∀ᶠ (n : ℕ) in Filter.atTop,
                                              DominantFiveBody.physicalSourceFullAngularField (eps n)
                                                    (r n (3 : DominantFiveBody.Satellite))
                                                    (theta n (3 : DominantFiveBody.Satellite))
                                                    (r n (0 : DominantFiveBody.Satellite))
                                                    (theta n (0 : DominantFiveBody.Satellite)) <
                                                  (0 : ℝ) ∧
                                                (0 : ℝ) <
                                                    DominantFiveBody.physicalSourceFullAngularField (eps n)
                                                      (r n (3 : DominantFiveBody.Satellite))
                                                      (theta n (3 : DominantFiveBody.Satellite))
                                                      (r n (2 : DominantFiveBody.Satellite))
                                                      (theta n (2 : DominantFiveBody.Satellite)) ∧
                                                  (r n (0 : DominantFiveBody.Satellite) ≤
                                                        r n (2 : DominantFiveBody.Satellite) →
                                                      (0 : ℝ) <
                                                          DominantFiveBody.physicalSourceFullAngularField (eps n)
                                                              (r n (3 : DominantFiveBody.Satellite))
                                                              (theta n (3 : DominantFiveBody.Satellite))
                                                              (r n (2 : DominantFiveBody.Satellite))
                                                              (theta n (2 : DominantFiveBody.Satellite)) -
                                                            DominantFiveBody.physicalSourceFullAngularField (eps n)
                                                              (r n (3 : DominantFiveBody.Satellite))
                                                              (theta n (3 : DominantFiveBody.Satellite))
                                                              (r n (0 : DominantFiveBody.Satellite))
                                                              (theta n (0 : DominantFiveBody.Satellite)) ∧
                                                        DominantFiveBody.physicalSourceFullAngularField (eps n)
                                                              (r n (3 : DominantFiveBody.Satellite))
                                                              (theta n (3 : DominantFiveBody.Satellite))
                                                              (r n (2 : DominantFiveBody.Satellite))
                                                              (theta n (2 : DominantFiveBody.Satellite)) -
                                                            DominantFiveBody.physicalSourceFullAngularField (eps n)
                                                              (r n (3 : DominantFiveBody.Satellite))
                                                              (theta n (3 : DominantFiveBody.Satellite))
                                                              (r n (0 : DominantFiveBody.Satellite))
                                                              (theta n (0 : DominantFiveBody.Satellite)) ≤
                                                          -k *
                                                              (r n (2 : DominantFiveBody.Satellite) -
                                                                r n (0 : DominantFiveBody.Satellite)) +
                                                            A *
                                                              (theta n (2 : DominantFiveBody.Satellite) -
                                                                theta n (0 : DominantFiveBody.Satellite))) ∧
                                                    (mu n (0 : DominantFiveBody.Satellite) +
                                                                mu n (1 : DominantFiveBody.Satellite) +
                                                              mu n (2 : DominantFiveBody.Satellite)) *
                                                            (theta n (2 : DominantFiveBody.Satellite) -
                                                              theta n (0 : DominantFiveBody.Satellite)) /
                                                          DominantFiveBody.tripleLowDiameter
                                                              (DominantFiveBody.satellitesRelative (x n)) ^
                                                            (3 : ℕ) ≤
                                                        (16 : ℝ) * mu n (3 : DominantFiveBody.Satellite) *
                                                          (DominantFiveBody.physicalSourceFullAngularField (eps n)
                                                              (r n (3 : DominantFiveBody.Satellite))
                                                              (theta n (3 : DominantFiveBody.Satellite))
                                                              (r n (2 : DominantFiveBody.Satellite))
                                                              (theta n (2 : DominantFiveBody.Satellite)) -
                                                            DominantFiveBody.physicalSourceFullAngularField (eps n)
                                                              (r n (3 : DominantFiveBody.Satellite))
                                                              (theta n (3 : DominantFiveBody.Satellite))
                                                              (r n (0 : DominantFiveBody.Satellite))
                                                              (theta n (0 : DominantFiveBody.Satellite))) ∧
                                                      (16 : ℝ) * mu n (3 : DominantFiveBody.Satellite) *
                                                          (DominantFiveBody.physicalSourceFullAngularField (eps n)
                                                              (r n (3 : DominantFiveBody.Satellite))
                                                              (theta n (3 : DominantFiveBody.Satellite))
                                                              (r n (2 : DominantFiveBody.Satellite))
                                                              (theta n (2 : DominantFiveBody.Satellite)) -
                                                            DominantFiveBody.physicalSourceFullAngularField (eps n)
                                                              (r n (3 : DominantFiveBody.Satellite))
                                                              (theta n (3 : DominantFiveBody.Satellite))
                                                              (r n (0 : DominantFiveBody.Satellite))
                                                              (theta n (0 : DominantFiveBody.Satellite))) ≤
                                                        C * mu n (3 : DominantFiveBody.Satellite) *
                                                          (theta n (2 : DominantFiveBody.Satellite) -
                                                            theta n (0 : DominantFiveBody.Satellite)) := @DominantFiveBody.normalized_complete_lower_triple_original_initial_estimates

-- Source binding: prose:449
example : ∀ (angle psi : ℝ),
  angle - psi = DominantFiveBody.Coorbital.h →
    ∃ (eta : ℝ) (k : ℝ) (C : ℝ),
      (0 : ℝ) < eta ∧
        (0 : ℝ) < k ∧
          (0 : ℝ) < C ∧
            ∀ (eps s theta ra rb va vb : ℝ),
              |eps| < eta →
                Dist.dist (s, theta) ((1 : ℝ), angle) < eta →
                  ra ≤ rb →
                    Dist.dist (ra, va) ((1 : ℝ), psi) < eta →
                      Dist.dist (rb, va) ((1 : ℝ), psi) < eta →
                        Dist.dist (rb, vb) ((1 : ℝ), psi) < eta →
                          DominantFiveBody.physicalSourceFullAngularField eps s theta rb vb -
                              DominantFiveBody.physicalSourceFullAngularField eps s theta ra va ≤
                            -k * (rb - ra) + C * |vb - va| := @DominantFiveBody.physicalSourceFullAngularField_left_difference_control

-- Source binding: prose:453
example : ∀ (ra rb rc va vb vc S K : ℝ),
  (0 : ℝ) ≤ S →
    (0 : ℝ) ≤ K →
      va < vb →
        vb < vc →
          ra - rb ≤ S * (vb - va) →
            rb - rc ≤ S * (vc - vb) →
              (ra ≤ rc → rc - ra ≤ K * (vc - va)) →
                |rb - ra| ≤ (K + (2 : ℝ) * S) * (vc - va) ∧
                  |rc - ra| ≤ (K + (2 : ℝ) * S) * (vc - va) ∧ |rc - rb| ≤ (K + (2 : ℝ) * S) * (vc - va) := @DominantFiveBody.three_radii_spread_le_width

-- Source binding: prose:455
example : ∀ (eps d : ℝ) (r theta : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite),
  (0 : ℝ) ≤ eps →
    (0 : ℝ) < d →
      d ≤ (1 / 4 : ℝ) →
        (1 / 2 : ℝ) ≤ r i →
          (1 / 2 : ℝ) ≤ r j →
            (1 / 2 : ℝ) ≤ Real.sinc (theta j - theta i) →
              (0 : ℝ) < DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r theta) i j →
                DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r theta) i j ≤ d →
                  (1 : ℝ) / ((16 : ℝ) * d ^ (3 : ℕ)) ≤ DominantFiveBody.tripleAngularCoefficient eps r theta i j := @DominantFiveBody.tripleAngularCoefficient_lower

-- Source binding: prose:455
example : ∀ (eps : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ),
  (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.angularResidual eps mu r theta i = (0 : ℝ)) →
    mu (3 : DominantFiveBody.Satellite) *
        (DominantFiveBody.physicalSourceFullAngularField eps (r (3 : DominantFiveBody.Satellite))
            (theta (3 : DominantFiveBody.Satellite)) (r (2 : DominantFiveBody.Satellite))
            (theta (2 : DominantFiveBody.Satellite)) -
          DominantFiveBody.physicalSourceFullAngularField eps (r (3 : DominantFiveBody.Satellite))
            (theta (3 : DominantFiveBody.Satellite)) (r (0 : DominantFiveBody.Satellite))
            (theta (0 : DominantFiveBody.Satellite))) =
      (mu (0 : DominantFiveBody.Satellite) + mu (2 : DominantFiveBody.Satellite)) *
            (theta (2 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite)) *
          DominantFiveBody.tripleAngularCoefficient eps r theta (0 : DominantFiveBody.Satellite)
            (2 : DominantFiveBody.Satellite) +
        mu (1 : DominantFiveBody.Satellite) *
          ((theta (1 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite)) *
              DominantFiveBody.tripleAngularCoefficient eps r theta (0 : DominantFiveBody.Satellite)
                (1 : DominantFiveBody.Satellite) +
            (theta (2 : DominantFiveBody.Satellite) - theta (1 : DominantFiveBody.Satellite)) *
              DominantFiveBody.tripleAngularCoefficient eps r theta (1 : DominantFiveBody.Satellite)
                (2 : DominantFiveBody.Satellite)) := @DominantFiveBody.physical_triple_extreme_angular_identity

-- Source binding: display:456
example : ∀ (eps d : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.PositiveRatio mu →
    (0 : ℝ) < theta (1 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite) →
      (0 : ℝ) < theta (2 : DominantFiveBody.Satellite) - theta (1 : DominantFiveBody.Satellite) →
        (1 : ℝ) / ((16 : ℝ) * d ^ (3 : ℕ)) ≤
            DominantFiveBody.tripleAngularCoefficient eps r theta (0 : DominantFiveBody.Satellite)
              (1 : DominantFiveBody.Satellite) →
          (1 : ℝ) / ((16 : ℝ) * d ^ (3 : ℕ)) ≤
              DominantFiveBody.tripleAngularCoefficient eps r theta (0 : DominantFiveBody.Satellite)
                (2 : DominantFiveBody.Satellite) →
            (1 : ℝ) / ((16 : ℝ) * d ^ (3 : ℕ)) ≤
                DominantFiveBody.tripleAngularCoefficient eps r theta (1 : DominantFiveBody.Satellite)
                  (2 : DominantFiveBody.Satellite) →
              (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.angularResidual eps mu r theta i = (0 : ℝ)) →
                (mu (0 : DominantFiveBody.Satellite) + mu (1 : DominantFiveBody.Satellite) +
                        mu (2 : DominantFiveBody.Satellite)) *
                      (theta (2 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite)) /
                    d ^ (3 : ℕ) ≤
                  (16 : ℝ) * mu (3 : DominantFiveBody.Satellite) *
                    (DominantFiveBody.physicalSourceFullAngularField eps (r (3 : DominantFiveBody.Satellite))
                        (theta (3 : DominantFiveBody.Satellite)) (r (2 : DominantFiveBody.Satellite))
                        (theta (2 : DominantFiveBody.Satellite)) -
                      DominantFiveBody.physicalSourceFullAngularField eps (r (3 : DominantFiveBody.Satellite))
                        (theta (3 : DominantFiveBody.Satellite)) (r (0 : DominantFiveBody.Satellite))
                        (theta (0 : DominantFiveBody.Satellite))) := @DominantFiveBody.physical_triple_extreme_mass_width_bound

-- Source binding: display:456
example : ∀ (eps d C : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.PositiveRatio mu →
    (0 : ℝ) < d →
      (0 : ℝ) < theta (1 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite) →
        (0 : ℝ) < theta (2 : DominantFiveBody.Satellite) - theta (1 : DominantFiveBody.Satellite) →
          (1 : ℝ) / ((16 : ℝ) * d ^ (3 : ℕ)) ≤
              DominantFiveBody.tripleAngularCoefficient eps r theta (0 : DominantFiveBody.Satellite)
                (1 : DominantFiveBody.Satellite) →
            (1 : ℝ) / ((16 : ℝ) * d ^ (3 : ℕ)) ≤
                DominantFiveBody.tripleAngularCoefficient eps r theta (0 : DominantFiveBody.Satellite)
                  (2 : DominantFiveBody.Satellite) →
              (1 : ℝ) / ((16 : ℝ) * d ^ (3 : ℕ)) ≤
                  DominantFiveBody.tripleAngularCoefficient eps r theta (1 : DominantFiveBody.Satellite)
                    (2 : DominantFiveBody.Satellite) →
                (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.angularResidual eps mu r theta i = (0 : ℝ)) →
                  DominantFiveBody.physicalSourceFullAngularField eps (r (3 : DominantFiveBody.Satellite))
                          (theta (3 : DominantFiveBody.Satellite)) (r (2 : DominantFiveBody.Satellite))
                          (theta (2 : DominantFiveBody.Satellite)) -
                        DominantFiveBody.physicalSourceFullAngularField eps (r (3 : DominantFiveBody.Satellite))
                          (theta (3 : DominantFiveBody.Satellite)) (r (0 : DominantFiveBody.Satellite))
                          (theta (0 : DominantFiveBody.Satellite)) ≤
                      C * (theta (2 : DominantFiveBody.Satellite) - theta (0 : DominantFiveBody.Satellite)) →
                    (mu (0 : DominantFiveBody.Satellite) + mu (1 : DominantFiveBody.Satellite) +
                          mu (2 : DominantFiveBody.Satellite)) /
                        d ^ (3 : ℕ) ≤
                      (16 : ℝ) * C * mu (3 : DominantFiveBody.Satellite) := @DominantFiveBody.triple_mass_cube_upper_of_extreme_rows

-- Source binding: prose:461
example : ∀ (q : ℕ → DominantFiveBody.SatelliteConfiguration),
  (∀ (n : ℕ), DominantFiveBody.RelativeCollisionFree (q n)) →
    ∃ (phi : ℕ → ℕ) (z : DominantFiveBody.Satellite → DominantFiveBody.Plane),
      StrictMono phi ∧
        (∀ (i : DominantFiveBody.TripleLabel),
            Filter.Tendsto
              (fun (n : ℕ) =>
                (DominantFiveBody.tripleLowDiameter (q (phi n)))⁻¹ •
                  (q (phi n) (Fin.castSucc i) - q (phi n) (0 : DominantFiveBody.Satellite)))
              Filter.atTop (𝓝 (z (Fin.castSucc i)))) ∧
          z (0 : DominantFiveBody.Satellite) = (0 : DominantFiveBody.Plane) ∧
            (z (0 : DominantFiveBody.Satellite) ≠ z (1 : DominantFiveBody.Satellite) ∨
              z (0 : DominantFiveBody.Satellite) ≠ z (2 : DominantFiveBody.Satellite) ∨
                z (1 : DominantFiveBody.Satellite) ≠ z (2 : DominantFiveBody.Satellite)) := @DominantFiveBody.lower_triple_scaled_positions_compact_subsequence

-- Source binding: prose:461
example : ∀ (mu : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration)
  (S : Finset DominantFiveBody.Satellite) (v : DominantFiveBody.Plane),
  ∑ i ∈ S, ∑ j ∈ S, mu i * mu j * Inner.inner ℝ (DominantFiveBody.newtonTargetField (q j) (q i)) v = (0 : ℝ) := @DominantFiveBody.satellite_group_internal_projection_zero

-- Source binding: prose:461
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration)
  (S : Finset DominantFiveBody.Satellite),
  S.Nonempty →
    (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < mu i) →
      (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.vectorResidual eps mu q i = (0 : DominantFiveBody.Plane)) →
        ∀ (v : DominantFiveBody.Plane),
          (DominantFiveBody.satelliteGroupScalarAverage mu S fun (i : DominantFiveBody.Satellite) =>
                  Inner.inner ℝ (DominantFiveBody.primaryRadialField (q i)) v) +
                eps * DominantFiveBody.satelliteGroupExteriorProjection mu q S v -
              eps * Inner.inner ℝ (DominantFiveBody.relativeField mu q) v =
            (0 : ℝ) := @DominantFiveBody.physical_current_group_projection_average

-- Source binding: prose:461
example : ∀ (mu : DominantFiveBody.MassRatio),
  DominantFiveBody.PositiveRatio mu →
    ∀ (q : DominantFiveBody.SatelliteConfiguration),
      DominantFiveBody.RelativeCollisionFree q →
        ∀ (S : Finset DominantFiveBody.Satellite),
          S.Nonempty →
            ∀ (p : DominantFiveBody.Satellite) (v : DominantFiveBody.Plane),
              ‖v‖ = (1 : ℝ) →
                ∀ (d eta C : ℝ),
                  (0 : ℝ) < d →
                    (0 : ℝ) < eta →
                      (0 : ℝ) < C →
                        (∀ i ∈ S, ∀ j ∈ Sᶜ.erase p, eta * d ≤ DominantFiveBody.satelliteDistance q j i) →
                          (∑ j ∈ Finset.univ.erase p, mu j) / d ^ (3 : ℕ) ≤ C →
                            |DominantFiveBody.satelliteGroupScalarAverage mu S fun (i : DominantFiveBody.Satellite) =>
                                  ∑ j ∈ Sᶜ.erase p,
                                    mu j * Inner.inner ℝ (DominantFiveBody.newtonTargetField (q j) (q i)) v| ≤
                              C / eta ^ (2 : ℕ) * d := @DominantFiveBody.satelliteGroupNearProjection_abs_bound

-- Source binding: prose:461
example : ∀ (q : ℕ → DominantFiveBody.SatelliteConfiguration) (d : ℕ → ℝ),
  (∀ (n : ℕ), (0 : ℝ) < d n) →
    ∀ (E S : Finset DominantFiveBody.Satellite),
      S ⊆ E →
        ∀ (ref : DominantFiveBody.Satellite) (z : DominantFiveBody.Satellite → DominantFiveBody.Plane),
          (∀ i ∈ E, Filter.Tendsto (fun (n : ℕ) => (d n)⁻¹ • (q n i - q n ref)) Filter.atTop (𝓝 (z i))) →
            (∀ i ∈ S, ∀ j ∈ E \ S, z i ≠ z j) →
              ∃ (eta : ℝ),
                (0 : ℝ) < eta ∧
                  ∀ᶠ (n : ℕ) in Filter.atTop,
                    ∀ i ∈ S, ∀ j ∈ E \ S, eta * d n ≤ DominantFiveBody.satelliteDistance (q n) j i := @DominantFiveBody.equal_scaled_class_cross_separation

-- Source binding: prose:461
example : ∀ (q : ℕ → DominantFiveBody.SatelliteConfiguration) (q0 : DominantFiveBody.SatelliteConfiguration),
  Filter.Tendsto q Filter.atTop (𝓝 q0) →
    ∀ (E : Finset DominantFiveBody.Satellite),
      E.Nonempty →
        ∀ (ref p : DominantFiveBody.Satellite) (c : DominantFiveBody.Plane),
          q0 ref = c →
            (∀ i ∈ E, q0 i = c) →
              q0 p ≠ c →
                ∀ (d : ℕ → ℝ),
                  (∀ (n : ℕ), (0 : ℝ) < d n) →
                    (∀ (n : ℕ), ∀ i ∈ E, DominantFiveBody.satelliteDistance (q n) ref i ≤ d n) →
                      ∀ (v : DominantFiveBody.Plane),
                        ‖v‖ = (1 : ℝ) →
                          ∃ (K : ℝ),
                            (0 : ℝ) < K ∧
                              ∀ᶠ (n : ℕ) in Filter.atTop,
                                ∀ i ∈ E,
                                  |Inner.inner ℝ
                                        (DominantFiveBody.newtonTargetField (q n p) (q n i) -
                                          DominantFiveBody.newtonTargetField (q n p) (q n ref))
                                        v| ≤
                                    K * d n := @DominantFiveBody.finite_exterior_scaled_difference_bound

-- Source binding: prose:461
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (q : ℕ → DominantFiveBody.SatelliteConfiguration),
  Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
    (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
      (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
          DominantFiveBody.vectorResidual (eps n) (mu n) (q n) i = (0 : DominantFiveBody.Plane)) →
        (∀ (n : ℕ), DominantFiveBody.RelativeCollisionFree (q n)) →
          ∀ (q0 : DominantFiveBody.SatelliteConfiguration),
            Filter.Tendsto q Filter.atTop (𝓝 q0) →
              ∀ (p : DominantFiveBody.Satellite) (c : DominantFiveBody.Plane),
                ‖c‖ = (1 : ℝ) →
                  (∀ i ∈ Finset.univ.erase p, q0 i = c) →
                    q0 p ≠ c →
                      ∀ (d : ℕ → ℝ),
                        (∀ (n : ℕ), (0 : ℝ) < d n) →
                          (∀ (n : ℕ),
                              ∀ i ∈ Finset.univ.erase p,
                                ∀ j ∈ Finset.univ.erase p, DominantFiveBody.satelliteDistance (q n) i j ≤ d n) →
                            (∃ (C : ℝ),
                                (0 : ℝ) < C ∧
                                  ∀ᶠ (n : ℕ) in Filter.atTop, (∑ i ∈ Finset.univ.erase p, mu n i) / d n ^ (3 : ℕ) ≤ C) →
                              ∀ (ref : DominantFiveBody.Satellite)
                                (z : DominantFiveBody.Satellite → DominantFiveBody.Plane),
                                (∀ i ∈ Finset.univ.erase p,
                                    Filter.Tendsto (fun (n : ℕ) => (d n)⁻¹ • (q n i - q n ref)) Filter.atTop
                                      (𝓝 (z i))) →
                                  ∀ (S T : Finset DominantFiveBody.Satellite),
                                    S ⊆ Finset.univ.erase p →
                                      T ⊆ Finset.univ.erase p →
                                        ∀ (a b : DominantFiveBody.Satellite),
                                          a ∈ S →
                                            b ∈ T →
                                              (∀ i ∈ Finset.univ.erase p, i ∈ S ↔ z i = z a) →
                                                (∀ i ∈ Finset.univ.erase p, i ∈ T ↔ z i = z b) →
                                                  ∀ (v : DominantFiveBody.Plane),
                                                    ‖v‖ = (1 : ℝ) →
                                                      Filter.Tendsto
                                                          (fun (n : ℕ) =>
                                                            Inner.inner ℝ
                                                                (DominantFiveBody.primaryRadialField (q n a) -
                                                                  DominantFiveBody.primaryRadialField (q n b))
                                                                v /
                                                              d n)
                                                          Filter.atTop (𝓝 (0 : ℝ)) ∧
                                                        ∃ (R : ℕ → ℝ) (B : ℕ → ℝ),
                                                          (∀ (n : ℕ),
                                                              Inner.inner ℝ
                                                                  (DominantFiveBody.primaryRadialField (q n a) -
                                                                    DominantFiveBody.primaryRadialField (q n b))
                                                                  v =
                                                                R n + eps n * B n) ∧
                                                            Filter.Tendsto (fun (n : ℕ) => R n / d n) Filter.atTop
                                                                (𝓝 (0 : ℝ)) ∧
                                                              ∃ (C : ℝ), ∀ᶠ (n : ℕ) in Filter.atTop, |B n / d n| ≤ C := @DominantFiveBody.physical_triple_equal_scaled_groups_primary_projection_limit

-- Source binding: display:462
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration)
  (S T : Finset DominantFiveBody.Satellite),
  S.Nonempty →
    T.Nonempty →
      (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < mu i) →
        (∀ (i : DominantFiveBody.Satellite),
            DominantFiveBody.vectorResidual eps mu q i = (0 : DominantFiveBody.Plane)) →
          ∀ (v : DominantFiveBody.Plane),
            ((DominantFiveBody.satelliteGroupScalarAverage mu S fun (i : DominantFiveBody.Satellite) =>
                    Inner.inner ℝ (DominantFiveBody.primaryRadialField (q i)) v) -
                  DominantFiveBody.satelliteGroupScalarAverage mu T fun (i : DominantFiveBody.Satellite) =>
                    Inner.inner ℝ (DominantFiveBody.primaryRadialField (q i)) v) +
                eps *
                  (DominantFiveBody.satelliteGroupExteriorProjection mu q S v -
                    DominantFiveBody.satelliteGroupExteriorProjection mu q T v) =
              (0 : ℝ) := @DominantFiveBody.physical_two_current_groups_projection_difference

-- Source binding: display:462
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (q : ℕ → DominantFiveBody.SatelliteConfiguration),
  Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
    (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
      (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
          DominantFiveBody.vectorResidual (eps n) (mu n) (q n) i = (0 : DominantFiveBody.Plane)) →
        (∀ (n : ℕ), DominantFiveBody.RelativeCollisionFree (q n)) →
          ∀ (q0 : DominantFiveBody.SatelliteConfiguration),
            Filter.Tendsto q Filter.atTop (𝓝 q0) →
              ∀ (p : DominantFiveBody.Satellite) (c : DominantFiveBody.Plane),
                ‖c‖ = (1 : ℝ) →
                  (∀ i ∈ Finset.univ.erase p, q0 i = c) →
                    q0 p ≠ c →
                      ∀ (d : ℕ → ℝ),
                        (∀ (n : ℕ), (0 : ℝ) < d n) →
                          (∀ (n : ℕ),
                              ∀ i ∈ Finset.univ.erase p,
                                ∀ j ∈ Finset.univ.erase p, DominantFiveBody.satelliteDistance (q n) i j ≤ d n) →
                            (∃ (C : ℝ),
                                (0 : ℝ) < C ∧
                                  ∀ᶠ (n : ℕ) in Filter.atTop, (∑ i ∈ Finset.univ.erase p, mu n i) / d n ^ (3 : ℕ) ≤ C) →
                              ∀ (ref : DominantFiveBody.Satellite)
                                (z : DominantFiveBody.Satellite → DominantFiveBody.Plane),
                                (∀ i ∈ Finset.univ.erase p,
                                    Filter.Tendsto (fun (n : ℕ) => (d n)⁻¹ • (q n i - q n ref)) Filter.atTop
                                      (𝓝 (z i))) →
                                  ∀ (S T : Finset DominantFiveBody.Satellite),
                                    S ⊆ Finset.univ.erase p →
                                      T ⊆ Finset.univ.erase p →
                                        ∀ (a b : DominantFiveBody.Satellite),
                                          a ∈ S →
                                            b ∈ T →
                                              (∀ i ∈ Finset.univ.erase p, i ∈ S ↔ z i = z a) →
                                                (∀ i ∈ Finset.univ.erase p, i ∈ T ↔ z i = z b) →
                                                  Filter.Tendsto
                                                    (fun (n : ℕ) =>
                                                      (d n)⁻¹ •
                                                        (DominantFiveBody.primaryRadialField (q n a) -
                                                          DominantFiveBody.primaryRadialField (q n b)))
                                                    Filter.atTop (𝓝 (0 : DominantFiveBody.Plane)) := @DominantFiveBody.physical_triple_equal_scaled_groups_primary_vector_limit

-- Source binding: prose:465
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (q : ℕ → DominantFiveBody.SatelliteConfiguration),
  Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
    (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
      (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
          DominantFiveBody.vectorResidual (eps n) (mu n) (q n) i = (0 : DominantFiveBody.Plane)) →
        (∀ (n : ℕ), DominantFiveBody.RelativeCollisionFree (q n)) →
          ∀ (q0 : DominantFiveBody.SatelliteConfiguration),
            Filter.Tendsto q Filter.atTop (𝓝 q0) →
              ∀ (p : DominantFiveBody.Satellite) (c : DominantFiveBody.Plane),
                ‖c‖ = (1 : ℝ) →
                  (∀ i ∈ Finset.univ.erase p, q0 i = c) →
                    q0 p ≠ c →
                      ∀ (d : ℕ → ℝ),
                        (∀ (n : ℕ), (0 : ℝ) < d n) →
                          (∀ (n : ℕ),
                              ∀ i ∈ Finset.univ.erase p,
                                ∀ j ∈ Finset.univ.erase p, DominantFiveBody.satelliteDistance (q n) i j ≤ d n) →
                            (∃ (C : ℝ),
                                (0 : ℝ) < C ∧
                                  ∀ᶠ (n : ℕ) in Filter.atTop, (∑ i ∈ Finset.univ.erase p, mu n i) / d n ^ (3 : ℕ) ≤ C) →
                              ∀ (ref : DominantFiveBody.Satellite)
                                (z : DominantFiveBody.Satellite → DominantFiveBody.Plane),
                                (∀ i ∈ Finset.univ.erase p,
                                    Filter.Tendsto (fun (n : ℕ) => (d n)⁻¹ • (q n i - q n ref)) Filter.atTop
                                      (𝓝 (z i))) →
                                  ∀ (a b : DominantFiveBody.Satellite),
                                    a ∈ Finset.univ.erase p →
                                      b ∈ Finset.univ.erase p →
                                        Filter.Tendsto (fun (n : ℕ) => Inner.inner ℝ ((d n)⁻¹ • (q n b - q n a)) c)
                                          Filter.atTop (𝓝 (0 : ℝ)) := @DominantFiveBody.physical_triple_scaled_groups_radial_projection_limit

-- Source binding: prose:465
example : ∀ (ra va rb vb d : ℕ → ℝ) (psi : ℝ),
  Filter.Tendsto va Filter.atTop (𝓝 psi) →
    Filter.Tendsto vb Filter.atTop (𝓝 psi) →
      (∀ (n : ℕ), (0 : ℝ) < d n) →
        (∀ (n : ℕ),
            ‖(d n)⁻¹ • (DominantFiveBody.polarPoint (rb n) (vb n) - DominantFiveBody.polarPoint (ra n) (va n))‖ ≤
              (1 : ℝ)) →
          Filter.Tendsto
              (fun (n : ℕ) =>
                Inner.inner ℝ
                  ((d n)⁻¹ • (DominantFiveBody.polarPoint (rb n) (vb n) - DominantFiveBody.polarPoint (ra n) (va n)))
                  (DominantFiveBody.polarPoint (1 : ℝ) psi))
              Filter.atTop (𝓝 (0 : ℝ)) →
            Filter.Tendsto (fun (n : ℕ) => (rb n - ra n) / d n) Filter.atTop (𝓝 (0 : ℝ)) := @DominantFiveBody.polar_scaled_radius_difference_tendsto_zero

-- Source binding: prose:465
example : ∀ (ra rb va vb d : ℝ),
  (‖DominantFiveBody.polarPoint rb vb - DominantFiveBody.polarPoint ra va‖ / d) ^ (2 : ℕ) =
    ((rb - ra) / d) ^ (2 : ℕ) + ra * rb * Real.sinc ((vb - va) / (2 : ℝ)) ^ (2 : ℕ) * ((vb - va) / d) ^ (2 : ℕ) := @DominantFiveBody.polar_scaled_distance_square

-- Source binding: prose:465
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (z : DominantFiveBody.Satellite → DominantFiveBody.Plane),
                                      (∀ (i : DominantFiveBody.TripleLabel),
                                          Filter.Tendsto
                                            (fun (n : ℕ) =>
                                              (DominantFiveBody.tripleLowDiameter
                                                    (DominantFiveBody.satellitesRelative (x n)))⁻¹ •
                                                (DominantFiveBody.satellitesRelative (x n) (Fin.castSucc i) -
                                                  DominantFiveBody.satellitesRelative (x n)
                                                    (0 : DominantFiveBody.Satellite)))
                                            Filter.atTop (𝓝 (z (Fin.castSucc i)))) →
                                        (∀ (i j : DominantFiveBody.TripleLabel),
                                            Filter.Tendsto
                                              (fun (n : ℕ) =>
                                                (r n (Fin.castSucc j) - r n (Fin.castSucc i)) /
                                                  DominantFiveBody.tripleLowDiameter
                                                    (DominantFiveBody.satellitesRelative (x n)))
                                              Filter.atTop (𝓝 (0 : ℝ))) ∧
                                          Filter.Tendsto
                                            (fun (n : ℕ) =>
                                              (theta n (2 : DominantFiveBody.Satellite) -
                                                  theta n (0 : DominantFiveBody.Satellite)) /
                                                DominantFiveBody.tripleLowDiameter
                                                  (DominantFiveBody.satellitesRelative (x n)))
                                            Filter.atTop (𝓝 (1 : ℝ)) := @DominantFiveBody.normalized_complete_lower_triple_original_group_geometry_of_scaled_limits

-- Source binding: prose:467
example : ∀ (eps : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.PositiveRatio mu →
    (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.angularResidual eps mu r theta i = (0 : ℝ)) →
      ∀ (S : Finset DominantFiveBody.Satellite),
        S.Nonempty →
          ∀ p ∉ S,
            ((DominantFiveBody.satelliteGroupScalarAverage mu S fun (i : DominantFiveBody.Satellite) =>
                  ∑ j ∈ Sᶜ.erase p, mu j * DominantFiveBody.fullAngularMatrix eps r theta i j) +
                mu p *
                  DominantFiveBody.satelliteGroupScalarAverage mu S fun (i : DominantFiveBody.Satellite) =>
                    DominantFiveBody.physicalSourceFullAngularField eps (r p) (theta p) (r i) (theta i)) =
              (0 : ℝ) := @DominantFiveBody.physical_current_group_full_angular_average

-- Source binding: prose:467
example : ∀ (eps : ℝ) (r theta : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite),
  (0 : ℝ) ≤ eps →
    (0 : ℝ) < r i →
      (0 : ℝ) < r j →
        r i ≤ (2 : ℝ) →
          r j ≤ (2 : ℝ) →
            ∀ (d eta : ℝ),
              (0 : ℝ) < d →
                (0 : ℝ) < eta →
                  |theta j - theta i| ≤ (2 : ℝ) * d →
                    eta * d ≤ DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r theta) i j →
                      |DominantFiveBody.fullAngularMatrix eps r theta i j| ≤
                        ((8 : ℝ) / eta ^ (3 : ℕ) + (8 : ℝ) * d ^ (3 : ℕ)) / d ^ (2 : ℕ) := @DominantFiveBody.fullAngularMatrix_cross_distance_abs_bound

-- Source binding: prose:467
example : ∀ (mu : DominantFiveBody.MassRatio),
  DominantFiveBody.PositiveRatio mu →
    ∀ (F : DominantFiveBody.Satellite → DominantFiveBody.Satellite → ℝ) (S : Finset DominantFiveBody.Satellite),
      S.Nonempty →
        ∀ (p : DominantFiveBody.Satellite) (d K : ℝ),
          (0 : ℝ) < d →
            (0 : ℝ) ≤ K →
              (∀ i ∈ S, ∀ j ∈ Sᶜ.erase p, |F i j| ≤ K / d ^ (2 : ℕ)) →
                |(DominantFiveBody.satelliteGroupScalarAverage mu S fun (i : DominantFiveBody.Satellite) =>
                        ∑ j ∈ Sᶜ.erase p, mu j * F i j) /
                      d| ≤
                  K * ((∑ j ∈ Finset.univ.erase p, mu j) / d ^ (3 : ℕ)) := @DominantFiveBody.current_group_near_angular_scaled_abs_bound

-- Source binding: prose:467
example : ∀ (eps : ℕ → ℝ) (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ) (d : ℕ → ℝ),
  (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
    (∀ (n : ℕ), (0 : ℝ) ≤ eps n) →
      ∀ (S : Finset DominantFiveBody.Satellite),
        S.Nonempty →
          ∀ (p : DominantFiveBody.Satellite) (eta : ℝ),
            (0 : ℝ) < eta →
              (∀ (n : ℕ), (0 : ℝ) < d n) →
                Filter.Tendsto d Filter.atTop (𝓝 (0 : ℝ)) →
                  Filter.Tendsto (fun (n : ℕ) => (∑ j ∈ Finset.univ.erase p, mu n j) / d n ^ (3 : ℕ)) Filter.atTop
                      (𝓝 (0 : ℝ)) →
                    (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                      (∀ᶠ (n : ℕ) in Filter.atTop, ∀ i ∈ Finset.univ.erase p, r n i ≤ (2 : ℝ)) →
                        S ⊆ Finset.univ.erase p →
                          (∀ᶠ (n : ℕ) in Filter.atTop,
                              ∀ i ∈ S, ∀ j ∈ Sᶜ.erase p, |theta n j - theta n i| ≤ (2 : ℝ) * d n) →
                            (∀ᶠ (n : ℕ) in Filter.atTop,
                                ∀ i ∈ S,
                                  ∀ j ∈ Sᶜ.erase p,
                                    eta * d n ≤
                                      DominantFiveBody.satelliteDistance
                                        (DominantFiveBody.polarSatellites (r n) (theta n)) i j) →
                              Filter.Tendsto
                                (fun (n : ℕ) =>
                                  (DominantFiveBody.satelliteGroupScalarAverage (mu n) S
                                      fun (i : DominantFiveBody.Satellite) =>
                                      ∑ j ∈ Sᶜ.erase p,
                                        mu n j * DominantFiveBody.fullAngularMatrix (eps n) (r n) (theta n) i j) /
                                    d n)
                                Filter.atTop (𝓝 (0 : ℝ)) := @DominantFiveBody.actual_group_near_angular_scaled_tendsto_zero

-- Source binding: prose:467
example : ∀ (eps : ℕ → ℝ) (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ) (d : ℕ → ℝ),
  (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
    (∀ (n : ℕ), (0 : ℝ) < d n) →
      (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
          DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = (0 : ℝ)) →
        ∀ (S : Finset DominantFiveBody.Satellite),
          S.Nonempty →
            ∀ p ∉ S,
              ∀ (a : DominantFiveBody.Satellite),
                Filter.Tendsto (fun (n : ℕ) => mu n p) Filter.atTop (𝓝 (1 : ℝ)) →
                  Filter.Tendsto
                      (fun (n : ℕ) =>
                        (DominantFiveBody.satelliteGroupScalarAverage (mu n) S fun (i : DominantFiveBody.Satellite) =>
                            ∑ j ∈ Sᶜ.erase p, mu n j * DominantFiveBody.fullAngularMatrix (eps n) (r n) (theta n) i j) /
                          d n)
                      Filter.atTop (𝓝 (0 : ℝ)) →
                    (∀ i ∈ S,
                        Filter.Tendsto
                          (fun (n : ℕ) =>
                            (DominantFiveBody.physicalSourceFullAngularField (eps n) (r n p) (theta n p) (r n i)
                                  (theta n i) -
                                DominantFiveBody.physicalSourceFullAngularField (eps n) (r n p) (theta n p) (r n a)
                                  (theta n a)) /
                              d n)
                          Filter.atTop (𝓝 (0 : ℝ))) →
                      Filter.Tendsto
                        (fun (n : ℕ) =>
                          DominantFiveBody.physicalSourceFullAngularField (eps n) (r n p) (theta n p) (r n a)
                              (theta n a) /
                            d n)
                        Filter.atTop (𝓝 (0 : ℝ)) := @DominantFiveBody.actual_current_angular_group_representative_scaled_limit

-- Source binding: prose:467
example : ∀ (eps : ℕ → ℝ) (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ) (d : ℕ → ℝ),
  (∀ (n : ℕ), (0 : ℝ) ≤ eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
          (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
              DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = (0 : ℝ)) →
            ∀ (p ref : DominantFiveBody.Satellite) (psi angle0 : ℝ)
              (z : DominantFiveBody.Satellite → DominantFiveBody.Plane),
              (∀ (n : ℕ), (0 : ℝ) < d n) →
                Filter.Tendsto d Filter.atTop (𝓝 (0 : ℝ)) →
                  (∀ (i : DominantFiveBody.Satellite), Filter.Tendsto (fun (n : ℕ) => r n i) Filter.atTop (𝓝 (1 : ℝ))) →
                    Filter.Tendsto (fun (n : ℕ) => theta n p) Filter.atTop (𝓝 angle0) →
                      (∀ i ∈ Finset.univ.erase p, Filter.Tendsto (fun (n : ℕ) => theta n i) Filter.atTop (𝓝 psi)) →
                        angle0 ≠ psi →
                          |angle0 - psi| < Real.pi →
                            |psi - angle0| = DominantFiveBody.Coorbital.h →
                              Filter.Tendsto (fun (n : ℕ) => mu n p) Filter.atTop (𝓝 (1 : ℝ)) →
                                (∀ i ∈ Finset.univ.erase p,
                                    Filter.Tendsto
                                      (fun (n : ℕ) =>
                                        (d n)⁻¹ •
                                          (DominantFiveBody.polarSatellites (r n) (theta n) i -
                                            DominantFiveBody.polarSatellites (r n) (theta n) ref))
                                      Filter.atTop (𝓝 (z i))) →
                                  (∀ i ∈ Finset.univ.erase p,
                                      ∀ j ∈ Finset.univ.erase p,
                                        Filter.Tendsto (fun (n : ℕ) => (r n j - r n i) / d n) Filter.atTop
                                          (𝓝 (0 : ℝ))) →
                                    (∀ᶠ (n : ℕ) in Filter.atTop,
                                        ∀ i ∈ Finset.univ.erase p,
                                          ∀ j ∈ Finset.univ.erase p, |theta n j - theta n i| ≤ (2 : ℝ) * d n) →
                                      Filter.Tendsto
                                          (fun (n : ℕ) => (∑ i ∈ Finset.univ.erase p, mu n i) / d n ^ (3 : ℕ))
                                          Filter.atTop (𝓝 (0 : ℝ)) →
                                        ∀ (a b : DominantFiveBody.Satellite),
                                          a ∈ Finset.univ.erase p → b ∈ Finset.univ.erase p → z a ≠ z b → False := @DominantFiveBody.physical_triple_original_angular_groups_zero_cube_impossible

-- Source binding: prose:467
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (z : DominantFiveBody.Satellite → DominantFiveBody.Plane),
                                      (∀ (i : DominantFiveBody.TripleLabel),
                                          Filter.Tendsto
                                            (fun (n : ℕ) =>
                                              (DominantFiveBody.tripleLowDiameter
                                                    (DominantFiveBody.satellitesRelative (x n)))⁻¹ •
                                                (DominantFiveBody.satellitesRelative (x n) (Fin.castSucc i) -
                                                  DominantFiveBody.satellitesRelative (x n)
                                                    (0 : DominantFiveBody.Satellite)))
                                            Filter.atTop (𝓝 (z (Fin.castSucc i)))) →
                                        Filter.Tendsto
                                            (fun (n : ℕ) =>
                                              (mu n (0 : DominantFiveBody.Satellite) +
                                                    mu n (1 : DominantFiveBody.Satellite) +
                                                  mu n (2 : DominantFiveBody.Satellite)) /
                                                DominantFiveBody.tripleLowDiameter
                                                    (DominantFiveBody.satellitesRelative (x n)) ^
                                                  (3 : ℕ))
                                            Filter.atTop (𝓝 (0 : ℝ)) →
                                          ∀ (a b : DominantFiveBody.TripleLabel),
                                            z (Fin.castSucc a) ≠ z (Fin.castSucc b) → False := @DominantFiveBody.normalized_complete_lower_triple_original_angular_scaled_zero_cube_impossible

-- Source binding: prose:467
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    Filter.Tendsto
                                        (fun (n : ℕ) =>
                                          (mu n (0 : DominantFiveBody.Satellite) +
                                                mu n (1 : DominantFiveBody.Satellite) +
                                              mu n (2 : DominantFiveBody.Satellite)) /
                                            DominantFiveBody.tripleLowDiameter
                                                (DominantFiveBody.satellitesRelative (x n)) ^
                                              (3 : ℕ))
                                        Filter.atTop (𝓝 (0 : ℝ)) →
                                      False := @DominantFiveBody.normalized_complete_lower_triple_original_group_zero_cube_impossible

-- Source binding: prop:nested-scale
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                      (Fin.castSucc b) /
                                                    DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              (↑b : ℕ) = (↑a : ℕ) + (1 : ℕ) ∧
                                                Filter.Tendsto
                                                    (fun (n : ℕ) =>
                                                      (mu n (Fin.castSucc a) + mu n (Fin.castSucc b)) /
                                                        (mu n (0 : DominantFiveBody.Satellite) +
                                                            mu n (1 : DominantFiveBody.Satellite) +
                                                          mu n (2 : DominantFiveBody.Satellite)))
                                                    Filter.atTop (𝓝 (0 : ℝ)) ∧
                                                  Filter.Tendsto
                                                      (fun (n : ℕ) =>
                                                        (mu n (0 : DominantFiveBody.Satellite) +
                                                              mu n (1 : DominantFiveBody.Satellite) +
                                                            mu n (2 : DominantFiveBody.Satellite)) /
                                                          DominantFiveBody.tripleLowDiameter
                                                              (DominantFiveBody.satellitesRelative (x n)) ^
                                                            (3 : ℕ))
                                                      Filter.atTop (𝓝 (9 / 4 : ℝ)) ∧
                                                    Filter.Tendsto
                                                        (fun (n : ℕ) =>
                                                          (mu n (Fin.castSucc a) + mu n (Fin.castSucc b)) /
                                                            DominantFiveBody.satelliteDistance
                                                                (DominantFiveBody.satellitesRelative (x n))
                                                                (Fin.castSucc a) (Fin.castSucc b) ^
                                                              (3 : ℕ))
                                                        Filter.atTop (𝓝 (27 / 4 : ℝ)) ∧
                                                      Filter.Tendsto
                                                          (fun (n : ℕ) =>
                                                            (theta n (Fin.castSucc b) - theta n (Fin.castSucc a)) /
                                                              DominantFiveBody.satelliteDistance
                                                                (DominantFiveBody.satellitesRelative (x n))
                                                                (Fin.castSucc a) (Fin.castSucc b))
                                                          Filter.atTop (𝓝 (1 : ℝ)) ∧
                                                        ∃ (C : ℝ),
                                                          (0 : ℝ) < C ∧
                                                            ∀ᶠ (n : ℕ) in Filter.atTop,
                                                              |r n (Fin.castSucc b) - r n (Fin.castSucc a)| ≤
                                                                C * eps n *
                                                                  DominantFiveBody.satelliteDistance
                                                                    (DominantFiveBody.satellitesRelative (x n))
                                                                    (Fin.castSucc a) (Fin.castSucc b) := @DominantFiveBody.normalized_complete_lower_triple_nested_scale_complete

-- Source binding: prop:nested-scale
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (0 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.succ a)
                                                      (Fin.succ b) /
                                                    DominantFiveBody.tripleHighDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              (↑b : ℕ) = (↑a : ℕ) + (1 : ℕ) ∧
                                                Filter.Tendsto
                                                    (fun (n : ℕ) =>
                                                      (mu n (Fin.succ a) + mu n (Fin.succ b)) /
                                                        (mu n (1 : DominantFiveBody.Satellite) +
                                                            mu n (2 : DominantFiveBody.Satellite) +
                                                          mu n (3 : DominantFiveBody.Satellite)))
                                                    Filter.atTop (𝓝 (0 : ℝ)) ∧
                                                  Filter.Tendsto
                                                      (fun (n : ℕ) =>
                                                        (mu n (1 : DominantFiveBody.Satellite) +
                                                              mu n (2 : DominantFiveBody.Satellite) +
                                                            mu n (3 : DominantFiveBody.Satellite)) /
                                                          DominantFiveBody.tripleHighDiameter
                                                              (DominantFiveBody.satellitesRelative (x n)) ^
                                                            (3 : ℕ))
                                                      Filter.atTop (𝓝 (9 / 4 : ℝ)) ∧
                                                    Filter.Tendsto
                                                        (fun (n : ℕ) =>
                                                          (mu n (Fin.succ a) + mu n (Fin.succ b)) /
                                                            DominantFiveBody.satelliteDistance
                                                                (DominantFiveBody.satellitesRelative (x n)) (Fin.succ a)
                                                                (Fin.succ b) ^
                                                              (3 : ℕ))
                                                        Filter.atTop (𝓝 (27 / 4 : ℝ)) ∧
                                                      Filter.Tendsto
                                                          (fun (n : ℕ) =>
                                                            (theta n (Fin.succ b) - theta n (Fin.succ a)) /
                                                              DominantFiveBody.satelliteDistance
                                                                (DominantFiveBody.satellitesRelative (x n)) (Fin.succ a)
                                                                (Fin.succ b))
                                                          Filter.atTop (𝓝 (1 : ℝ)) ∧
                                                        ∃ (C : ℝ),
                                                          (0 : ℝ) < C ∧
                                                            ∀ᶠ (n : ℕ) in Filter.atTop,
                                                              |r n (Fin.succ b) - r n (Fin.succ a)| ≤
                                                                C * eps n *
                                                                  DominantFiveBody.satelliteDistance
                                                                    (DominantFiveBody.satellitesRelative (x n))
                                                                    (Fin.succ a) (Fin.succ b) := @DominantFiveBody.normalized_complete_upper_triple_nested_scale_complete

-- Source binding: prose:477
example : ∀ (q : ℕ → DominantFiveBody.SatelliteConfiguration) (a b c : DominantFiveBody.Satellite) (d : ℕ → ℝ),
  (∀ (n : ℕ), (0 : ℝ) < d n) →
    (∀ (n : ℕ), d n = DominantFiveBody.tripleLargestDistance (q n) a b c) →
      Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satelliteDistance (q n) a b / d n) Filter.atTop (𝓝 (0 : ℝ)) →
        Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satelliteDistance (q n) a c / d n) Filter.atTop (𝓝 (1 : ℝ)) ∧
          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satelliteDistance (q n) b c / d n) Filter.atTop (𝓝 (1 : ℝ)) := @DominantFiveBody.nested_cross_distance_diameter_ratios

-- Source binding: prose:477
example : ∀ (eps : Nat → Real) (mu : Nat → DominantFiveBody.MassRatio) (x : Nat → DominantFiveBody.Configuration),
  (∀ (n : Nat), @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) (eps n)) →
    @Filter.Tendsto Nat Real eps (@Filter.atTop Nat Nat.instPreorder)
        (@nhds Real
          (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
          (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))) →
      (∀ (n : Nat), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : Nat), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : Nat), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : Nat → DominantFiveBody.Satellite → Real),
              (∀ (n : Nat) (i : DominantFiveBody.Satellite),
                  @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) (r n i)) →
                (∀ (n : Nat),
                    @Eq DominantFiveBody.SatelliteConfiguration (DominantFiveBody.satellitesRelative (x n))
                      (DominantFiveBody.polarSatellites (r n) (theta n))) →
                  (∀ (n : Nat),
                      @DominantFiveBody.OrderedSemicircle (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      @Filter.Tendsto Nat DominantFiveBody.MassRatio mu (@Filter.atTop Nat Nat.instPreorder)
                          (@nhds DominantFiveBody.MassRatio
                            (@Pi.topologicalSpace DominantFiveBody.Satellite
                              (fun (a : DominantFiveBody.Satellite) => Real) fun (i : DominantFiveBody.Satellite) =>
                              @UniformSpace.toTopologicalSpace Real
                                (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                            muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          @Filter.Tendsto Nat DominantFiveBody.SatelliteConfiguration
                              (fun (n : Nat) => DominantFiveBody.satellitesRelative (x n))
                              (@Filter.atTop Nat Nat.instPreorder)
                              (@nhds DominantFiveBody.SatelliteConfiguration
                                (@Pi.topologicalSpace DominantFiveBody.Satellite
                                  (fun (a : DominantFiveBody.Satellite) => DominantFiveBody.Plane)
                                  fun (i : DominantFiveBody.Satellite) =>
                                  @PiLp.topologicalSpace
                                    (@OfNat.ofNat ENNReal (nat_lit 2)
                                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                        (@AddMonoidWithOne.toNatCast ENNReal
                                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                            ENNReal.instAddCommMonoidWithOne))
                                        PiLp.innerProductSpace._proof_1))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (fun (x : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
                                    fun (i : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
                                    @UniformSpace.toTopologicalSpace Real
                                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                                qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → Real),
                              @Filter.Tendsto Nat (DominantFiveBody.Satellite → Real) theta
                                  (@Filter.atTop Nat Nat.instPreorder)
                                  (@nhds (DominantFiveBody.Satellite → Real)
                                    (@Pi.topologicalSpace DominantFiveBody.Satellite
                                      (fun (a : DominantFiveBody.Satellite) => Real)
                                      fun (i : DominantFiveBody.Satellite) =>
                                      @UniformSpace.toTopologicalSpace Real
                                        (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                                    theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (@OfNat.ofNat DominantFiveBody.Satellite (nat_lit 3)
                                        (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                          (nat_lit 3)))
                                      center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      @LT.lt DominantFiveBody.TripleLabel
                                          (@instLTFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) a b →
                                        @Ne DominantFiveBody.TripleLabel c a →
                                          @Ne DominantFiveBody.TripleLabel c b →
                                            @Filter.Tendsto Nat Real
                                                (fun (n : Nat) =>
                                                  @HDiv.hDiv Real Real Real
                                                    (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                                    (DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n))
                                                      (@Fin.castSucc
                                                        (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) a)
                                                      (@Fin.castSucc
                                                        (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b))
                                                    (DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n))))
                                                (@Filter.atTop Nat Nat.instPreorder)
                                                (@nhds Real
                                                  (@UniformSpace.toTopologicalSpace Real
                                                    (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                                                  (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))) →
                                              And
                                                (Or
                                                  (And
                                                    (@Eq DominantFiveBody.TripleLabel a
                                                      (@OfNat.ofNat DominantFiveBody.TripleLabel (nat_lit 0)
                                                        (@Fin.instOfNat
                                                          (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                          (@Nat.instNeZeroSucc
                                                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                          (nat_lit 0))))
                                                    (And
                                                      (@Eq DominantFiveBody.TripleLabel b
                                                        (@OfNat.ofNat DominantFiveBody.TripleLabel (nat_lit 1)
                                                          (@Fin.instOfNat
                                                            (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                            (@Nat.instNeZeroSucc
                                                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                            (nat_lit 1))))
                                                      (@Eq DominantFiveBody.TripleLabel c
                                                        (@OfNat.ofNat DominantFiveBody.TripleLabel (nat_lit 2)
                                                          (@Fin.instOfNat
                                                            (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                            (@Nat.instNeZeroSucc
                                                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                            (nat_lit 2))))))
                                                  (And
                                                    (@Eq DominantFiveBody.TripleLabel a
                                                      (@OfNat.ofNat DominantFiveBody.TripleLabel (nat_lit 1)
                                                        (@Fin.instOfNat
                                                          (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                          (@Nat.instNeZeroSucc
                                                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                          (nat_lit 1))))
                                                    (And
                                                      (@Eq DominantFiveBody.TripleLabel b
                                                        (@OfNat.ofNat DominantFiveBody.TripleLabel (nat_lit 2)
                                                          (@Fin.instOfNat
                                                            (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                            (@Nat.instNeZeroSucc
                                                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                            (nat_lit 2))))
                                                      (@Eq DominantFiveBody.TripleLabel c
                                                        (@OfNat.ofNat DominantFiveBody.TripleLabel (nat_lit 0)
                                                          (@Fin.instOfNat
                                                            (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                            (@Nat.instNeZeroSucc
                                                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                            (nat_lit 0)))))))
                                                (And
                                                  (@Filter.Tendsto Nat Real
                                                    (fun (n : Nat) =>
                                                      @HDiv.hDiv Real Real Real
                                                        (@instHDiv Real
                                                          (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                                        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                                          (theta n
                                                            (@Fin.castSucc
                                                              (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                              b))
                                                          (theta n
                                                            (@Fin.castSucc
                                                              (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                              a)))
                                                        (DominantFiveBody.tripleLowDiameter
                                                          (DominantFiveBody.satellitesRelative (x n))))
                                                    (@Filter.atTop Nat Nat.instPreorder)
                                                    (@nhds Real
                                                      (@UniformSpace.toTopologicalSpace Real
                                                        (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                                                      (@OfNat.ofNat Real (nat_lit 0)
                                                        (@Zero.toOfNat0 Real Real.instZero))))
                                                  (And
                                                    (∀ (i : DominantFiveBody.TripleLabel),
                                                      @Membership.mem DominantFiveBody.TripleLabel
                                                          (Finset DominantFiveBody.TripleLabel)
                                                          (@SetLike.instMembership (Finset DominantFiveBody.TripleLabel)
                                                            DominantFiveBody.TripleLabel
                                                            (@Finset.instSetLike DominantFiveBody.TripleLabel))
                                                          (@Insert.insert DominantFiveBody.TripleLabel
                                                            (Finset DominantFiveBody.TripleLabel)
                                                            (@Finset.instInsert DominantFiveBody.TripleLabel
                                                              (instDecidableEqFin
                                                                (@OfNat.ofNat Nat (nat_lit 3)
                                                                  (instOfNatNat (nat_lit 3)))))
                                                            a
                                                            (@Singleton.singleton DominantFiveBody.TripleLabel
                                                              (Finset DominantFiveBody.TripleLabel)
                                                              (@Finset.instSingleton DominantFiveBody.TripleLabel) b))
                                                          i →
                                                        @Filter.Tendsto Nat Real
                                                          (fun (n : Nat) =>
                                                            @HDiv.hDiv Real Real Real
                                                              (@instHDiv Real
                                                                (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                                              (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                                                (theta n
                                                                  (@Fin.castSucc
                                                                    (@OfNat.ofNat Nat (nat_lit 3)
                                                                      (instOfNatNat (nat_lit 3)))
                                                                    c))
                                                                (theta n
                                                                  (@Fin.castSucc
                                                                    (@OfNat.ofNat Nat (nat_lit 3)
                                                                      (instOfNatNat (nat_lit 3)))
                                                                    i)))
                                                              (DominantFiveBody.tripleLowDiameter
                                                                (DominantFiveBody.satellitesRelative (x n))))
                                                          (@Filter.atTop Nat Nat.instPreorder)
                                                          (@nhds Real
                                                            (@UniformSpace.toTopologicalSpace Real
                                                              (@PseudoMetricSpace.toUniformSpace Real
                                                                Real.pseudoMetricSpace))
                                                            (DominantFiveBody.lowNestedOrientation a c)))
                                                    (And
                                                      (∀ (i : DominantFiveBody.TripleLabel),
                                                        @Membership.mem DominantFiveBody.TripleLabel
                                                            (Finset DominantFiveBody.TripleLabel)
                                                            (@SetLike.instMembership
                                                              (Finset DominantFiveBody.TripleLabel)
                                                              DominantFiveBody.TripleLabel
                                                              (@Finset.instSetLike DominantFiveBody.TripleLabel))
                                                            (@Insert.insert DominantFiveBody.TripleLabel
                                                              (Finset DominantFiveBody.TripleLabel)
                                                              (@Finset.instInsert DominantFiveBody.TripleLabel
                                                                (instDecidableEqFin
                                                                  (@OfNat.ofNat Nat (nat_lit 3)
                                                                    (instOfNatNat (nat_lit 3)))))
                                                              a
                                                              (@Singleton.singleton DominantFiveBody.TripleLabel
                                                                (Finset DominantFiveBody.TripleLabel)
                                                                (@Finset.instSingleton DominantFiveBody.TripleLabel) b))
                                                            i →
                                                          @Filter.Tendsto Nat DominantFiveBody.Plane
                                                            (fun (n : Nat) =>
                                                              @HSMul.hSMul Real DominantFiveBody.Plane
                                                                DominantFiveBody.Plane
                                                                (@instHSMul Real DominantFiveBody.Plane
                                                                  (@WithLp.instSMul
                                                                    (@OfNat.ofNat ENNReal (nat_lit 2)
                                                                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                                                        (@AddMonoidWithOne.toNatCast ENNReal
                                                                          (@AddCommMonoidWithOne.toAddMonoidWithOne
                                                                            ENNReal ENNReal.instAddCommMonoidWithOne))
                                                                        PiLp.innerProductSpace._proof_1))
                                                                    Real
                                                                    ((i :
                                                                        Fin
                                                                          (@OfNat.ofNat Nat (nat_lit 2)
                                                                            (instOfNatNat (nat_lit 2)))) →
                                                                      (fun
                                                                            (x :
                                                                              Fin
                                                                                (@OfNat.ofNat Nat (nat_lit 2)
                                                                                  (instOfNatNat (nat_lit 2)))) =>
                                                                          Real)
                                                                        i)
                                                                    (@Function.hasSMul
                                                                      (Fin
                                                                        (@OfNat.ofNat Nat (nat_lit 2)
                                                                          (instOfNatNat (nat_lit 2))))
                                                                      Real Real (@instSMulOfMul Real Real.instMul))))
                                                                (@Inv.inv Real Real.instInv
                                                                  (DominantFiveBody.tripleLowDiameter
                                                                    (DominantFiveBody.satellitesRelative (x n))))
                                                                (@HSub.hSub DominantFiveBody.Plane
                                                                  DominantFiveBody.Plane DominantFiveBody.Plane
                                                                  (@instHSub DominantFiveBody.Plane
                                                                    (@SubNegMonoid.toSub DominantFiveBody.Plane
                                                                      (@AddGroup.toSubNegMonoid DominantFiveBody.Plane
                                                                        (@AddCommGroup.toAddGroup DominantFiveBody.Plane
                                                                          (@WithLp.instAddCommGroup
                                                                            (@OfNat.ofNat ENNReal (nat_lit 2)
                                                                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                                                                (@AddMonoidWithOne.toNatCast ENNReal
                                                                                  (@AddCommMonoidWithOne.toAddMonoidWithOne
                                                                                    ENNReal
                                                                                    ENNReal.instAddCommMonoidWithOne))
                                                                                PiLp.innerProductSpace._proof_1))
                                                                            ((i :
                                                                                Fin
                                                                                  (@OfNat.ofNat Nat (nat_lit 2)
                                                                                    (instOfNatNat (nat_lit 2)))) →
                                                                              (fun
                                                                                    (x :
                                                                                      Fin
                                                                                        (@OfNat.ofNat Nat (nat_lit 2)
                                                                                          (instOfNatNat
                                                                                            (nat_lit 2)))) =>
                                                                                  Real)
                                                                                i)
                                                                            (@Pi.addCommGroup
                                                                              (Fin
                                                                                (@OfNat.ofNat Nat (nat_lit 2)
                                                                                  (instOfNatNat (nat_lit 2))))
                                                                              (fun
                                                                                  (x :
                                                                                    Fin
                                                                                      (@OfNat.ofNat Nat (nat_lit 2)
                                                                                        (instOfNatNat (nat_lit 2)))) =>
                                                                                Real)
                                                                              fun
                                                                                (i :
                                                                                  Fin
                                                                                    (@OfNat.ofNat Nat (nat_lit 2)
                                                                                      (instOfNatNat (nat_lit 2)))) =>
                                                                              Real.instAddCommGroup))))))
                                                                  (DominantFiveBody.satellitesRelative (x n)
                                                                    (@Fin.castSucc
                                                                      (@OfNat.ofNat Nat (nat_lit 3)
                                                                        (instOfNatNat (nat_lit 3)))
                                                                      c))
                                                                  (DominantFiveBody.satellitesRelative (x n)
                                                                    (@Fin.castSucc
                                                                      (@OfNat.ofNat Nat (nat_lit 3)
                                                                        (instOfNatNat (nat_lit 3)))
                                                                      i))))
                                                            (@Filter.atTop Nat Nat.instPreorder)
                                                            (@nhds DominantFiveBody.Plane
                                                              (@PiLp.topologicalSpace
                                                                (@OfNat.ofNat ENNReal (nat_lit 2)
                                                                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                                                    (@AddMonoidWithOne.toNatCast ENNReal
                                                                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                                                        ENNReal.instAddCommMonoidWithOne))
                                                                    PiLp.innerProductSpace._proof_1))
                                                                (Fin
                                                                  (@OfNat.ofNat Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2))))
                                                                (fun
                                                                    (x :
                                                                      Fin
                                                                        (@OfNat.ofNat Nat (nat_lit 2)
                                                                          (instOfNatNat (nat_lit 2)))) =>
                                                                  Real)
                                                                fun
                                                                  (i :
                                                                    Fin
                                                                      (@OfNat.ofNat Nat (nat_lit 2)
                                                                        (instOfNatNat (nat_lit 2)))) =>
                                                                @UniformSpace.toTopologicalSpace Real
                                                                  (@PseudoMetricSpace.toUniformSpace Real
                                                                    Real.pseudoMetricSpace))
                                                              (@HSMul.hSMul Real DominantFiveBody.Plane
                                                                DominantFiveBody.Plane
                                                                (@instHSMul Real DominantFiveBody.Plane
                                                                  (@WithLp.instSMul
                                                                    (@OfNat.ofNat ENNReal (nat_lit 2)
                                                                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                                                        (@AddMonoidWithOne.toNatCast ENNReal
                                                                          (@AddCommMonoidWithOne.toAddMonoidWithOne
                                                                            ENNReal ENNReal.instAddCommMonoidWithOne))
                                                                        PiLp.innerProductSpace._proof_1))
                                                                    Real
                                                                    ((i :
                                                                        Fin
                                                                          (@OfNat.ofNat Nat (nat_lit 2)
                                                                            (instOfNatNat (nat_lit 2)))) →
                                                                      (fun
                                                                            (x :
                                                                              Fin
                                                                                (@OfNat.ofNat Nat (nat_lit 2)
                                                                                  (instOfNatNat (nat_lit 2)))) =>
                                                                          Real)
                                                                        i)
                                                                    (@Function.hasSMul
                                                                      (Fin
                                                                        (@OfNat.ofNat Nat (nat_lit 2)
                                                                          (instOfNatNat (nat_lit 2))))
                                                                      Real Real (@instSMulOfMul Real Real.instMul))))
                                                                (DominantFiveBody.lowNestedOrientation a c)
                                                                (DominantFiveBody.quarterTurn
                                                                  (DominantFiveBody.polarPoint
                                                                    (@OfNat.ofNat Real (nat_lit 1)
                                                                      (@One.toOfNat1 Real Real.instOne))
                                                                    (theta0
                                                                      (@OfNat.ofNat DominantFiveBody.Satellite
                                                                        (nat_lit 0)
                                                                        (@Fin.instOfNat
                                                                          (@OfNat.ofNat Nat (nat_lit 4)
                                                                            (instOfNatNat (nat_lit 4)))
                                                                          (@Nat.instNeZeroSucc
                                                                            (@OfNat.ofNat Nat (nat_lit 3)
                                                                              (instOfNatNat (nat_lit 3))))
                                                                          (nat_lit 0)))))))))
                                                      (∀ (i : DominantFiveBody.TripleLabel),
                                                        @Membership.mem DominantFiveBody.TripleLabel
                                                            (Finset DominantFiveBody.TripleLabel)
                                                            (@SetLike.instMembership
                                                              (Finset DominantFiveBody.TripleLabel)
                                                              DominantFiveBody.TripleLabel
                                                              (@Finset.instSetLike DominantFiveBody.TripleLabel))
                                                            (@Insert.insert DominantFiveBody.TripleLabel
                                                              (Finset DominantFiveBody.TripleLabel)
                                                              (@Finset.instInsert DominantFiveBody.TripleLabel
                                                                (instDecidableEqFin
                                                                  (@OfNat.ofNat Nat (nat_lit 3)
                                                                    (instOfNatNat (nat_lit 3)))))
                                                              a
                                                              (@Singleton.singleton DominantFiveBody.TripleLabel
                                                                (Finset DominantFiveBody.TripleLabel)
                                                                (@Finset.instSingleton DominantFiveBody.TripleLabel) b))
                                                            i →
                                                          @Filter.Tendsto Nat Real
                                                            (fun (n : Nat) =>
                                                              @HDiv.hDiv Real Real Real
                                                                (@instHDiv Real
                                                                  (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                                                (DominantFiveBody.satelliteDistance
                                                                  (DominantFiveBody.satellitesRelative (x n))
                                                                  (@Fin.castSucc
                                                                    (@OfNat.ofNat Nat (nat_lit 3)
                                                                      (instOfNatNat (nat_lit 3)))
                                                                    i)
                                                                  (@Fin.castSucc
                                                                    (@OfNat.ofNat Nat (nat_lit 3)
                                                                      (instOfNatNat (nat_lit 3)))
                                                                    c))
                                                                (DominantFiveBody.tripleLowDiameter
                                                                  (DominantFiveBody.satellitesRelative (x n))))
                                                            (@Filter.atTop Nat Nat.instPreorder)
                                                            (@nhds Real
                                                              (@UniformSpace.toTopologicalSpace Real
                                                                (@PseudoMetricSpace.toUniformSpace Real
                                                                  Real.pseudoMetricSpace))
                                                              (@OfNat.ofNat Real (nat_lit 1)
                                                                (@One.toOfNat1 Real Real.instOne))))))) := @DominantFiveBody.normalized_complete_lower_triple_nested_directions

-- Source binding: prose:477
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ),
              DominantFiveBody.StrictConvexInOrder { labels := Equiv.refl DominantFiveBody.Label, primary_first := rfl }
                (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                      i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a ≠ b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                      (Fin.castSucc b) /
                                                    DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∀ (i j : DominantFiveBody.TripleLabel),
                                                Filter.Tendsto
                                                  (fun (n : ℕ) =>
                                                    (r n (Fin.castSucc j) - r n (Fin.castSucc i)) /
                                                      DominantFiveBody.tripleLowDiameter
                                                        (DominantFiveBody.satellitesRelative (x n)))
                                                  Filter.atTop (𝓝 (0 : ℝ)) := @DominantFiveBody.normalized_complete_lower_triple_nested_radial_limits

-- Source binding: prose:477
example : ∀ (qa qb qc : ℕ → DominantFiveBody.Plane) (d : ℕ → ℝ) (u : DominantFiveBody.Plane),
  (∀ (n : ℕ), (0 : ℝ) < d n) →
    Filter.Tendsto (fun (n : ℕ) => (d n)⁻¹ • (qc n - qa n)) Filter.atTop (𝓝 u) →
      Filter.Tendsto (fun (n : ℕ) => ‖qb n - qa n‖ / d n) Filter.atTop (𝓝 (0 : ℝ)) →
        ∀ (eta : ℝ),
          (0 : ℝ) < eta →
            ∀ᶠ (n : ℕ) in Filter.atTop,
              ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ),
                ‖(d n)⁻¹ • (qc n - DominantFiveBody.physicalPairSegmentPoint (qa n) (qb n) t) - u‖ < eta := @DominantFiveBody.physical_pair_segment_scaled_displacement_uniform

-- Source binding: prose:477
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                      (Fin.castSucc b) /
                                                    DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∀ (eta : ℝ),
                                                (0 : ℝ) < eta →
                                                  ∀ᶠ (n : ℕ) in Filter.atTop,
                                                    ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ),
                                                      ‖(DominantFiveBody.tripleLowDiameter
                                                                  (DominantFiveBody.satellitesRelative (x n)))⁻¹ •
                                                              (DominantFiveBody.satellitesRelative (x n)
                                                                  (Fin.castSucc c) -
                                                                DominantFiveBody.physicalPairSegmentPoint
                                                                  (DominantFiveBody.satellitesRelative (x n)
                                                                    (Fin.castSucc a))
                                                                  (DominantFiveBody.satellitesRelative (x n)
                                                                    (Fin.castSucc b))
                                                                  t) -
                                                            DominantFiveBody.lowNestedOrientation a c •
                                                              DominantFiveBody.quarterTurn
                                                                (DominantFiveBody.polarPoint (1 : ℝ)
                                                                  (theta0 (0 : DominantFiveBody.Satellite)))‖ <
                                                        eta := @DominantFiveBody.normalized_complete_lower_triple_nested_segment_scaled_geometry_uniform

-- Source binding: prose:477
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (0 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.succ a)
                                                      (Fin.succ b) /
                                                    DominantFiveBody.tripleHighDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∀ (eta : ℝ),
                                                (0 : ℝ) < eta →
                                                  ∀ᶠ (n : ℕ) in Filter.atTop,
                                                    ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ),
                                                      ‖(DominantFiveBody.tripleHighDiameter
                                                                  (DominantFiveBody.satellitesRelative (x n)))⁻¹ •
                                                              (DominantFiveBody.satellitesRelative (x n) (Fin.succ c) -
                                                                DominantFiveBody.physicalPairSegmentPoint
                                                                  (DominantFiveBody.satellitesRelative (x n)
                                                                    (Fin.succ a))
                                                                  (DominantFiveBody.satellitesRelative (x n)
                                                                    (Fin.succ b))
                                                                  t) -
                                                            DominantFiveBody.lowNestedOrientation a c •
                                                              DominantFiveBody.quarterTurn
                                                                (DominantFiveBody.polarPoint (1 : ℝ)
                                                                  (theta0 (3 : DominantFiveBody.Satellite)))‖ <
                                                        eta := @DominantFiveBody.normalized_complete_upper_triple_nested_segment_scaled_geometry_uniform

-- Source binding: prose:477
example : ∀ (qa qb qc : ℕ → DominantFiveBody.Plane) (d : ℕ → ℝ) (u : DominantFiveBody.Plane),
  (∀ (n : ℕ), (0 : ℝ) < d n) →
    ‖u‖ = (1 : ℝ) →
      Filter.Tendsto (fun (n : ℕ) => (d n)⁻¹ • (qc n - qa n)) Filter.atTop (𝓝 u) →
        Filter.Tendsto (fun (n : ℕ) => ‖qb n - qa n‖ / d n) Filter.atTop (𝓝 (0 : ℝ)) →
          ∀ (eta : ℝ),
            (0 : ℝ) < eta →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ),
                  |‖qc n - DominantFiveBody.physicalPairSegmentPoint (qa n) (qb n) t‖ / d n - (1 : ℝ)| < eta := @DominantFiveBody.physical_pair_segment_near_distance_uniform

-- Source binding: prose:477
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                      (Fin.castSucc b) /
                                                    DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∀ (eta : ℝ),
                                                (0 : ℝ) < eta →
                                                  ∀ᶠ (n : ℕ) in Filter.atTop,
                                                    ∀ rho ∈ Set.uIcc (r n (Fin.castSucc a)) (r n (Fin.castSucc b)),
                                                      ∀
                                                        v ∈
                                                          Set.uIcc (theta n (Fin.castSucc a))
                                                            (theta n (Fin.castSucc b)),
                                                        |(theta n (Fin.castSucc c) - v) /
                                                                  DominantFiveBody.tripleLowDiameter
                                                                    (DominantFiveBody.satellitesRelative (x n)) -
                                                                DominantFiveBody.lowNestedOrientation a c| <
                                                            eta ∧
                                                          |(rho - r n (Fin.castSucc c)) /
                                                                  DominantFiveBody.tripleLowDiameter
                                                                    (DominantFiveBody.satellitesRelative (x n))| <
                                                              eta ∧
                                                            |‖DominantFiveBody.polarPoint rho v -
                                                                        DominantFiveBody.polarPoint
                                                                          (r n (Fin.castSucc c))
                                                                          (theta n (Fin.castSucc c))‖ /
                                                                    DominantFiveBody.tripleLowDiameter
                                                                      (DominantFiveBody.satellitesRelative (x n)) -
                                                                  (1 : ℝ)| <
                                                              eta := @DominantFiveBody.normalized_complete_lower_triple_nested_rectangle_near_geometry_uniform

-- Source binding: prose:477
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (0 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.succ a)
                                                      (Fin.succ b) /
                                                    DominantFiveBody.tripleHighDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∀ (eta : ℝ),
                                                (0 : ℝ) < eta →
                                                  ∀ᶠ (n : ℕ) in Filter.atTop,
                                                    ∀ rho ∈ Set.uIcc (r n (Fin.succ a)) (r n (Fin.succ b)),
                                                      ∀ v ∈ Set.uIcc (theta n (Fin.succ a)) (theta n (Fin.succ b)),
                                                        |(theta n (Fin.succ c) - v) /
                                                                  DominantFiveBody.tripleHighDiameter
                                                                    (DominantFiveBody.satellitesRelative (x n)) -
                                                                DominantFiveBody.lowNestedOrientation a c| <
                                                            eta ∧
                                                          |(rho - r n (Fin.succ c)) /
                                                                  DominantFiveBody.tripleHighDiameter
                                                                    (DominantFiveBody.satellitesRelative (x n))| <
                                                              eta ∧
                                                            |‖DominantFiveBody.polarPoint rho v -
                                                                        DominantFiveBody.polarPoint (r n (Fin.succ c))
                                                                          (theta n (Fin.succ c))‖ /
                                                                    DominantFiveBody.tripleHighDiameter
                                                                      (DominantFiveBody.satellitesRelative (x n)) -
                                                                  (1 : ℝ)| <
                                                              eta := @DominantFiveBody.normalized_complete_upper_triple_nested_rectangle_near_geometry_uniform

-- Source binding: prose:482
example : ∀ (source target : DominantFiveBody.Plane),
  source ≠ target → ‖DominantFiveBody.newtonTargetDerivative source target‖ ≤ (4 : ℝ) / ‖source - target‖ ^ (3 : ℕ) := @DominantFiveBody.newtonTargetDerivative_operator_norm_bound

-- Source binding: prose:482
example : ∀ (mu : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration) (a b : DominantFiveBody.Satellite)
  (y : DominantFiveBody.Plane),
  (∀ j ∈ DominantFiveBody.pairExteriorLabels a b, q j ≠ y) →
    HasFDerivAt (DominantFiveBody.pairExteriorField mu q a b)
      (∑ j ∈ DominantFiveBody.pairExteriorLabels a b, mu j • DominantFiveBody.newtonTargetDerivative (q j) y) y := @DominantFiveBody.pairExteriorField_hasFDerivAt

-- Source binding: prose:482
example : ∀ (mu : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration) (a b : DominantFiveBody.Satellite)
  (y : DominantFiveBody.Plane),
  (∀ j ∈ DominantFiveBody.pairExteriorLabels a b, (0 : ℝ) ≤ mu j) →
    (∀ j ∈ DominantFiveBody.pairExteriorLabels a b, q j ≠ y) →
      ‖fderiv ℝ (DominantFiveBody.pairExteriorField mu q a b) y‖ ≤
        ∑ j ∈ DominantFiveBody.pairExteriorLabels a b, mu j * ((4 : ℝ) / ‖q j - y‖ ^ (3 : ℕ)) := @DominantFiveBody.pairExteriorField_fderiv_norm_bound

-- Source binding: prose:482
example : ∀ (mu : DominantFiveBody.MassRatio),
  DominantFiveBody.PositiveRatio mu →
    ∀ (q : DominantFiveBody.SatelliteConfiguration) (a b c p : DominantFiveBody.Satellite),
      a ≠ b →
        c ≠ p →
          c ∈ DominantFiveBody.pairExteriorLabels a b →
            p ∈ DominantFiveBody.pairExteriorLabels a b →
              ∀ (y : DominantFiveBody.Plane) (d C : ℝ),
                (0 : ℝ) < d →
                  (0 : ℝ) < C →
                    d / (2 : ℝ) ≤ ‖q c - y‖ →
                      (1 / 2 : ℝ) ≤ ‖q p - y‖ →
                        mu c / d ^ (3 : ℕ) ≤ C →
                          ‖fderiv ℝ (DominantFiveBody.pairExteriorField mu q a b) y‖ ≤ (32 : ℝ) * (C + (1 : ℝ)) := @DominantFiveBody.pairExteriorField_fderiv_norm_bound_two_sources

-- Source binding: prose:482
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                      (Fin.castSucc b) /
                                                    DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∀ᶠ (n : ℕ) in Filter.atTop,
                                                ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ),
                                                  ‖fderiv ℝ
                                                        (DominantFiveBody.pairExteriorField (mu n)
                                                          (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                          (Fin.castSucc b))
                                                        (DominantFiveBody.physicalPairSegmentPoint
                                                          (DominantFiveBody.satellitesRelative (x n) (Fin.castSucc a))
                                                          (DominantFiveBody.satellitesRelative (x n) (Fin.castSucc b))
                                                          t)‖ ≤
                                                    (128 : ℝ) := @DominantFiveBody.normalized_complete_lower_triple_nested_segment_derivative_bound

-- Source binding: prose:482
example : ∀ (mu : ℕ → DominantFiveBody.MassRatio) (d : ℕ → ℝ) (q : ℕ → DominantFiveBody.SatelliteConfiguration)
  (a b c p : DominantFiveBody.Satellite),
  a ≠ b →
    c ≠ p →
      c ∈ DominantFiveBody.pairExteriorLabels a b →
        p ∈ DominantFiveBody.pairExteriorLabels a b →
          (∀ (n : ℕ), DominantFiveBody.RelativeCollisionFree (q n)) →
            (∀ (n : ℕ), (0 : ℝ) < d n) →
              ∀ (U v e z : DominantFiveBody.Plane),
                ‖U‖ = (1 : ℝ) →
                  ∀ (L M : ℝ),
                    z ≠ e →
                      Filter.Tendsto (fun (n : ℕ) => (d n)⁻¹ • (q n c - q n a)) Filter.atTop (𝓝 U) →
                        Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satelliteDistance (q n) a b / d n) Filter.atTop
                            (𝓝 (0 : ℝ)) →
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.physicalPairDirection (q n) a b) Filter.atTop
                              (𝓝 v) →
                            Filter.Tendsto (fun (n : ℕ) => mu n c / d n ^ (3 : ℕ)) Filter.atTop (𝓝 L) →
                              Filter.Tendsto (fun (n : ℕ) => mu n p) Filter.atTop (𝓝 M) →
                                Filter.Tendsto (fun (n : ℕ) => q n a) Filter.atTop (𝓝 e) →
                                  Filter.Tendsto (fun (n : ℕ) => q n b) Filter.atTop (𝓝 e) →
                                    Filter.Tendsto (fun (n : ℕ) => q n p) Filter.atTop (𝓝 z) →
                                      Filter.Tendsto
                                        (fun (n : ℕ) =>
                                          DominantFiveBody.pairSecantExteriorField (mu n) (q n) a b
                                            (DominantFiveBody.physicalPairDirection (q n) a b))
                                        Filter.atTop
                                        (𝓝
                                          (L •
                                              DominantFiveBody.dividedNewtonTargetField U (0 : DominantFiveBody.Plane)
                                                (0 : DominantFiveBody.Plane) v +
                                            M • DominantFiveBody.dividedNewtonTargetField z e e v)) := @DominantFiveBody.physical_nested_pair_exterior_secant_limit

-- Source binding: eq:nested-field
example : ∀ (mu r theta : DominantFiveBody.Satellite → ℝ) (a b c p : DominantFiveBody.Satellite),
  a ≠ b →
    c ≠ p →
      c ∈ DominantFiveBody.pairExteriorLabels a b →
        p ∈ DominantFiveBody.pairExteriorLabels a b →
          ∀ (rho v : ℝ),
            DominantFiveBody.physicalPairExteriorAngularRadialDerivative mu r theta a b rho v =
              mu c * DominantFiveBody.physicalSourceAngularRadialDerivative (r c) (theta c) rho v +
                mu p * DominantFiveBody.physicalSourceAngularRadialDerivative (r p) (theta p) rho v := @DominantFiveBody.physicalPairExteriorAngularRadialDerivative_eq_selected

-- Source binding: eq:nested-field
example : ∀ (mu r theta : DominantFiveBody.Satellite → ℝ) (a b c p : DominantFiveBody.Satellite),
  a ≠ b →
    c ≠ p →
      c ∈ DominantFiveBody.pairExteriorLabels a b →
        p ∈ DominantFiveBody.pairExteriorLabels a b →
          ∀ (rho v : ℝ),
            DominantFiveBody.physicalPairExteriorAngularAngularDerivative mu r theta a b rho v =
              mu c * DominantFiveBody.physicalSourceAngularAngularDerivative (r c) (theta c) rho v +
                mu p * DominantFiveBody.physicalSourceAngularAngularDerivative (r p) (theta p) rho v := @DominantFiveBody.physicalPairExteriorAngularAngularDerivative_eq_selected

-- Source binding: prop:nested-scale.actual_current_weight_group_radial
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (q : ℕ → DominantFiveBody.SatelliteConfiguration),
  Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
    (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
      (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
          DominantFiveBody.vectorResidual (eps n) (mu n) (q n) i = (0 : DominantFiveBody.Plane)) →
        (∀ (n : ℕ), DominantFiveBody.RelativeCollisionFree (q n)) →
          ∀ (mu0 : DominantFiveBody.MassRatio),
            Filter.Tendsto mu Filter.atTop (𝓝 mu0) →
              ∀ (a b c p : DominantFiveBody.Satellite),
                a ≠ b →
                  c ≠ p →
                    c ∈ DominantFiveBody.pairExteriorLabels a b →
                      p ∈ DominantFiveBody.pairExteriorLabels a b →
                        ∀ (c0 p0 : DominantFiveBody.Plane),
                          ‖c0‖ = (1 : ℝ) →
                            p0 ≠ c0 →
                              Filter.Tendsto (fun (n : ℕ) => q n a) Filter.atTop (𝓝 c0) →
                                Filter.Tendsto (fun (n : ℕ) => q n b) Filter.atTop (𝓝 c0) →
                                  Filter.Tendsto (fun (n : ℕ) => q n c) Filter.atTop (𝓝 c0) →
                                    Filter.Tendsto (fun (n : ℕ) => q n p) Filter.atTop (𝓝 p0) →
                                      ∀ (d : ℕ → ℝ),
                                        (∀ (n : ℕ), (0 : ℝ) < d n) →
                                          (∀ (n : ℕ), d n = DominantFiveBody.tripleLargestDistance (q n) a b c) →
                                            Filter.Tendsto
                                                (fun (n : ℕ) => DominantFiveBody.satelliteDistance (q n) a b / d n)
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∀ (C : ℝ),
                                                (∀ᶠ (n : ℕ) in Filter.atTop,
                                                    (mu n a + mu n b + mu n c) / d n ^ (3 : ℕ) ≤ C) →
                                                  Filter.Tendsto
                                                      (fun (n : ℕ) => Inner.inner ℝ ((d n)⁻¹ • (q n a - q n c)) c0)
                                                      Filter.atTop (𝓝 (0 : ℝ)) ∧
                                                    Filter.Tendsto
                                                      (fun (n : ℕ) => Inner.inner ℝ ((d n)⁻¹ • (q n b - q n c)) c0)
                                                      Filter.atTop (𝓝 (0 : ℝ)) := @DominantFiveBody.physical_nested_group_radial_projections_tendsto

-- Source binding: prose:487
example : ∀ (massC massP rc vc rp vp ra va rb vb d : Nat → Real) (psi angle0 omega L M : Real),
  @Filter.Tendsto Nat Real rc (@Filter.atTop Nat Nat.instPreorder)
      (@nhds Real
        (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
        (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) →
    @Filter.Tendsto Nat Real rp (@Filter.atTop Nat Nat.instPreorder)
        (@nhds Real
          (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) →
      @Filter.Tendsto Nat Real ra (@Filter.atTop Nat Nat.instPreorder)
          (@nhds Real
            (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) →
        @Filter.Tendsto Nat Real rb (@Filter.atTop Nat Nat.instPreorder)
            (@nhds Real
              (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
              (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) →
          @Filter.Tendsto Nat Real vc (@Filter.atTop Nat Nat.instPreorder)
              (@nhds Real
                (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                psi) →
            @Filter.Tendsto Nat Real vp (@Filter.atTop Nat Nat.instPreorder)
                (@nhds Real
                  (@UniformSpace.toTopologicalSpace Real
                    (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                  angle0) →
              @Filter.Tendsto Nat Real va (@Filter.atTop Nat Nat.instPreorder)
                  (@nhds Real
                    (@UniformSpace.toTopologicalSpace Real
                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                    psi) →
                @Filter.Tendsto Nat Real vb (@Filter.atTop Nat Nat.instPreorder)
                    (@nhds Real
                      (@UniformSpace.toTopologicalSpace Real
                        (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                      psi) →
                  (∀ (n : Nat),
                      @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                        (d n)) →
                    @Filter.Tendsto Nat Real d (@Filter.atTop Nat Nat.instPreorder)
                        (@nhds Real
                          (@UniformSpace.toTopologicalSpace Real
                            (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                          (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))) →
                      @Eq Real
                          (@HPow.hPow Real Nat Real
                            (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) omega
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) →
                        @Filter.Tendsto Nat Real
                            (fun (n : Nat) =>
                              @HDiv.hDiv Real Real Real
                                (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (rb n) (ra n)) (d n))
                            (@Filter.atTop Nat Nat.instPreorder)
                            (@nhds Real
                              (@UniformSpace.toTopologicalSpace Real
                                (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                              (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))) →
                          @Filter.Tendsto Nat Real
                              (fun (n : Nat) =>
                                @HDiv.hDiv Real Real Real
                                  (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (vb n) (va n)) (d n))
                              (@Filter.atTop Nat Nat.instPreorder)
                              (@nhds Real
                                (@UniformSpace.toTopologicalSpace Real
                                  (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                                (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))) →
                            @Filter.Tendsto Nat Real
                                (fun (n : Nat) =>
                                  @HDiv.hDiv Real Real Real
                                    (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (rc n) (ra n)) (d n))
                                (@Filter.atTop Nat Nat.instPreorder)
                                (@nhds Real
                                  (@UniformSpace.toTopologicalSpace Real
                                    (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                                  (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))) →
                              @Filter.Tendsto Nat Real
                                  (fun (n : Nat) =>
                                    @HDiv.hDiv Real Real Real
                                      (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (vc n) (va n)) (d n))
                                  (@Filter.atTop Nat Nat.instPreorder)
                                  (@nhds Real
                                    (@UniformSpace.toTopologicalSpace Real
                                      (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                                    omega) →
                                @Filter.Tendsto Nat Real
                                    (fun (n : Nat) =>
                                      @HDiv.hDiv Real Real Real
                                        (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (massC n)
                                        (@HPow.hPow Real Nat Real
                                          (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
                                          (d n) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    (@Filter.atTop Nat Nat.instPreorder)
                                    (@nhds Real
                                      (@UniformSpace.toTopologicalSpace Real
                                        (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                                      L) →
                                  @Filter.Tendsto Nat Real massP (@Filter.atTop Nat Nat.instPreorder)
                                      (@nhds Real
                                        (@UniformSpace.toTopologicalSpace Real
                                          (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                                        M) →
                                    @Ne Real angle0 psi →
                                      @LT.lt Real Real.instLT
                                          (@abs Real Real.lattice Real.instAddGroup
                                            (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) angle0 psi))
                                          Real.pi →
                                        ∀ (eta : Real),
                                          @LT.lt Real Real.instLT
                                              (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) eta →
                                            @Filter.Eventually Nat
                                              (fun (n : Nat) =>
                                                ∀ (rho : Real),
                                                  @Membership.mem Real (Set Real) (@Set.instMembership Real)
                                                      (@Set.uIcc Real Real.lattice (ra n) (rb n)) rho →
                                                    ∀ (v : Real),
                                                      @Membership.mem Real (Set Real) (@Set.instMembership Real)
                                                          (@Set.uIcc Real Real.lattice (va n) (vb n)) v →
                                                        And
                                                          (@LT.lt Real Real.instLT
                                                            (@abs Real Real.lattice Real.instAddGroup
                                                              (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                                                                (massC n)
                                                                (DominantFiveBody.physicalSourceAngularRadialDerivative
                                                                  (rc n) (vc n) rho v)))
                                                            eta)
                                                          (And
                                                            (@LT.lt Real Real.instLT
                                                              (@abs Real Real.lattice Real.instAddGroup
                                                                (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                                                  (@HMul.hMul Real Real Real
                                                                    (@instHMul Real Real.instMul) (massC n)
                                                                    (DominantFiveBody.physicalSourceAngularAngularDerivative
                                                                      (rc n) (vc n) rho v))
                                                                  (@HMul.hMul Real Real Real
                                                                    (@instHMul Real Real.instMul)
                                                                    (@OfNat.ofNat Real (nat_lit 2)
                                                                      (@instOfNatAtLeastTwo Real (nat_lit 2)
                                                                        Real.instNatCast
                                                                        (@Nat.instAtLeastTwoHAddOfNat
                                                                          (@OfNat.ofNat Nat (nat_lit 1)
                                                                            (instOfNatNat (nat_lit 1)))
                                                                          (@Nat.instNeZeroSucc
                                                                            (@OfNat.ofNat Nat (nat_lit 0)
                                                                              (instOfNatNat (nat_lit 0)))))))
                                                                    L)))
                                                              eta)
                                                            (And
                                                              (@LT.lt Real Real.instLT
                                                                (@abs Real Real.lattice Real.instAddGroup
                                                                  (@HSub.hSub Real Real Real
                                                                    (@instHSub Real Real.instSub)
                                                                    (@HMul.hMul Real Real Real
                                                                      (@instHMul Real Real.instMul) (massP n)
                                                                      (DominantFiveBody.physicalSourceAngularRadialDerivative
                                                                        (rp n) (vp n) rho v))
                                                                    (@HMul.hMul Real Real Real
                                                                      (@instHMul Real Real.instMul) M
                                                                      (DominantFiveBody.physicalSourceAngularRadialDerivative
                                                                        (@OfNat.ofNat Real (nat_lit 1)
                                                                          (@One.toOfNat1 Real Real.instOne))
                                                                        angle0
                                                                        (@OfNat.ofNat Real (nat_lit 1)
                                                                          (@One.toOfNat1 Real Real.instOne))
                                                                        psi))))
                                                                eta)
                                                              (@LT.lt Real Real.instLT
                                                                (@abs Real Real.lattice Real.instAddGroup
                                                                  (@HSub.hSub Real Real Real
                                                                    (@instHSub Real Real.instSub)
                                                                    (@HMul.hMul Real Real Real
                                                                      (@instHMul Real Real.instMul) (massP n)
                                                                      (DominantFiveBody.physicalSourceAngularAngularDerivative
                                                                        (rp n) (vp n) rho v))
                                                                    (@HMul.hMul Real Real Real
                                                                      (@instHMul Real Real.instMul) M
                                                                      (DominantFiveBody.Coorbital.kappa
                                                                        (@abs Real Real.lattice Real.instAddGroup
                                                                          (@HSub.hSub Real Real Real
                                                                            (@instHSub Real Real.instSub) psi
                                                                            angle0))))))
                                                                eta))))
                                              (@Filter.atTop Nat Nat.instPreorder) := @DominantFiveBody.physical_nested_polar_rectangle_derivatives_individually_uniform

-- Source binding: prose:487
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                      (Fin.castSucc b) /
                                                    DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∀ (eta : ℝ),
                                                (0 : ℝ) < eta →
                                                  ∀ᶠ (n : ℕ) in Filter.atTop,
                                                    ∀ rho ∈ Set.uIcc (r n (Fin.castSucc a)) (r n (Fin.castSucc b)),
                                                      ∀
                                                        v ∈
                                                          Set.uIcc (theta n (Fin.castSucc a))
                                                            (theta n (Fin.castSucc b)),
                                                        |mu n (Fin.castSucc c) *
                                                                DominantFiveBody.physicalSourceAngularRadialDerivative
                                                                  (r n (Fin.castSucc c)) (theta n (Fin.castSucc c)) rho
                                                                  v| <
                                                            eta ∧
                                                          |mu n (Fin.castSucc c) *
                                                                    DominantFiveBody.physicalSourceAngularAngularDerivative
                                                                      (r n (Fin.castSucc c)) (theta n (Fin.castSucc c))
                                                                      rho v -
                                                                  (2 : ℝ) * mu n (Fin.castSucc c) /
                                                                    DominantFiveBody.tripleLowDiameter
                                                                        (DominantFiveBody.satellitesRelative (x n)) ^
                                                                      (3 : ℕ)| <
                                                              eta ∧
                                                            |mu n (3 : DominantFiveBody.Satellite) *
                                                                      DominantFiveBody.physicalSourceAngularRadialDerivative
                                                                        (r n (3 : DominantFiveBody.Satellite))
                                                                        (theta n (3 : DominantFiveBody.Satellite)) rho
                                                                        v +
                                                                    (3 : ℝ) * √(3 : ℝ) / (4 : ℝ)| <
                                                                eta ∧
                                                              |mu n (3 : DominantFiveBody.Satellite) *
                                                                      DominantFiveBody.physicalSourceAngularAngularDerivative
                                                                        (r n (3 : DominantFiveBody.Satellite))
                                                                        (theta n (3 : DominantFiveBody.Satellite)) rho
                                                                        v -
                                                                    (9 / 4 : ℝ)| <
                                                                eta := @DominantFiveBody.normalized_complete_lower_triple_nested_rectangle_individual_limits

-- Source binding: prose:487
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (0 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.succ a)
                                                      (Fin.succ b) /
                                                    DominantFiveBody.tripleHighDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∀ (eta : ℝ),
                                                (0 : ℝ) < eta →
                                                  ∀ᶠ (n : ℕ) in Filter.atTop,
                                                    ∀ rho ∈ Set.uIcc (r n (Fin.succ a)) (r n (Fin.succ b)),
                                                      ∀ v ∈ Set.uIcc (theta n (Fin.succ a)) (theta n (Fin.succ b)),
                                                        |mu n (Fin.succ c) *
                                                                DominantFiveBody.physicalSourceAngularRadialDerivative
                                                                  (r n (Fin.succ c)) (theta n (Fin.succ c)) rho v| <
                                                            eta ∧
                                                          |mu n (Fin.succ c) *
                                                                    DominantFiveBody.physicalSourceAngularAngularDerivative
                                                                      (r n (Fin.succ c)) (theta n (Fin.succ c)) rho v -
                                                                  (2 : ℝ) * mu n (Fin.succ c) /
                                                                    DominantFiveBody.tripleHighDiameter
                                                                        (DominantFiveBody.satellitesRelative (x n)) ^
                                                                      (3 : ℕ)| <
                                                              eta ∧
                                                            |mu n (0 : DominantFiveBody.Satellite) *
                                                                      DominantFiveBody.physicalSourceAngularRadialDerivative
                                                                        (r n (0 : DominantFiveBody.Satellite))
                                                                        (theta n (0 : DominantFiveBody.Satellite)) rho
                                                                        v -
                                                                    (3 : ℝ) * √(3 : ℝ) / (4 : ℝ)| <
                                                                eta ∧
                                                              |mu n (0 : DominantFiveBody.Satellite) *
                                                                      DominantFiveBody.physicalSourceAngularAngularDerivative
                                                                        (r n (0 : DominantFiveBody.Satellite))
                                                                        (theta n (0 : DominantFiveBody.Satellite)) rho
                                                                        v -
                                                                    (9 / 4 : ℝ)| <
                                                                eta := @DominantFiveBody.normalized_complete_upper_triple_nested_rectangle_individual_limits

-- Source binding: prose:487
example : ∀ (mass s angle rho v d : ℝ),
  (0 : ℝ) ≤ mass →
    (0 : ℝ) < d →
      |s| ≤ (2 : ℝ) →
        |angle - v| ≤ (2 : ℝ) * d →
          d / (2 : ℝ) ≤ ‖DominantFiveBody.polarPoint rho v - DominantFiveBody.polarPoint s angle‖ →
            |mass * DominantFiveBody.physicalSourceAngularRadialDerivative s angle rho v| ≤
              (1536 : ℝ) * (mass / d ^ (3 : ℕ)) * (|rho - s| / d + d) := @DominantFiveBody.physicalSourceAngularRadialDerivative_near_display_bound

-- Source binding: prose:487
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                      (Fin.castSucc b) /
                                                    DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∀ᶠ (n : ℕ) in Filter.atTop,
                                                ∀ rho ∈ Set.uIcc (r n (Fin.castSucc a)) (r n (Fin.castSucc b)),
                                                  ∀ v ∈ Set.uIcc (theta n (Fin.castSucc a)) (theta n (Fin.castSucc b)),
                                                    |mu n (Fin.castSucc c) *
                                                          DominantFiveBody.physicalSourceAngularRadialDerivative
                                                            (r n (Fin.castSucc c)) (theta n (Fin.castSucc c)) rho v| ≤
                                                      (1536 : ℝ) *
                                                          (mu n (Fin.castSucc c) /
                                                            DominantFiveBody.tripleLowDiameter
                                                                (DominantFiveBody.satellitesRelative (x n)) ^
                                                              (3 : ℕ)) *
                                                        (|rho - r n (Fin.castSucc c)| /
                                                            DominantFiveBody.tripleLowDiameter
                                                              (DominantFiveBody.satellitesRelative (x n)) +
                                                          DominantFiveBody.tripleLowDiameter
                                                            (DominantFiveBody.satellitesRelative (x n))) := @DominantFiveBody.normalized_complete_lower_triple_nested_rectangle_near_display_bound

-- Source binding: prose:487
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (0 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.succ a)
                                                      (Fin.succ b) /
                                                    DominantFiveBody.tripleHighDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∀ᶠ (n : ℕ) in Filter.atTop,
                                                ∀ rho ∈ Set.uIcc (r n (Fin.succ a)) (r n (Fin.succ b)),
                                                  ∀ v ∈ Set.uIcc (theta n (Fin.succ a)) (theta n (Fin.succ b)),
                                                    |mu n (Fin.succ c) *
                                                          DominantFiveBody.physicalSourceAngularRadialDerivative
                                                            (r n (Fin.succ c)) (theta n (Fin.succ c)) rho v| ≤
                                                      (1536 : ℝ) *
                                                          (mu n (Fin.succ c) /
                                                            DominantFiveBody.tripleHighDiameter
                                                                (DominantFiveBody.satellitesRelative (x n)) ^
                                                              (3 : ℕ)) *
                                                        (|rho - r n (Fin.succ c)| /
                                                            DominantFiveBody.tripleHighDiameter
                                                              (DominantFiveBody.satellitesRelative (x n)) +
                                                          DominantFiveBody.tripleHighDiameter
                                                            (DominantFiveBody.satellitesRelative (x n))) := @DominantFiveBody.normalized_complete_upper_triple_nested_rectangle_near_display_bound

-- Source binding: prose:487
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                      (Fin.castSucc b) /
                                                    DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∀ (eta : ℝ),
                                                (0 : ℝ) < eta →
                                                  ∀ᶠ (n : ℕ) in Filter.atTop,
                                                    ∀ rho ∈ Set.uIcc (r n (Fin.castSucc a)) (r n (Fin.castSucc b)),
                                                      ∀
                                                        v ∈
                                                          Set.uIcc (theta n (Fin.castSucc a))
                                                            (theta n (Fin.castSucc b)),
                                                        |(1536 : ℝ) *
                                                                (mu n (Fin.castSucc c) /
                                                                  DominantFiveBody.tripleLowDiameter
                                                                      (DominantFiveBody.satellitesRelative (x n)) ^
                                                                    (3 : ℕ)) *
                                                              (|rho - r n (Fin.castSucc c)| /
                                                                  DominantFiveBody.tripleLowDiameter
                                                                    (DominantFiveBody.satellitesRelative (x n)) +
                                                                DominantFiveBody.tripleLowDiameter
                                                                  (DominantFiveBody.satellitesRelative (x n)))| <
                                                          eta := @DominantFiveBody.normalized_complete_lower_triple_nested_rectangle_near_display_rhs_vanishes

-- Source binding: prose:487
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (0 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.succ a)
                                                      (Fin.succ b) /
                                                    DominantFiveBody.tripleHighDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∀ (eta : ℝ),
                                                (0 : ℝ) < eta →
                                                  ∀ᶠ (n : ℕ) in Filter.atTop,
                                                    ∀ rho ∈ Set.uIcc (r n (Fin.succ a)) (r n (Fin.succ b)),
                                                      ∀ v ∈ Set.uIcc (theta n (Fin.succ a)) (theta n (Fin.succ b)),
                                                        |(1536 : ℝ) *
                                                                (mu n (Fin.succ c) /
                                                                  DominantFiveBody.tripleHighDiameter
                                                                      (DominantFiveBody.satellitesRelative (x n)) ^
                                                                    (3 : ℕ)) *
                                                              (|rho - r n (Fin.succ c)| /
                                                                  DominantFiveBody.tripleHighDiameter
                                                                    (DominantFiveBody.satellitesRelative (x n)) +
                                                                DominantFiveBody.tripleHighDiameter
                                                                  (DominantFiveBody.satellitesRelative (x n)))| <
                                                          eta := @DominantFiveBody.normalized_complete_upper_triple_nested_rectangle_near_display_rhs_vanishes

-- Source binding: eq:nested-derivatives
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (clusterCenter : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) clusterCenter →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                      (Fin.castSucc b) /
                                                    DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              (∃ (C : ℝ),
                                                  (0 : ℝ) < C ∧
                                                    ∀ᶠ (n : ℕ) in Filter.atTop,
                                                      ∀ rho ∈ Set.uIcc (r n (Fin.castSucc a)) (r n (Fin.castSucc b)),
                                                        ∀
                                                          v ∈
                                                            Set.uIcc (theta n (Fin.castSucc a))
                                                              (theta n (Fin.castSucc b)),
                                                          DominantFiveBody.physicalPairExteriorAngularRadialDerivative
                                                                (mu n) (r n) (theta n) (Fin.castSucc a) (Fin.castSucc b)
                                                                rho v ≤
                                                              -C⁻¹ ∧
                                                            |DominantFiveBody.physicalPairExteriorAngularRadialDerivative
                                                                    (mu n) (r n) (theta n) (Fin.castSucc a)
                                                                    (Fin.castSucc b) rho v| +
                                                                |DominantFiveBody.physicalPairExteriorAngularAngularDerivative
                                                                    (mu n) (r n) (theta n) (Fin.castSucc a)
                                                                    (Fin.castSucc b) rho v| ≤
                                                              C) ∧
                                                ∀ (eta : ℝ),
                                                  (0 : ℝ) < eta →
                                                    ∀ᶠ (n : ℕ) in Filter.atTop,
                                                      ∀ rho ∈ Set.uIcc (r n (Fin.castSucc a)) (r n (Fin.castSucc b)),
                                                        ∀
                                                          v ∈
                                                            Set.uIcc (theta n (Fin.castSucc a))
                                                              (theta n (Fin.castSucc b)),
                                                          |DominantFiveBody.physicalPairExteriorAngularAngularDerivative
                                                                  (mu n) (r n) (theta n) (Fin.castSucc a)
                                                                  (Fin.castSucc b) rho v -
                                                                ((9 / 4 : ℝ) +
                                                                  (2 : ℝ) * mu n (Fin.castSucc c) /
                                                                    DominantFiveBody.tripleLowDiameter
                                                                        (DominantFiveBody.satellitesRelative (x n)) ^
                                                                      (3 : ℕ))| <
                                                            eta := @DominantFiveBody.normalized_complete_lower_triple_nested_rectangle_controls

-- Source binding: eq:nested-derivatives
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (clusterCenter : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (0 : DominantFiveBody.Satellite) clusterCenter →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.succ a)
                                                      (Fin.succ b) /
                                                    DominantFiveBody.tripleHighDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              (∃ (C : ℝ),
                                                  (0 : ℝ) < C ∧
                                                    ∀ᶠ (n : ℕ) in Filter.atTop,
                                                      ∀ rho ∈ Set.uIcc (r n (Fin.succ a)) (r n (Fin.succ b)),
                                                        ∀ v ∈ Set.uIcc (theta n (Fin.succ a)) (theta n (Fin.succ b)),
                                                          -DominantFiveBody.physicalPairExteriorAngularRadialDerivative
                                                                  (mu n) (r n) (theta n) (Fin.succ a) (Fin.succ b) rho
                                                                  v ≤
                                                              -C⁻¹ ∧
                                                            |DominantFiveBody.physicalPairExteriorAngularRadialDerivative
                                                                    (mu n) (r n) (theta n) (Fin.succ a) (Fin.succ b) rho
                                                                    v| +
                                                                |DominantFiveBody.physicalPairExteriorAngularAngularDerivative
                                                                    (mu n) (r n) (theta n) (Fin.succ a) (Fin.succ b) rho
                                                                    v| ≤
                                                              C) ∧
                                                ∀ (eta : ℝ),
                                                  (0 : ℝ) < eta →
                                                    ∀ᶠ (n : ℕ) in Filter.atTop,
                                                      ∀ rho ∈ Set.uIcc (r n (Fin.succ a)) (r n (Fin.succ b)),
                                                        ∀ v ∈ Set.uIcc (theta n (Fin.succ a)) (theta n (Fin.succ b)),
                                                          |DominantFiveBody.physicalPairExteriorAngularAngularDerivative
                                                                  (mu n) (r n) (theta n) (Fin.succ a) (Fin.succ b) rho
                                                                  v -
                                                                ((9 / 4 : ℝ) +
                                                                  (2 : ℝ) * mu n (Fin.succ c) /
                                                                    DominantFiveBody.tripleHighDiameter
                                                                        (DominantFiveBody.satellitesRelative (x n)) ^
                                                                      (3 : ℕ))| <
                                                            eta := @DominantFiveBody.normalized_complete_upper_triple_nested_rectangle_controls

-- Source binding: prose:492
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (q : ℕ → DominantFiveBody.SatelliteConfiguration)
  (a b : DominantFiveBody.Satellite),
  a ≠ b →
    (∀ (n : ℕ), DominantFiveBody.RelativeCollisionFree (q n)) →
      (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
          DominantFiveBody.vectorResidual (eps n) (mu n) (q n) i = (0 : DominantFiveBody.Plane)) →
        ∀ (c v : DominantFiveBody.Plane),
          ‖c‖ = (1 : ℝ) →
            Filter.Tendsto (fun (n : ℕ) => q n a) Filter.atTop (𝓝 c) →
              Filter.Tendsto (fun (n : ℕ) => q n b) Filter.atTop (𝓝 c) →
                Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.physicalPairDirection (q n) a b) Filter.atTop (𝓝 v) →
                  Filter.Tendsto
                      (fun (n : ℕ) =>
                        eps n •
                          DominantFiveBody.pairSecantExteriorField (mu n) (q n) a b
                            (DominantFiveBody.physicalPairDirection (q n) a b))
                      Filter.atTop (𝓝 (0 : DominantFiveBody.Plane)) →
                    Filter.Tendsto
                          (fun (n : ℕ) =>
                            eps n * (mu n a + mu n b) / DominantFiveBody.satelliteDistance (q n) a b ^ (3 : ℕ))
                          Filter.atTop (𝓝 (0 : ℝ)) ∧
                        Inner.inner ℝ v c = (0 : ℝ) ∨
                      Filter.Tendsto
                          (fun (n : ℕ) =>
                            eps n * (mu n a + mu n b) / DominantFiveBody.satelliteDistance (q n) a b ^ (3 : ℕ))
                          Filter.atTop (𝓝 (3 : ℝ)) ∧
                        (v = c ∨ v = -c) := @DominantFiveBody.physical_pair_direction_alternative_of_exterior_vanishes

-- Source binding: prose:492
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (d : ℕ → ℝ)
  (a b c p : DominantFiveBody.Satellite),
  a ≠ b →
    c ≠ p →
      c ∈ DominantFiveBody.pairExteriorLabels a b →
        p ∈ DominantFiveBody.pairExteriorLabels a b →
          (∀ (n : ℕ), DominantFiveBody.RelativeCollisionFree (DominantFiveBody.polarSatellites (r n) (theta n))) →
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
                DominantFiveBody.vectorResidual (eps n) (mu n) (DominantFiveBody.polarSatellites (r n) (theta n)) i =
                  (0 : DominantFiveBody.Plane)) →
              Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
                (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                  (∀ (i : DominantFiveBody.Satellite), Filter.Tendsto (fun (n : ℕ) => r n i) Filter.atTop (𝓝 (1 : ℝ))) →
                    ∀ (psi angle0 : ℝ),
                      Filter.Tendsto (fun (n : ℕ) => theta n a) Filter.atTop (𝓝 psi) →
                        Filter.Tendsto (fun (n : ℕ) => theta n b) Filter.atTop (𝓝 psi) →
                          Filter.Tendsto (fun (n : ℕ) => theta n c) Filter.atTop (𝓝 psi) →
                            Filter.Tendsto (fun (n : ℕ) => theta n p) Filter.atTop (𝓝 angle0) →
                              (0 : ℝ) < angle0 - psi ∧ angle0 - psi < Real.pi →
                                (∀ (n : ℕ), (0 : ℝ) < d n) →
                                  Filter.Tendsto d Filter.atTop (𝓝 (0 : ℝ)) →
                                    ∀ (U v : DominantFiveBody.Plane),
                                      ‖U‖ = (1 : ℝ) →
                                        Inner.inner ℝ U (DominantFiveBody.polarPoint (1 : ℝ) psi) = (0 : ℝ) →
                                          ∀ (L : ℝ),
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  (d n)⁻¹ •
                                                    (DominantFiveBody.polarPoint (r n c) (theta n c) -
                                                      DominantFiveBody.polarPoint (r n a) (theta n a)))
                                                Filter.atTop (𝓝 U) →
                                              Filter.Tendsto
                                                  (fun (n : ℕ) =>
                                                    DominantFiveBody.satelliteDistance
                                                        (DominantFiveBody.polarSatellites (r n) (theta n)) a b /
                                                      d n)
                                                  Filter.atTop (𝓝 (0 : ℝ)) →
                                                Filter.Tendsto
                                                    (fun (n : ℕ) =>
                                                      DominantFiveBody.physicalPairDirection
                                                        (DominantFiveBody.polarSatellites (r n) (theta n)) a b)
                                                    Filter.atTop (𝓝 v) →
                                                  Filter.Tendsto (fun (n : ℕ) => mu n c / d n ^ (3 : ℕ)) Filter.atTop
                                                      (𝓝 L) →
                                                    Filter.Tendsto (fun (n : ℕ) => mu n p) Filter.atTop (𝓝 (1 : ℝ)) →
                                                      (∀ (n : ℕ),
                                                          (0 : ℝ) < theta n b - theta n a ∧
                                                            theta n b - theta n a < Real.pi) →
                                                        (∀ᶠ (n : ℕ) in Filter.atTop,
                                                            (0 : ℝ) <
                                                              DominantFiveBody.physicalPairExteriorAngularField (mu n)
                                                                  (r n) (theta n) a b (r n b) (theta n b) -
                                                                DominantFiveBody.physicalPairExteriorAngularField (mu n)
                                                                  (r n) (theta n) a b (r n a) (theta n a)) →
                                                          (∀ᶠ (n : ℕ) in Filter.atTop,
                                                              (0 : ℝ) <
                                                                DominantFiveBody.det2
                                                                  (DominantFiveBody.polarPoint (r n b) (theta n b) -
                                                                    DominantFiveBody.polarPoint (r n a) (theta n a))
                                                                  (DominantFiveBody.polarPoint (r n p) (theta n p) -
                                                                    DominantFiveBody.polarPoint (r n a) (theta n a))) →
                                                            v =
                                                                DominantFiveBody.quarterTurn
                                                                  (DominantFiveBody.polarPoint (1 : ℝ) psi) ∧
                                                              Filter.Tendsto
                                                                  (fun (n : ℕ) =>
                                                                    eps n * (mu n a + mu n b) /
                                                                      DominantFiveBody.satelliteDistance
                                                                          (DominantFiveBody.polarSatellites (r n)
                                                                            (theta n))
                                                                          a b ^
                                                                        (3 : ℕ))
                                                                  Filter.atTop (𝓝 (0 : ℝ)) ∧
                                                                Filter.Tendsto
                                                                    (fun (n : ℕ) =>
                                                                      (theta n b - theta n a) /
                                                                        DominantFiveBody.satelliteDistance
                                                                          (DominantFiveBody.polarSatellites (r n)
                                                                            (theta n))
                                                                          a b)
                                                                    Filter.atTop (𝓝 (1 : ℝ)) ∧
                                                                  Filter.Tendsto
                                                                    (fun (n : ℕ) =>
                                                                      (r n b - r n a) /
                                                                        DominantFiveBody.satelliteDistance
                                                                          (DominantFiveBody.polarSatellites (r n)
                                                                            (theta n))
                                                                          a b)
                                                                    Filter.atTop (𝓝 (0 : ℝ)) := @DominantFiveBody.physical_nested_pair_selected_tangential

-- Source binding: prose:492
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (d : ℕ → ℝ)
  (a b c p : DominantFiveBody.Satellite),
  a ≠ b →
    c ≠ p →
      c ∈ DominantFiveBody.pairExteriorLabels a b →
        p ∈ DominantFiveBody.pairExteriorLabels a b →
          (∀ (n : ℕ), DominantFiveBody.RelativeCollisionFree (DominantFiveBody.polarSatellites (r n) (theta n))) →
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
                DominantFiveBody.vectorResidual (eps n) (mu n) (DominantFiveBody.polarSatellites (r n) (theta n)) i =
                  (0 : DominantFiveBody.Plane)) →
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
                  DominantFiveBody.tangentialResidual (mu n) (r n) (theta n) i = (0 : ℝ)) →
                Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
                  (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < mu n i) →
                    (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                      (∀ (i : DominantFiveBody.Satellite),
                          Filter.Tendsto (fun (n : ℕ) => r n i) Filter.atTop (𝓝 (1 : ℝ))) →
                        Filter.Tendsto (fun (n : ℕ) => mu n a) Filter.atTop (𝓝 (0 : ℝ)) →
                          Filter.Tendsto (fun (n : ℕ) => mu n b) Filter.atTop (𝓝 (0 : ℝ)) →
                            ∀ (psi angle0 : ℝ),
                              Filter.Tendsto (fun (n : ℕ) => theta n a) Filter.atTop (𝓝 psi) →
                                Filter.Tendsto (fun (n : ℕ) => theta n b) Filter.atTop (𝓝 psi) →
                                  Filter.Tendsto (fun (n : ℕ) => theta n c) Filter.atTop (𝓝 psi) →
                                    Filter.Tendsto (fun (n : ℕ) => theta n p) Filter.atTop (𝓝 angle0) →
                                      (0 : ℝ) < angle0 - psi ∧ angle0 - psi < Real.pi →
                                        (∀ (n : ℕ), (0 : ℝ) < d n) →
                                          Filter.Tendsto d Filter.atTop (𝓝 (0 : ℝ)) →
                                            ∀ (U : DominantFiveBody.Plane),
                                              ‖U‖ = (1 : ℝ) →
                                                Inner.inner ℝ U (DominantFiveBody.polarPoint (1 : ℝ) psi) = (0 : ℝ) →
                                                  Filter.Tendsto
                                                      (fun (n : ℕ) =>
                                                        (d n)⁻¹ •
                                                          (DominantFiveBody.polarPoint (r n c) (theta n c) -
                                                            DominantFiveBody.polarPoint (r n a) (theta n a)))
                                                      Filter.atTop (𝓝 U) →
                                                    Filter.Tendsto
                                                        (fun (n : ℕ) =>
                                                          DominantFiveBody.satelliteDistance
                                                              (DominantFiveBody.polarSatellites (r n) (theta n)) a b /
                                                            d n)
                                                        Filter.atTop (𝓝 (0 : ℝ)) →
                                                      Filter.Tendsto (fun (n : ℕ) => mu n p) Filter.atTop (𝓝 (1 : ℝ)) →
                                                        (∀ (n : ℕ),
                                                            (0 : ℝ) < theta n b - theta n a ∧
                                                              theta n b - theta n a < Real.pi) →
                                                          (∀ᶠ (n : ℕ) in Filter.atTop,
                                                              (0 : ℝ) <
                                                                DominantFiveBody.physicalPairExteriorAngularField (mu n)
                                                                    (r n) (theta n) a b (r n b) (theta n b) -
                                                                  DominantFiveBody.physicalPairExteriorAngularField
                                                                    (mu n) (r n) (theta n) a b (r n a) (theta n a)) →
                                                            (∀ᶠ (n : ℕ) in Filter.atTop,
                                                                (0 : ℝ) <
                                                                  DominantFiveBody.det2
                                                                    (DominantFiveBody.polarPoint (r n b) (theta n b) -
                                                                      DominantFiveBody.polarPoint (r n a) (theta n a))
                                                                    (DominantFiveBody.polarPoint (r n p) (theta n p) -
                                                                      DominantFiveBody.polarPoint (r n a)
                                                                        (theta n a))) →
                                                              Filter.Tendsto
                                                                  (fun (n : ℕ) =>
                                                                    (mu n a + mu n b + mu n c) / d n ^ (3 : ℕ))
                                                                  Filter.atTop
                                                                  (𝓝
                                                                    (DominantFiveBody.Coorbital.kappa |psi - angle0|)) →
                                                                Filter.Tendsto
                                                                    (fun (n : ℕ) =>
                                                                      DominantFiveBody.physicalPairDirection
                                                                        (DominantFiveBody.polarSatellites (r n)
                                                                          (theta n))
                                                                        a b)
                                                                    Filter.atTop
                                                                    (𝓝
                                                                      (DominantFiveBody.quarterTurn
                                                                        (DominantFiveBody.polarPoint (1 : ℝ) psi))) ∧
                                                                  Filter.Tendsto
                                                                      (fun (n : ℕ) =>
                                                                        eps n * (mu n a + mu n b) /
                                                                          DominantFiveBody.satelliteDistance
                                                                              (DominantFiveBody.polarSatellites (r n)
                                                                                (theta n))
                                                                              a b ^
                                                                            (3 : ℕ))
                                                                      Filter.atTop (𝓝 (0 : ℝ)) ∧
                                                                    Filter.Tendsto
                                                                        (fun (n : ℕ) =>
                                                                          (theta n b - theta n a) /
                                                                            DominantFiveBody.satelliteDistance
                                                                              (DominantFiveBody.polarSatellites (r n)
                                                                                (theta n))
                                                                              a b)
                                                                        Filter.atTop (𝓝 (1 : ℝ)) ∧
                                                                      Filter.Tendsto
                                                                          (fun (n : ℕ) =>
                                                                            (r n b - r n a) /
                                                                              DominantFiveBody.satelliteDistance
                                                                                (DominantFiveBody.polarSatellites (r n)
                                                                                  (theta n))
                                                                                a b)
                                                                          Filter.atTop (𝓝 (0 : ℝ)) ∧
                                                                        Filter.Tendsto
                                                                            (fun (n : ℕ) =>
                                                                              (mu n a + mu n b) /
                                                                                DominantFiveBody.satelliteDistance
                                                                                    (DominantFiveBody.polarSatellites
                                                                                      (r n) (theta n))
                                                                                    a b ^
                                                                                  (3 : ℕ))
                                                                            Filter.atTop
                                                                            (𝓝
                                                                              ((3 : ℝ) *
                                                                                DominantFiveBody.Coorbital.kappa
                                                                                  |psi - angle0|)) ∧
                                                                          Filter.Tendsto
                                                                              (fun (n : ℕ) => mu n c / d n ^ (3 : ℕ))
                                                                              Filter.atTop
                                                                              (𝓝
                                                                                (DominantFiveBody.Coorbital.kappa
                                                                                  |psi - angle0|)) ∧
                                                                            Filter.Tendsto
                                                                              (fun (n : ℕ) =>
                                                                                (mu n a + mu n b) / d n ^ (3 : ℕ))
                                                                              Filter.atTop (𝓝 (0 : ℝ)) := @DominantFiveBody.physical_nested_pair_unselected_precise_scales

-- Source binding: prose:492
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                      (Fin.castSucc b) /
                                                    DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              Filter.Tendsto
                                                  (fun (n : ℕ) =>
                                                    DominantFiveBody.physicalPairDirection
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                      (Fin.castSucc b))
                                                  Filter.atTop
                                                  (𝓝
                                                    (DominantFiveBody.quarterTurn
                                                      (DominantFiveBody.polarPoint (1 : ℝ)
                                                        (theta0 (0 : DominantFiveBody.Satellite))))) ∧
                                                Filter.Tendsto
                                                    (fun (n : ℕ) =>
                                                      eps n * (mu n (Fin.castSucc a) + mu n (Fin.castSucc b)) /
                                                        DominantFiveBody.satelliteDistance
                                                            (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                            (Fin.castSucc b) ^
                                                          (3 : ℕ))
                                                    Filter.atTop (𝓝 (0 : ℝ)) ∧
                                                  Filter.Tendsto
                                                      (fun (n : ℕ) =>
                                                        (theta n (Fin.castSucc b) - theta n (Fin.castSucc a)) /
                                                          DominantFiveBody.satelliteDistance
                                                            (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                            (Fin.castSucc b))
                                                      Filter.atTop (𝓝 (1 : ℝ)) ∧
                                                    Filter.Tendsto
                                                        (fun (n : ℕ) =>
                                                          (r n (Fin.castSucc b) - r n (Fin.castSucc a)) /
                                                            DominantFiveBody.satelliteDistance
                                                              (DominantFiveBody.satellitesRelative (x n))
                                                              (Fin.castSucc a) (Fin.castSucc b))
                                                        Filter.atTop (𝓝 (0 : ℝ)) ∧
                                                      Filter.Tendsto
                                                          (fun (n : ℕ) =>
                                                            (mu n (Fin.castSucc a) + mu n (Fin.castSucc b)) /
                                                              DominantFiveBody.satelliteDistance
                                                                  (DominantFiveBody.satellitesRelative (x n))
                                                                  (Fin.castSucc a) (Fin.castSucc b) ^
                                                                (3 : ℕ))
                                                          Filter.atTop (𝓝 (27 / 4 : ℝ)) ∧
                                                        Filter.Tendsto
                                                            (fun (n : ℕ) =>
                                                              mu n (Fin.castSucc c) /
                                                                DominantFiveBody.tripleLowDiameter
                                                                    (DominantFiveBody.satellitesRelative (x n)) ^
                                                                  (3 : ℕ))
                                                            Filter.atTop (𝓝 (9 / 4 : ℝ)) ∧
                                                          Filter.Tendsto
                                                            (fun (n : ℕ) =>
                                                              (mu n (Fin.castSucc a) + mu n (Fin.castSucc b)) /
                                                                DominantFiveBody.tripleLowDiameter
                                                                    (DominantFiveBody.satellitesRelative (x n)) ^
                                                                  (3 : ℕ))
                                                            Filter.atTop (𝓝 (0 : ℝ)) := @DominantFiveBody.normalized_complete_lower_triple_nested_precise_scales

-- Source binding: display:493
example : ∀ (xi nu s d : ℝ),
  (0 : ℝ) < s → (0 : ℝ) < d → (0 : ℝ) < nu → xi / nu = xi / s ^ (3 : ℕ) / (nu / d ^ (3 : ℕ)) * (s / d) ^ (3 : ℕ) := @DominantFiveBody.positive_two_scale_fraction_identity

-- Source binding: prose:496
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (r theta : ℕ → DominantFiveBody.Satellite → ℝ)
  (a b : DominantFiveBody.Satellite),
  a ≠ b →
    (∀ (n : ℕ), (0 : ℝ) ≤ eps n) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
          (∀ (n : ℕ), DominantFiveBody.RelativeCollisionFree (DominantFiveBody.polarSatellites (r n) (theta n))) →
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
                DominantFiveBody.vectorResidual (eps n) (mu n) (DominantFiveBody.polarSatellites (r n) (theta n)) i =
                  (0 : DominantFiveBody.Plane)) →
              Filter.Tendsto
                  (fun (n : ℕ) =>
                    eps n * (mu n a + mu n b) /
                      DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a b ^
                        (3 : ℕ))
                  Filter.atTop (𝓝 (0 : ℝ)) →
                Filter.Tendsto (fun (n : ℕ) => theta n b - theta n a) Filter.atTop (𝓝 (0 : ℝ)) →
                  ∀ (M : DominantFiveBody.Plane),
                    Filter.Tendsto
                        (fun (n : ℕ) =>
                          DominantFiveBody.pairSecantExteriorField (mu n)
                            (DominantFiveBody.polarSatellites (r n) (theta n)) a b
                            (DominantFiveBody.physicalPairDirection (DominantFiveBody.polarSatellites (r n) (theta n)) a
                              b))
                        Filter.atTop (𝓝 M) →
                      ∃ (C : ℝ),
                        (0 : ℝ) < C ∧
                          ∀ᶠ (n : ℕ) in Filter.atTop,
                            |r n b - r n a| ≤
                              C * eps n *
                                DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a
                                  b := @DominantFiveBody.physical_pair_radial_bound_of_exterior_secant_limit

-- Source binding: prose:496
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                      (Fin.castSucc b) /
                                                    DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              ∃ (C : ℝ),
                                                (0 : ℝ) < C ∧
                                                  ∀ᶠ (n : ℕ) in Filter.atTop,
                                                    |r n (Fin.castSucc b) - r n (Fin.castSucc a)| ≤
                                                      C * eps n *
                                                        DominantFiveBody.satelliteDistance
                                                          (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                          (Fin.castSucc b) := @DominantFiveBody.normalized_complete_lower_triple_nested_radial_bound

-- Source binding: prose:498
example : ∀ (eps : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ) (a b c p : DominantFiveBody.Satellite),
  a ≠ b →
    c ≠ p →
      c ∈ DominantFiveBody.pairExteriorLabels a b →
        p ∈ DominantFiveBody.pairExteriorLabels a b →
          mu a + mu b ≠ (0 : ℝ) →
            (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.angularResidual eps mu r theta i = (0 : ℝ)) →
              (mu a + mu b + mu c) * DominantFiveBody.nestedPairCurrentKernel eps mu r theta a b c +
                  mu p *
                    (DominantFiveBody.nestedPairCurrentExterior eps mu r theta a b p -
                      DominantFiveBody.fullAngularMatrix eps r theta c p) =
                (0 : ℝ) := @DominantFiveBody.physical_nested_macro_average

-- Source binding: prose:498
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
  (0 : ℝ) < eps →
    DominantFiveBody.PositiveRatio mu →
      DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
        ∀ (r theta : DominantFiveBody.Satellite → ℝ),
          (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) →
            DominantFiveBody.satellitesRelative x = DominantFiveBody.polarSatellites r theta →
              ∀ (a b c p : DominantFiveBody.Satellite),
                a ≠ b →
                  c ≠ p →
                    c ∈ DominantFiveBody.pairExteriorLabels a b →
                      p ∈ DominantFiveBody.pairExteriorLabels a b →
                        (mu a + mu b + mu c) * DominantFiveBody.nestedPairCurrentKernel eps mu r theta a b c +
                            ((1 : ℝ) - (mu a + mu b + mu c)) *
                              (DominantFiveBody.nestedPairCurrentExterior eps mu r theta a b p -
                                DominantFiveBody.fullAngularMatrix eps r theta c p) =
                          (0 : ℝ) := @DominantFiveBody.normalized_nested_macro_average

-- Source binding: prop:nested-scale.actual_macro_cube_bridge
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
              (∀ (n : ℕ),
                  DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                (∀ (i : DominantFiveBody.Satellite), Filter.Tendsto (fun (n : ℕ) => r n i) Filter.atTop (𝓝 (1 : ℝ))) →
                  ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                    Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                      ∀ (a b c p : DominantFiveBody.Satellite),
                        a ≠ b →
                          c ≠ p →
                            c ∈ DominantFiveBody.pairExteriorLabels a b →
                              p ∈ DominantFiveBody.pairExteriorLabels a b →
                                ∀ (psi omega : ℝ),
                                  omega ≠ (0 : ℝ) →
                                    theta0 a = psi →
                                      theta0 b = psi →
                                        theta0 c = psi →
                                          theta0 p ≠ psi →
                                            |theta0 p - psi| < Real.pi →
                                              ∀ (d : ℕ → ℝ),
                                                (∀ (n : ℕ), (0 : ℝ) < d n) →
                                                  Filter.Tendsto d Filter.atTop (𝓝 (0 : ℝ)) →
                                                    Filter.Tendsto (fun (n : ℕ) => (r n c - r n a) / d n) Filter.atTop
                                                        (𝓝 (0 : ℝ)) →
                                                      Filter.Tendsto (fun (n : ℕ) => (r n c - r n b) / d n) Filter.atTop
                                                          (𝓝 (0 : ℝ)) →
                                                        Filter.Tendsto (fun (n : ℕ) => (theta n c - theta n a) / d n)
                                                            Filter.atTop (𝓝 omega) →
                                                          Filter.Tendsto (fun (n : ℕ) => (theta n c - theta n b) / d n)
                                                              Filter.atTop (𝓝 omega) →
                                                            Filter.Tendsto
                                                                (fun (n : ℕ) =>
                                                                  DominantFiveBody.satelliteDistance
                                                                      (DominantFiveBody.satellitesRelative (x n)) a c /
                                                                    d n)
                                                                Filter.atTop (𝓝 (1 : ℝ)) →
                                                              Filter.Tendsto
                                                                  (fun (n : ℕ) =>
                                                                    DominantFiveBody.satelliteDistance
                                                                        (DominantFiveBody.satellitesRelative (x n)) b
                                                                        c /
                                                                      d n)
                                                                  Filter.atTop (𝓝 (1 : ℝ)) →
                                                                Filter.Tendsto
                                                                  (fun (n : ℕ) =>
                                                                    (mu n a + mu n b + mu n c) / d n ^ (3 : ℕ))
                                                                  Filter.atTop
                                                                  (𝓝
                                                                    (DominantFiveBody.Coorbital.kappa |psi - theta0 p|)) := @DominantFiveBody.normalized_nested_macro_mass_cube_limit_of_first_order_geometry

-- Source binding: prose:502
example : ∀ (eps s angle rho v d : ℕ → ℝ) (omega : ℝ),
  Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
    Filter.Tendsto s Filter.atTop (𝓝 (1 : ℝ)) →
      Filter.Tendsto rho Filter.atTop (𝓝 (1 : ℝ)) →
        (∀ (n : ℕ), (0 : ℝ) < d n) →
          Filter.Tendsto d Filter.atTop (𝓝 (0 : ℝ)) →
            Filter.Tendsto (fun (n : ℕ) => angle n - v n) Filter.atTop (𝓝 (0 : ℝ)) →
              Filter.Tendsto (fun (n : ℕ) => (angle n - v n) / d n) Filter.atTop (𝓝 omega) →
                (∀ (n : ℕ), DominantFiveBody.polarPoint (s n) (angle n) ≠ DominantFiveBody.polarPoint (rho n) (v n)) →
                  Filter.Tendsto
                      (fun (n : ℕ) =>
                        ‖DominantFiveBody.polarPoint (rho n) (v n) - DominantFiveBody.polarPoint (s n) (angle n)‖ / d n)
                      Filter.atTop (𝓝 (1 : ℝ)) →
                    Filter.Tendsto
                      (fun (n : ℕ) =>
                        d n ^ (2 : ℕ) *
                          DominantFiveBody.physicalSourceFullAngularField (eps n) (s n) (angle n) (rho n) (v n))
                      Filter.atTop (𝓝 omega) := @DominantFiveBody.physicalSourceFullAngularField_near_scaled_limit

-- Source binding: prose:502
example : ∀ (eps s angle ra va rb vb d : ℕ → ℝ) (angle0 psi omega : ℝ),
  Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
    Filter.Tendsto s Filter.atTop (𝓝 (1 : ℝ)) →
      Filter.Tendsto angle Filter.atTop (𝓝 angle0) →
        Filter.Tendsto ra Filter.atTop (𝓝 (1 : ℝ)) →
          Filter.Tendsto rb Filter.atTop (𝓝 (1 : ℝ)) →
            Filter.Tendsto va Filter.atTop (𝓝 psi) →
              Filter.Tendsto vb Filter.atTop (𝓝 psi) →
                (∀ (n : ℕ), (0 : ℝ) < d n) →
                  Filter.Tendsto (fun (n : ℕ) => (rb n - ra n) / d n) Filter.atTop (𝓝 (0 : ℝ)) →
                    Filter.Tendsto (fun (n : ℕ) => (vb n - va n) / d n) Filter.atTop (𝓝 omega) →
                      angle0 ≠ psi →
                        |angle0 - psi| < Real.pi →
                          Filter.Tendsto
                            (fun (n : ℕ) =>
                              (DominantFiveBody.physicalSourceFullAngularField (eps n) (s n) (angle n) (rb n) (vb n) -
                                  DominantFiveBody.physicalSourceFullAngularField (eps n) (s n) (angle n) (ra n)
                                    (va n)) /
                                d n)
                            Filter.atTop (𝓝 (omega * DominantFiveBody.Coorbital.kappa |psi - angle0|)) := @DominantFiveBody.physicalSourceFullAngularField_moving_secant_limit

-- Source binding: prose:502
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (a b c : DominantFiveBody.TripleLabel),
                                      a < b →
                                        c ≠ a →
                                          c ≠ b →
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.satelliteDistance
                                                      (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                      (Fin.castSucc b) /
                                                    DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)))
                                                Filter.atTop (𝓝 (0 : ℝ)) →
                                              Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  (mu n (0 : DominantFiveBody.Satellite) +
                                                        mu n (1 : DominantFiveBody.Satellite) +
                                                      mu n (2 : DominantFiveBody.Satellite)) /
                                                    DominantFiveBody.tripleLowDiameter
                                                        (DominantFiveBody.satellitesRelative (x n)) ^
                                                      (3 : ℕ))
                                                Filter.atTop (𝓝 (9 / 4 : ℝ)) := @DominantFiveBody.normalized_complete_lower_triple_nested_macro_mass_cube_limit

-- Source binding: prose:502
example : ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ) (d : ℕ → ℝ) (a b c p : DominantFiveBody.Satellite),
  a ≠ b →
    c ≠ p →
      c ∈ DominantFiveBody.pairExteriorLabels a b →
        p ∈ DominantFiveBody.pairExteriorLabels a b →
          (∀ (n : ℕ), DominantFiveBody.RelativeCollisionFree (DominantFiveBody.polarSatellites (r n) (theta n))) →
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < mu n i) →
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ) (i : DominantFiveBody.Satellite),
                    DominantFiveBody.tangentialResidual (mu n) (r n) (theta n) i = (0 : ℝ)) →
                  (∀ (i : DominantFiveBody.Satellite), Filter.Tendsto (fun (n : ℕ) => r n i) Filter.atTop (𝓝 (1 : ℝ))) →
                    Filter.Tendsto (fun (n : ℕ) => mu n a) Filter.atTop (𝓝 (0 : ℝ)) →
                      Filter.Tendsto (fun (n : ℕ) => mu n b) Filter.atTop (𝓝 (0 : ℝ)) →
                        ∀ (psi angle0 : ℝ),
                          Filter.Tendsto (fun (n : ℕ) => theta n a) Filter.atTop (𝓝 psi) →
                            Filter.Tendsto (fun (n : ℕ) => theta n b) Filter.atTop (𝓝 psi) →
                              Filter.Tendsto (fun (n : ℕ) => theta n c) Filter.atTop (𝓝 psi) →
                                Filter.Tendsto (fun (n : ℕ) => theta n p) Filter.atTop (𝓝 angle0) →
                                  angle0 ≠ psi →
                                    |angle0 - psi| < Real.pi →
                                      (∀ (n : ℕ), (0 : ℝ) < d n) →
                                        Filter.Tendsto d Filter.atTop (𝓝 (0 : ℝ)) →
                                          ∀ (U : DominantFiveBody.Plane),
                                            ‖U‖ = (1 : ℝ) →
                                              Inner.inner ℝ U (DominantFiveBody.polarPoint (1 : ℝ) psi) = (0 : ℝ) →
                                                ∀ (L : ℝ),
                                                  Filter.Tendsto
                                                      (fun (n : ℕ) =>
                                                        (d n)⁻¹ •
                                                          (DominantFiveBody.polarPoint (r n c) (theta n c) -
                                                            DominantFiveBody.polarPoint (r n a) (theta n a)))
                                                      Filter.atTop (𝓝 U) →
                                                    Filter.Tendsto
                                                        (fun (n : ℕ) =>
                                                          DominantFiveBody.satelliteDistance
                                                              (DominantFiveBody.polarSatellites (r n) (theta n)) a b /
                                                            d n)
                                                        Filter.atTop (𝓝 (0 : ℝ)) →
                                                      Filter.Tendsto
                                                          (fun (n : ℕ) =>
                                                            DominantFiveBody.physicalPairDirection
                                                              (DominantFiveBody.polarSatellites (r n) (theta n)) a b)
                                                          Filter.atTop
                                                          (𝓝
                                                            (DominantFiveBody.quarterTurn
                                                              (DominantFiveBody.polarPoint (1 : ℝ) psi))) →
                                                        Filter.Tendsto (fun (n : ℕ) => mu n c / d n ^ (3 : ℕ))
                                                            Filter.atTop (𝓝 L) →
                                                          Filter.Tendsto (fun (n : ℕ) => mu n p) Filter.atTop
                                                              (𝓝 (1 : ℝ)) →
                                                            (∀ (n : ℕ),
                                                                (0 : ℝ) < theta n b - theta n a ∧
                                                                  theta n b - theta n a < Real.pi) →
                                                              Filter.Tendsto
                                                                  (fun (n : ℕ) =>
                                                                    (theta n b - theta n a) /
                                                                      DominantFiveBody.satelliteDistance
                                                                        (DominantFiveBody.polarSatellites (r n)
                                                                          (theta n))
                                                                        a b)
                                                                  Filter.atTop (𝓝 (1 : ℝ)) →
                                                                Filter.Tendsto
                                                                    (fun (n : ℕ) =>
                                                                      (r n b - r n a) /
                                                                        DominantFiveBody.satelliteDistance
                                                                          (DominantFiveBody.polarSatellites (r n)
                                                                            (theta n))
                                                                          a b)
                                                                    Filter.atTop (𝓝 (0 : ℝ)) →
                                                                  Filter.Tendsto
                                                                    (fun (n : ℕ) =>
                                                                      (mu n a + mu n b) /
                                                                        DominantFiveBody.satelliteDistance
                                                                            (DominantFiveBody.polarSatellites (r n)
                                                                              (theta n))
                                                                            a b ^
                                                                          (3 : ℕ))
                                                                    Filter.atTop
                                                                    (𝓝
                                                                      (DominantFiveBody.Coorbital.kappa |psi - angle0| +
                                                                        (2 : ℝ) * L)) := @DominantFiveBody.physical_nested_pair_mass_cube_limit_of_tangential

-- Source binding: prose:502
example : ∀ (xi mc s d : ℕ → ℝ) (D L : ℝ),
  (∀ (n : ℕ), (0 : ℝ) < s n) →
    (∀ (n : ℕ), (0 : ℝ) < d n) →
      Filter.Tendsto (fun (n : ℕ) => s n / d n) Filter.atTop (𝓝 (0 : ℝ)) →
        Filter.Tendsto (fun (n : ℕ) => (xi n + mc n) / d n ^ (3 : ℕ)) Filter.atTop (𝓝 D) →
          Filter.Tendsto (fun (n : ℕ) => xi n / s n ^ (3 : ℕ)) Filter.atTop (𝓝 (D + (2 : ℝ) * L)) →
            Filter.Tendsto (fun (n : ℕ) => mc n / d n ^ (3 : ℕ)) Filter.atTop (𝓝 L) →
              L = D ∧
                Filter.Tendsto (fun (n : ℕ) => xi n / d n ^ (3 : ℕ)) Filter.atTop (𝓝 (0 : ℝ)) ∧
                  Filter.Tendsto (fun (n : ℕ) => mc n / d n ^ (3 : ℕ)) Filter.atTop (𝓝 D) ∧
                    Filter.Tendsto (fun (n : ℕ) => xi n / s n ^ (3 : ℕ)) Filter.atTop (𝓝 ((3 : ℝ) * D)) := @DominantFiveBody.nested_precise_two_cube_limits_of_selected

-- Source binding: prose:505
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ),
              DominantFiveBody.StrictConvexInOrder { labels := Equiv.refl DominantFiveBody.Label, primary_first := rfl }
                (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                      i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                Function.Injective qLimit ∨
                                  (∃ (a : DominantFiveBody.Satellite) (b : DominantFiveBody.Satellite),
                                      a < b ∧ DominantFiveBody.CompleteLimitingSatellitePair qLimit a b (qLimit a)) ∨
                                    ∃ (p : DominantFiveBody.Satellite),
                                      (p = (0 : DominantFiveBody.Satellite) ∨ p = (3 : DominantFiveBody.Satellite)) ∧
                                        ∃ (c : DominantFiveBody.Plane),
                                          DominantFiveBody.CompleteLimitingSatelliteTriple qLimit p c := @DominantFiveBody.normalized_ordered_collision_classes_exhaustive

-- Source binding: prose:505
example : ∀ (q : ℕ → DominantFiveBody.SatelliteConfiguration),
  (∀ (n : ℕ), DominantFiveBody.RelativeCollisionFree (q n)) →
    ∃ (phi : ℕ → ℕ),
      StrictMono phi ∧
        ((∃ (a : DominantFiveBody.TripleLabel) (b : DominantFiveBody.TripleLabel) (c : DominantFiveBody.TripleLabel),
            a < b ∧
              c ≠ a ∧
                c ≠ b ∧
                  Filter.Tendsto
                    (fun (n : ℕ) =>
                      DominantFiveBody.satelliteDistance (q (phi n)) (Fin.castSucc a) (Fin.castSucc b) /
                        DominantFiveBody.tripleLowDiameter (q (phi n)))
                    Filter.atTop (𝓝 (0 : ℝ))) ∨
          ∃ (eta : ℝ),
            (0 : ℝ) < eta ∧
              ∀ (n : ℕ) (i j : DominantFiveBody.TripleLabel),
                i ≠ j →
                  eta * DominantFiveBody.tripleLowDiameter (q (phi n)) ≤
                    DominantFiveBody.satelliteDistance (q (phi n)) (Fin.castSucc i) (Fin.castSucc j)) := @DominantFiveBody.low_triple_scale_cases

-- Source binding: eq:chi
example : ∀ (t b : ℝ),
  DominantFiveBody.singleScaleChi t b = t * b ^ (2 : ℕ) / (2 : ℝ) * Real.sinc (t * b / (2 : ℝ)) ^ (2 : ℕ) ∧
    (1 : ℝ) - Real.cos (t * b) = t * DominantFiveBody.singleScaleChi t b := @DominantFiveBody.singleScaleChi_complete

-- Source binding: prose:513
example : ∀ (v : DominantFiveBody.PairJointVariables) (keepD : Bool),
  DominantFiveBody.PairChartRegular (v.1 (0 : Fin (4 : ℕ))) (v.1 (1 : Fin (4 : ℕ))) (v.1 (3 : Fin (4 : ℕ))) v.2 →
    AnalyticAt ℝ
      (fun (w : DominantFiveBody.PairJointVariables) =>
        DominantFiveBody.pairChartExtendedRows (w.1 (0 : Fin (4 : ℕ))) (w.1 (1 : Fin (4 : ℕ))) (w.1 (2 : Fin (4 : ℕ)))
          (w.1 (3 : Fin (4 : ℕ))) keepD w.2)
      v := @DominantFiveBody.pairChartExtendedRows_joint_analyticAt

-- Source binding: prose:513
example : ∀ (v : DominantFiveBody.TripleJointVariables),
  DominantFiveBody.TripleChartRegular (v.1 (0 : Fin (5 : ℕ))) (v.1 (1 : Fin (5 : ℕ)))
      (DominantFiveBody.tripleJointAlpha v.1) v.2 →
    AnalyticAt ℝ
      (fun (w : DominantFiveBody.TripleJointVariables) =>
        DominantFiveBody.tripleChartExtendedRows (w.1 (0 : Fin (5 : ℕ))) (w.1 (1 : Fin (5 : ℕ)))
          (DominantFiveBody.tripleJointAlpha w.1) w.2)
      v := @DominantFiveBody.tripleChartExtendedRows_joint_analyticAt

-- Source binding: prose:513
example : ∀ (v : DominantFiveBody.NestedJointVariables),
  DominantFiveBody.NestedChartRegular (v.1 (0 : Fin (4 : ℕ))) (v.1 (1 : Fin (4 : ℕ))) (v.1 (2 : Fin (4 : ℕ)))
      (v.1 (3 : Fin (4 : ℕ))) v.2 →
    AnalyticAt ℝ
      (fun (w : DominantFiveBody.NestedJointVariables) =>
        DominantFiveBody.nestedChartExtendedRows (w.1 (0 : Fin (4 : ℕ))) (w.1 (1 : Fin (4 : ℕ))) (w.1 (2 : Fin (4 : ℕ)))
          (w.1 (3 : Fin (4 : ℕ))) w.2)
      v := @DominantFiveBody.nestedChartExtendedRows_joint_analyticAt

-- Source binding: prose:513
example : ∀ (eps t p alpha : Real) (keepD : Bool) (y : DominantFiveBody.PairChartVariables),
  @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) t →
    @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
        (DominantFiveBody.pairChartWSq t alpha y) →
      @Ne Real
          (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) eps)
          (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) →
        @Ne Real
            (DominantFiveBody.pairChartRadii t alpha y
              (@OfNat.ofNat DominantFiveBody.Satellite (nat_lit 0)
                (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0))))
            (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) →
          @Ne Real
              (DominantFiveBody.pairChartRadii t alpha y
                (@OfNat.ofNat DominantFiveBody.Satellite (nat_lit 1)
                  (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1))))
              (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) →
            (∀ (i : DominantFiveBody.Satellite),
                @Membership.mem DominantFiveBody.Satellite (Finset DominantFiveBody.Satellite)
                    (@SetLike.instMembership (Finset DominantFiveBody.Satellite) DominantFiveBody.Satellite
                      (@Finset.instSetLike DominantFiveBody.Satellite))
                    (@Insert.insert DominantFiveBody.Satellite (Finset DominantFiveBody.Satellite)
                      (@Finset.instInsert DominantFiveBody.Satellite
                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                      (@OfNat.ofNat DominantFiveBody.Satellite (nat_lit 2)
                        (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 2)))
                      (@Singleton.singleton DominantFiveBody.Satellite (Finset DominantFiveBody.Satellite)
                        (@Finset.instSingleton DominantFiveBody.Satellite)
                        (@OfNat.ofNat DominantFiveBody.Satellite (nat_lit 3)
                          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (nat_lit 3)))))
                    i →
                  And
                    (@Ne DominantFiveBody.Plane (DominantFiveBody.pairChartPoints t alpha y i)
                      (DominantFiveBody.pairChartPoints t alpha y
                        (@OfNat.ofNat DominantFiveBody.Satellite (nat_lit 0)
                          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (nat_lit 0)))))
                    (@Ne DominantFiveBody.Plane (DominantFiveBody.pairChartPoints t alpha y i)
                      (DominantFiveBody.pairChartPoints t alpha y
                        (@OfNat.ofNat DominantFiveBody.Satellite (nat_lit 1)
                          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (nat_lit 1)))))) →
              @Eq DominantFiveBody.PairChartVariables (DominantFiveBody.pairChartExtendedRows eps t p alpha keepD y)
                (DominantFiveBody.pairChartPhysicalRows eps t p alpha keepD y) := @DominantFiveBody.pairChartExtendedRows_eq_physical

-- Source binding: prose:513
example : ∀ (eps t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  (0 : ℝ) < t →
    (1 : ℝ) + eps ≠ (0 : ℝ) →
      (∀ (i j : DominantFiveBody.TripleLabel), i ≠ j → (0 : ℝ) < DominantFiveBody.tripleChartWSq t alpha y i j) →
        (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleChartRadii t alpha y (Fin.castSucc i) ≠ (0 : ℝ)) →
          (∀ (i : DominantFiveBody.TripleLabel),
              DominantFiveBody.tripleChartPoints t alpha y (3 : DominantFiveBody.Satellite) ≠
                DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc i)) →
            DominantFiveBody.tripleChartExtendedRows eps t alpha y =
              DominantFiveBody.tripleChartPhysicalRows eps t alpha y := @DominantFiveBody.tripleChartExtendedRows_eq_physical

-- Source binding: prose:513
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  (0 : ℝ) < t →
    (0 : ℝ) < eta →
      (1 : ℝ) + eps ≠ (0 : ℝ) →
        (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.nestedChartRadii t eta alpha y i ≠ (0 : ℝ)) →
          (0 : ℝ) < DominantFiveBody.nestedInnerWSq t eta alpha y →
            (∀ (j : Fin (2 : ℕ)), (0 : ℝ) < DominantFiveBody.nestedOuterWSq t eta alpha y j) →
              (∀ (i : Fin (3 : ℕ)),
                  DominantFiveBody.nestedChartPoints t eta alpha y (3 : DominantFiveBody.Satellite) ≠
                    DominantFiveBody.nestedChartPoints t eta alpha y i.castSucc) →
                DominantFiveBody.nestedChartExtendedRows eps t eta alpha y =
                  DominantFiveBody.nestedChartPhysicalRows eps t eta alpha y := @DominantFiveBody.nestedChartExtendedRows_eq_physical

-- Source binding: eq:hadamard
example : ∀ (K : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)),
  IsOpen U →
    ContDiffOn ℝ (1 : ℕ∞ω) K U →
      ∀ (rho v t u z : ℝ),
        t ≠ (0 : ℝ) →
          (∀ s ∈ Set.Icc (0 : ℝ) (1 : ℝ), (rho + s * (t * u), v + s * (t * z)) ∈ U) →
            (K (rho + t * u, v + t * z) - K (rho, v)) / t =
              ∫ (s : ℝ) in (0 : ℝ)..(1 : ℝ),
                u * (fderiv ℝ K (rho + s * (t * u), v + s * (t * z)) : ℝ × ℝ → ℝ) ((1 : ℝ), (0 : ℝ)) +
                  z * (fderiv ℝ K (rho + s * (t * u), v + s * (t * z)) : ℝ × ℝ → ℝ) ((0 : ℝ), (1 : ℝ)) := @DominantFiveBody.hadamard_target_difference

-- Source binding: display:521
example : ∀ (R t wi wj zi zj : ℝ),
  DominantFiveBody.singleScaleWSq R t wi wj zi zj =
    (wi - wj) ^ (2 : ℕ) +
      (R + t * wi) * (R + t * wj) * (zi - zj) ^ (2 : ℕ) * Real.sinc (t * (zi - zj) / (2 : ℝ)) ^ (2 : ℕ) := @DominantFiveBody.singleScaleWSq_formula_complete

-- Source binding: display:521
example : ∀ (R psi t wi wj zi zj : ℝ),
  ‖DominantFiveBody.polarPoint (DominantFiveBody.singleScaleRadius R t wi)
            (DominantFiveBody.singleScaleAngle psi t zi) -
          DominantFiveBody.polarPoint (DominantFiveBody.singleScaleRadius R t wj)
            (DominantFiveBody.singleScaleAngle psi t zj)‖ ^
      (2 : ℕ) =
    t ^ (2 : ℕ) * DominantFiveBody.singleScaleWSq R t wi wj zi zj := @DominantFiveBody.singleScale_distance_sq

-- Source binding: display:521
example : ∀ (R psi t wi wj zi zj : ℝ),
  (0 : ℝ) < t →
    (0 : ℝ) < DominantFiveBody.singleScaleWSq R t wi wj zi zj →
      ‖DominantFiveBody.polarPoint (DominantFiveBody.singleScaleRadius R t wi)
              (DominantFiveBody.singleScaleAngle psi t zi) -
            DominantFiveBody.polarPoint (DominantFiveBody.singleScaleRadius R t wj)
              (DominantFiveBody.singleScaleAngle psi t zj)‖ =
        t * DominantFiveBody.singleScaleW R t wi wj zi zj := @DominantFiveBody.singleScale_distance

-- Source binding: eq:regular-int
example : ∀ (p : DominantFiveBody.SingleScaleVariables) (psi : ℝ),
  (0 : ℝ) < p (1 : Fin (8 : ℕ)) →
    (0 : ℝ) <
        DominantFiveBody.singleScaleWSq (p (0 : Fin (8 : ℕ))) (p (1 : Fin (8 : ℕ))) (p (2 : Fin (8 : ℕ)))
          (p (3 : Fin (8 : ℕ))) (p (4 : Fin (8 : ℕ))) (p (5 : Fin (8 : ℕ))) →
      DominantFiveBody.singleScaleRadialTerm p =
        -p (6 : Fin (8 : ℕ)) * (p (1 : Fin (8 : ℕ)) ^ (3 : ℕ) * p (7 : Fin (8 : ℕ))) *
            (DominantFiveBody.singleScaleRadius (p (0 : Fin (8 : ℕ))) (p (1 : Fin (8 : ℕ))) (p (2 : Fin (8 : ℕ))) -
              DominantFiveBody.singleScaleRadius (p (0 : Fin (8 : ℕ))) (p (1 : Fin (8 : ℕ))) (p (3 : Fin (8 : ℕ))) *
                Real.cos
                  (DominantFiveBody.singleScaleAngle psi (p (1 : Fin (8 : ℕ))) (p (4 : Fin (8 : ℕ))) -
                    DominantFiveBody.singleScaleAngle psi (p (1 : Fin (8 : ℕ))) (p (5 : Fin (8 : ℕ))))) /
          ‖DominantFiveBody.polarPoint
                  (DominantFiveBody.singleScaleRadius (p (0 : Fin (8 : ℕ))) (p (1 : Fin (8 : ℕ))) (p (2 : Fin (8 : ℕ))))
                  (DominantFiveBody.singleScaleAngle psi (p (1 : Fin (8 : ℕ))) (p (4 : Fin (8 : ℕ)))) -
                DominantFiveBody.polarPoint
                  (DominantFiveBody.singleScaleRadius (p (0 : Fin (8 : ℕ))) (p (1 : Fin (8 : ℕ))) (p (3 : Fin (8 : ℕ))))
                  (DominantFiveBody.singleScaleAngle psi (p (1 : Fin (8 : ℕ))) (p (5 : Fin (8 : ℕ))))‖ ^
            (3 : ℕ) := @DominantFiveBody.singleScaleRadialTerm_eq_physical

-- Source binding: eq:regular-int
example : ∀ (p : DominantFiveBody.SingleScaleVariables) (psi : ℝ),
  (0 : ℝ) < p (1 : Fin (8 : ℕ)) →
    (0 : ℝ) <
        DominantFiveBody.singleScaleWSq (p (0 : Fin (8 : ℕ))) (p (1 : Fin (8 : ℕ))) (p (2 : Fin (8 : ℕ)))
          (p (3 : Fin (8 : ℕ))) (p (4 : Fin (8 : ℕ))) (p (5 : Fin (8 : ℕ))) →
      (1 : ℝ) + p (6 : Fin (8 : ℕ)) ≠ (0 : ℝ) →
        DominantFiveBody.singleScaleAngularTerm p =
          p (1 : Fin (8 : ℕ)) ^ (3 : ℕ) * p (7 : Fin (8 : ℕ)) *
                  DominantFiveBody.singleScaleRadius (p (0 : Fin (8 : ℕ))) (p (1 : Fin (8 : ℕ))) (p (2 : Fin (8 : ℕ))) *
                DominantFiveBody.singleScaleRadius (p (0 : Fin (8 : ℕ))) (p (1 : Fin (8 : ℕ))) (p (3 : Fin (8 : ℕ))) *
              Real.sin
                (DominantFiveBody.singleScaleAngle psi (p (1 : Fin (8 : ℕ))) (p (5 : Fin (8 : ℕ))) -
                  DominantFiveBody.singleScaleAngle psi (p (1 : Fin (8 : ℕ))) (p (4 : Fin (8 : ℕ)))) *
            ((‖DominantFiveBody.polarPoint
                        (DominantFiveBody.singleScaleRadius (p (0 : Fin (8 : ℕ))) (p (1 : Fin (8 : ℕ)))
                          (p (2 : Fin (8 : ℕ))))
                        (DominantFiveBody.singleScaleAngle psi (p (1 : Fin (8 : ℕ))) (p (4 : Fin (8 : ℕ)))) -
                      DominantFiveBody.polarPoint
                        (DominantFiveBody.singleScaleRadius (p (0 : Fin (8 : ℕ))) (p (1 : Fin (8 : ℕ)))
                          (p (3 : Fin (8 : ℕ))))
                        (DominantFiveBody.singleScaleAngle psi (p (1 : Fin (8 : ℕ))) (p (5 : Fin (8 : ℕ))))‖ ^
                  (3 : ℕ))⁻¹ -
              ((1 : ℝ) + p (6 : Fin (8 : ℕ)))⁻¹) := @DominantFiveBody.singleScaleAngularTerm_eq_physical

-- Source binding: eq:regular-int
example : ∀ (eps t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  (0 : ℝ) < t →
    (∀ (j : DominantFiveBody.TripleLabel), j ≠ i → (0 : ℝ) < DominantFiveBody.tripleChartWSq t alpha y i j) →
      DominantFiveBody.tripleInternalRadial eps t alpha y i =
        ∑ j ∈ Finset.univ.erase i,
          -eps * DominantFiveBody.tripleChartMass t alpha (Fin.castSucc j) *
              (DominantFiveBody.tripleChartRadii t alpha y (Fin.castSucc i) -
                DominantFiveBody.tripleChartRadii t alpha y (Fin.castSucc j) *
                  Real.cos
                    (DominantFiveBody.tripleChartAngles t alpha y (Fin.castSucc i) -
                      DominantFiveBody.tripleChartAngles t alpha y (Fin.castSucc j))) /
            DominantFiveBody.satelliteDistance (DominantFiveBody.tripleChartPoints t alpha y) (Fin.castSucc i)
                (Fin.castSucc j) ^
              (3 : ℕ) := @DominantFiveBody.tripleInternalRadial_eq_physical

-- Source binding: eq:regular-int
example : ∀ (eps t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  (0 : ℝ) < t →
    (∀ (j : DominantFiveBody.TripleLabel), j ≠ i → (0 : ℝ) < DominantFiveBody.tripleChartWSq t alpha y i j) →
      (1 : ℝ) + eps ≠ (0 : ℝ) →
        DominantFiveBody.tripleInternalAngular eps t alpha y i =
          ∑ j ∈ Finset.univ.erase i,
            DominantFiveBody.tripleChartMass t alpha (Fin.castSucc j) *
                    DominantFiveBody.tripleChartRadii t alpha y (Fin.castSucc i) *
                  DominantFiveBody.tripleChartRadii t alpha y (Fin.castSucc j) *
                Real.sin
                  (DominantFiveBody.tripleChartAngles t alpha y (Fin.castSucc j) -
                    DominantFiveBody.tripleChartAngles t alpha y (Fin.castSucc i)) *
              ((DominantFiveBody.satelliteDistance (DominantFiveBody.tripleChartPoints t alpha y) (Fin.castSucc i)
                      (Fin.castSucc j) ^
                    (3 : ℕ))⁻¹ -
                ((1 : ℝ) + eps)⁻¹) := @DominantFiveBody.tripleInternalAngular_eq_physical

-- Source binding: eq:regular-int
example : ∀ (eps t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  DominantFiveBody.tripleInternalRadial eps t alpha y i =
    -eps * t *
      ∑ j ∈ Finset.univ.erase i,
        alpha j *
            (DominantFiveBody.tripleChartRadialPositions alpha y i -
                DominantFiveBody.tripleChartRadialPositions alpha y j +
              DominantFiveBody.tripleChartRadii t alpha y (Fin.castSucc j) *
                DominantFiveBody.singleScaleChi t
                  (DominantFiveBody.tripleChartAngularPositions alpha y i -
                    DominantFiveBody.tripleChartAngularPositions alpha y j)) *
          (DominantFiveBody.tripleChartW t alpha y i j ^ (3 : ℕ))⁻¹ := @DominantFiveBody.tripleInternalRadial_source_formula

-- Source binding: eq:regular-int
example : ∀ (eps t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  DominantFiveBody.tripleInternalAngular eps t alpha y i =
    -t *
      ∑ j ∈ Finset.univ.erase i,
        alpha j * DominantFiveBody.tripleChartRadii t alpha y (Fin.castSucc i) *
                DominantFiveBody.tripleChartRadii t alpha y (Fin.castSucc j) *
              (DominantFiveBody.tripleChartAngularPositions alpha y i -
                DominantFiveBody.tripleChartAngularPositions alpha y j) *
            Real.sinc
              (t *
                (DominantFiveBody.tripleChartAngularPositions alpha y i -
                  DominantFiveBody.tripleChartAngularPositions alpha y j)) *
          ((DominantFiveBody.tripleChartW t alpha y i j ^ (3 : ℕ))⁻¹ - t ^ (3 : ℕ) / ((1 : ℝ) + eps)) := @DominantFiveBody.tripleInternalAngular_source_formula

-- Source binding: eq:regular-int
example : ∀ (eps t alpha : ℝ) (y : DominantFiveBody.PairChartVariables),
  alpha * DominantFiveBody.pairInternalRadialA eps t alpha y +
      ((1 : ℝ) - alpha) * DominantFiveBody.pairInternalRadialB eps t alpha y =
    -eps * alpha * ((1 : ℝ) - alpha) *
          (DominantFiveBody.pairChartRadii t alpha y (0 : DominantFiveBody.Satellite) +
            DominantFiveBody.pairChartRadii t alpha y (1 : DominantFiveBody.Satellite)) *
        ((1 : ℝ) - Real.cos (t * y (6 : Fin (7 : ℕ)))) *
      (DominantFiveBody.pairChartW t alpha y ^ (3 : ℕ))⁻¹ := @DominantFiveBody.pairInternal_weighted_radial_source

-- Source binding: prose:532
example : ∀ (n : ℕ∞ω) (p : DominantFiveBody.SingleScaleVariables),
  (0 : ℝ) <
      DominantFiveBody.singleScaleWSq (p (0 : Fin (8 : ℕ))) (p (1 : Fin (8 : ℕ))) (p (2 : Fin (8 : ℕ)))
        (p (3 : Fin (8 : ℕ))) (p (4 : Fin (8 : ℕ))) (p (5 : Fin (8 : ℕ))) →
    ContDiffAt ℝ n DominantFiveBody.singleScaleRadialTerm p := @DominantFiveBody.singleScaleRadialTerm_contDiffAt

-- Source binding: prose:532
example : ∀ (n : ℕ∞ω) (p : DominantFiveBody.SingleScaleVariables),
  (0 : ℝ) <
      DominantFiveBody.singleScaleWSq (p (0 : Fin (8 : ℕ))) (p (1 : Fin (8 : ℕ))) (p (2 : Fin (8 : ℕ)))
        (p (3 : Fin (8 : ℕ))) (p (4 : Fin (8 : ℕ))) (p (5 : Fin (8 : ℕ))) →
    (1 : ℝ) + p (6 : Fin (8 : ℕ)) ≠ (0 : ℝ) → ContDiffAt ℝ n DominantFiveBody.singleScaleAngularTerm p := @DominantFiveBody.singleScaleAngularTerm_contDiffAt

-- Source binding: prose:532
example : ∀ {n : ℕ} (eps t R : ℝ) (alpha w z : Fin n → ℝ),
  ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, DominantFiveBody.singleScaleWeightedAngularPair eps t R alpha w z i j =
    (0 : ℝ) := @DominantFiveBody.singleScale_internal_weighted_angular_sum

-- Source binding: prose:532
example : ∀ {n : ℕ} (eps t R : ℝ) (alpha w z : Fin n → ℝ) (i j : Fin n),
  DominantFiveBody.singleScaleWeightedRadialPair eps t R alpha w z i j +
      DominantFiveBody.singleScaleWeightedRadialPair eps t R alpha w z j i =
    -eps * alpha i * alpha j *
          (DominantFiveBody.singleScaleRadius R t (w i) + DominantFiveBody.singleScaleRadius R t (w j)) *
        ((1 : ℝ) - Real.cos (t * (z i - z j))) *
      (DominantFiveBody.singleScaleW R t (w i) (w j) (z i) (z j) ^ (3 : ℕ))⁻¹ := @DominantFiveBody.singleScaleWeightedRadialPair_pair_sum

-- Source binding: prose:532
example : ∀ (eps t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  ∑ i : DominantFiveBody.TripleLabel, alpha i * DominantFiveBody.tripleInternalAngular eps t alpha y i = (0 : ℝ) := @DominantFiveBody.tripleInternal_weighted_angular_zero

-- Source binding: display:533
example : ∀ (eps t R : ℝ) (alpha w z : Fin (3 : ℕ) → ℝ),
  ∑ i : Fin (3 : ℕ), ∑ j ∈ Finset.univ.erase i, DominantFiveBody.singleScaleWeightedRadialPair eps t R alpha w z i j =
    ∑ i : Fin (3 : ℕ),
      ∑ j : Fin (3 : ℕ) with i < j,
        -eps * alpha i * alpha j *
              (DominantFiveBody.singleScaleRadius R t (w i) + DominantFiveBody.singleScaleRadius R t (w j)) *
            ((1 : ℝ) - Real.cos (t * (z i - z j))) *
          (DominantFiveBody.singleScaleW R t (w i) (w j) (z i) (z j) ^ (3 : ℕ))⁻¹ := @DominantFiveBody.singleScale_three_weighted_radial_sum

-- Source binding: display:533
example : ∀ (eps t R : ℝ) (alpha w z : Fin (2 : ℕ) → ℝ),
  ∑ i : Fin (2 : ℕ), ∑ j ∈ Finset.univ.erase i, DominantFiveBody.singleScaleWeightedRadialPair eps t R alpha w z i j =
    -eps * alpha (0 : Fin (2 : ℕ)) * alpha (1 : Fin (2 : ℕ)) *
          (DominantFiveBody.singleScaleRadius R t (w (0 : Fin (2 : ℕ))) +
            DominantFiveBody.singleScaleRadius R t (w (1 : Fin (2 : ℕ)))) *
        ((1 : ℝ) - Real.cos (t * (z (0 : Fin (2 : ℕ)) - z (1 : Fin (2 : ℕ))))) *
      (DominantFiveBody.singleScaleW R t (w (0 : Fin (2 : ℕ))) (w (1 : Fin (2 : ℕ))) (z (0 : Fin (2 : ℕ)))
            (z (1 : Fin (2 : ℕ))) ^
          (3 : ℕ))⁻¹ := @DominantFiveBody.singleScale_pair_weighted_radial_sum

-- Source binding: display:533
example : ∀ (eps t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  ∑ i : DominantFiveBody.TripleLabel, alpha i * DominantFiveBody.tripleInternalRadial eps t alpha y i =
    ∑ i : DominantFiveBody.TripleLabel,
      ∑ j : DominantFiveBody.TripleLabel with i < j,
        -eps * alpha i * alpha j *
              (DominantFiveBody.tripleChartRadii t alpha y (Fin.castSucc i) +
                DominantFiveBody.tripleChartRadii t alpha y (Fin.castSucc j)) *
            ((1 : ℝ) -
              Real.cos
                (t *
                  (DominantFiveBody.tripleChartAngularPositions alpha y i -
                    DominantFiveBody.tripleChartAngularPositions alpha y j))) *
          (DominantFiveBody.tripleChartW t alpha y i j ^ (3 : ℕ))⁻¹ := @DominantFiveBody.tripleInternal_weighted_radial_upper_sum

-- Source binding: prose:537
example : ∀ (n : ℕ∞ω) (v : DominantFiveBody.PairJointVariables),
  DominantFiveBody.PairChartRegular (v.1 (0 : Fin (4 : ℕ))) (v.1 (1 : Fin (4 : ℕ))) (v.1 (3 : Fin (4 : ℕ))) v.2 →
    ∀ (i : DominantFiveBody.Satellite),
      i = (0 : DominantFiveBody.Satellite) ∨ i = (1 : DominantFiveBody.Satellite) →
        ContDiffAt ℝ n
          (fun (w : DominantFiveBody.PairJointVariables) =>
            DominantFiveBody.pairRadialExterior (w.1 (0 : Fin (4 : ℕ))) (w.1 (1 : Fin (4 : ℕ))) (w.1 (2 : Fin (4 : ℕ)))
              (w.1 (3 : Fin (4 : ℕ))) w.2 i)
          v := @DominantFiveBody.pairRadialExterior_joint_contDiffAt

-- Source binding: prose:537
example : ∀ (n : ℕ∞ω) (v : DominantFiveBody.PairJointVariables),
  DominantFiveBody.PairChartRegular (v.1 (0 : Fin (4 : ℕ))) (v.1 (1 : Fin (4 : ℕ))) (v.1 (3 : Fin (4 : ℕ))) v.2 →
    ∀ (i : DominantFiveBody.Satellite),
      i = (0 : DominantFiveBody.Satellite) ∨ i = (1 : DominantFiveBody.Satellite) →
        ContDiffAt ℝ n
          (fun (w : DominantFiveBody.PairJointVariables) =>
            DominantFiveBody.pairAngularExterior (w.1 (0 : Fin (4 : ℕ))) (w.1 (1 : Fin (4 : ℕ))) (w.1 (2 : Fin (4 : ℕ)))
              (w.1 (3 : Fin (4 : ℕ))) w.2 i)
          v := @DominantFiveBody.pairAngularExterior_joint_contDiffAt

-- Source binding: prose:537
example : ∀ (n : ℕ∞ω) (v : DominantFiveBody.TripleJointVariables),
  DominantFiveBody.TripleChartRegular (v.1 (0 : Fin (5 : ℕ))) (v.1 (1 : Fin (5 : ℕ)))
      (DominantFiveBody.tripleJointAlpha v.1) v.2 →
    ∀ (i : DominantFiveBody.TripleLabel),
      ContDiffAt ℝ n
        (fun (w : DominantFiveBody.TripleJointVariables) =>
          DominantFiveBody.tripleRadialExterior (w.1 (0 : Fin (5 : ℕ))) (w.1 (1 : Fin (5 : ℕ)))
            (DominantFiveBody.tripleJointAlpha w.1) w.2 i)
        v := @DominantFiveBody.tripleRadialExterior_joint_contDiffAt

-- Source binding: prose:537
example : ∀ (n : ℕ∞ω) (v : DominantFiveBody.TripleJointVariables),
  DominantFiveBody.TripleChartRegular (v.1 (0 : Fin (5 : ℕ))) (v.1 (1 : Fin (5 : ℕ)))
      (DominantFiveBody.tripleJointAlpha v.1) v.2 →
    ∀ (i : DominantFiveBody.TripleLabel),
      ContDiffAt ℝ n
        (fun (w : DominantFiveBody.TripleJointVariables) =>
          DominantFiveBody.tripleAngularExterior (w.1 (0 : Fin (5 : ℕ))) (w.1 (1 : Fin (5 : ℕ)))
            (DominantFiveBody.tripleJointAlpha w.1) w.2 i)
        v := @DominantFiveBody.tripleAngularExterior_joint_contDiffAt

-- Source binding: prose:539
example : ∀ (mu theta : DominantFiveBody.Satellite → ℝ),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) ≤ mu i) →
    ∑ i : DominantFiveBody.Satellite, mu i = (1 : ℝ) →
      DominantFiveBody.SeparatedSemicircle theta →
        (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.coorbitalResidual mu theta i = (0 : ℝ)) →
          ∃ (p : DominantFiveBody.Satellite) (y : DominantFiveBody.SliceCoordinates),
            (1 / 4 : ℝ) ≤ mu p ∧
              (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.sliceRadii y i = (1 : ℝ)) ∧
                (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.fixedAngleAngles p y i = theta i - theta p) ∧
                  DominantFiveBody.SeparatedSemicircle (DominantFiveBody.sliceAngles y) ∧
                    DominantFiveBody.fixedAngleDeletedResidual ((0 : ℝ), mu) p p y =
                        (0 : DominantFiveBody.SliceCoordinates) ∧
                      (fderiv ℝ (DominantFiveBody.fixedAngleDeletedResidual ((0 : ℝ), mu) p p) y).IsInvertible ∧
                        ContDiffAt ℝ ∞
                          (fun (z : DominantFiveBody.ContinuationParameter × DominantFiveBody.SliceCoordinates) =>
                            DominantFiveBody.reducedResidual z.1 z.2)
                          (((0 : ℝ),
                              mu ∘
                                (⇑(DominantFiveBody.fixedAnglePermutation p) :
                                  DominantFiveBody.Satellite → DominantFiveBody.Satellite)),
                            y) := @DominantFiveBody.closedCoorbital_largest_mass_gauge

-- Source binding: prose:539
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (p : DominantFiveBody.Satellite),
  DominantFiveBody.fixedAngleDeletedResidual (eps, mu) p p =
    DominantFiveBody.reducedResidual
      (eps,
        mu ∘ (⇑(DominantFiveBody.fixedAnglePermutation p) : DominantFiveBody.Satellite → DominantFiveBody.Satellite)) := @DominantFiveBody.fixedAngleDeletedResidual_same_eq

-- Source binding: prose:539
example : ∀ (μ : DominantFiveBody.MassRatio) (y : DominantFiveBody.SliceCoordinates),
  (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.sliceRadii y i = (1 : ℝ)) →
    (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) ≤ μ i) →
      ∑ i : DominantFiveBody.Satellite, μ i = (1 : ℝ) →
        (0 : ℝ) < μ (0 : DominantFiveBody.Satellite) →
          DominantFiveBody.SeparatedSemicircle (DominantFiveBody.sliceAngles y) →
            (∀ (i : DominantFiveBody.Satellite),
                DominantFiveBody.coorbitalResidual μ (DominantFiveBody.sliceAngles y) i = (0 : ℝ)) →
              ∃ (e : Equiv.Perm DominantFiveBody.Satellite) (η : ℝ) (r : ℝ) (C : ℝ),
                (0 : ℝ) < η ∧
                  (0 : ℝ) < r ∧
                    (0 : ℝ) < C ∧
                      ∃ (ψ : DominantFiveBody.ContinuationParameter → DominantFiveBody.SliceCoordinates),
                        DominantFiveBody.OrderedSemicircle
                            (DominantFiveBody.sliceAngles y ∘
                              (⇑e : DominantFiveBody.Satellite → DominantFiveBody.Satellite)) ∧
                          ψ ((0 : ℝ), μ) = y ∧
                            ContDiffOn ℝ ∞ ψ (Metric.ball ((0 : ℝ), μ) η) ∧
                              ∀ (ε : ℝ) (ν : DominantFiveBody.MassRatio),
                                |ε| < η →
                                  Dist.dist ν μ < η →
                                    DominantFiveBody.StrictConvexInOrder (DominantFiveBody.satelliteHullOrder e)
                                        (DominantFiveBody.slicePhysicalConfiguration (ε, ν) (ψ (ε, ν))) ∧
                                      DominantFiveBody.OrderedSemicircle
                                          (DominantFiveBody.sliceAngles (ψ (ε, ν)) ∘
                                            (⇑e : DominantFiveBody.Satellite → DominantFiveBody.Satellite)) ∧
                                        Dist.dist (ψ (ε, ν)) y < r / (2 : ℝ) ∧
                                          DominantFiveBody.SliceRegular (ε, ν) (ψ (ε, ν)) ∧
                                            (DominantFiveBody.reducedJacobian (ε, ν) (ψ (ε, ν))).IsInvertible ∧
                                              ‖(DominantFiveBody.reducedJacobian (ε, ν) (ψ (ε, ν))).inverse‖ ≤ C ∧
                                                DominantFiveBody.reducedResidual (ε, ν) (ψ (ε, ν)) =
                                                    (0 : DominantFiveBody.SliceCoordinates) ∧
                                                  (∀ (z : DominantFiveBody.SliceCoordinates),
                                                      Dist.dist z y < r →
                                                        (DominantFiveBody.reducedResidual (ε, ν) z =
                                                            (0 : DominantFiveBody.SliceCoordinates) ↔
                                                          ψ (ε, ν) = z)) ∧
                                                    ((0 : ℝ) < ε →
                                                        DominantFiveBody.PositiveRatio ν →
                                                          DominantFiveBody.NormalizedCentralConfiguration
                                                              (DominantFiveBody.masses ε ν)
                                                              (DominantFiveBody.slicePhysicalConfiguration (ε, ν)
                                                                (ψ (ε, ν))) ∧
                                                            DominantFiveBody.StrictConvexCentralConfiguration
                                                                (DominantFiveBody.masses ε ν)
                                                                (DominantFiveBody.satelliteHullOrder e)
                                                                (DominantFiveBody.slicePhysicalConfiguration (ε, ν)
                                                                  (ψ (ε, ν))) ∧
                                                              DominantFiveBody.ShapeHessianNondegenerate
                                                                (DominantFiveBody.masses ε ν) (1 : ℝ)
                                                                (DominantFiveBody.slicePhysicalConfiguration (ε, ν)
                                                                  (ψ (ε, ν)))) ∧
                                                      (ε = (0 : ℝ) →
                                                        DominantFiveBody.PositiveRatio ν →
                                                          (∀ (i : DominantFiveBody.Satellite),
                                                              DominantFiveBody.sliceRadii (ψ (ε, ν)) i = (1 : ℝ)) ∧
                                                            DominantFiveBody.RelativeCollisionFree
                                                                (DominantFiveBody.sliceSatellites (ψ (ε, ν))) ∧
                                                              (∀ (i : DominantFiveBody.Satellite),
                                                                  DominantFiveBody.coorbitalResidual ν
                                                                      (DominantFiveBody.sliceAngles (ψ (ε, ν))) i =
                                                                    (0 : ℝ)) ∧
                                                                DominantFiveBody.coorbitalRootAngles
                                                                    (ν ∘
                                                                      (⇑e :
                                                                        DominantFiveBody.Satellite →
                                                                          DominantFiveBody.Satellite)) =
                                                                  fun (i : DominantFiveBody.Satellite) =>
                                                                  DominantFiveBody.sliceAngles (ψ (ε, ν))
                                                                      ((e :
                                                                          DominantFiveBody.Satellite →
                                                                            DominantFiveBody.Satellite)
                                                                        i) -
                                                                    DominantFiveBody.sliceAngles (ψ (ε, ν))
                                                                      ((e :
                                                                          DominantFiveBody.Satellite →
                                                                            DominantFiveBody.Satellite)
                                                                        (0 : DominantFiveBody.Satellite))) := @DominantFiveBody.noCollision_physical_local_continuation

-- Source binding: prose:539
example : ∀ (μ : DominantFiveBody.MassRatio) (y : DominantFiveBody.SliceCoordinates),
  (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.sliceRadii y i = (1 : ℝ)) →
    (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) ≤ μ i) →
      ∑ i : DominantFiveBody.Satellite, μ i = (1 : ℝ) →
        (0 : ℝ) < μ (0 : DominantFiveBody.Satellite) →
          DominantFiveBody.SeparatedSemicircle (DominantFiveBody.sliceAngles y) →
            (∀ (i : DominantFiveBody.Satellite),
                DominantFiveBody.coorbitalResidual μ (DominantFiveBody.sliceAngles y) i = (0 : ℝ)) →
              (DominantFiveBody.reducedJacobian ((0 : ℝ), μ) y).IsInvertible := @DominantFiveBody.reducedJacobian_at_closed_separated_root_isInvertible

-- Source binding: display:541
example : ∀ (mu : DominantFiveBody.MassRatio) (p : DominantFiveBody.Satellite) (y : DominantFiveBody.SliceCoordinates),
  (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.sliceRadii y i = (1 : ℝ)) →
    DominantFiveBody.SeparatedSemicircle (DominantFiveBody.sliceAngles y) →
      ∃ (L : Matrix (Fin (3 : ℕ)) (Fin (4 : ℕ)) ℝ),
        ((LinearMap.toMatrix' : ((Fin (7 : ℕ) → ℝ) →ₗ[ℝ] Fin (7 : ℕ) → ℝ) → Matrix (Fin (7 : ℕ)) (Fin (7 : ℕ)) ℝ)
                (↑(fderiv ℝ (DominantFiveBody.fixedAngleDeletedResidual ((0 : ℝ), mu) p p) y) :
                  DominantFiveBody.SliceCoordinates →ₗ[ℝ] DominantFiveBody.SliceCoordinates)).submatrix
            (⇑finSumFinEquiv : Fin (4 : ℕ) ⊕ Fin (3 : ℕ) → Fin ((4 : ℕ) + (3 : ℕ)))
            (⇑finSumFinEquiv : Fin (4 : ℕ) ⊕ Fin (3 : ℕ) → Fin ((4 : ℕ) + (3 : ℕ))) =
          Matrix.fromBlocks ((3 : ℝ) • (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) ℝ))
            (0 : Matrix (Fin (4 : ℕ)) (Fin (3 : ℕ)) ℝ) L
            (DominantFiveBody.deletedAngularJacobian
              (mu ∘
                (⇑(DominantFiveBody.fixedAnglePermutation p) : DominantFiveBody.Satellite → DominantFiveBody.Satellite))
              (DominantFiveBody.sliceAngles y) (0 : DominantFiveBody.Satellite) (0 : DominantFiveBody.Satellite)) := @DominantFiveBody.fixedAngle_zero_source_full_block

-- Source binding: display:541
example : ∀ (mu : DominantFiveBody.MassRatio) (y : DominantFiveBody.SliceCoordinates),
  DominantFiveBody.SliceRegular ((0 : ℝ), mu) y →
    (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.sliceRadii y i = (1 : ℝ)) →
      DominantFiveBody.SeparatedSemicircle (DominantFiveBody.sliceAngles y) →
        (LinearMap.toMatrix' : ((Fin (3 : ℕ) → ℝ) →ₗ[ℝ] Fin (3 : ℕ) → ℝ) → Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) ℝ)
            (↑(DominantFiveBody.reducedAngularJacobian ((0 : ℝ), mu) y) : (Fin (3 : ℕ) → ℝ) →ₗ[ℝ] Fin (3 : ℕ) → ℝ) =
          DominantFiveBody.deletedAngularJacobian mu (DominantFiveBody.sliceAngles y) (0 : DominantFiveBody.Satellite)
            (0 : DominantFiveBody.Satellite) := @DominantFiveBody.reducedAngularJacobian_zero_full_matrix

-- Source binding: prose:544
example : ∀ (μ : DominantFiveBody.MassRatio) (y₀ : DominantFiveBody.SliceCoordinates),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) ≤ μ i) →
    ∑ i : DominantFiveBody.Satellite, μ i = (1 : ℝ) →
      (0 : ℝ) < μ (0 : DominantFiveBody.Satellite) →
        DominantFiveBody.SliceRegular ((0 : ℝ), μ) y₀ →
          DominantFiveBody.SeparatedSemicircle (DominantFiveBody.sliceAngles y₀) →
            ∀ (ν : ℕ → DominantFiveBody.MassRatio) (ε : ℕ → ℝ) (y : ℕ → DominantFiveBody.SliceCoordinates),
              (∀ (n : ℕ), DominantFiveBody.PositiveRatio (ν n)) →
                (∀ (n : ℕ), (0 : ℝ) < ε n) →
                  Filter.Tendsto ν Filter.atTop (𝓝 μ) →
                    Filter.Tendsto ε Filter.atTop (𝓝 (0 : ℝ)) →
                      Filter.Tendsto y Filter.atTop (𝓝 y₀) →
                        (∀ (n : ℕ),
                            DominantFiveBody.reducedResidual (ε n, ν n) (y n) =
                              (0 : DominantFiveBody.SliceCoordinates)) →
                          Nonempty (DominantFiveBody.NoCollisionCapturedBranches ν ε y) := @DominantFiveBody.noCollision_actual_sequence_capture_of_regular_limit

-- Source binding: eq:pair-chart-mass
example : ∀ (t p alpha : ℝ) (y : DominantFiveBody.PairChartVariables),
  DominantFiveBody.pairChartMass t p alpha =
      ![t ^ (3 : ℕ) * alpha, t ^ (3 : ℕ) * ((1 : ℝ) - alpha), ((1 : ℝ) - t ^ (3 : ℕ)) * p,
        ((1 : ℝ) - t ^ (3 : ℕ)) * ((1 : ℝ) - p)] ∧
    DominantFiveBody.pairChartRadii t alpha y =
        ![y (2 : Fin (7 : ℕ)) - ((1 : ℝ) - alpha) * t * y (3 : Fin (7 : ℕ)),
          y (2 : Fin (7 : ℕ)) + alpha * t * y (3 : Fin (7 : ℕ)), y (0 : Fin (7 : ℕ)), y (1 : Fin (7 : ℕ))] ∧
      DominantFiveBody.pairChartAngles t alpha y =
        ![y (5 : Fin (7 : ℕ)) - ((1 : ℝ) - alpha) * t * y (6 : Fin (7 : ℕ)),
          y (5 : Fin (7 : ℕ)) + alpha * t * y (6 : Fin (7 : ℕ)), (0 : ℝ), y (4 : Fin (7 : ℕ))] := @DominantFiveBody.pairChart_coordinates_complete

-- Source binding: display:557
example : ∀ (eps t p alpha p0 : ℝ) (y : DominantFiveBody.PairChartVariables),
  have R :=
    DominantFiveBody.radialResidual eps (DominantFiveBody.pairChartMass t p alpha)
      (DominantFiveBody.pairChartRadii t alpha y) (DominantFiveBody.pairChartAngles t alpha y);
  have T :=
    DominantFiveBody.angularResidual eps (DominantFiveBody.pairChartMass t p alpha)
      (DominantFiveBody.pairChartRadii t alpha y) (DominantFiveBody.pairChartAngles t alpha y);
  DominantFiveBody.pairChartPhysicalRows eps t p alpha (DominantFiveBody.pairSourceKeepD p0) y =
    ![R (2 : DominantFiveBody.Satellite), R (3 : DominantFiveBody.Satellite),
      alpha * R (0 : DominantFiveBody.Satellite) + ((1 : ℝ) - alpha) * R (1 : DominantFiveBody.Satellite),
      (R (1 : DominantFiveBody.Satellite) - R (0 : DominantFiveBody.Satellite)) / t,
      T (if (1 / 2 : ℝ) ≤ p0 then (3 : DominantFiveBody.Satellite) else (2 : DominantFiveBody.Satellite)),
      alpha * T (0 : DominantFiveBody.Satellite) + ((1 : ℝ) - alpha) * T (1 : DominantFiveBody.Satellite),
      (T (1 : DominantFiveBody.Satellite) - T (0 : DominantFiveBody.Satellite)) / t] := @DominantFiveBody.pairChartRows_half_interval_choice

-- Source binding: display:557
example : ∀ (eps t p alpha : ℝ) (keepD : Bool) (y : DominantFiveBody.PairChartVariables),
  t ≠ (0 : ℝ) →
    DominantFiveBody.pairChartMass t p alpha
          (if keepD = Bool.true then (2 : DominantFiveBody.Satellite) else (3 : DominantFiveBody.Satellite)) ≠
        (0 : ℝ) →
      (DominantFiveBody.pairChartPhysicalRows eps t p alpha keepD y = (0 : DominantFiveBody.PairChartVariables) ↔
        (∀ (i : DominantFiveBody.Satellite),
            DominantFiveBody.radialResidual eps (DominantFiveBody.pairChartMass t p alpha)
                (DominantFiveBody.pairChartRadii t alpha y) (DominantFiveBody.pairChartAngles t alpha y) i =
              (0 : ℝ)) ∧
          ∀ (i : DominantFiveBody.Satellite),
            DominantFiveBody.angularResidual eps (DominantFiveBody.pairChartMass t p alpha)
                (DominantFiveBody.pairChartRadii t alpha y) (DominantFiveBody.pairChartAngles t alpha y) i =
              (0 : ℝ)) := @DominantFiveBody.pairChartPhysicalRows_zero_iff

-- Source binding: prose:561
example : ∀ (t p p0 alpha : ℝ),
  t ^ (3 : ℕ) ≤ (1 / 2 : ℝ) →
    |p - p0| ≤ (1 / 4 : ℝ) →
      DominantFiveBody.pairChartMass t p alpha
          (if (1 / 2 : ℝ) ≤ p0 then (2 : DominantFiveBody.Satellite) else (3 : DominantFiveBody.Satellite)) ≥
        (1 / 8 : ℝ) := @DominantFiveBody.pairChart_omitted_mass_lower_fixed_anchor

-- Source binding: prose:561
example : ∀ (t alpha : ℝ), (DominantFiveBody.pairCoordinateMatrix t alpha).det = t := @DominantFiveBody.pairCoordinateMatrix_det

-- Source binding: prose:561
example : ∀ (t alpha : ℝ) (rows : DominantFiveBody.Satellite → ℝ),
  t ≠ (0 : ℝ) →
    rows (0 : DominantFiveBody.Satellite) =
        DominantFiveBody.pairRowAverage alpha rows - ((1 : ℝ) - alpha) * t * DominantFiveBody.pairRowDifference t rows ∧
      rows (1 : DominantFiveBody.Satellite) =
        DominantFiveBody.pairRowAverage alpha rows + alpha * t * DominantFiveBody.pairRowDifference t rows := @DominantFiveBody.pairRows_recovery

-- Source binding: eq:pair-W
example : ∀ (t alpha : ℝ) (y : DominantFiveBody.PairChartVariables),
  DominantFiveBody.pairChartWSq t alpha y =
    y (3 : Fin (7 : ℕ)) ^ (2 : ℕ) +
      DominantFiveBody.pairChartRadii t alpha y (0 : DominantFiveBody.Satellite) *
            DominantFiveBody.pairChartRadii t alpha y (1 : DominantFiveBody.Satellite) *
          y (6 : Fin (7 : ℕ)) ^ (2 : ℕ) *
        Real.sinc (t * y (6 : Fin (7 : ℕ)) / (2 : ℝ)) ^ (2 : ℕ) := @DominantFiveBody.pairChartWSq_formula_complete

-- Source binding: eq:pair-W
example : ∀ (t alpha : ℝ) (y : DominantFiveBody.PairChartVariables),
  DominantFiveBody.satelliteDistance
        (DominantFiveBody.polarSatellites (DominantFiveBody.pairChartRadii t alpha y)
          (DominantFiveBody.pairChartAngles t alpha y))
        (0 : DominantFiveBody.Satellite) (1 : DominantFiveBody.Satellite) ^
      (2 : ℕ) =
    t ^ (2 : ℕ) * DominantFiveBody.pairChartWSq t alpha y := @DominantFiveBody.pairChart_distance_sq

-- Source binding: prose:567
example : ∀ (n : ℕ∞ω) (v : DominantFiveBody.PairJointVariables),
  DominantFiveBody.PairChartRegular (v.1 (0 : Fin (4 : ℕ))) (v.1 (1 : Fin (4 : ℕ))) (v.1 (3 : Fin (4 : ℕ))) v.2 →
    ∀ (keepD : Bool),
      ContDiffAt ℝ n
        (fun (w : DominantFiveBody.PairJointVariables) =>
          DominantFiveBody.pairChartExtendedRows (w.1 (0 : Fin (4 : ℕ))) (w.1 (1 : Fin (4 : ℕ))) (w.1 (2 : Fin (4 : ℕ)))
            (w.1 (3 : Fin (4 : ℕ))) keepD w.2)
        v := @DominantFiveBody.pairChartExtendedRows_joint_contDiffAt

-- Source binding: prose:567
example : ∀ (p psi : ℝ) (keepD : Bool),
  (0 : ℝ) ≤ p →
    p ≤ (1 : ℝ) →
      (if keepD = Bool.true then (0 : ℝ) < p else p < (1 : ℝ)) →
        psi ≠ (0 : ℝ) →
          psi ≠ DominantFiveBody.Coorbital.h →
            DominantFiveBody.twoSourceSpan psi < Real.pi →
              p * DominantFiveBody.coorbitalKernel psi +
                    ((1 : ℝ) - p) * DominantFiveBody.coorbitalKernel (psi - DominantFiveBody.Coorbital.h) =
                  (0 : ℝ) →
                ∀ (tau : ℝ),
                  (0 : ℝ) < tau →
                    have y0 :=
                      DominantFiveBody.pairUnitPoint DominantFiveBody.Coorbital.h psi
                        (DominantFiveBody.pairBoundaryScale
                          (DominantFiveBody.pairProbeDerivative p DominantFiveBody.Coorbital.h psi));
                    ∃ (eta : ℝ) (r : ℝ) (C : ℝ),
                      (0 : ℝ) < eta ∧
                        (0 : ℝ) < r ∧
                          (0 : ℝ) < C ∧
                            r ≤ tau ∧
                              eta ≤ r ∧
                                ∀ alpha ∈ Set.Icc (0 : ℝ) (1 : ℝ),
                                  ∃ (branch :
                                    DominantFiveBody.PairChartParameters → DominantFiveBody.PairChartVariables),
                                    branch ![(0 : ℝ), (0 : ℝ), p, alpha] = y0 ∧
                                      ContDiffOn ℝ ∞ branch (Metric.ball ![(0 : ℝ), (0 : ℝ), p, alpha] eta) ∧
                                        ∀ (q : Fin (Nat.succ (0 : ℕ)).succ.succ.succ → ℝ),
                                          Dist.dist q ![(0 : ℝ), (0 : ℝ), p, alpha] < eta →
                                            Dist.dist (branch q) y0 < r / (2 : ℝ) ∧
                                              DominantFiveBody.PairChartRegular
                                                  (q (0 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                  (q (1 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                  (q (3 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ)) (branch q) ∧
                                                (DominantFiveBody.pairChartJacobian
                                                      (q (0 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                      (q (1 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                      (q (2 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                      (q (3 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ)) keepD
                                                      (branch q)).IsInvertible ∧
                                                  ‖(DominantFiveBody.pairChartJacobian
                                                            (q (0 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                            (q (1 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                            (q (2 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                            (q (3 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ)) keepD
                                                            (branch q)).inverse‖ ≤
                                                      C ∧
                                                    DominantFiveBody.pairChartParameterRows keepD q (branch q) =
                                                        (0 : DominantFiveBody.PairChartVariables) ∧
                                                      ∀ (y : DominantFiveBody.PairChartVariables),
                                                        Dist.dist y y0 < r →
                                                          (DominantFiveBody.pairChartParameterRows keepD q y =
                                                              (0 : DominantFiveBody.PairChartVariables) ↔
                                                            branch q = y) := @DominantFiveBody.pairChart_compact_boundary_continuation

-- Source binding: prose:567
example : ∀ (p alpha : ℝ) (y : DominantFiveBody.PairChartVariables),
  DominantFiveBody.pairRadialMean (0 : ℝ) (0 : ℝ) p alpha y = y (2 : Fin (7 : ℕ)) - (y (2 : Fin (7 : ℕ)) ^ (2 : ℕ))⁻¹ := @DominantFiveBody.pairRadialMean_at_boundary

-- Source binding: prose:567
example : ∀ (p alpha : ℝ) (y : DominantFiveBody.PairChartVariables),
  DominantFiveBody.pairRadialDifference (0 : ℝ) (0 : ℝ) p alpha y =
    y (3 : Fin (7 : ℕ)) *
      ((1 : ℝ) + (2 : ℝ) * y (2 : Fin (7 : ℕ)) / (y (2 : Fin (7 : ℕ)) ^ (2 : ℕ) * y (2 : Fin (7 : ℕ)) ^ (2 : ℕ))) := @DominantFiveBody.pairRadialDifference_at_boundary

-- Source binding: prose:567
example : ∀ (p alpha : ℝ) (keepD : Bool) (y : DominantFiveBody.PairChartVariables) (i : Fin (3 : ℕ)),
  DominantFiveBody.pairChartExtendedRows (0 : ℝ) (0 : ℝ) p alpha keepD y i.castSucc.castSucc.castSucc.castSucc =
    y i.castSucc.castSucc.castSucc.castSucc - (y i.castSucc.castSucc.castSucc.castSucc ^ (2 : ℕ))⁻¹ := @DominantFiveBody.pairChart_boundary_radial

-- Source binding: display:568
example : ∀ (p rc rd omega rho v : ℝ),
  DominantFiveBody.twoSourcePolarAngular p rc rd omega (rho, v) =
    rho *
      (p * rc * Real.sin ((0 : ℝ) - v) *
          ((‖DominantFiveBody.polarPoint rho v - DominantFiveBody.polarPoint rc (0 : ℝ)‖ ^ (3 : ℕ))⁻¹ - (1 : ℝ)) +
        ((1 : ℝ) - p) * rd * Real.sin (omega - v) *
          ((‖DominantFiveBody.polarPoint rho v - DominantFiveBody.polarPoint rd omega‖ ^ (3 : ℕ))⁻¹ - (1 : ℝ))) := @DominantFiveBody.twoSourcePolarAngular_source_formula

-- Source binding: display:568
example : ∀ (p rc rd omega : ℝ) (x v : ℝ × ℝ),
  DominantFiveBody.polarPoint rc (0 : ℝ) ≠ DominantFiveBody.polarPoint x.1 x.2 →
    DominantFiveBody.polarPoint rd omega ≠ DominantFiveBody.polarPoint x.1 x.2 →
      (fderiv ℝ (DominantFiveBody.twoSourcePolarAngular p rc rd omega) x : ℝ × ℝ → ℝ) v =
        Inner.inner ℝ
            ((DominantFiveBody.twoSourceTargetDerivative p rc rd omega (DominantFiveBody.polarPoint x.1 x.2) :
                DominantFiveBody.Plane → DominantFiveBody.Plane)
              ((DominantFiveBody.polarPointDerivative x : ℝ × ℝ → DominantFiveBody.Plane) v))
            (DominantFiveBody.quarterTurn (DominantFiveBody.polarPoint x.1 x.2)) +
          Inner.inner ℝ (DominantFiveBody.twoSourceTargetField p rc rd omega (DominantFiveBody.polarPoint x.1 x.2))
            (DominantFiveBody.quarterTurn
              ((DominantFiveBody.polarPointDerivative x : ℝ × ℝ → DominantFiveBody.Plane) v)) := @DominantFiveBody.twoSourcePolarAngular_fderiv_apply

-- Source binding: eq:pair-boundary
example : ∀ (p alpha : ℝ) (y : DominantFiveBody.PairChartVariables),
  DominantFiveBody.pairAngularMean (0 : ℝ) (0 : ℝ) p alpha y =
    DominantFiveBody.twoSourcePolarAngular p (y (0 : Fin (7 : ℕ))) (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ)))
      (y (2 : Fin (7 : ℕ)), y (5 : Fin (7 : ℕ))) := @DominantFiveBody.pairAngularMean_at_boundary

-- Source binding: eq:pair-boundary
example : ∀ (p alpha : ℝ) (y : DominantFiveBody.PairChartVariables),
  DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ) ≠
      DominantFiveBody.polarPoint (y (2 : Fin (7 : ℕ))) (y (5 : Fin (7 : ℕ))) →
    DominantFiveBody.polarPoint (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ))) ≠
        DominantFiveBody.polarPoint (y (2 : Fin (7 : ℕ))) (y (5 : Fin (7 : ℕ))) →
      DominantFiveBody.pairAngularDifference (0 : ℝ) (0 : ℝ) p alpha y =
        (fderiv ℝ
                (DominantFiveBody.twoSourcePolarAngular p (y (0 : Fin (7 : ℕ))) (y (1 : Fin (7 : ℕ)))
                  (y (4 : Fin (7 : ℕ))))
                (y (2 : Fin (7 : ℕ)), y (5 : Fin (7 : ℕ))) :
              ℝ × ℝ → ℝ)
            (y (3 : Fin (7 : ℕ)), y (6 : Fin (7 : ℕ))) -
          y (2 : Fin (7 : ℕ)) ^ (2 : ℕ) * y (6 : Fin (7 : ℕ)) /
            √(y (3 : Fin (7 : ℕ)) ^ (2 : ℕ) + y (2 : Fin (7 : ℕ)) ^ (2 : ℕ) * y (6 : Fin (7 : ℕ)) ^ (2 : ℕ)) ^ (3 : ℕ) := @DominantFiveBody.pairAngularDifference_at_boundary

-- Source binding: prose:577
example : ∀ (p alpha omega psi z : ℝ) (keepD : Bool),
  DominantFiveBody.PairChartRegular (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.pairUnitPoint omega psi z) →
    ∀ (v : DominantFiveBody.PairChartVariables) (i : Fin (3 : ℕ)),
      (DominantFiveBody.pairChartJacobian (0 : ℝ) (0 : ℝ) p alpha keepD (DominantFiveBody.pairUnitPoint omega psi z) :
            DominantFiveBody.PairChartVariables → DominantFiveBody.PairChartVariables)
          v i.castSucc.castSucc.castSucc.castSucc =
        (3 : ℝ) * v i.castSucc.castSucc.castSucc.castSucc := @DominantFiveBody.pairChartJacobian_unit_radial

-- Source binding: prose:577
example : ∀ (p alpha omega psi z : ℝ) (keepD : Bool),
  DominantFiveBody.PairChartRegular (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.pairUnitPoint omega psi z) →
    ∀ (v : DominantFiveBody.PairChartVariables),
      (DominantFiveBody.pairChartJacobian (0 : ℝ) (0 : ℝ) p alpha keepD (DominantFiveBody.pairUnitPoint omega psi z) :
            DominantFiveBody.PairChartVariables → DominantFiveBody.PairChartVariables)
          v (3 : Fin (7 : ℕ)) =
        (3 : ℝ) * v (3 : Fin (7 : ℕ)) := @DominantFiveBody.pairChartJacobian_unit_radial_difference

-- Source binding: prose:577
example : ∀ (p alpha omega psi z : ℝ) (keepD : Bool),
  DominantFiveBody.PairChartRegular (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.pairUnitPoint omega psi z) →
    omega ≠ (0 : ℝ) →
      |omega| < Real.pi →
        ∀ (v : DominantFiveBody.PairChartVariables),
          v (0 : Fin (7 : ℕ)) = (0 : ℝ) →
            v (1 : Fin (7 : ℕ)) = (0 : ℝ) →
              v (2 : Fin (7 : ℕ)) = (0 : ℝ) →
                v (3 : Fin (7 : ℕ)) = (0 : ℝ) →
                  (DominantFiveBody.pairChartJacobian (0 : ℝ) (0 : ℝ) p alpha keepD
                          (DominantFiveBody.pairUnitPoint omega psi z) :
                        DominantFiveBody.PairChartVariables → DominantFiveBody.PairChartVariables)
                      v (4 : Fin (7 : ℕ)) =
                    (if keepD = Bool.true then p * DominantFiveBody.Coorbital.kappa |omega|
                      else -((1 : ℝ) - p) * DominantFiveBody.Coorbital.kappa |omega|) *
                      v (4 : Fin (7 : ℕ)) := @DominantFiveBody.pairChartJacobian_unit_exterior

-- Source binding: prose:577
example : ∀ (p alpha omega psi z : ℝ) (keepD : Bool),
  DominantFiveBody.PairChartRegular (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.pairUnitPoint omega psi z) →
    psi ≠ (0 : ℝ) →
      psi ≠ omega →
        |psi| < Real.pi →
          |psi - omega| < Real.pi →
            ∀ (v : DominantFiveBody.PairChartVariables),
              v (0 : Fin (7 : ℕ)) = (0 : ℝ) →
                v (1 : Fin (7 : ℕ)) = (0 : ℝ) →
                  v (2 : Fin (7 : ℕ)) = (0 : ℝ) →
                    v (3 : Fin (7 : ℕ)) = (0 : ℝ) →
                      v (4 : Fin (7 : ℕ)) = (0 : ℝ) →
                        (DominantFiveBody.pairChartJacobian (0 : ℝ) (0 : ℝ) p alpha keepD
                                (DominantFiveBody.pairUnitPoint omega psi z) :
                              DominantFiveBody.PairChartVariables → DominantFiveBody.PairChartVariables)
                            v (5 : Fin (7 : ℕ)) =
                          DominantFiveBody.pairProbeDerivative p omega psi * v (5 : Fin (7 : ℕ)) := @DominantFiveBody.pairChartJacobian_unit_mean

-- Source binding: prose:577
example : ∀ (p alpha omega psi z : ℝ) (keepD : Bool),
  DominantFiveBody.PairChartRegular (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.pairUnitPoint omega psi z) →
    (0 : ℝ) < z →
      psi ≠ (0 : ℝ) →
        psi ≠ omega →
          |psi| < Real.pi →
            |psi - omega| < Real.pi →
              DominantFiveBody.pairProbeDerivative p omega psi * z ^ (3 : ℕ) = (1 : ℝ) →
                ∀ (v : DominantFiveBody.PairChartVariables),
                  v (0 : Fin (7 : ℕ)) = (0 : ℝ) →
                    v (1 : Fin (7 : ℕ)) = (0 : ℝ) →
                      v (2 : Fin (7 : ℕ)) = (0 : ℝ) →
                        v (3 : Fin (7 : ℕ)) = (0 : ℝ) →
                          v (4 : Fin (7 : ℕ)) = (0 : ℝ) →
                            v (5 : Fin (7 : ℕ)) = (0 : ℝ) →
                              (DominantFiveBody.pairChartJacobian (0 : ℝ) (0 : ℝ) p alpha keepD
                                      (DominantFiveBody.pairUnitPoint omega psi z) :
                                    DominantFiveBody.PairChartVariables → DominantFiveBody.PairChartVariables)
                                  v (6 : Fin (7 : ℕ)) =
                                (3 : ℝ) * DominantFiveBody.pairProbeDerivative p omega psi * v (6 : Fin (7 : ℕ)) := @DominantFiveBody.pairChartJacobian_unit_difference

-- Source binding: eq:pair-J
example : ∀ (p0 alpha psi z : ℝ),
  DominantFiveBody.PairChartRegular (0 : ℝ) (0 : ℝ) alpha
      (DominantFiveBody.pairUnitPoint DominantFiveBody.Coorbital.h psi z) →
    (DominantFiveBody.pairChartJacobian (0 : ℝ) (0 : ℝ) p0 alpha (DominantFiveBody.pairSourceKeepD p0)
            (DominantFiveBody.pairUnitPoint DominantFiveBody.Coorbital.h psi z) :
          DominantFiveBody.PairChartVariables → DominantFiveBody.PairChartVariables)
        ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ)] (4 : Fin (7 : ℕ)) =
      DominantFiveBody.pairSourceA0 p0 := @DominantFiveBody.pairChartJacobian_exterior_source_a0

-- Source binding: prose:582
example : ∀ (p0 : ℝ), |DominantFiveBody.pairSourceA0 p0| ≥ (9 / 8 : ℝ) := @DominantFiveBody.pairSourceA0_abs_lower

-- Source binding: prose:582
example : ∀ (p alpha psi z : ℝ) (keepD : Bool),
  (0 : ℝ) ≤ p →
    p ≤ (1 : ℝ) →
      (if keepD = Bool.true then (0 : ℝ) < p else p < (1 : ℝ)) →
        (0 : ℝ) < z →
          psi ≠ (0 : ℝ) →
            psi ≠ DominantFiveBody.Coorbital.h →
              DominantFiveBody.twoSourceSpan psi < Real.pi →
                p * DominantFiveBody.coorbitalKernel psi +
                      ((1 : ℝ) - p) * DominantFiveBody.coorbitalKernel (psi - DominantFiveBody.Coorbital.h) =
                    (0 : ℝ) →
                  DominantFiveBody.pairProbeDerivative p DominantFiveBody.Coorbital.h psi * z ^ (3 : ℕ) = (1 : ℝ) →
                    (DominantFiveBody.pairChartJacobian (0 : ℝ) (0 : ℝ) p alpha keepD
                        (DominantFiveBody.pairUnitPoint DominantFiveBody.Coorbital.h psi z)).IsInvertible := @DominantFiveBody.pairChartJacobian_boundary_isInvertible

-- Source binding: prose:582
example : ∀ (t p alpha : ℝ) (keepD : Bool) (y : DominantFiveBody.PairChartVariables),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < DominantFiveBody.pairChartRadii t alpha y i) →
    DominantFiveBody.pairChartExtendedRows (0 : ℝ) t p alpha keepD y = (0 : DominantFiveBody.PairChartVariables) →
      (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.pairChartRadii t alpha y i = (1 : ℝ)) ∧
        y (3 : Fin (7 : ℕ)) = (0 : ℝ) := @DominantFiveBody.pairChart_zero_eps_all_scale_faces

-- Source binding: prose:582
example : ∀ (eps t p alpha : ℝ) (keepD : Bool) (y : DominantFiveBody.PairChartVariables),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < DominantFiveBody.pairChartRadii t alpha y i) →
    DominantFiveBody.pairChartExtendedRows eps t p alpha keepD y = (0 : DominantFiveBody.PairChartVariables) →
      y (3 : Fin (7 : ℕ)) = eps * DominantFiveBody.pairRadialRootQuotient (![eps, t, p, alpha], y) := @DominantFiveBody.pairRadial_root_exact_factor

-- Source binding: prose:582
example : ∀ (K : Set DominantFiveBody.PairJointVariables),
  IsCompact K →
    (∀ v ∈ K,
        DominantFiveBody.PairChartRegular (v.1 (0 : Fin (4 : ℕ))) (v.1 (1 : Fin (4 : ℕ))) (v.1 (3 : Fin (4 : ℕ))) v.2 ∧
          ∀ (i : DominantFiveBody.Satellite),
            (0 : ℝ) < DominantFiveBody.pairChartRadii (v.1 (1 : Fin (4 : ℕ))) (v.1 (3 : Fin (4 : ℕ))) v.2 i) →
      ∃ (C : ℝ),
        (0 : ℝ) < C ∧
          ∃ (U : Set DominantFiveBody.PairJointVariables),
            IsOpen U ∧
              K ⊆ U ∧
                ∀ v ∈ U,
                  ∀ (keepD : Bool),
                    DominantFiveBody.pairChartExtendedRows (v.1 (0 : Fin (4 : ℕ))) (v.1 (1 : Fin (4 : ℕ)))
                          (v.1 (2 : Fin (4 : ℕ))) (v.1 (3 : Fin (4 : ℕ))) keepD v.2 =
                        (0 : DominantFiveBody.PairChartVariables) →
                      |v.2 (3 : Fin (7 : ℕ))| ≤ C * |v.1 (0 : Fin (4 : ℕ))| := @DominantFiveBody.pairRadial_root_compact_uniform_bound

-- Source binding: eq:pair-areas
example : ∀ (alpha omega psi z : Real),
  @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) z →
    @Ne Real psi (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) →
      @Ne Real psi omega →
        @LT.lt Real Real.instLT (@abs Real Real.lattice Real.instAddGroup psi) Real.pi →
          @LT.lt Real Real.instLT
              (@abs Real Real.lattice Real.instAddGroup
                (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) psi omega))
              Real.pi →
            And
              (@Eq Real
                (DominantFiveBody.pairAreaQuotient (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                  alpha (DominantFiveBody.pairUnitPoint omega psi z)
                  (@OfNat.ofNat DominantFiveBody.Label (nat_lit 0)
                    (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0))))
                z)
              (And
                (@Eq Real
                  (DominantFiveBody.pairAreaQuotient (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                    alpha (DominantFiveBody.pairUnitPoint omega psi z)
                    (@OfNat.ofNat DominantFiveBody.Label (nat_lit 3)
                      (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 3))))
                  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) z
                    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                      (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) (Real.cos psi))))
                (And
                  (@Eq Real
                    (DominantFiveBody.pairAreaQuotient
                      (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) alpha
                      (DominantFiveBody.pairUnitPoint omega psi z)
                      (@OfNat.ofNat DominantFiveBody.Label (nat_lit 4)
                        (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 4))))
                    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) z
                      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                        (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                        (Real.cos (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) omega psi)))))
                  (∀ (j : DominantFiveBody.Label),
                    @Membership.mem DominantFiveBody.Label (Finset DominantFiveBody.Label)
                        (@SetLike.instMembership (Finset DominantFiveBody.Label) DominantFiveBody.Label
                          (@Finset.instSetLike DominantFiveBody.Label))
                        (@Insert.insert DominantFiveBody.Label (Finset DominantFiveBody.Label)
                          (@Finset.instInsert DominantFiveBody.Label
                            (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                          (@OfNat.ofNat DominantFiveBody.Label (nat_lit 0)
                            (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                              (nat_lit 0)))
                          (@Insert.insert DominantFiveBody.Label (Finset DominantFiveBody.Label)
                            (@Finset.instInsert DominantFiveBody.Label
                              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                            (@OfNat.ofNat DominantFiveBody.Label (nat_lit 3)
                              (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                (nat_lit 3)))
                            (@Singleton.singleton DominantFiveBody.Label (Finset DominantFiveBody.Label)
                              (@Finset.instSingleton DominantFiveBody.Label)
                              (@OfNat.ofNat DominantFiveBody.Label (nat_lit 4)
                                (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                  (nat_lit 4))))))
                        j →
                      @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                        (DominantFiveBody.pairAreaQuotient
                          (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) alpha
                          (DominantFiveBody.pairUnitPoint omega psi z) j)))) := @DominantFiveBody.pair_areas_boundary_complete

-- Source binding: eq:pair-areas
example : ∀ (t alpha : ℝ) (y : DominantFiveBody.PairChartVariables) (j : DominantFiveBody.Label),
  DominantFiveBody.orientedArea (DominantFiveBody.liftRelative (DominantFiveBody.pairChartPoints t alpha y))
      (1 : DominantFiveBody.Label) (2 : DominantFiveBody.Label) j =
    t * DominantFiveBody.pairAreaQuotient t alpha y j := @DominantFiveBody.pairArea_factor

-- Source binding: eq:pair-areas
example : ∀ (n : ℕ∞ω) (j : DominantFiveBody.Label),
  ContDiff ℝ n fun (v : DominantFiveBody.PairJointVariables) =>
    DominantFiveBody.pairAreaQuotient (v.1 (1 : Fin (4 : ℕ))) (v.1 (3 : Fin (4 : ℕ))) v.2 j := @DominantFiveBody.pairAreaQuotient_joint_contDiff

-- Source binding: prose:589
example : ∀ (p psi : ℝ) (keepD : Bool),
  (0 : ℝ) ≤ p →
    p ≤ (1 : ℝ) →
      (if keepD = Bool.true then (0 : ℝ) < p else p < (1 : ℝ)) →
        psi ≠ (0 : ℝ) →
          psi ≠ DominantFiveBody.Coorbital.h →
            DominantFiveBody.twoSourceSpan psi < Real.pi →
              p * DominantFiveBody.coorbitalKernel psi +
                    ((1 : ℝ) - p) * DominantFiveBody.coorbitalKernel (psi - DominantFiveBody.Coorbital.h) =
                  (0 : ℝ) →
                ∀ (tau : ℝ),
                  (0 : ℝ) < tau →
                    have y0 :=
                      DominantFiveBody.pairUnitPoint DominantFiveBody.Coorbital.h psi
                        (DominantFiveBody.pairBoundaryScale
                          (DominantFiveBody.pairProbeDerivative p DominantFiveBody.Coorbital.h psi));
                    ∃ (eta : ℝ) (r : ℝ) (C : ℝ),
                      (0 : ℝ) < eta ∧
                        (0 : ℝ) < r ∧
                          (0 : ℝ) < C ∧
                            r ≤ tau ∧
                              eta ≤ r ∧
                                ∀ alpha ∈ Set.Icc (0 : ℝ) (1 : ℝ),
                                  ∃ (branch :
                                    DominantFiveBody.PairChartParameters → DominantFiveBody.PairChartVariables),
                                    branch ![(0 : ℝ), (0 : ℝ), p, alpha] = y0 ∧
                                      ContDiffOn ℝ ∞ branch (Metric.ball ![(0 : ℝ), (0 : ℝ), p, alpha] eta) ∧
                                        ∀ (q : Fin (Nat.succ (0 : ℕ)).succ.succ.succ → ℝ),
                                          Dist.dist q ![(0 : ℝ), (0 : ℝ), p, alpha] < eta →
                                            Dist.dist (branch q) y0 < r / (2 : ℝ) ∧
                                              DominantFiveBody.PairChartRegular
                                                  (q (0 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                  (q (1 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                  (q (3 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ)) (branch q) ∧
                                                (q, branch q) ∈
                                                    DominantFiveBody.pairPhysicalSafeSet
                                                      (DominantFiveBody.pairBoundaryHullOrder psi) ∧
                                                  (DominantFiveBody.pairChartJacobian
                                                        (q (0 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                        (q (1 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                        (q (2 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                        (q (3 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ)) keepD
                                                        (branch q)).IsInvertible ∧
                                                    ‖(DominantFiveBody.pairChartJacobian
                                                              (q (0 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                              (q (1 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                              (q (2 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                              (q (3 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ)) keepD
                                                              (branch q)).inverse‖ ≤
                                                        C ∧
                                                      DominantFiveBody.pairChartParameterRows keepD q (branch q) =
                                                          (0 : DominantFiveBody.PairChartVariables) ∧
                                                        (∀ (y : DominantFiveBody.PairChartVariables),
                                                            Dist.dist y y0 < r →
                                                              (DominantFiveBody.pairChartParameterRows keepD q y =
                                                                  (0 : DominantFiveBody.PairChartVariables) ↔
                                                                branch q = y)) ∧
                                                          ((0 : ℝ) < q (0 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ) →
                                                            (0 : ℝ) < q (1 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ) →
                                                              DominantFiveBody.PositiveRatio
                                                                  (DominantFiveBody.pairChartMass
                                                                    (q (1 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                                    (q (2 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                                    (q (3 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))) →
                                                                DominantFiveBody.StrictConvexCentralConfiguration
                                                                    (DominantFiveBody.masses
                                                                      (q (0 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                                      (DominantFiveBody.pairChartMass
                                                                        (q (1 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                                        (q (2 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                                        (q
                                                                          (3 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))))
                                                                    (DominantFiveBody.pairBoundaryHullOrder psi)
                                                                    (DominantFiveBody.pairChartConfiguration q
                                                                      (branch q)) ∧
                                                                  DominantFiveBody.NondegenerateCentralConfiguration
                                                                    (DominantFiveBody.masses
                                                                      (q (0 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                                      (DominantFiveBody.pairChartMass
                                                                        (q (1 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                                        (q (2 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                                        (q
                                                                          (3 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))))
                                                                    (DominantFiveBody.pairChartConfiguration q
                                                                      (branch q))) := @DominantFiveBody.pairChart_compact_physical_continuation

-- Source binding: prose:589
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ),
              DominantFiveBody.StrictConvexInOrder { labels := Equiv.refl DominantFiveBody.Label, primary_first := rfl }
                (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                      i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (a b : DominantFiveBody.Satellite),
                              a < b →
                                ∀ (c : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c →
                                    ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                                      Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                        ∀ (u w : DominantFiveBody.Satellite),
                                          u < w →
                                            u ∈ DominantFiveBody.pairExteriorLabels a b →
                                              w ∈ DominantFiveBody.pairExteriorLabels a b →
                                                ∀ (e : Equiv.Perm DominantFiveBody.Satellite),
                                                  (e : DominantFiveBody.Satellite → DominantFiveBody.Satellite)
                                                        (0 : DominantFiveBody.Satellite) =
                                                      a →
                                                    (e : DominantFiveBody.Satellite → DominantFiveBody.Satellite)
                                                          (1 : DominantFiveBody.Satellite) =
                                                        b →
                                                      (e : DominantFiveBody.Satellite → DominantFiveBody.Satellite)
                                                            (2 : DominantFiveBody.Satellite) =
                                                          u →
                                                        (e : DominantFiveBody.Satellite → DominantFiveBody.Satellite)
                                                              (3 : DominantFiveBody.Satellite) =
                                                            w →
                                                          Filter.Tendsto
                                                              (fun (n : ℕ) =>
                                                                DominantFiveBody.pairPhysicalScale
                                                                  (mu n ∘
                                                                    (⇑e :
                                                                      DominantFiveBody.Satellite →
                                                                        DominantFiveBody.Satellite)))
                                                              Filter.atTop (𝓝 (0 : ℝ)) ∧
                                                            Filter.Tendsto
                                                                (fun (n : ℕ) =>
                                                                  DominantFiveBody.pairExteriorFraction
                                                                    (mu n ∘
                                                                      (⇑e :
                                                                        DominantFiveBody.Satellite →
                                                                          DominantFiveBody.Satellite)))
                                                                Filter.atTop (𝓝 (muLimit u)) ∧
                                                              Filter.Tendsto
                                                                (fun (n : ℕ) =>
                                                                  DominantFiveBody.pairVariablesFromPolar
                                                                    (DominantFiveBody.pairPhysicalScale
                                                                      (mu n ∘
                                                                        (⇑e :
                                                                          DominantFiveBody.Satellite →
                                                                            DominantFiveBody.Satellite)))
                                                                    (DominantFiveBody.pairPhysicalFraction
                                                                      (mu n ∘
                                                                        (⇑e :
                                                                          DominantFiveBody.Satellite →
                                                                            DominantFiveBody.Satellite)))
                                                                    (r n ∘
                                                                      (⇑e :
                                                                        DominantFiveBody.Satellite →
                                                                          DominantFiveBody.Satellite))
                                                                    fun (i : DominantFiveBody.Satellite) =>
                                                                    theta n
                                                                        ((e :
                                                                            DominantFiveBody.Satellite →
                                                                              DominantFiveBody.Satellite)
                                                                          i) -
                                                                      theta n u)
                                                                Filter.atTop
                                                                (𝓝
                                                                  (DominantFiveBody.pairUnitPoint
                                                                    DominantFiveBody.Coorbital.h (theta0 a - theta0 u)
                                                                    (DominantFiveBody.pairBoundaryScale
                                                                      (DominantFiveBody.pairProbeDerivative (muLimit u)
                                                                        DominantFiveBody.Coorbital.h
                                                                        (theta0 a - theta0 u))))) := @DominantFiveBody.normalized_complete_pair_actual_chart_limits

-- Source binding: prose:589
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ),
              DominantFiveBody.StrictConvexInOrder { labels := Equiv.refl DominantFiveBody.Label, primary_first := rfl }
                (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                      i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (a b : DominantFiveBody.Satellite),
                              a < b →
                                ∀ (c : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c →
                                    ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                                      Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                        ∀ (u w : DominantFiveBody.Satellite),
                                          u < w →
                                            u ∈ DominantFiveBody.pairExteriorLabels a b →
                                              w ∈ DominantFiveBody.pairExteriorLabels a b →
                                                ∀ (e : Equiv.Perm DominantFiveBody.Satellite),
                                                  (e : DominantFiveBody.Satellite → DominantFiveBody.Satellite)
                                                        (0 : DominantFiveBody.Satellite) =
                                                      a →
                                                    (e : DominantFiveBody.Satellite → DominantFiveBody.Satellite)
                                                          (1 : DominantFiveBody.Satellite) =
                                                        b →
                                                      (e : DominantFiveBody.Satellite → DominantFiveBody.Satellite)
                                                            (2 : DominantFiveBody.Satellite) =
                                                          u →
                                                        (e : DominantFiveBody.Satellite → DominantFiveBody.Satellite)
                                                              (3 : DominantFiveBody.Satellite) =
                                                            w →
                                                          ∃ (keepD : Bool),
                                                            Nonempty
                                                              (DominantFiveBody.PairCapturedBranches eps
                                                                (fun (n : ℕ) =>
                                                                  DominantFiveBody.pairPhysicalScale
                                                                    (mu n ∘
                                                                      (⇑e :
                                                                        DominantFiveBody.Satellite →
                                                                          DominantFiveBody.Satellite)))
                                                                (fun (n : ℕ) =>
                                                                  DominantFiveBody.pairExteriorFraction
                                                                    (mu n ∘
                                                                      (⇑e :
                                                                        DominantFiveBody.Satellite →
                                                                          DominantFiveBody.Satellite)))
                                                                (fun (n : ℕ) =>
                                                                  DominantFiveBody.pairPhysicalFraction
                                                                    (mu n ∘
                                                                      (⇑e :
                                                                        DominantFiveBody.Satellite →
                                                                          DominantFiveBody.Satellite)))
                                                                (fun (n : ℕ) =>
                                                                  DominantFiveBody.pairVariablesFromPolar
                                                                    (DominantFiveBody.pairPhysicalScale
                                                                      (mu n ∘
                                                                        (⇑e :
                                                                          DominantFiveBody.Satellite →
                                                                            DominantFiveBody.Satellite)))
                                                                    (DominantFiveBody.pairPhysicalFraction
                                                                      (mu n ∘
                                                                        (⇑e :
                                                                          DominantFiveBody.Satellite →
                                                                            DominantFiveBody.Satellite)))
                                                                    (r n ∘
                                                                      (⇑e :
                                                                        DominantFiveBody.Satellite →
                                                                          DominantFiveBody.Satellite))
                                                                    fun (i : DominantFiveBody.Satellite) =>
                                                                    theta n
                                                                        ((e :
                                                                            DominantFiveBody.Satellite →
                                                                              DominantFiveBody.Satellite)
                                                                          i) -
                                                                      theta n u)
                                                                (theta0 a - theta0 u) keepD) := @DominantFiveBody.normalized_complete_pair_actual_capture

-- Source binding: eq:internal
example : ∀ (alpha : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), (0 : ℝ) < alpha i) →
    ∃! z : DominantFiveBody.TripleVector,
      DominantFiveBody.TripleOrdered z ∧
        (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha z i = (0 : ℝ)) ∧
          ∑ i : DominantFiveBody.TripleLabel, alpha i * z i = (0 : ℝ) := @DominantFiveBody.tripleScalar_potential_root_existsUnique_centered

-- Source binding: eq:internal
example : ∀ (alpha x y : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), (0 : ℝ) ≤ alpha i) →
    DominantFiveBody.TripleOrdered x →
      DominantFiveBody.TripleOrdered y →
        (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha x i = (0 : ℝ)) →
          (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha y i = (0 : ℝ)) → x = y := @DominantFiveBody.tripleScalar_root_unique_by_integratedJacobian

-- Source binding: eq:internal
example : ∀ (alpha z : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha z i = (0 : ℝ)) →
    ∑ i : DominantFiveBody.TripleLabel, alpha i * z i = (0 : ℝ) := @DominantFiveBody.tripleScalar_root_weighted_center

-- Source binding: prose:599
example : ∀ (alpha z : DominantFiveBody.TripleVector),
  DominantFiveBody.tripleScalarPotential alpha z =
    DominantFiveBody.tripleD0 / (2 : ℝ) * ∑ i : DominantFiveBody.TripleLabel, alpha i * z i ^ (2 : ℕ) +
      ∑ p ∈ DominantFiveBody.tripleScalarPairs, alpha p.1 * alpha p.2 / |z p.1 - z p.2| := @DominantFiveBody.tripleScalarPotential_source_formula

-- Source binding: prose:599
example : ∀ (alpha : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), (0 : ℝ) < alpha i) →
    StrictConvexOn ℝ DominantFiveBody.tripleScalarChamber (DominantFiveBody.tripleScalarPotential alpha) := @DominantFiveBody.tripleScalarPotential_strictConvexOn

-- Source binding: prose:599
example : ∀ (alpha : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), (0 : ℝ) < alpha i) →
    IsProperMap fun (z : { z : DominantFiveBody.TripleVector // DominantFiveBody.TripleOrdered z }) =>
      DominantFiveBody.tripleScalarPotential alpha (↑z : DominantFiveBody.TripleVector) := @DominantFiveBody.tripleScalarPotential_isProperMap

-- Source binding: prose:599
example : ∀ (alpha z : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), (0 : ℝ) < alpha i) →
    DominantFiveBody.TripleOrdered z →
      ∀ (i : DominantFiveBody.TripleLabel),
        (fderiv ℝ (DominantFiveBody.tripleScalarPotential alpha) z : DominantFiveBody.TripleVector → ℝ)
              (Pi.single i (1 : ℝ)) /
            alpha i =
          DominantFiveBody.tripleScalarResidual alpha z i := @DominantFiveBody.tripleScalarPotential_divided_gradient

-- Source binding: prose:599
example : ∀ (alpha z : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), (0 : ℝ) < alpha i) →
    DominantFiveBody.TripleOrdered z →
      (fderiv ℝ (DominantFiveBody.tripleScalarPotential alpha) z = (0 : DominantFiveBody.TripleVector →L[ℝ] ℝ) ↔
        ∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha z i = (0 : ℝ)) := @DominantFiveBody.tripleScalarPotential_critical_iff_root

-- Source binding: prose:599
example : ∀ (alpha : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), (0 : ℝ) < alpha i) →
    ∃ (z : DominantFiveBody.TripleVector),
      DominantFiveBody.TripleOrdered z ∧
        IsMinOn (DominantFiveBody.tripleScalarPotential alpha) DominantFiveBody.tripleScalarChamber z := @DominantFiveBody.tripleScalarPotential_exists_minimizer

-- Source binding: prose:604
example : ∀ (alpha z : DominantFiveBody.TripleVector),
  (∀ (i j : DominantFiveBody.TripleLabel), i ≠ j → z i ≠ z j) →
    HasFDerivAt
      (fun (y : DominantFiveBody.TripleVector) (i : DominantFiveBody.TripleLabel) =>
        DominantFiveBody.tripleScalarResidual alpha y i)
      (DominantFiveBody.tripleScalarDifferential alpha z) z := @DominantFiveBody.tripleScalarResidual_hasFDerivAt

-- Source binding: prose:604
example : ∀ (alpha z : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel),
      DominantFiveBody.tripleScalarJacobian alpha z i i =
        DominantFiveBody.tripleD0 + (2 : ℝ) * ∑ j ∈ Finset.univ.erase i, alpha j / |z i - z j| ^ (3 : ℕ)) ∧
    ∀ (i j : DominantFiveBody.TripleLabel),
      i ≠ j → DominantFiveBody.tripleScalarJacobian alpha z i j = (-2 : ℝ) * alpha j / |z i - z j| ^ (3 : ℕ) := @DominantFiveBody.tripleScalar_J_entries_complete

-- Source binding: prose:609
example : ∀ (alpha z : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), (0 : ℝ) ≤ alpha i) →
    ∀ (i : DominantFiveBody.TripleLabel),
      ∑ j ∈ Finset.univ.erase i, ‖DominantFiveBody.tripleScalarJacobian alpha z i j‖ <
        ‖DominantFiveBody.tripleScalarJacobian alpha z i i‖ := @DominantFiveBody.tripleScalarJacobian_strict_row_dominance

-- Source binding: prose:609
example : ∀ (alpha z v : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), (0 : ℝ) ≤ alpha i) →
    DominantFiveBody.tripleD0 * ‖v‖ ≤ ‖(DominantFiveBody.tripleScalarJacobian alpha z).mulVec v‖ := @DominantFiveBody.tripleScalarJacobian_lower_norm_bound

-- Source binding: prose:609
example : ∀ (x y : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleOrdered x →
    DominantFiveBody.TripleOrdered y →
      ∀ s ∈ Set.Icc (0 : ℝ) (1 : ℝ), DominantFiveBody.TripleOrdered (DominantFiveBody.tripleOrderedSegment x y s) := @DominantFiveBody.tripleOrderedSegment_ordered

-- Source binding: prose:609
example : ∀ (alpha x y : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleOrdered x →
    DominantFiveBody.TripleOrdered y →
      ∀ (i j : DominantFiveBody.TripleLabel),
        DominantFiveBody.tripleIntegratedJacobian alpha x y i j =
          if i = j then
            DominantFiveBody.tripleD0 +
              ∑ k ∈ Finset.univ.erase i, DominantFiveBody.tripleIntegratedCoefficient alpha x y i k
          else -DominantFiveBody.tripleIntegratedCoefficient alpha x y i j := @DominantFiveBody.tripleIntegratedJacobian_entries

-- Source binding: prose:609
example : ∀ (alpha x y v : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), (0 : ℝ) ≤ alpha i) →
    DominantFiveBody.TripleOrdered x →
      DominantFiveBody.TripleOrdered y →
        DominantFiveBody.tripleD0 * ‖v‖ ≤ ‖(DominantFiveBody.tripleIntegratedJacobian alpha x y).mulVec v‖ := @DominantFiveBody.tripleIntegratedJacobian_lower_norm_bound

-- Source binding: prose:609
example : ∀ (alpha x y : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleOrdered x →
    DominantFiveBody.TripleOrdered y →
      (fun (i : DominantFiveBody.TripleLabel) =>
          DominantFiveBody.tripleScalarResidual alpha y i - DominantFiveBody.tripleScalarResidual alpha x i) =
        (DominantFiveBody.tripleIntegratedJacobian alpha x y).mulVec (y - x) := @DominantFiveBody.tripleScalarResidual_ordered_segment_integral

-- Source binding: eq:LB
example : ∀ (alpha : DominantFiveBody.TripleVector),
  ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
    DominantFiveBody.tripleGapMatrix = !![(-1 : ℝ), (1 : ℝ), (0 : ℝ); (0 : ℝ), (-1 : ℝ), (1 : ℝ)] ∧
      DominantFiveBody.tripleCenteringMatrix alpha =
          !![-(alpha (1 : DominantFiveBody.TripleLabel) + alpha (2 : DominantFiveBody.TripleLabel)),
              -alpha (2 : DominantFiveBody.TripleLabel);
            alpha (0 : DominantFiveBody.TripleLabel), -alpha (2 : DominantFiveBody.TripleLabel);
            alpha (0 : DominantFiveBody.TripleLabel),
              alpha (0 : DominantFiveBody.TripleLabel) + alpha (1 : DominantFiveBody.TripleLabel)] ∧
        DominantFiveBody.tripleGapMatrix * DominantFiveBody.tripleCenteringMatrix alpha =
            (1 : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ) ∧
          ∀ (v : DominantFiveBody.TripleGaps),
            ∑ i : DominantFiveBody.TripleLabel, alpha i * (DominantFiveBody.tripleCenteringMatrix alpha).mulVec v i =
              (0 : ℝ) := @DominantFiveBody.tripleScalar_matrices_complete

-- Source binding: eq:regular-coordinates
example : ∀ (t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  DominantFiveBody.tripleChartMass t alpha =
      ![t ^ (3 : ℕ) * alpha (0 : DominantFiveBody.TripleLabel), t ^ (3 : ℕ) * alpha (1 : DominantFiveBody.TripleLabel),
        t ^ (3 : ℕ) * alpha (2 : DominantFiveBody.TripleLabel), (1 : ℝ) - t ^ (3 : ℕ)] ∧
    DominantFiveBody.tripleChartRadialPositions alpha y =
        (DominantFiveBody.tripleCenteringMatrix alpha).mulVec ![y (2 : Fin (7 : ℕ)), y (3 : Fin (7 : ℕ))] ∧
      DominantFiveBody.tripleChartAngularPositions alpha y =
          (DominantFiveBody.tripleCenteringMatrix alpha).mulVec ![y (5 : Fin (7 : ℕ)), y (6 : Fin (7 : ℕ))] ∧
        DominantFiveBody.tripleChartRadii t alpha y =
            ![y (1 : Fin (7 : ℕ)) +
                t * DominantFiveBody.tripleChartRadialPositions alpha y (0 : DominantFiveBody.TripleLabel),
              y (1 : Fin (7 : ℕ)) +
                t * DominantFiveBody.tripleChartRadialPositions alpha y (1 : DominantFiveBody.TripleLabel),
              y (1 : Fin (7 : ℕ)) +
                t * DominantFiveBody.tripleChartRadialPositions alpha y (2 : DominantFiveBody.TripleLabel),
              y (0 : Fin (7 : ℕ))] ∧
          DominantFiveBody.tripleChartAngles t alpha y =
            ![y (4 : Fin (7 : ℕ)) +
                t * DominantFiveBody.tripleChartAngularPositions alpha y (0 : DominantFiveBody.TripleLabel),
              y (4 : Fin (7 : ℕ)) +
                t * DominantFiveBody.tripleChartAngularPositions alpha y (1 : DominantFiveBody.TripleLabel),
              y (4 : Fin (7 : ℕ)) +
                t * DominantFiveBody.tripleChartAngularPositions alpha y (2 : DominantFiveBody.TripleLabel),
              (0 : ℝ)] := @DominantFiveBody.tripleChart_coordinates_complete

-- Source binding: prose:626
example : ∀ (t : ℝ) (alpha : DominantFiveBody.TripleVector) (P : DominantFiveBody.Satellite → ℝ),
  t ≠ (0 : ℝ) →
    ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
      DominantFiveBody.tripleClusterRows P =
        (fun (x : DominantFiveBody.TripleLabel) => DominantFiveBody.tripleRowAverage alpha P) +
          t • (DominantFiveBody.tripleCenteringMatrix alpha).mulVec (DominantFiveBody.tripleRowDifferences t P) := @DominantFiveBody.tripleRows_recovery

-- Source binding: prose:626
example : ∀ (t : ℝ) (alpha : DominantFiveBody.TripleVector) (P : DominantFiveBody.Satellite → ℝ),
  t ≠ (0 : ℝ) →
    ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
      (DominantFiveBody.tripleRowAverage alpha P = (0 : ℝ) ∧
          DominantFiveBody.tripleRowDifferences t P = (0 : DominantFiveBody.TripleGaps) ↔
        DominantFiveBody.tripleClusterRows P = (0 : DominantFiveBody.TripleVector)) := @DominantFiveBody.tripleRows_zero_iff

-- Source binding: prose:626
example : ∀ (n : ℕ∞ω) (v : DominantFiveBody.TripleJointVariables),
  DominantFiveBody.TripleChartRegular (v.1 (0 : Fin (5 : ℕ))) (v.1 (1 : Fin (5 : ℕ)))
      (DominantFiveBody.tripleJointAlpha v.1) v.2 →
    ContDiffAt ℝ n
      (fun (w : DominantFiveBody.TripleJointVariables) =>
        DominantFiveBody.tripleChartExtendedRows (w.1 (0 : Fin (5 : ℕ))) (w.1 (1 : Fin (5 : ℕ)))
          (DominantFiveBody.tripleJointAlpha w.1) w.2)
      v := @DominantFiveBody.tripleChartExtendedRows_joint_contDiffAt

-- Source binding: prose:626
example : ∀ (eps t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  (0 : ℝ) < eps →
    (0 : ℝ) < t →
      ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
        DominantFiveBody.PositiveRatio (DominantFiveBody.tripleChartMass t alpha) →
          DominantFiveBody.TripleChartRegular eps t alpha y →
            (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < DominantFiveBody.tripleChartRadii t alpha y i) →
              (DominantFiveBody.tripleChartExtendedRows eps t alpha y = (0 : DominantFiveBody.TripleChartVariables) ↔
                DominantFiveBody.NormalizedCentralConfiguration
                  (DominantFiveBody.masses eps (DominantFiveBody.tripleChartMass t alpha))
                  (DominantFiveBody.centeredFromRelative eps (DominantFiveBody.tripleChartMass t alpha)
                    (DominantFiveBody.tripleChartPoints t alpha y))) := @DominantFiveBody.tripleChartExtendedRows_zero_iff_normalized

-- Source binding: prose:628
example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
    DominantFiveBody.tripleRadialMean (0 : ℝ) (0 : ℝ) alpha y = y (1 : Fin (7 : ℕ)) - (y (1 : Fin (7 : ℕ)) ^ (2 : ℕ))⁻¹ := @DominantFiveBody.tripleRadialMean_at_boundary

-- Source binding: prose:628
example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
    ∀ (k : Fin (2 : ℕ)),
      DominantFiveBody.tripleRadialDifference (0 : ℝ) (0 : ℝ) alpha y k =
        DominantFiveBody.tripleChartRadialGaps y k *
          ((1 : ℝ) + (2 : ℝ) * y (1 : Fin (7 : ℕ)) / (y (1 : Fin (7 : ℕ)) ^ (2 : ℕ) * y (1 : Fin (7 : ℕ)) ^ (2 : ℕ))) := @DominantFiveBody.tripleRadialDifference_at_boundary

-- Source binding: prose:628
example : ∀ (alpha : DominantFiveBody.TripleVector),
  ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
    ∀ (y : DominantFiveBody.TripleChartVariables) (i : Fin (2 : ℕ)),
      DominantFiveBody.tripleChartExtendedRows (0 : ℝ) (0 : ℝ) alpha y i.castSucc.castSucc.castSucc.castSucc.castSucc =
        y i.castSucc.castSucc.castSucc.castSucc.castSucc -
          (y i.castSucc.castSucc.castSucc.castSucc.castSucc ^ (2 : ℕ))⁻¹ := @DominantFiveBody.tripleChart_boundary_radial

-- Source binding: eq:Hzero
example : ∀ (rho v r : ℝ),
  DominantFiveBody.regularTripleScalarH r (rho, v) =
    -rho * r * Real.sin v * ((rho ^ (2 : ℕ) + r ^ (2 : ℕ) - (2 : ℝ) * rho * r * Real.cos v) ^ (-3 / 2 : ℝ) - (1 : ℝ)) := @DominantFiveBody.regularTripleScalarH_source_formula

-- Source binding: display:634
example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  DominantFiveBody.regularTripleBoundaryM alpha y i =
    DominantFiveBody.regularTripleScalarH_rho (y (0 : Fin (7 : ℕ))) (y (1 : Fin (7 : ℕ)), y (4 : Fin (7 : ℕ))) *
          DominantFiveBody.tripleChartRadialPositions alpha y i +
        DominantFiveBody.regularTripleScalarH_v (y (0 : Fin (7 : ℕ))) (y (1 : Fin (7 : ℕ)), y (4 : Fin (7 : ℕ))) *
          DominantFiveBody.tripleChartAngularPositions alpha y i -
      ∑ j ∈ Finset.univ.erase i,
        alpha j * y (1 : Fin (7 : ℕ)) ^ (2 : ℕ) *
            (DominantFiveBody.tripleChartAngularPositions alpha y i -
              DominantFiveBody.tripleChartAngularPositions alpha y j) /
          ((DominantFiveBody.tripleChartRadialPositions alpha y i -
                  DominantFiveBody.tripleChartRadialPositions alpha y j) ^
                (2 : ℕ) +
              y (1 : Fin (7 : ℕ)) ^ (2 : ℕ) *
                (DominantFiveBody.tripleChartAngularPositions alpha y i -
                    DominantFiveBody.tripleChartAngularPositions alpha y j) ^
                  (2 : ℕ)) ^
            (3 / 2 : ℝ) := @DominantFiveBody.regularTripleBoundaryM_source_formula

-- Source binding: display:634
example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ) ≠
      DominantFiveBody.polarPoint (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ))) →
    DominantFiveBody.tripleAngularDifference (0 : ℝ) (0 : ℝ) alpha y =
      DominantFiveBody.tripleGapMatrix.mulVec (DominantFiveBody.regularTripleBoundaryM alpha y) := @DominantFiveBody.tripleAngularDifference_boundary_eq_LM

-- Source binding: display:634
example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
    DominantFiveBody.tripleAngularMean (0 : ℝ) (0 : ℝ) alpha y =
      -y (1 : Fin (7 : ℕ)) * y (0 : Fin (7 : ℕ)) * Real.sin (y (4 : Fin (7 : ℕ))) *
        ((y (1 : Fin (7 : ℕ)) ^ (2 : ℕ) + y (0 : Fin (7 : ℕ)) ^ (2 : ℕ) -
              (2 : ℝ) * y (1 : Fin (7 : ℕ)) * y (0 : Fin (7 : ℕ)) * Real.cos (y (4 : Fin (7 : ℕ)))) ^
            (-3 / 2 : ℝ) -
          (1 : ℝ)) := @DominantFiveBody.tripleAngularMean_boundary_source_H

-- Source binding: prose:638
example : ∀ (alpha : DominantFiveBody.TripleVector) (psi : ℝ) (g : DominantFiveBody.TripleGaps),
  psi ≠ (0 : ℝ) →
    |psi| < Real.pi →
      DominantFiveBody.Coorbital.kappa |psi| = DominantFiveBody.tripleD0 →
        DominantFiveBody.tripleAngularDifference (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.tripleUnitPoint psi g) =
          DominantFiveBody.tripleGapMatrix.mulVec fun (i : DominantFiveBody.TripleLabel) =>
            DominantFiveBody.tripleScalarResidual alpha ((DominantFiveBody.tripleCenteringMatrix alpha).mulVec g) i := @DominantFiveBody.tripleAngularDifference_unit_scalar

-- Source binding: prose:638
example : ∀ (alpha : DominantFiveBody.TripleVector) (v : DominantFiveBody.TripleGaps),
  DominantFiveBody.TripleWeights alpha →
    (DominantFiveBody.tripleGapMatrix.mulVec fun (i : DominantFiveBody.TripleLabel) =>
          DominantFiveBody.tripleScalarResidual alpha ((DominantFiveBody.tripleCenteringMatrix alpha).mulVec v) i) =
        (0 : Fin (2 : ℕ) → ℝ) →
      ∀ (i : DominantFiveBody.TripleLabel),
        DominantFiveBody.tripleScalarResidual alpha ((DominantFiveBody.tripleCenteringMatrix alpha).mulVec v) i =
          (0 : ℝ) := @DominantFiveBody.tripleScalar_centered_gap_root_recovery

-- Source binding: prose:638
example : ∀ (alpha : DominantFiveBody.TripleVector),
  ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
    ∀ (psi : ℝ),
      |psi| = DominantFiveBody.Coorbital.h →
        ∀ (g : DominantFiveBody.TripleGaps),
          (∀ (i : DominantFiveBody.TripleLabel),
              DominantFiveBody.tripleScalarResidual alpha ((DominantFiveBody.tripleCenteringMatrix alpha).mulVec g) i =
                (0 : ℝ)) →
            DominantFiveBody.tripleChartExtendedRows (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.tripleUnitPoint psi g) =
              (0 : DominantFiveBody.TripleChartVariables) := @DominantFiveBody.tripleChartExtendedRows_unit_root

-- Source binding: prose:638
example : ∀ (alpha : DominantFiveBody.TripleVector),
  ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
    ∀ (psi : ℝ) (g : DominantFiveBody.TripleGaps),
      DominantFiveBody.TripleChartRegular (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.tripleUnitPoint psi g) →
        ∀ (v : DominantFiveBody.TripleChartVariables) (i : Fin (2 : ℕ)),
          (DominantFiveBody.tripleChartJacobian (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.tripleUnitPoint psi g) :
                DominantFiveBody.TripleChartVariables → DominantFiveBody.TripleChartVariables)
              v i.castSucc.castSucc.castSucc.castSucc.castSucc =
            (3 : ℝ) * v i.castSucc.castSucc.castSucc.castSucc.castSucc := @DominantFiveBody.tripleChartJacobian_unit_radial

-- Source binding: prose:638
example : ∀ (alpha : DominantFiveBody.TripleVector),
  ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
    ∀ (psi : ℝ) (g : DominantFiveBody.TripleGaps),
      DominantFiveBody.TripleChartRegular (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.tripleUnitPoint psi g) →
        ∀ (v : DominantFiveBody.TripleChartVariables) (k : Fin (2 : ℕ)),
          (DominantFiveBody.tripleChartJacobian (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.tripleUnitPoint psi g) :
                DominantFiveBody.TripleChartVariables → DominantFiveBody.TripleChartVariables)
              v k.castSucc.castSucc.castSucc.succ.succ =
            (3 : ℝ) * v k.castSucc.castSucc.castSucc.succ.succ := @DominantFiveBody.tripleChartJacobian_unit_radial_difference

-- Source binding: prose:638
example : ∀ (alpha : DominantFiveBody.TripleVector),
  ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
    ∀ (psi : ℝ) (g : DominantFiveBody.TripleGaps),
      DominantFiveBody.TripleChartRegular (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.tripleUnitPoint psi g) →
        psi ≠ (0 : ℝ) →
          |psi| < Real.pi →
            ∀ (v : DominantFiveBody.TripleChartVariables),
              v (0 : Fin (7 : ℕ)) = (0 : ℝ) →
                v (1 : Fin (7 : ℕ)) = (0 : ℝ) →
                  v (2 : Fin (7 : ℕ)) = (0 : ℝ) →
                    v (3 : Fin (7 : ℕ)) = (0 : ℝ) →
                      (DominantFiveBody.tripleChartJacobian (0 : ℝ) (0 : ℝ) alpha
                              (DominantFiveBody.tripleUnitPoint psi g) :
                            DominantFiveBody.TripleChartVariables → DominantFiveBody.TripleChartVariables)
                          v (4 : Fin (7 : ℕ)) =
                        DominantFiveBody.Coorbital.kappa |psi| * v (4 : Fin (7 : ℕ)) := @DominantFiveBody.tripleChartJacobian_unit_mean

-- Source binding: prose:638
example : ∀ (alpha : DominantFiveBody.TripleVector) (psi : ℝ) (g : DominantFiveBody.TripleGaps),
  DominantFiveBody.TripleChartRegular (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.tripleUnitPoint psi g) →
    psi ≠ (0 : ℝ) →
      |psi| < Real.pi →
        DominantFiveBody.Coorbital.kappa |psi| = DominantFiveBody.tripleD0 →
          (∀ (i j : DominantFiveBody.TripleLabel),
              i ≠ j →
                (DominantFiveBody.tripleCenteringMatrix alpha).mulVec g i ≠
                  (DominantFiveBody.tripleCenteringMatrix alpha).mulVec g j) →
            ∀ (v : DominantFiveBody.TripleChartVariables),
              v (0 : Fin (7 : ℕ)) = (0 : ℝ) →
                v (1 : Fin (7 : ℕ)) = (0 : ℝ) →
                  v (2 : Fin (7 : ℕ)) = (0 : ℝ) →
                    v (3 : Fin (7 : ℕ)) = (0 : ℝ) →
                      v (4 : Fin (7 : ℕ)) = (0 : ℝ) →
                        ∀ (k : Fin (2 : ℕ)),
                          (DominantFiveBody.tripleChartJacobian (0 : ℝ) (0 : ℝ) alpha
                                  (DominantFiveBody.tripleUnitPoint psi g) :
                                DominantFiveBody.TripleChartVariables → DominantFiveBody.TripleChartVariables)
                              v k.succ.succ.succ.succ.succ =
                            (DominantFiveBody.tripleReducedDifferential alpha
                                  ((DominantFiveBody.tripleCenteringMatrix alpha).mulVec g) :
                                DominantFiveBody.TripleGaps → DominantFiveBody.TripleGaps)
                              ![v (5 : Fin (7 : ℕ)), v (6 : Fin (7 : ℕ))] k := @DominantFiveBody.tripleChartJacobian_unit_difference

-- Source binding: eq:Kreg
example : ∀ (alpha z : DominantFiveBody.TripleVector),
  DominantFiveBody.tripleReducedJacobian alpha z =
    DominantFiveBody.tripleGapMatrix * DominantFiveBody.tripleScalarJacobian alpha z *
      DominantFiveBody.tripleCenteringMatrix alpha := @DominantFiveBody.tripleReducedJacobian_formula_complete

-- Source binding: eq:Kreg
example : ∀ (alpha z : DominantFiveBody.TripleVector) (v : DominantFiveBody.TripleGaps),
  (DominantFiveBody.tripleReducedDifferential alpha z : DominantFiveBody.TripleGaps → DominantFiveBody.TripleGaps) v =
    (DominantFiveBody.tripleReducedJacobian alpha z).mulVec v := @DominantFiveBody.tripleReducedDifferential_matrix

-- Source binding: prose:642
example : ∀ (alpha z : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleWeights alpha → (DominantFiveBody.tripleReducedJacobian alpha z).det ≠ (0 : ℝ) := @DominantFiveBody.tripleReducedJacobian_det_ne_zero

-- Source binding: prose:642
example : ∀ (alpha z : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleWeights alpha →
    DominantFiveBody.TripleOrdered z →
      (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha z i = (0 : ℝ)) →
        ∀ (psi : ℝ),
          |psi| = DominantFiveBody.Coorbital.h →
            ∀ (tau : ℝ),
              (0 : ℝ) < tau →
                ∃ (eta : ℝ) (r : ℝ) (C : ℝ),
                  (0 : ℝ) < eta ∧
                    (0 : ℝ) < r ∧
                      (0 : ℝ) < C ∧
                        r ≤ tau ∧
                          eta ≤ r ∧
                            ∃ (branch : DominantFiveBody.TripleChartParameters → DominantFiveBody.TripleChartVariables),
                              branch (DominantFiveBody.tripleBoundaryParameter alpha) =
                                  DominantFiveBody.tripleUnitPoint psi (DominantFiveBody.tripleGapMatrix.mulVec z) ∧
                                ContDiffOn ℝ ∞ branch
                                    (Metric.ball (DominantFiveBody.tripleBoundaryParameter alpha) eta) ∧
                                  ∀ (q : DominantFiveBody.TripleChartParameters),
                                    Dist.dist q (DominantFiveBody.tripleBoundaryParameter alpha) < eta →
                                      Dist.dist (branch q)
                                            (DominantFiveBody.tripleUnitPoint psi
                                              (DominantFiveBody.tripleGapMatrix.mulVec z)) <
                                          r / (2 : ℝ) ∧
                                        DominantFiveBody.TripleChartRegular (q (0 : Fin (5 : ℕ))) (q (1 : Fin (5 : ℕ)))
                                            (DominantFiveBody.tripleJointAlpha q) (branch q) ∧
                                          (DominantFiveBody.tripleChartJacobian (q (0 : Fin (5 : ℕ)))
                                                (q (1 : Fin (5 : ℕ))) (DominantFiveBody.tripleJointAlpha q)
                                                (branch q)).IsInvertible ∧
                                            ‖(DominantFiveBody.tripleChartJacobian (q (0 : Fin (5 : ℕ)))
                                                      (q (1 : Fin (5 : ℕ))) (DominantFiveBody.tripleJointAlpha q)
                                                      (branch q)).inverse‖ ≤
                                                C ∧
                                              DominantFiveBody.tripleChartParameterRows q (branch q) =
                                                  (0 : DominantFiveBody.TripleChartVariables) ∧
                                                ∀ (y : DominantFiveBody.TripleChartVariables),
                                                  Dist.dist y
                                                        (DominantFiveBody.tripleUnitPoint psi
                                                          (DominantFiveBody.tripleGapMatrix.mulVec z)) <
                                                      r →
                                                    (DominantFiveBody.tripleChartParameterRows q y =
                                                        (0 : DominantFiveBody.TripleChartVariables) ↔
                                                      branch q = y) := @DominantFiveBody.tripleChart_boundary_continuation_of_scalar_root

-- Source binding: prose:642
example : ∀ (t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
    (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < DominantFiveBody.tripleChartRadii t alpha y i) →
      DominantFiveBody.tripleChartExtendedRows (0 : ℝ) t alpha y = (0 : DominantFiveBody.TripleChartVariables) →
        (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.tripleChartRadii t alpha y i = (1 : ℝ)) ∧
          DominantFiveBody.tripleChartRadialGaps y = (0 : DominantFiveBody.TripleGaps) ∧
            y (0 : Fin (7 : ℕ)) = (1 : ℝ) ∧ y (1 : Fin (7 : ℕ)) = (1 : ℝ) := @DominantFiveBody.tripleChart_zero_eps_all_scale_faces

-- Source binding: prose:642
example : ∀ (alpha z : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleWeights alpha →
    DominantFiveBody.TripleOrdered z →
      (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha z i = (0 : ℝ)) →
        ∀ (tau : ℝ),
          tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
            ∀ (bound : ℝ),
              (0 : ℝ) < bound →
                ∃ (eta : ℝ) (r : ℝ) (C : ℝ),
                  (0 : ℝ) < eta ∧
                    (0 : ℝ) < r ∧
                      (0 : ℝ) < C ∧
                        r ≤ bound ∧
                          eta ≤ r ∧
                            ∃ (branch : DominantFiveBody.TripleChartParameters → DominantFiveBody.TripleChartVariables),
                              branch (DominantFiveBody.tripleBoundaryParameter alpha) =
                                  DominantFiveBody.tripleUnitPoint (tau * DominantFiveBody.Coorbital.h)
                                    (DominantFiveBody.tripleGapMatrix.mulVec z) ∧
                                ContDiffOn ℝ ∞ branch
                                    (Metric.ball (DominantFiveBody.tripleBoundaryParameter alpha) eta) ∧
                                  ∀ (q : DominantFiveBody.TripleChartParameters),
                                    Dist.dist q (DominantFiveBody.tripleBoundaryParameter alpha) < eta →
                                      Dist.dist (branch q)
                                            (DominantFiveBody.tripleUnitPoint (tau * DominantFiveBody.Coorbital.h)
                                              (DominantFiveBody.tripleGapMatrix.mulVec z)) <
                                          r / (2 : ℝ) ∧
                                        DominantFiveBody.TripleChartRegular (q (0 : Fin (5 : ℕ))) (q (1 : Fin (5 : ℕ)))
                                            (DominantFiveBody.tripleJointAlpha q) (branch q) ∧
                                          (q, branch q) ∈ DominantFiveBody.triplePhysicalRegularSet ∧
                                            (DominantFiveBody.tripleChartJacobian (q (0 : Fin (5 : ℕ)))
                                                  (q (1 : Fin (5 : ℕ))) (DominantFiveBody.tripleJointAlpha q)
                                                  (branch q)).IsInvertible ∧
                                              ‖(DominantFiveBody.tripleChartJacobian (q (0 : Fin (5 : ℕ)))
                                                        (q (1 : Fin (5 : ℕ))) (DominantFiveBody.tripleJointAlpha q)
                                                        (branch q)).inverse‖ ≤
                                                  C ∧
                                                DominantFiveBody.tripleChartParameterRows q (branch q) =
                                                    (0 : DominantFiveBody.TripleChartVariables) ∧
                                                  (∀ (y : DominantFiveBody.TripleChartVariables),
                                                      Dist.dist y
                                                            (DominantFiveBody.tripleUnitPoint
                                                              (tau * DominantFiveBody.Coorbital.h)
                                                              (DominantFiveBody.tripleGapMatrix.mulVec z)) <
                                                          r →
                                                        (DominantFiveBody.tripleChartParameterRows q y =
                                                            (0 : DominantFiveBody.TripleChartVariables) ↔
                                                          branch q = y)) ∧
                                                    ((0 : ℝ) < q (1 : Fin (5 : ℕ)) →
                                                        ∑ i : DominantFiveBody.TripleLabel,
                                                              DominantFiveBody.tripleJointAlpha q i =
                                                            (1 : ℝ) →
                                                          DominantFiveBody.StrictConvexInOrder
                                                            (DominantFiveBody.tripleBoundaryHullOrder tau)
                                                            (DominantFiveBody.liftRelative
                                                              (DominantFiveBody.tripleChartPoints (q (1 : Fin (5 : ℕ)))
                                                                (DominantFiveBody.tripleJointAlpha q) (branch q)))) ∧
                                                      ((0 : ℝ) < q (0 : Fin (5 : ℕ)) →
                                                          (0 : ℝ) < q (1 : Fin (5 : ℕ)) →
                                                            ∑ i : DominantFiveBody.TripleLabel,
                                                                  DominantFiveBody.tripleJointAlpha q i =
                                                                (1 : ℝ) →
                                                              DominantFiveBody.PositiveRatio
                                                                  (DominantFiveBody.tripleChartMass
                                                                    (q (1 : Fin (5 : ℕ)))
                                                                    (DominantFiveBody.tripleJointAlpha q)) →
                                                                DominantFiveBody.StrictConvexCentralConfiguration
                                                                    (DominantFiveBody.masses (q (0 : Fin (5 : ℕ)))
                                                                      (DominantFiveBody.tripleChartMass
                                                                        (q (1 : Fin (5 : ℕ)))
                                                                        (DominantFiveBody.tripleJointAlpha q)))
                                                                    (DominantFiveBody.tripleBoundaryHullOrder tau)
                                                                    (DominantFiveBody.tripleChartConfiguration q
                                                                      (branch q)) ∧
                                                                  DominantFiveBody.NondegenerateCentralConfiguration
                                                                    (DominantFiveBody.masses (q (0 : Fin (5 : ℕ)))
                                                                      (DominantFiveBody.tripleChartMass
                                                                        (q (1 : Fin (5 : ℕ)))
                                                                        (DominantFiveBody.tripleJointAlpha q)))
                                                                    (DominantFiveBody.tripleChartConfiguration q
                                                                      (branch q))) ∧
                                                        (q (0 : Fin (5 : ℕ)) = (0 : ℝ) →
                                                          (0 : ℝ) < q (1 : Fin (5 : ℕ)) →
                                                            ∑ i : DominantFiveBody.TripleLabel,
                                                                  DominantFiveBody.tripleJointAlpha q i =
                                                                (1 : ℝ) →
                                                              DominantFiveBody.PositiveRatio
                                                                  (DominantFiveBody.tripleChartMass
                                                                    (q (1 : Fin (5 : ℕ)))
                                                                    (DominantFiveBody.tripleJointAlpha q)) →
                                                                (∀ (i : DominantFiveBody.Satellite),
                                                                    DominantFiveBody.tripleChartRadii
                                                                        (q (1 : Fin (5 : ℕ)))
                                                                        (DominantFiveBody.tripleJointAlpha q) (branch q)
                                                                        i =
                                                                      (1 : ℝ)) ∧
                                                                  DominantFiveBody.RelativeCollisionFree
                                                                      (DominantFiveBody.tripleChartPoints
                                                                        (q (1 : Fin (5 : ℕ)))
                                                                        (DominantFiveBody.tripleJointAlpha q)
                                                                        (branch q)) ∧
                                                                    DominantFiveBody.SeparatedSemicircle
                                                                        (DominantFiveBody.tripleChartAngles
                                                                          (q (1 : Fin (5 : ℕ)))
                                                                          (DominantFiveBody.tripleJointAlpha q)
                                                                          (branch q)) ∧
                                                                      ∀ (i : DominantFiveBody.Satellite),
                                                                        DominantFiveBody.coorbitalResidual
                                                                            (DominantFiveBody.tripleChartMass
                                                                              (q (1 : Fin (5 : ℕ)))
                                                                              (DominantFiveBody.tripleJointAlpha q))
                                                                            (DominantFiveBody.tripleChartAngles
                                                                              (q (1 : Fin (5 : ℕ)))
                                                                              (DominantFiveBody.tripleJointAlpha q)
                                                                              (branch q))
                                                                            i =
                                                                          (0 : ℝ)) := @DominantFiveBody.tripleChart_convex_physical_continuation

-- Source binding: prose:642
example : ∀ (alpha : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleWeights alpha →
    ∀ (psi : ℝ),
      |psi| = DominantFiveBody.Coorbital.h →
        ∀ (g : DominantFiveBody.TripleGaps),
          (∀ (i j : DominantFiveBody.TripleLabel),
              i ≠ j →
                (DominantFiveBody.tripleCenteringMatrix alpha).mulVec g i ≠
                  (DominantFiveBody.tripleCenteringMatrix alpha).mulVec g j) →
            (∀ (i : DominantFiveBody.TripleLabel),
                DominantFiveBody.tripleScalarResidual alpha ((DominantFiveBody.tripleCenteringMatrix alpha).mulVec g)
                    i =
                  (0 : ℝ)) →
              ∃ (delta : ℝ) (C : ℝ),
                (0 : ℝ) < delta ∧
                  (0 : ℝ) < C ∧
                    ∃ (branch : DominantFiveBody.TripleChartParameters → DominantFiveBody.TripleChartVariables),
                      branch (DominantFiveBody.tripleBoundaryParameter alpha) = DominantFiveBody.tripleUnitPoint psi g ∧
                        ContDiffOn ℝ ∞ branch (Metric.ball (DominantFiveBody.tripleBoundaryParameter alpha) delta) ∧
                          ∀ (q : DominantFiveBody.TripleChartParameters),
                            Dist.dist q (DominantFiveBody.tripleBoundaryParameter alpha) < delta →
                              DominantFiveBody.tripleChartParameterRows q (branch q) =
                                  (0 : DominantFiveBody.TripleChartVariables) ∧
                                (∑ i : DominantFiveBody.TripleLabel, DominantFiveBody.tripleJointAlpha q i = (1 : ℝ) →
                                  |branch q (0 : Fin (7 : ℕ)) - (1 : ℝ)| + |branch q (1 : Fin (7 : ℕ)) - (1 : ℝ)| +
                                        |branch q (2 : Fin (7 : ℕ))| +
                                      |branch q (3 : Fin (7 : ℕ))| ≤
                                    C * |q (0 : Fin (5 : ℕ))|) := @DominantFiveBody.tripleChart_radial_uniform_epsilon_bound

-- Source binding: prose:644
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ),
              DominantFiveBody.StrictConvexInOrder { labels := Equiv.refl DominantFiveBody.Label, primary_first := rfl }
                (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                      i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (3 : DominantFiveBody.Satellite) center →
                                    ∀ (eta : ℝ),
                                      (0 : ℝ) < eta →
                                        (∀ᶠ (n : ℕ) in Filter.atTop,
                                            ∀ (i j : DominantFiveBody.TripleLabel),
                                              i ≠ j →
                                                eta *
                                                    DominantFiveBody.tripleLowDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)) ≤
                                                  DominantFiveBody.satelliteDistance
                                                    (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc i)
                                                    (Fin.castSucc j)) →
                                          ∃ (phi : ℕ → ℕ),
                                            StrictMono phi ∧
                                              Nonempty
                                                (DominantFiveBody.TripleCapturedBranches (eps ∘ phi)
                                                  (fun (n : ℕ) => DominantFiveBody.triplePhysicalScale (mu (phi n)))
                                                  (fun (n : ℕ) => DominantFiveBody.triplePhysicalWeights (mu (phi n)))
                                                  (fun (n : ℕ) =>
                                                    DominantFiveBody.tripleVariablesFromPolar
                                                      (DominantFiveBody.triplePhysicalScale (mu (phi n)))
                                                      (DominantFiveBody.triplePhysicalWeights (mu (phi n))) (r (phi n))
                                                      fun (i : DominantFiveBody.Satellite) =>
                                                      theta (phi n) i - theta (phi n) (3 : DominantFiveBody.Satellite))
                                                  (-1 : ℝ)) := @DominantFiveBody.normalized_complete_lower_triple_regular_actual_capture

-- Source binding: prose:644
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                ∀ (center : DominantFiveBody.Plane),
                                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                      (0 : DominantFiveBody.Satellite) center →
                                    ∀ (eta : ℝ),
                                      (0 : ℝ) < eta →
                                        (∀ᶠ (n : ℕ) in Filter.atTop,
                                            ∀ (i j : DominantFiveBody.TripleLabel),
                                              i ≠ j →
                                                eta *
                                                    DominantFiveBody.tripleHighDiameter
                                                      (DominantFiveBody.satellitesRelative (x n)) ≤
                                                  DominantFiveBody.satelliteDistance
                                                    (DominantFiveBody.satellitesRelative (x n)) (Fin.succ i)
                                                    (Fin.succ j)) →
                                          ∃ (phi : ℕ → ℕ),
                                            StrictMono phi ∧
                                              Nonempty
                                                (DominantFiveBody.TripleCapturedBranches (eps ∘ phi)
                                                  (fun (n : ℕ) =>
                                                    DominantFiveBody.triplePhysicalScale
                                                      (mu (phi n) ∘
                                                        (⇑DominantFiveBody.upperTripleChartPermutation :
                                                          DominantFiveBody.Satellite → DominantFiveBody.Satellite)))
                                                  (fun (n : ℕ) =>
                                                    DominantFiveBody.triplePhysicalWeights
                                                      (mu (phi n) ∘
                                                        (⇑DominantFiveBody.upperTripleChartPermutation :
                                                          DominantFiveBody.Satellite → DominantFiveBody.Satellite)))
                                                  (fun (n : ℕ) =>
                                                    DominantFiveBody.tripleVariablesFromPolar
                                                      (DominantFiveBody.triplePhysicalScale
                                                        (mu (phi n) ∘
                                                          (⇑DominantFiveBody.upperTripleChartPermutation :
                                                            DominantFiveBody.Satellite → DominantFiveBody.Satellite)))
                                                      (DominantFiveBody.triplePhysicalWeights
                                                        (mu (phi n) ∘
                                                          (⇑DominantFiveBody.upperTripleChartPermutation :
                                                            DominantFiveBody.Satellite → DominantFiveBody.Satellite)))
                                                      (r (phi n) ∘
                                                        (⇑DominantFiveBody.upperTripleChartPermutation :
                                                          DominantFiveBody.Satellite → DominantFiveBody.Satellite))
                                                      fun (i : DominantFiveBody.Satellite) =>
                                                      theta (phi n)
                                                          ((DominantFiveBody.upperTripleChartPermutation :
                                                              DominantFiveBody.Satellite → DominantFiveBody.Satellite)
                                                            i) -
                                                        theta (phi n) (0 : DominantFiveBody.Satellite))
                                                  (1 : ℝ)) := @DominantFiveBody.normalized_complete_upper_triple_regular_actual_capture

-- Source binding: eq:nest-masses
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedChartMass t eta alpha =
      ![t ^ (3 : ℕ) * eta ^ (3 : ℕ) * alpha, t ^ (3 : ℕ) * eta ^ (3 : ℕ) * ((1 : ℝ) - alpha),
        t ^ (3 : ℕ) * ((1 : ℝ) - eta ^ (3 : ℕ)), (1 : ℝ) - t ^ (3 : ℕ)] ∧
    DominantFiveBody.nestedCoordinates t eta alpha (y (1 : Fin (7 : ℕ))) (y (2 : Fin (7 : ℕ))) (y (3 : Fin (7 : ℕ))) =
        ![y (1 : Fin (7 : ℕ)) - ((1 : ℝ) - eta ^ (3 : ℕ)) * t * y (2 : Fin (7 : ℕ)) -
            ((1 : ℝ) - alpha) * t * eta * y (3 : Fin (7 : ℕ)),
          y (1 : Fin (7 : ℕ)) - ((1 : ℝ) - eta ^ (3 : ℕ)) * t * y (2 : Fin (7 : ℕ)) +
            alpha * t * eta * y (3 : Fin (7 : ℕ)),
          y (1 : Fin (7 : ℕ)) + eta ^ (3 : ℕ) * t * y (2 : Fin (7 : ℕ))] ∧
      DominantFiveBody.nestedCoordinates t eta alpha (y (4 : Fin (7 : ℕ))) (y (5 : Fin (7 : ℕ))) (y (6 : Fin (7 : ℕ))) =
          ![y (4 : Fin (7 : ℕ)) - ((1 : ℝ) - eta ^ (3 : ℕ)) * t * y (5 : Fin (7 : ℕ)) -
              ((1 : ℝ) - alpha) * t * eta * y (6 : Fin (7 : ℕ)),
            y (4 : Fin (7 : ℕ)) - ((1 : ℝ) - eta ^ (3 : ℕ)) * t * y (5 : Fin (7 : ℕ)) +
              alpha * t * eta * y (6 : Fin (7 : ℕ)),
            y (4 : Fin (7 : ℕ)) + eta ^ (3 : ℕ) * t * y (5 : Fin (7 : ℕ))] ∧
        (DominantFiveBody.nestedChartRadii t eta alpha y =
            Fin.append
              (DominantFiveBody.nestedCoordinates t eta alpha (y (1 : Fin (7 : ℕ))) (y (2 : Fin (7 : ℕ)))
                (y (3 : Fin (7 : ℕ))))
              fun (x : Fin (1 : ℕ)) => y (0 : Fin (7 : ℕ))) ∧
          DominantFiveBody.nestedChartAngles t eta alpha y =
            Fin.append
              (DominantFiveBody.nestedCoordinates t eta alpha (y (4 : Fin (7 : ℕ))) (y (5 : Fin (7 : ℕ)))
                (y (6 : Fin (7 : ℕ))))
              fun (x : Fin (1 : ℕ)) => (0 : ℝ) := @DominantFiveBody.nestedChart_coordinates_complete

-- Source binding: eq:nest-rows
example : ∀ (t eta alpha : ℝ) (P : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.nestedPairAverage alpha P =
      alpha * P (0 : DominantFiveBody.Satellite) + ((1 : ℝ) - alpha) * P (1 : DominantFiveBody.Satellite) ∧
    DominantFiveBody.nestedRowAverage eta alpha P =
        eta ^ (3 : ℕ) *
            (alpha * P (0 : DominantFiveBody.Satellite) + ((1 : ℝ) - alpha) * P (1 : DominantFiveBody.Satellite)) +
          ((1 : ℝ) - eta ^ (3 : ℕ)) * P (2 : DominantFiveBody.Satellite) ∧
      DominantFiveBody.nestedRowOuterDifference t alpha P =
          (P (2 : DominantFiveBody.Satellite) -
              (alpha * P (0 : DominantFiveBody.Satellite) + ((1 : ℝ) - alpha) * P (1 : DominantFiveBody.Satellite))) /
            t ∧
        DominantFiveBody.nestedRowInnerDifference t eta P =
          (P (1 : DominantFiveBody.Satellite) - P (0 : DominantFiveBody.Satellite)) / (t * eta) := @DominantFiveBody.nestedRows_formula_complete

-- Source binding: eq:nest-recovery
example : ∀ (t eta alpha : ℝ) (rows : DominantFiveBody.Satellite → ℝ),
  t ≠ (0 : ℝ) →
    eta ≠ (0 : ℝ) →
      DominantFiveBody.nestedPairAverage alpha rows =
          DominantFiveBody.nestedRowAverage eta alpha rows -
            ((1 : ℝ) - eta ^ (3 : ℕ)) * t * DominantFiveBody.nestedRowOuterDifference t alpha rows ∧
        rows (2 : DominantFiveBody.Satellite) =
            DominantFiveBody.nestedRowAverage eta alpha rows +
              eta ^ (3 : ℕ) * t * DominantFiveBody.nestedRowOuterDifference t alpha rows ∧
          rows (0 : DominantFiveBody.Satellite) =
              DominantFiveBody.nestedPairAverage alpha rows -
                ((1 : ℝ) - alpha) * t * eta * DominantFiveBody.nestedRowInnerDifference t eta rows ∧
            rows (1 : DominantFiveBody.Satellite) =
              DominantFiveBody.nestedPairAverage alpha rows +
                alpha * t * eta * DominantFiveBody.nestedRowInnerDifference t eta rows := @DominantFiveBody.nestedRows_recovery

-- Source binding: prose:675
example : ∀ (t eta alpha : ℝ),
  ((LinearMap.toMatrix' : ((Fin (7 : ℕ) → ℝ) →ₗ[ℝ] Fin (7 : ℕ) → ℝ) → Matrix (Fin (7 : ℕ)) (Fin (7 : ℕ)) ℝ)
          (↑(DominantFiveBody.nestedToFixedSlice t eta alpha) :
            DominantFiveBody.NestedChartVariables →ₗ[ℝ] DominantFiveBody.SliceCoordinates)).submatrix
      (⇑DominantFiveBody.nestedCoordinateIndex : Fin (1 : ℕ) ⊕ Fin (3 : ℕ) ⊕ Fin (3 : ℕ) → Fin (7 : ℕ))
      (⇑DominantFiveBody.nestedCoordinateIndex : Fin (1 : ℕ) ⊕ Fin (3 : ℕ) ⊕ Fin (3 : ℕ) → Fin (7 : ℕ)) =
    Matrix.fromBlocks (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) ℝ)
      (0 : Matrix (Fin (1 : ℕ)) (Fin (3 : ℕ) ⊕ Fin (3 : ℕ)) ℝ) (0 : Matrix (Fin (3 : ℕ) ⊕ Fin (3 : ℕ)) (Fin (1 : ℕ)) ℝ)
      (Matrix.fromBlocks (DominantFiveBody.nestedCoordinateBlock t eta alpha) (0 : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) ℝ)
        (0 : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) ℝ) (DominantFiveBody.nestedCoordinateBlock t eta alpha)) := @DominantFiveBody.nestedToFixedSlice_full_matrix

-- Source binding: prose:675
example : ∀ (t eta alpha : ℝ),
  ((LinearMap.toMatrix' : ((Fin (7 : ℕ) → ℝ) →ₗ[ℝ] Fin (7 : ℕ) → ℝ) → Matrix (Fin (7 : ℕ)) (Fin (7 : ℕ)) ℝ)
        (↑(DominantFiveBody.nestedToFixedSlice t eta alpha) :
          DominantFiveBody.NestedChartVariables →ₗ[ℝ] DominantFiveBody.SliceCoordinates)).det =
    t ^ (4 : ℕ) * eta ^ (2 : ℕ) := @DominantFiveBody.nestedToFixedSlice_full_det

-- Source binding: prose:675
example : ∀ (t eta alpha : ℝ),
  |((LinearMap.toMatrix' : ((Fin (7 : ℕ) → ℝ) →ₗ[ℝ] Fin (7 : ℕ) → ℝ) → Matrix (Fin (7 : ℕ)) (Fin (7 : ℕ)) ℝ)
          (↑(DominantFiveBody.nestedToFixedSlice t eta alpha) :
            DominantFiveBody.NestedChartVariables →ₗ[ℝ] DominantFiveBody.SliceCoordinates)).det| =
    t ^ (4 : ℕ) * eta ^ (2 : ℕ) := @DominantFiveBody.nestedToFixedSlice_full_abs_det

-- Source binding: prose:675
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  t ≠ (0 : ℝ) →
    eta ≠ (0 : ℝ) →
      (1 : ℝ) - t ^ (3 : ℕ) ≠ (0 : ℝ) →
        (DominantFiveBody.nestedChartPhysicalRows eps t eta alpha y = (0 : DominantFiveBody.NestedChartVariables) ↔
          (∀ (i : DominantFiveBody.Satellite),
              DominantFiveBody.radialResidual eps (DominantFiveBody.nestedChartMass t eta alpha)
                  (DominantFiveBody.nestedChartRadii t eta alpha y) (DominantFiveBody.nestedChartAngles t eta alpha y)
                  i =
                (0 : ℝ)) ∧
            ∀ (i : DominantFiveBody.Satellite),
              DominantFiveBody.angularResidual eps (DominantFiveBody.nestedChartMass t eta alpha)
                  (DominantFiveBody.nestedChartRadii t eta alpha y) (DominantFiveBody.nestedChartAngles t eta alpha y)
                  i =
                (0 : ℝ)) := @DominantFiveBody.nestedChartPhysicalRows_zero_iff

-- Source binding: prose:675
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  (0 : ℝ) < eps →
    (0 : ℝ) < t →
      (0 : ℝ) < eta →
        DominantFiveBody.PositiveRatio (DominantFiveBody.nestedChartMass t eta alpha) →
          DominantFiveBody.NestedChartRegular eps t eta alpha y →
            (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < DominantFiveBody.nestedChartRadii t eta alpha y i) →
              (DominantFiveBody.nestedChartExtendedRows eps t eta alpha y =
                  (0 : DominantFiveBody.NestedChartVariables) ↔
                DominantFiveBody.NormalizedCentralConfiguration
                  (DominantFiveBody.masses eps (DominantFiveBody.nestedChartMass t eta alpha))
                  (DominantFiveBody.centeredFromRelative eps (DominantFiveBody.nestedChartMass t eta alpha)
                    (DominantFiveBody.nestedChartPoints t eta alpha y))) := @DominantFiveBody.nestedChartExtendedRows_zero_iff_normalized

-- Source binding: prose:677
example : ∀ (eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedOuterRadialGaps eta alpha y =
      ![y (2 : Fin (7 : ℕ)) + ((1 : ℝ) - alpha) * eta * y (3 : Fin (7 : ℕ)),
        y (2 : Fin (7 : ℕ)) - alpha * eta * y (3 : Fin (7 : ℕ))] ∧
    DominantFiveBody.nestedOuterAngularGaps eta alpha y =
      ![y (5 : Fin (7 : ℕ)) + ((1 : ℝ) - alpha) * eta * y (6 : Fin (7 : ℕ)),
        y (5 : Fin (7 : ℕ)) - alpha * eta * y (6 : Fin (7 : ℕ))] := @DominantFiveBody.nestedGaps_formula_complete

-- Source binding: prose:677
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  (0 : ℝ) < t →
    (0 : ℝ) < eta →
      (0 : ℝ) < DominantFiveBody.nestedInnerWSq t eta alpha y →
        DominantFiveBody.satelliteDistance (DominantFiveBody.nestedChartPoints t eta alpha y)
            (0 : DominantFiveBody.Satellite) (1 : DominantFiveBody.Satellite) =
          t * eta * DominantFiveBody.nestedInnerW t eta alpha y := @DominantFiveBody.nestedInner_distance

-- Source binding: prose:677
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : Fin (2 : ℕ)),
  (0 : ℝ) < t →
    (0 : ℝ) < DominantFiveBody.nestedOuterWSq t eta alpha y i →
      DominantFiveBody.satelliteDistance (DominantFiveBody.nestedChartPoints t eta alpha y) (Fin.castAdd (2 : ℕ) i)
          (2 : DominantFiveBody.Satellite) =
        t * DominantFiveBody.nestedOuterW t eta alpha y i := @DominantFiveBody.nestedOuter_distance

-- Source binding: eq:nest-distances
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedInnerWSq t eta alpha y =
    y (3 : Fin (7 : ℕ)) ^ (2 : ℕ) +
      DominantFiveBody.nestedChartRadii t eta alpha y (0 : DominantFiveBody.Satellite) *
            DominantFiveBody.nestedChartRadii t eta alpha y (1 : DominantFiveBody.Satellite) *
          y (6 : Fin (7 : ℕ)) ^ (2 : ℕ) *
        Real.sinc (t * eta * y (6 : Fin (7 : ℕ)) / (2 : ℝ)) ^ (2 : ℕ) := @DominantFiveBody.nestedInnerWSq_formula

-- Source binding: eq:nest-distances
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : Fin (2 : ℕ)),
  DominantFiveBody.nestedOuterWSq t eta alpha y i =
    DominantFiveBody.nestedOuterRadialGaps eta alpha y i ^ (2 : ℕ) +
      DominantFiveBody.nestedChartRadii t eta alpha y (Fin.castAdd (2 : ℕ) i) *
            DominantFiveBody.nestedChartRadii t eta alpha y (2 : DominantFiveBody.Satellite) *
          DominantFiveBody.nestedOuterAngularGaps eta alpha y i ^ (2 : ℕ) *
        Real.sinc (t * DominantFiveBody.nestedOuterAngularGaps eta alpha y i / (2 : ℝ)) ^ (2 : ℕ) := @DominantFiveBody.nestedOuterWSq_formula

-- Source binding: display:684
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (rho v : ℝ),
  DominantFiveBody.nestedScalarH eps t eta alpha y rho v =
    -((1 : ℝ) - t ^ (3 : ℕ)) * rho * y (0 : Fin (7 : ℕ)) * Real.sin v *
      ((‖DominantFiveBody.polarPoint rho v - DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ)‖ ^ (3 : ℕ))⁻¹ -
        ((1 : ℝ) + eps)⁻¹) := @DominantFiveBody.nestedScalarH_source_formula

-- Source binding: display:684
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (rho v : ℝ),
  DominantFiveBody.nestedScalarK eps t eta alpha y rho v =
    rho - (rho ^ (2 : ℕ))⁻¹ -
        eps * ((1 : ℝ) - t ^ (3 : ℕ)) * (rho - y (0 : Fin (7 : ℕ)) * Real.cos v) /
          ‖DominantFiveBody.polarPoint rho v - DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ)‖ ^ (3 : ℕ) -
      eps * ((1 : ℝ) + eps)⁻¹ *
        Inner.inner ℝ
          (DominantFiveBody.relativeAverage (DominantFiveBody.nestedChartMass t eta alpha)
            (DominantFiveBody.nestedChartPoints t eta alpha y))
          (DominantFiveBody.polarPoint (1 : ℝ) v) := @DominantFiveBody.nestedScalarK_source_formula

-- Source binding: display:684
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : DominantFiveBody.Satellite),
  DominantFiveBody.nestedAngularExterior eps t eta alpha y i =
      DominantFiveBody.nestedScalarH eps t eta alpha y (DominantFiveBody.nestedChartRadii t eta alpha y i)
        (DominantFiveBody.nestedChartAngles t eta alpha y i) ∧
    DominantFiveBody.nestedRadialExterior eps t eta alpha y i =
      DominantFiveBody.nestedScalarK eps t eta alpha y (DominantFiveBody.nestedChartRadii t eta alpha y i)
        (DominantFiveBody.nestedChartAngles t eta alpha y i) := @DominantFiveBody.nestedScalarFields_at_actual_targets

-- Source binding: display:684
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : Fin (3 : ℕ)),
  (0 : ℝ) < t →
    (0 : ℝ) < eta →
      (0 : ℝ) < DominantFiveBody.nestedInnerWSq t eta alpha y →
        (∀ (j : Fin (2 : ℕ)), (0 : ℝ) < DominantFiveBody.nestedOuterWSq t eta alpha y j) →
          DominantFiveBody.radialResidual eps (DominantFiveBody.nestedChartMass t eta alpha)
              (DominantFiveBody.nestedChartRadii t eta alpha y) (DominantFiveBody.nestedChartAngles t eta alpha y)
              i.castSucc =
            DominantFiveBody.nestedRadialExterior eps t eta alpha y i.castSucc +
              DominantFiveBody.nestedInternalRadial eps t eta alpha y i.castSucc := @DominantFiveBody.nestedRadialExterior_recovery

-- Source binding: display:684
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : Fin (3 : ℕ)),
  (0 : ℝ) < t →
    (0 : ℝ) < eta →
      (0 : ℝ) < DominantFiveBody.nestedInnerWSq t eta alpha y →
        (∀ (j : Fin (2 : ℕ)), (0 : ℝ) < DominantFiveBody.nestedOuterWSq t eta alpha y j) →
          (1 : ℝ) + eps ≠ (0 : ℝ) →
            DominantFiveBody.angularResidual eps (DominantFiveBody.nestedChartMass t eta alpha)
                (DominantFiveBody.nestedChartRadii t eta alpha y) (DominantFiveBody.nestedChartAngles t eta alpha y)
                i.castSucc =
              DominantFiveBody.nestedAngularExterior eps t eta alpha y i.castSucc +
                DominantFiveBody.nestedInternalAngular eps t eta alpha y i.castSucc := @DominantFiveBody.nestedAngularExterior_recovery

-- Source binding: display:693
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : Fin (2 : ℕ)),
  DominantFiveBody.nestedOuterL eps t eta alpha y i =
    DominantFiveBody.nestedChartRadii t eta alpha y (Fin.castAdd (2 : ℕ) i) *
            DominantFiveBody.nestedChartRadii t eta alpha y (2 : DominantFiveBody.Satellite) *
          DominantFiveBody.nestedOuterAngularGaps eta alpha y i *
        Real.sinc (t * DominantFiveBody.nestedOuterAngularGaps eta alpha y i) *
      ((DominantFiveBody.nestedOuterW t eta alpha y i ^ (3 : ℕ))⁻¹ - t ^ (3 : ℕ) / ((1 : ℝ) + eps)) := @DominantFiveBody.nestedOuterL_formula

-- Source binding: display:693
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedInnerM eps t eta alpha y =
    DominantFiveBody.nestedChartRadii t eta alpha y (0 : DominantFiveBody.Satellite) *
            DominantFiveBody.nestedChartRadii t eta alpha y (1 : DominantFiveBody.Satellite) *
          y (6 : Fin (7 : ℕ)) *
        Real.sinc (t * eta * y (6 : Fin (7 : ℕ))) *
      ((DominantFiveBody.nestedInnerW t eta alpha y ^ (3 : ℕ))⁻¹ - t ^ (3 : ℕ) * eta ^ (3 : ℕ) / ((1 : ℝ) + eps)) := @DominantFiveBody.nestedInnerM_formula

-- Source binding: eq:nest-angular
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  (0 : ℝ) < t →
    (0 : ℝ) < eta →
      (1 : ℝ) + eps ≠ (0 : ℝ) →
        (0 : ℝ) < DominantFiveBody.nestedInnerWSq t eta alpha y →
          (∀ (i : Fin (2 : ℕ)), (0 : ℝ) < DominantFiveBody.nestedOuterWSq t eta alpha y i) →
            have T :=
              DominantFiveBody.angularResidual eps (DominantFiveBody.nestedChartMass t eta alpha)
                (DominantFiveBody.nestedChartRadii t eta alpha y) (DominantFiveBody.nestedChartAngles t eta alpha y);
            have H := DominantFiveBody.nestedScalarTargetH eps t eta alpha y;
            have L0 :=
              alpha * DominantFiveBody.nestedOuterL eps t eta alpha y (0 : Fin (2 : ℕ)) +
                ((1 : ℝ) - alpha) * DominantFiveBody.nestedOuterL eps t eta alpha y (1 : Fin (2 : ℕ));
            DominantFiveBody.nestedRowAverage eta alpha T =
                eta ^ (3 : ℕ) * DominantFiveBody.nestedPairAverage alpha H +
                  ((1 : ℝ) - eta ^ (3 : ℕ)) * H (2 : DominantFiveBody.Satellite) ∧
              DominantFiveBody.nestedRowOuterDifference t alpha T =
                  (H (2 : DominantFiveBody.Satellite) - DominantFiveBody.nestedPairAverage alpha H) / t - L0 ∧
                DominantFiveBody.nestedRowInnerDifference t eta T =
                  (H (1 : DominantFiveBody.Satellite) - H (0 : DominantFiveBody.Satellite)) / (t * eta) +
                      ((1 : ℝ) - eta ^ (3 : ℕ)) *
                          (DominantFiveBody.nestedOuterL eps t eta alpha y (1 : Fin (2 : ℕ)) -
                            DominantFiveBody.nestedOuterL eps t eta alpha y (0 : Fin (2 : ℕ))) /
                        eta -
                    DominantFiveBody.nestedInnerM eps t eta alpha y := @DominantFiveBody.nestedAngularRows_source_complete

-- Source binding: display:706
example : ∀ (eps t rc : ℝ) (v : DominantFiveBody.NestedScalarTarget),
  (0 : ℝ) < DominantFiveBody.nestedScalarTargetWSq t rc v →
    DominantFiveBody.nestedScalarAngularKernel eps t rc v =
      v.1 * rc * v.2.2 * Real.sinc (t * v.2.2) *
        ((v.2.1 ^ (2 : ℕ) + v.1 * rc * v.2.2 ^ (2 : ℕ) * Real.sinc (t * v.2.2 / (2 : ℝ)) ^ (2 : ℕ)) ^ (-3 / 2 : ℝ) -
          t ^ (3 : ℕ) / ((1 : ℝ) + eps)) := @DominantFiveBody.nestedScalarAngularKernel_formula

-- Source binding: display:706
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : Fin (2 : ℕ)),
  DominantFiveBody.nestedScalarAngularKernel eps t
      (DominantFiveBody.nestedChartRadii t eta alpha y (2 : DominantFiveBody.Satellite))
      (DominantFiveBody.nestedScalarTargetPoint t eta alpha y i) =
    DominantFiveBody.nestedOuterL eps t eta alpha y i := @DominantFiveBody.nestedScalarAngularKernel_substitution

-- Source binding: eq:nest-kernel-difference
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  eta ≠ (0 : ℝ) →
    (∀ s ∈ Set.Icc (-((1 : ℝ) - alpha)) alpha,
        (0 : ℝ) <
          DominantFiveBody.nestedScalarTargetWSq t
            (DominantFiveBody.nestedChartRadii t eta alpha y (2 : DominantFiveBody.Satellite))
            (DominantFiveBody.nestedOriginalScalarPath t eta alpha y s)) →
      (DominantFiveBody.nestedOuterL eps t eta alpha y (1 : Fin (2 : ℕ)) -
            DominantFiveBody.nestedOuterL eps t eta alpha y (0 : Fin (2 : ℕ))) /
          eta =
        ∫ (s : ℝ) in -((1 : ℝ) - alpha)..alpha,
          t * y (3 : Fin (7 : ℕ)) *
                (fderiv ℝ
                      (DominantFiveBody.nestedScalarAngularKernel eps t
                        (DominantFiveBody.nestedChartRadii t eta alpha y (2 : DominantFiveBody.Satellite)))
                      (DominantFiveBody.nestedOriginalScalarPath t eta alpha y s) :
                    DominantFiveBody.NestedScalarTarget → ℝ)
                  ((1 : ℝ), (0 : ℝ), (0 : ℝ)) -
              y (3 : Fin (7 : ℕ)) *
                (fderiv ℝ
                      (DominantFiveBody.nestedScalarAngularKernel eps t
                        (DominantFiveBody.nestedChartRadii t eta alpha y (2 : DominantFiveBody.Satellite)))
                      (DominantFiveBody.nestedOriginalScalarPath t eta alpha y s) :
                    DominantFiveBody.NestedScalarTarget → ℝ)
                  ((0 : ℝ), (1 : ℝ), (0 : ℝ)) -
            y (6 : Fin (7 : ℕ)) *
              (fderiv ℝ
                    (DominantFiveBody.nestedScalarAngularKernel eps t
                      (DominantFiveBody.nestedChartRadii t eta alpha y (2 : DominantFiveBody.Satellite)))
                    (DominantFiveBody.nestedOriginalScalarPath t eta alpha y s) :
                  DominantFiveBody.NestedScalarTarget → ℝ)
                ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := @DominantFiveBody.nestedOuterL_original_integral

-- Source binding: eq:nest-kernel-difference
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedOriginalScalarPath t eta alpha y (-((1 : ℝ) - alpha)) =
      DominantFiveBody.nestedScalarTargetPoint t eta alpha y (0 : Fin (2 : ℕ)) ∧
    DominantFiveBody.nestedOriginalScalarPath t eta alpha y alpha =
      DominantFiveBody.nestedScalarTargetPoint t eta alpha y (1 : Fin (2 : ℕ)) := @DominantFiveBody.nestedOriginalScalarPath_endpoints

-- Source binding: eq:nest-kernel-difference
example : ∀ (psi omega : ℝ),
  |omega| = (1 : ℝ) →
    ∃ (delta : ℝ),
      (0 : ℝ) < delta ∧
        ∀ alpha0 ∈ Set.Icc (0 : ℝ) (1 : ℝ),
          ∀ (v : DominantFiveBody.NestedJointVariables),
            Dist.dist v
                  (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0,
                    DominantFiveBody.nestedBasePoint psi omega) <
                delta →
              ∀ s ∈ Set.Icc (-1 : ℝ) (1 : ℝ),
                (0 : ℝ) <
                  DominantFiveBody.nestedScalarTargetWSq (v.1 (1 : Fin (4 : ℕ)))
                    (DominantFiveBody.nestedChartRadii (v.1 (1 : Fin (4 : ℕ))) (v.1 (2 : Fin (4 : ℕ)))
                      (v.1 (3 : Fin (4 : ℕ))) v.2 (2 : DominantFiveBody.Satellite))
                    (DominantFiveBody.nestedOriginalScalarPath (v.1 (1 : Fin (4 : ℕ))) (v.1 (2 : Fin (4 : ℕ)))
                      (v.1 (3 : Fin (4 : ℕ))) v.2 s) := @DominantFiveBody.nestedOriginalScalarPath_positive_common_tube

-- Source binding: prose:716
example : ∀ (g : ℝ → ℝ) (alpha : ℝ),
  ∫ (s : ℝ) in -((1 : ℝ) - alpha)..alpha, g s = ∫ (x : ℝ) in (0 : ℝ)..(1 : ℝ), g (x - ((1 : ℝ) - alpha)) := @DominantFiveBody.nested_kernel_integral_shift

-- Source binding: display:719
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : Fin (2 : ℕ)),
  DominantFiveBody.nestedOuterN t eta alpha y i =
    (DominantFiveBody.nestedOuterRadialGaps eta alpha y i -
        DominantFiveBody.nestedChartRadii t eta alpha y (2 : DominantFiveBody.Satellite) *
          DominantFiveBody.singleScaleChi t (DominantFiveBody.nestedOuterAngularGaps eta alpha y i)) *
      (DominantFiveBody.nestedOuterW t eta alpha y i ^ (3 : ℕ))⁻¹ := @DominantFiveBody.nestedOuterN_formula

-- Source binding: display:719
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : Fin (2 : ℕ)),
  DominantFiveBody.nestedOuterO t eta alpha y i =
    (DominantFiveBody.nestedOuterRadialGaps eta alpha y i +
        DominantFiveBody.nestedChartRadii t eta alpha y (Fin.castAdd (2 : ℕ) i) *
          DominantFiveBody.singleScaleChi t (DominantFiveBody.nestedOuterAngularGaps eta alpha y i)) *
      (DominantFiveBody.nestedOuterW t eta alpha y i ^ (3 : ℕ))⁻¹ := @DominantFiveBody.nestedOuterO_formula

-- Source binding: display:719
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedInnerN t eta alpha y =
    (y (3 : Fin (7 : ℕ)) -
        DominantFiveBody.nestedChartRadii t eta alpha y (1 : DominantFiveBody.Satellite) *
          DominantFiveBody.singleScaleChi (t * eta) (y (6 : Fin (7 : ℕ)))) *
      (DominantFiveBody.nestedInnerW t eta alpha y ^ (3 : ℕ))⁻¹ := @DominantFiveBody.nestedInnerN_source_formula

-- Source binding: display:719
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedInnerO t eta alpha y =
    (y (3 : Fin (7 : ℕ)) +
        DominantFiveBody.nestedChartRadii t eta alpha y (0 : DominantFiveBody.Satellite) *
          DominantFiveBody.singleScaleChi (t * eta) (y (6 : Fin (7 : ℕ)))) *
      (DominantFiveBody.nestedInnerW t eta alpha y ^ (3 : ℕ))⁻¹ := @DominantFiveBody.nestedInnerO_source_formula

-- Source binding: prose:727
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedInnerJ eps t eta alpha y =
    -eps * t * eta * alpha * ((1 : ℝ) - alpha) *
          (DominantFiveBody.nestedChartRadii t eta alpha y (0 : DominantFiveBody.Satellite) +
            DominantFiveBody.nestedChartRadii t eta alpha y (1 : DominantFiveBody.Satellite)) *
        DominantFiveBody.singleScaleChi (t * eta) (y (6 : Fin (7 : ℕ))) *
      (DominantFiveBody.nestedInnerW t eta alpha y ^ (3 : ℕ))⁻¹ := @DominantFiveBody.nestedInnerJ_formula_complete

-- Source binding: eq:nest-radial
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  (0 : ℝ) < t →
    (0 : ℝ) < eta →
      (0 : ℝ) < DominantFiveBody.nestedInnerWSq t eta alpha y →
        (∀ (i : Fin (2 : ℕ)), (0 : ℝ) < DominantFiveBody.nestedOuterWSq t eta alpha y i) →
          have R :=
            DominantFiveBody.radialResidual eps (DominantFiveBody.nestedChartMass t eta alpha)
              (DominantFiveBody.nestedChartRadii t eta alpha y) (DominantFiveBody.nestedChartAngles t eta alpha y);
          have K := DominantFiveBody.nestedScalarTargetK eps t eta alpha y;
          have N0 :=
            alpha * DominantFiveBody.nestedOuterN t eta alpha y (0 : Fin (2 : ℕ)) +
              ((1 : ℝ) - alpha) * DominantFiveBody.nestedOuterN t eta alpha y (1 : Fin (2 : ℕ));
          have O0 :=
            alpha * DominantFiveBody.nestedOuterO t eta alpha y (0 : Fin (2 : ℕ)) +
              ((1 : ℝ) - alpha) * DominantFiveBody.nestedOuterO t eta alpha y (1 : Fin (2 : ℕ));
          have J := DominantFiveBody.nestedInnerJ eps t eta alpha y;
          DominantFiveBody.nestedRowAverage eta alpha R =
              eta ^ (3 : ℕ) * DominantFiveBody.nestedPairAverage alpha K +
                    ((1 : ℝ) - eta ^ (3 : ℕ)) * K (2 : DominantFiveBody.Satellite) +
                  eps * t * eta ^ (3 : ℕ) * ((1 : ℝ) - eta ^ (3 : ℕ)) * (N0 - O0) +
                eta ^ (3 : ℕ) * J ∧
            DominantFiveBody.nestedRowOuterDifference t alpha R =
                (K (2 : DominantFiveBody.Satellite) - DominantFiveBody.nestedPairAverage alpha K) / t -
                    eps * (eta ^ (3 : ℕ) * O0 + ((1 : ℝ) - eta ^ (3 : ℕ)) * N0) -
                  J / t ∧
              DominantFiveBody.nestedRowInnerDifference t eta R =
                (K (1 : DominantFiveBody.Satellite) - K (0 : DominantFiveBody.Satellite)) / (t * eta) +
                    eps * ((1 : ℝ) - eta ^ (3 : ℕ)) *
                        (DominantFiveBody.nestedOuterN t eta alpha y (1 : Fin (2 : ℕ)) -
                          DominantFiveBody.nestedOuterN t eta alpha y (0 : Fin (2 : ℕ))) /
                      eta -
                  eps *
                    (alpha * DominantFiveBody.nestedInnerO t eta alpha y +
                      ((1 : ℝ) - alpha) * DominantFiveBody.nestedInnerN t eta alpha y) := @DominantFiveBody.nestedRadialRows_source_complete

-- Source binding: prose:737
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedInnerJ eps t eta alpha y = t * DominantFiveBody.nestedInnerJOverT eps t eta alpha y := @DominantFiveBody.nestedInnerJ_factor

-- Source binding: prose:737
example : ∀ (n : ℕ∞ω) (v : DominantFiveBody.NestedJointVariables),
  (0 : ℝ) <
      DominantFiveBody.nestedInnerWSq (v.1 (1 : Fin (4 : ℕ))) (v.1 (2 : Fin (4 : ℕ))) (v.1 (3 : Fin (4 : ℕ))) v.2 →
    ContDiffAt ℝ n
      (fun (w : DominantFiveBody.NestedJointVariables) =>
        DominantFiveBody.nestedInnerJOverT (w.1 (0 : Fin (4 : ℕ))) (w.1 (1 : Fin (4 : ℕ))) (w.1 (2 : Fin (4 : ℕ)))
          (w.1 (3 : Fin (4 : ℕ))) w.2)
      v := @DominantFiveBody.nestedInnerJOverT_joint_contDiffAt

-- Source binding: prose:737
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  eta ≠ (0 : ℝ) →
    (∀ s ∈ Set.Icc (-((1 : ℝ) - alpha)) alpha,
        (0 : ℝ) <
          DominantFiveBody.nestedScalarTargetWSq t
            (DominantFiveBody.nestedChartRadii t eta alpha y (2 : DominantFiveBody.Satellite))
            (DominantFiveBody.nestedOriginalScalarPath t eta alpha y s)) →
      (DominantFiveBody.nestedOuterN t eta alpha y (1 : Fin (2 : ℕ)) -
            DominantFiveBody.nestedOuterN t eta alpha y (0 : Fin (2 : ℕ))) /
          eta =
        ∫ (s : ℝ) in -((1 : ℝ) - alpha)..alpha,
          t * y (3 : Fin (7 : ℕ)) *
                (fderiv ℝ
                      (DominantFiveBody.nestedScalarRadialKernel t
                        (DominantFiveBody.nestedChartRadii t eta alpha y (2 : DominantFiveBody.Satellite)))
                      (DominantFiveBody.nestedOriginalScalarPath t eta alpha y s) :
                    DominantFiveBody.NestedScalarTarget → ℝ)
                  ((1 : ℝ), (0 : ℝ), (0 : ℝ)) -
              y (3 : Fin (7 : ℕ)) *
                (fderiv ℝ
                      (DominantFiveBody.nestedScalarRadialKernel t
                        (DominantFiveBody.nestedChartRadii t eta alpha y (2 : DominantFiveBody.Satellite)))
                      (DominantFiveBody.nestedOriginalScalarPath t eta alpha y s) :
                    DominantFiveBody.NestedScalarTarget → ℝ)
                  ((0 : ℝ), (1 : ℝ), (0 : ℝ)) -
            y (6 : Fin (7 : ℕ)) *
              (fderiv ℝ
                    (DominantFiveBody.nestedScalarRadialKernel t
                      (DominantFiveBody.nestedChartRadii t eta alpha y (2 : DominantFiveBody.Satellite)))
                    (DominantFiveBody.nestedOriginalScalarPath t eta alpha y s) :
                  DominantFiveBody.NestedScalarTarget → ℝ)
                ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := @DominantFiveBody.nestedOuterN_original_integral

-- Source binding: display:738
example : ∀ (t rc : ℝ) (v : DominantFiveBody.NestedScalarTarget),
  (0 : ℝ) < DominantFiveBody.nestedScalarTargetWSq t rc v →
    DominantFiveBody.nestedScalarRadialKernel t rc v =
      (v.2.1 - rc * DominantFiveBody.singleScaleChi t v.2.2) *
        (v.2.1 ^ (2 : ℕ) + v.1 * rc * v.2.2 ^ (2 : ℕ) * Real.sinc (t * v.2.2 / (2 : ℝ)) ^ (2 : ℕ)) ^ (-3 / 2 : ℝ) := @DominantFiveBody.nestedScalarRadialKernel_formula

-- Source binding: display:738
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : Fin (2 : ℕ)),
  DominantFiveBody.nestedScalarRadialKernel t
      (DominantFiveBody.nestedChartRadii t eta alpha y (2 : DominantFiveBody.Satellite))
      (DominantFiveBody.nestedScalarTargetPoint t eta alpha y i) =
    DominantFiveBody.nestedOuterN t eta alpha y i := @DominantFiveBody.nestedScalarRadialKernel_substitution

-- Source binding: prose:742
example : ∀ (n : ℕ∞ω) (v : DominantFiveBody.NestedJointVariables),
  DominantFiveBody.NestedChartRegular (v.1 (0 : Fin (4 : ℕ))) (v.1 (1 : Fin (4 : ℕ))) (v.1 (2 : Fin (4 : ℕ)))
      (v.1 (3 : Fin (4 : ℕ))) v.2 →
    ContDiffAt ℝ n
      (fun (w : DominantFiveBody.NestedJointVariables) =>
        DominantFiveBody.nestedChartExtendedRows (w.1 (0 : Fin (4 : ℕ))) (w.1 (1 : Fin (4 : ℕ))) (w.1 (2 : Fin (4 : ℕ)))
          (w.1 (3 : Fin (4 : ℕ))) w.2)
      v := @DominantFiveBody.nestedChartExtendedRows_joint_contDiffAt

-- Source binding: prose:742
example : ∀ (psi omega : ℝ),
  |psi| = DominantFiveBody.Coorbital.h →
    |omega| = (1 : ℝ) →
      ∀ (tolerance : ℝ),
        (0 : ℝ) < tolerance →
          ∃ (delta : ℝ) (r : ℝ) (C : ℝ),
            (0 : ℝ) < delta ∧
              (0 : ℝ) < r ∧
                (0 : ℝ) < C ∧
                  r ≤ tolerance ∧
                    delta ≤ r ∧
                      ∀ alpha ∈ Set.Icc (0 : ℝ) (1 : ℝ),
                        ∃ (branch : DominantFiveBody.NestedChartParameters → DominantFiveBody.NestedChartVariables),
                          branch ![(0 : ℝ), (0 : ℝ), (0 : ℝ), alpha] = DominantFiveBody.nestedBasePoint psi omega ∧
                            ContDiffOn ℝ ∞ branch (Metric.ball ![(0 : ℝ), (0 : ℝ), (0 : ℝ), alpha] delta) ∧
                              ∀ (q : Fin (Nat.succ (0 : ℕ)).succ.succ.succ → ℝ),
                                Dist.dist q ![(0 : ℝ), (0 : ℝ), (0 : ℝ), alpha] < delta →
                                  Dist.dist (branch q) (DominantFiveBody.nestedBasePoint psi omega) < r / (2 : ℝ) ∧
                                    DominantFiveBody.NestedContinuationDomain (q, branch q) ∧
                                      (DominantFiveBody.nestedChartJacobian
                                            (q (0 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                            (q (1 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                            (q (2 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                            (q (3 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ)) (branch q)).IsInvertible ∧
                                        ‖(DominantFiveBody.nestedChartJacobian
                                                  (q (0 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                  (q (1 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                  (q (2 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ))
                                                  (q (3 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ)) (branch q)).inverse‖ ≤
                                            C ∧
                                          DominantFiveBody.nestedChartParameterRows q (branch q) =
                                              (0 : DominantFiveBody.NestedChartVariables) ∧
                                            ∀ (y : DominantFiveBody.NestedChartVariables),
                                              Dist.dist y (DominantFiveBody.nestedBasePoint psi omega) < r →
                                                (DominantFiveBody.nestedChartParameterRows q y =
                                                    (0 : DominantFiveBody.NestedChartVariables) ↔
                                                  branch q = y) := @DominantFiveBody.nestedChart_compact_boundary_continuation

-- Source binding: prose:744
example : ∀ (alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedRadialMean (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha y =
    y (1 : Fin (7 : ℕ)) - (y (1 : Fin (7 : ℕ)) ^ (2 : ℕ))⁻¹ := @DominantFiveBody.nestedRadialMean_at_boundary

-- Source binding: prose:744
example : ∀ (alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedRadialOuterDifference (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha y =
    y (2 : Fin (7 : ℕ)) *
      ((1 : ℝ) + (2 : ℝ) * y (1 : Fin (7 : ℕ)) / (y (1 : Fin (7 : ℕ)) ^ (2 : ℕ) * y (1 : Fin (7 : ℕ)) ^ (2 : ℕ))) := @DominantFiveBody.nestedRadialOuterDifference_at_boundary

-- Source binding: prose:744
example : ∀ (alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedRadialInnerDifference (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha y =
    y (3 : Fin (7 : ℕ)) *
      ((1 : ℝ) + (2 : ℝ) * y (1 : Fin (7 : ℕ)) / (y (1 : Fin (7 : ℕ)) ^ (2 : ℕ) * y (1 : Fin (7 : ℕ)) ^ (2 : ℕ))) := @DominantFiveBody.nestedRadialInnerDifference_at_boundary

-- Source binding: display:746
example : ∀ (R psi u1 u2 z1 z2 : ℝ),
  (0 : ℝ) < u1 ^ (2 : ℕ) + R ^ (2 : ℕ) * z1 ^ (2 : ℕ) →
    (0 : ℝ) < u2 ^ (2 : ℕ) + R ^ (2 : ℕ) * z2 ^ (2 : ℕ) →
      DominantFiveBody.nestedBoundaryKernel R psi (u1, z1) =
          R ^ (2 : ℕ) * z1 / (u1 ^ (2 : ℕ) + R ^ (2 : ℕ) * z1 ^ (2 : ℕ)) ^ (3 / 2 : ℝ) ∧
        DominantFiveBody.nestedBoundaryKernel R psi (u2, z2) =
          R ^ (2 : ℕ) * z2 / (u2 ^ (2 : ℕ) + R ^ (2 : ℕ) * z2 ^ (2 : ℕ)) ^ (3 / 2 : ℝ) := @DominantFiveBody.nestedBoundaryKernels_source_complete

-- Source binding: display:746
example : ∀ (alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedInnerM (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha y =
    DominantFiveBody.nestedBoundaryKernel (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ)))
      (y (3 : Fin (7 : ℕ)), y (6 : Fin (7 : ℕ))) := @DominantFiveBody.nestedInnerM_at_boundary

-- Source binding: eq:nest-boundary
example : ∀ (alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedAngularMean (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha y =
    DominantFiveBody.twoSourcePolarAngular (1 : ℝ) (y (0 : Fin (7 : ℕ))) (y (0 : Fin (7 : ℕ))) (0 : ℝ)
      (y (1 : Fin (7 : ℕ)), y (4 : Fin (7 : ℕ))) := @DominantFiveBody.nestedAngularMean_at_boundary

-- Source binding: eq:nest-boundary
example : ∀ (alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ) ≠
      DominantFiveBody.polarPoint (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ))) →
    DominantFiveBody.nestedAngularOuterDifference (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha y =
      (fderiv ℝ (DominantFiveBody.twoSourcePolarAngular (1 : ℝ) (y (0 : Fin (7 : ℕ))) (y (0 : Fin (7 : ℕ))) (0 : ℝ))
              (y (1 : Fin (7 : ℕ)), y (4 : Fin (7 : ℕ))) :
            ℝ × ℝ → ℝ)
          (y (2 : Fin (7 : ℕ)), y (5 : Fin (7 : ℕ))) -
        DominantFiveBody.nestedBoundaryKernel (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ)))
          (y (2 : Fin (7 : ℕ)), y (5 : Fin (7 : ℕ))) := @DominantFiveBody.nestedAngularOuterDifference_at_boundary

-- Source binding: eq:nest-boundary
example : ∀ (alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ) ≠
      DominantFiveBody.polarPoint (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ))) →
    (0 : ℝ) < y (2 : Fin (7 : ℕ)) ^ (2 : ℕ) + y (1 : Fin (7 : ℕ)) ^ (2 : ℕ) * y (5 : Fin (7 : ℕ)) ^ (2 : ℕ) →
      DominantFiveBody.nestedAngularInnerDifference (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha y =
        (fderiv ℝ (DominantFiveBody.twoSourcePolarAngular (1 : ℝ) (y (0 : Fin (7 : ℕ))) (y (0 : Fin (7 : ℕ))) (0 : ℝ))
                  (y (1 : Fin (7 : ℕ)), y (4 : Fin (7 : ℕ))) :
                ℝ × ℝ → ℝ)
              (y (3 : Fin (7 : ℕ)), y (6 : Fin (7 : ℕ))) -
            (fderiv ℝ (DominantFiveBody.nestedBoundaryKernel (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ))))
                  (y (2 : Fin (7 : ℕ)), y (5 : Fin (7 : ℕ))) :
                ℝ × ℝ → ℝ)
              (y (3 : Fin (7 : ℕ)), y (6 : Fin (7 : ℕ))) -
          DominantFiveBody.nestedBoundaryKernel (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ)))
            (y (3 : Fin (7 : ℕ)), y (6 : Fin (7 : ℕ))) := @DominantFiveBody.nestedAngularInnerDifference_at_boundary

-- Source binding: eq:nest-boundary
example : ∀ (R psi : ℝ) (v w : ℝ × ℝ),
  (DominantFiveBody.polarPointDerivative (R, psi) : ℝ × ℝ → DominantFiveBody.Plane) v ≠ (0 : DominantFiveBody.Plane) →
    (fderiv ℝ (DominantFiveBody.nestedBoundaryKernel R psi) v : ℝ × ℝ → ℝ) w =
      -Inner.inner ℝ
          ((DominantFiveBody.newtonTargetDerivative (0 : DominantFiveBody.Plane)
                (-(DominantFiveBody.polarPointDerivative (R, psi) : ℝ × ℝ → DominantFiveBody.Plane) v) :
              DominantFiveBody.Plane → DominantFiveBody.Plane)
            ((DominantFiveBody.polarPointDerivative (R, psi) : ℝ × ℝ → DominantFiveBody.Plane) w))
          (DominantFiveBody.quarterTurn (DominantFiveBody.polarPoint R psi)) := @DominantFiveBody.nestedBoundaryKernel_fderiv_apply

-- Source binding: eq:nest-base
example : ∀ (psi omega : ℝ),
  DominantFiveBody.nestedBasePoint psi omega =
    ![(1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), psi, omega * DominantFiveBody.tripleD0 ^ (-1 / 3 : ℝ),
      ((3 : ℝ) * DominantFiveBody.tripleD0) ^ (-1 / 3 : ℝ)] := @DominantFiveBody.nestedBasePoint_formula_complete

-- Source binding: eq:nest-base
example : ∀ (alpha psi omega : ℝ),
  |psi| = DominantFiveBody.Coorbital.h →
    |omega| = (1 : ℝ) →
      DominantFiveBody.nestedChartExtendedRows (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha
          (DominantFiveBody.nestedBasePoint psi omega) =
        (0 : DominantFiveBody.NestedChartVariables) := @DominantFiveBody.nestedChartExtendedRows_base_root

-- Source binding: prose:763
example : ∀ (alpha psi Z z : ℝ),
  DominantFiveBody.NestedChartRegular (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.nestedUnitPoint psi Z z) →
    ∀ (v : DominantFiveBody.NestedChartVariables) (i : Fin (2 : ℕ)),
      (DominantFiveBody.nestedChartJacobian (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.nestedUnitPoint psi Z z) :
            DominantFiveBody.NestedChartVariables → DominantFiveBody.NestedChartVariables)
          v i.castSucc.castSucc.castSucc.castSucc.castSucc =
        (3 : ℝ) * v i.castSucc.castSucc.castSucc.castSucc.castSucc := @DominantFiveBody.nestedChartJacobian_unit_radial

-- Source binding: prose:763
example : ∀ (alpha psi Z z : ℝ),
  DominantFiveBody.NestedChartRegular (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.nestedUnitPoint psi Z z) →
    ∀ (v : DominantFiveBody.NestedChartVariables) (k : Fin (2 : ℕ)),
      (DominantFiveBody.nestedChartJacobian (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.nestedUnitPoint psi Z z) :
            DominantFiveBody.NestedChartVariables → DominantFiveBody.NestedChartVariables)
          v k.castSucc.castSucc.castSucc.succ.succ =
        (3 : ℝ) * v k.castSucc.castSucc.castSucc.succ.succ := @DominantFiveBody.nestedChartJacobian_unit_radial_difference

-- Source binding: prose:763
example : ∀ (alpha psi omega : ℝ),
  |psi| = DominantFiveBody.Coorbital.h →
    |omega| = (1 : ℝ) →
      (DominantFiveBody.nestedBoundaryDerivativeMatrix alpha psi omega).IsLowerTriangular ∧
        (fun (i : Fin (7 : ℕ)) => DominantFiveBody.nestedBoundaryDerivativeMatrix alpha psi omega i i) =
          ![(3 : ℝ), (3 : ℝ), (3 : ℝ), (3 : ℝ), DominantFiveBody.tripleD0, (3 : ℝ) * DominantFiveBody.tripleD0,
            (9 : ℝ) * DominantFiveBody.tripleD0] := @DominantFiveBody.nestedBoundaryDerivativeMatrix_triangular_diagonal

-- Source binding: prose:763
example : ∀ (alpha psi omega : ℝ),
  |psi| = DominantFiveBody.Coorbital.h →
    |omega| = (1 : ℝ) →
      have Z := omega * DominantFiveBody.pairBoundaryScale DominantFiveBody.tripleD0;
      have z := DominantFiveBody.pairBoundaryScale ((3 : ℝ) * DominantFiveBody.tripleD0);
      have C := -(27 / 4 : ℝ) * Real.sin psi;
      DominantFiveBody.nestedAngularBoundaryMatrix alpha psi omega =
        ![![DominantFiveBody.tripleD0, (0 : ℝ), (0 : ℝ)], ![C * Z, (3 : ℝ) * DominantFiveBody.tripleD0, (0 : ℝ)],
          ![C * z, (-6 : ℝ) * DominantFiveBody.tripleD0 * z / Z, (9 : ℝ) * DominantFiveBody.tripleD0]] := @DominantFiveBody.nestedAngularBoundaryMatrix_source

-- Source binding: eq:nest-angle-J
example : DominantFiveBody.Coorbital.kappaPrime DominantFiveBody.Coorbital.h =
  -(27 / 4 : ℝ) * Real.sin DominantFiveBody.Coorbital.h := @DominantFiveBody.kappaPrime_h_source

-- Source binding: prose:771
example : ∀ (psi omega : ℝ),
  |omega| = (1 : ℝ) →
    have Z := omega * DominantFiveBody.pairBoundaryScale DominantFiveBody.tripleD0;
    have z := DominantFiveBody.pairBoundaryScale ((3 : ℝ) * DominantFiveBody.tripleD0);
    deriv (fun (s : ℝ) => DominantFiveBody.nestedBoundaryKernel (1 : ℝ) psi ((0 : ℝ), s)) Z =
        (-2 : ℝ) * DominantFiveBody.tripleD0 ∧
      deriv (fun (r : ℝ) => deriv (fun (s : ℝ) => DominantFiveBody.nestedBoundaryKernel (1 : ℝ) psi ((0 : ℝ), s)) r) Z =
          (6 : ℝ) * DominantFiveBody.tripleD0 / Z ∧
        deriv (fun (s : ℝ) => DominantFiveBody.nestedBoundaryKernel (1 : ℝ) psi ((0 : ℝ), s)) z =
          (-6 : ℝ) * DominantFiveBody.tripleD0 := @DominantFiveBody.nestedBoundaryKernel_original_derivatives

-- Source binding: prose:771
example : ∀ (alpha psi omega : ℝ),
  |psi| = DominantFiveBody.Coorbital.h →
    |omega| = (1 : ℝ) →
      DominantFiveBody.NestedChartRegular (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.nestedBasePoint psi omega) := @DominantFiveBody.nestedBasePoint_regular

-- Source binding: prose:771
example : ∀ (alpha beta psi omega : ℝ),
  |psi| = DominantFiveBody.Coorbital.h →
    |omega| = (1 : ℝ) →
      DominantFiveBody.nestedChartJacobian (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.nestedBasePoint psi omega) =
        DominantFiveBody.nestedChartJacobian (0 : ℝ) (0 : ℝ) (0 : ℝ) beta (DominantFiveBody.nestedBasePoint psi omega) := @DominantFiveBody.nestedChartJacobian_boundary_alpha_independent

-- Source binding: prose:771
example : ∀ (alpha psi omega : ℝ),
  |psi| = DominantFiveBody.Coorbital.h →
    |omega| = (1 : ℝ) →
      (DominantFiveBody.nestedBoundaryDerivativeMatrix alpha psi omega).det =
        (2187 : ℝ) * DominantFiveBody.tripleD0 ^ (3 : ℕ) := @DominantFiveBody.nestedBoundaryDerivativeMatrix_det

-- Source binding: prose:771
example : ∀ (alpha psi omega : ℝ),
  |psi| = DominantFiveBody.Coorbital.h →
    |omega| = (1 : ℝ) →
      (DominantFiveBody.nestedChartJacobian (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha
          (DominantFiveBody.nestedBasePoint psi omega)).IsInvertible := @DominantFiveBody.nestedChartJacobian_boundary_isInvertible

-- Source binding: prose:771
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < DominantFiveBody.nestedChartRadii t eta alpha y i) →
    DominantFiveBody.nestedChartExtendedRows (0 : ℝ) t eta alpha y = (0 : DominantFiveBody.NestedChartVariables) →
      (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.nestedChartRadii t eta alpha y i = (1 : ℝ)) ∧
        y (2 : Fin (7 : ℕ)) = (0 : ℝ) ∧
          y (3 : Fin (7 : ℕ)) = (0 : ℝ) ∧ y (0 : Fin (7 : ℕ)) = (1 : ℝ) ∧ y (1 : Fin (7 : ℕ)) = (1 : ℝ) := @DominantFiveBody.nestedChart_zero_eps_all_scale_faces

-- Source binding: prose:771
example : ∀ (alpha0 tau omega : ℝ),
  alpha0 ∈ Set.Icc (0 : ℝ) (1 : ℝ) →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      omega = (1 : ℝ) ∨ omega = (-1 : ℝ) →
        ∀ (bound : ℝ),
          (0 : ℝ) < bound →
            ∃ (delta : ℝ) (r : ℝ) (C : ℝ),
              (0 : ℝ) < delta ∧
                (0 : ℝ) < r ∧
                  (0 : ℝ) < C ∧
                    r ≤ bound ∧
                      delta ≤ r ∧
                        ∃ (branch : DominantFiveBody.NestedChartParameters → DominantFiveBody.NestedChartVariables),
                          branch (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) =
                              DominantFiveBody.nestedBasePoint (tau * DominantFiveBody.Coorbital.h) omega ∧
                            ContDiffOn ℝ ∞ branch
                                (Metric.ball (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) delta) ∧
                              ∀ (q : DominantFiveBody.NestedChartParameters),
                                Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < delta →
                                  Dist.dist (branch q)
                                        (DominantFiveBody.nestedBasePoint (tau * DominantFiveBody.Coorbital.h) omega) <
                                      r / (2 : ℝ) ∧
                                    DominantFiveBody.NestedContinuationDomain (q, branch q) ∧
                                      (DominantFiveBody.nestedChartJacobian (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ)))
                                            (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) (branch q)).IsInvertible ∧
                                        ‖(DominantFiveBody.nestedChartJacobian (q (0 : Fin (4 : ℕ)))
                                                  (q (1 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ)))
                                                  (branch q)).inverse‖ ≤
                                            C ∧
                                          DominantFiveBody.nestedChartParameterRows q (branch q) =
                                              (0 : DominantFiveBody.NestedChartVariables) ∧
                                            (∀ (y : DominantFiveBody.NestedChartVariables),
                                                Dist.dist y
                                                      (DominantFiveBody.nestedBasePoint
                                                        (tau * DominantFiveBody.Coorbital.h) omega) <
                                                    r →
                                                  (DominantFiveBody.nestedChartParameterRows q y =
                                                      (0 : DominantFiveBody.NestedChartVariables) ↔
                                                    branch q = y)) ∧
                                              ((0 : ℝ) < q (1 : Fin (4 : ℕ)) →
                                                  (0 : ℝ) < q (2 : Fin (4 : ℕ)) →
                                                    q (3 : Fin (4 : ℕ)) ∈ Set.Icc (0 : ℝ) (1 : ℝ) →
                                                      DominantFiveBody.StrictConvexInOrder
                                                        (DominantFiveBody.nestedBoundaryHullOrder tau omega)
                                                        (DominantFiveBody.liftRelative
                                                          (DominantFiveBody.nestedChartPoints (q (1 : Fin (4 : ℕ)))
                                                            (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) (branch q)))) ∧
                                                ((0 : ℝ) < q (0 : Fin (4 : ℕ)) →
                                                    (0 : ℝ) < q (1 : Fin (4 : ℕ)) →
                                                      (0 : ℝ) < q (2 : Fin (4 : ℕ)) →
                                                        q (3 : Fin (4 : ℕ)) ∈ Set.Icc (0 : ℝ) (1 : ℝ) →
                                                          DominantFiveBody.PositiveRatio
                                                              (DominantFiveBody.nestedChartMass (q (1 : Fin (4 : ℕ)))
                                                                (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ)))) →
                                                            DominantFiveBody.StrictConvexCentralConfiguration
                                                                (DominantFiveBody.masses (q (0 : Fin (4 : ℕ)))
                                                                  (DominantFiveBody.nestedChartMass
                                                                    (q (1 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))
                                                                    (q (3 : Fin (4 : ℕ)))))
                                                                (DominantFiveBody.nestedBoundaryHullOrder tau omega)
                                                                (DominantFiveBody.nestedChartConfiguration q
                                                                  (branch q)) ∧
                                                              DominantFiveBody.NondegenerateCentralConfiguration
                                                                (DominantFiveBody.masses (q (0 : Fin (4 : ℕ)))
                                                                  (DominantFiveBody.nestedChartMass
                                                                    (q (1 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))
                                                                    (q (3 : Fin (4 : ℕ)))))
                                                                (DominantFiveBody.nestedChartConfiguration q
                                                                  (branch q))) ∧
                                                  (q (0 : Fin (4 : ℕ)) = (0 : ℝ) →
                                                    (0 : ℝ) < q (1 : Fin (4 : ℕ)) →
                                                      (0 : ℝ) < q (2 : Fin (4 : ℕ)) →
                                                        DominantFiveBody.PositiveRatio
                                                            (DominantFiveBody.nestedChartMass (q (1 : Fin (4 : ℕ)))
                                                              (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ)))) →
                                                          (∀ (i : DominantFiveBody.Satellite),
                                                              DominantFiveBody.nestedChartRadii (q (1 : Fin (4 : ℕ)))
                                                                  (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) (branch q)
                                                                  i =
                                                                (1 : ℝ)) ∧
                                                            branch q (2 : Fin (7 : ℕ)) = (0 : ℝ) ∧
                                                              branch q (3 : Fin (7 : ℕ)) = (0 : ℝ) ∧
                                                                DominantFiveBody.RelativeCollisionFree
                                                                    (DominantFiveBody.nestedChartPoints
                                                                      (q (1 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))
                                                                      (q (3 : Fin (4 : ℕ))) (branch q)) ∧
                                                                  DominantFiveBody.SeparatedSemicircle
                                                                      (DominantFiveBody.nestedChartAngles
                                                                        (q (1 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))
                                                                        (q (3 : Fin (4 : ℕ))) (branch q)) ∧
                                                                    ∀ (i : DominantFiveBody.Satellite),
                                                                      DominantFiveBody.coorbitalResidual
                                                                          (DominantFiveBody.nestedChartMass
                                                                            (q (1 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))
                                                                            (q (3 : Fin (4 : ℕ))))
                                                                          (DominantFiveBody.nestedChartAngles
                                                                            (q (1 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))
                                                                            (q (3 : Fin (4 : ℕ))) (branch q))
                                                                          i =
                                                                        (0 : ℝ)) := @DominantFiveBody.nestedChart_convex_physical_continuation

-- Source binding: prose:771
example : ∀ (psi omega : ℝ),
  |psi| = DominantFiveBody.Coorbital.h →
    |omega| = (1 : ℝ) →
      ∃ (delta : ℝ) (C : ℝ),
        (0 : ℝ) < delta ∧
          (0 : ℝ) < C ∧
            ∀ alpha ∈ Set.Icc (0 : ℝ) (1 : ℝ),
              ∃ (branch : DominantFiveBody.NestedChartParameters → DominantFiveBody.NestedChartVariables),
                branch ![(0 : ℝ), (0 : ℝ), (0 : ℝ), alpha] = DominantFiveBody.nestedBasePoint psi omega ∧
                  ContDiffOn ℝ ∞ branch (Metric.ball ![(0 : ℝ), (0 : ℝ), (0 : ℝ), alpha] delta) ∧
                    ∀ (q : Fin (Nat.succ (0 : ℕ)).succ.succ.succ → ℝ),
                      Dist.dist q ![(0 : ℝ), (0 : ℝ), (0 : ℝ), alpha] < delta →
                        DominantFiveBody.NestedContinuationDomain (q, branch q) ∧
                          DominantFiveBody.nestedChartParameterRows q (branch q) =
                              (0 : DominantFiveBody.NestedChartVariables) ∧
                            |branch q (0 : Fin (7 : ℕ)) - (1 : ℝ)| + |branch q (1 : Fin (7 : ℕ)) - (1 : ℝ)| +
                                  |branch q (2 : Fin (7 : ℕ))| +
                                |branch q (3 : Fin (7 : ℕ))| ≤
                              C * |q (0 : Fin (Nat.succ (0 : ℕ)).succ.succ.succ)| := @DominantFiveBody.nestedChart_radial_uniform_epsilon_bound

-- Source binding: display:774
example : ∀ (mu : ℕ → DominantFiveBody.MassRatio),
  (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
    ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (psi omega : ℝ) (d s : ℕ → ℝ),
      (∀ (n : ℕ), (0 : ℝ) < d n) →
        (∀ (n : ℕ), (0 : ℝ) < s n) →
          Filter.Tendsto d Filter.atTop (𝓝 (0 : ℝ)) →
            Filter.Tendsto (fun (n : ℕ) => s n / d n) Filter.atTop (𝓝 (0 : ℝ)) →
              Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.triplePhysicalClusterMass (mu n) / d n ^ (3 : ℕ))
                  Filter.atTop (𝓝 DominantFiveBody.tripleD0) →
                Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.nestedPhysicalInnerMass (mu n) / s n ^ (3 : ℕ))
                    Filter.atTop (𝓝 ((3 : ℝ) * DominantFiveBody.tripleD0)) →
                  (∀ (i : DominantFiveBody.Satellite), Filter.Tendsto (fun (n : ℕ) => r n i) Filter.atTop (𝓝 (1 : ℝ))) →
                    (∀ (i : DominantFiveBody.TripleLabel),
                        Filter.Tendsto (fun (n : ℕ) => theta n (Fin.castSucc i)) Filter.atTop (𝓝 psi)) →
                      Filter.Tendsto
                          (fun (n : ℕ) =>
                            (r n (2 : DominantFiveBody.Satellite) - r n (0 : DominantFiveBody.Satellite)) / d n)
                          Filter.atTop (𝓝 (0 : ℝ)) →
                        Filter.Tendsto
                            (fun (n : ℕ) =>
                              (r n (2 : DominantFiveBody.Satellite) - r n (1 : DominantFiveBody.Satellite)) / d n)
                            Filter.atTop (𝓝 (0 : ℝ)) →
                          Filter.Tendsto
                              (fun (n : ℕ) =>
                                (theta n (2 : DominantFiveBody.Satellite) - theta n (0 : DominantFiveBody.Satellite)) /
                                  d n)
                              Filter.atTop (𝓝 omega) →
                            Filter.Tendsto
                                (fun (n : ℕ) =>
                                  (theta n (2 : DominantFiveBody.Satellite) -
                                      theta n (1 : DominantFiveBody.Satellite)) /
                                    d n)
                                Filter.atTop (𝓝 omega) →
                              Filter.Tendsto
                                  (fun (n : ℕ) =>
                                    (r n (1 : DominantFiveBody.Satellite) - r n (0 : DominantFiveBody.Satellite)) / s n)
                                  Filter.atTop (𝓝 (0 : ℝ)) →
                                Filter.Tendsto
                                    (fun (n : ℕ) =>
                                      (theta n (1 : DominantFiveBody.Satellite) -
                                          theta n (0 : DominantFiveBody.Satellite)) /
                                        s n)
                                    Filter.atTop (𝓝 (1 : ℝ)) →
                                  Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.nestedPhysicalScale (mu n))
                                      Filter.atTop (𝓝 (0 : ℝ)) ∧
                                    Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.nestedPhysicalEta (mu n))
                                        Filter.atTop (𝓝 (0 : ℝ)) ∧
                                      Filter.Tendsto
                                          (fun (n : ℕ) =>
                                            DominantFiveBody.nestedVariablesFromPolar
                                              (DominantFiveBody.nestedPhysicalScale (mu n))
                                              (DominantFiveBody.nestedPhysicalEta (mu n))
                                              (DominantFiveBody.nestedPhysicalAlpha (mu n)) (r n) (theta n))
                                          Filter.atTop (𝓝 (DominantFiveBody.nestedBasePoint psi omega)) ∧
                                        Filter.Tendsto
                                            (fun (n : ℕ) => d n / DominantFiveBody.nestedPhysicalScale (mu n))
                                            Filter.atTop
                                            (𝓝 (DominantFiveBody.pairBoundaryScale DominantFiveBody.tripleD0)) ∧
                                          Filter.Tendsto
                                              (fun (n : ℕ) =>
                                                s n /
                                                  (DominantFiveBody.nestedPhysicalScale (mu n) *
                                                    DominantFiveBody.nestedPhysicalEta (mu n)))
                                              Filter.atTop
                                              (𝓝
                                                (DominantFiveBody.pairBoundaryScale
                                                  ((3 : ℝ) * DominantFiveBody.tripleD0))) ∧
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.nestedRowOuterDifference
                                                    (DominantFiveBody.nestedPhysicalScale (mu n))
                                                    (DominantFiveBody.nestedPhysicalAlpha (mu n)) (r n))
                                                Filter.atTop (𝓝 (0 : ℝ)) ∧
                                              Filter.Tendsto
                                                  (fun (n : ℕ) =>
                                                    DominantFiveBody.nestedRowInnerDifference
                                                      (DominantFiveBody.nestedPhysicalScale (mu n))
                                                      (DominantFiveBody.nestedPhysicalEta (mu n)) (r n))
                                                  Filter.atTop (𝓝 (0 : ℝ)) ∧
                                                Filter.Tendsto
                                                    (fun (n : ℕ) =>
                                                      DominantFiveBody.nestedRowInnerDifference
                                                        (DominantFiveBody.nestedPhysicalScale (mu n))
                                                        (DominantFiveBody.nestedPhysicalEta (mu n)) (theta n))
                                                    Filter.atTop
                                                    (𝓝
                                                      (DominantFiveBody.pairBoundaryScale
                                                        ((3 : ℝ) * DominantFiveBody.tripleD0))) ∧
                                                  Filter.Tendsto
                                                      (fun (n : ℕ) =>
                                                        (theta n (2 : DominantFiveBody.Satellite) -
                                                            theta n (0 : DominantFiveBody.Satellite)) /
                                                          DominantFiveBody.nestedPhysicalScale (mu n))
                                                      Filter.atTop
                                                      (𝓝
                                                        (omega *
                                                          DominantFiveBody.pairBoundaryScale
                                                            DominantFiveBody.tripleD0)) ∧
                                                    Filter.Tendsto
                                                        (fun (n : ℕ) =>
                                                          (theta n (2 : DominantFiveBody.Satellite) -
                                                              theta n (1 : DominantFiveBody.Satellite)) /
                                                            DominantFiveBody.nestedPhysicalScale (mu n))
                                                        Filter.atTop
                                                        (𝓝
                                                          (omega *
                                                            DominantFiveBody.pairBoundaryScale
                                                              DominantFiveBody.tripleD0)) ∧
                                                      Filter.Tendsto
                                                        (fun (n : ℕ) =>
                                                          DominantFiveBody.nestedRowOuterDifference
                                                            (DominantFiveBody.nestedPhysicalScale (mu n))
                                                            (DominantFiveBody.nestedPhysicalAlpha (mu n)) (theta n))
                                                        Filter.atTop
                                                        (𝓝
                                                          (omega *
                                                            DominantFiveBody.pairBoundaryScale
                                                              DominantFiveBody.tripleD0)) := @DominantFiveBody.nestedSource_individual_inverse_limits

-- Source binding: display:774
example : ∀ (eps t eta s dr : ℕ → ℝ) (C z0 : ℝ),
  (∀ (n : ℕ), (0 : ℝ) ≤ eps n) →
    (∀ (n : ℕ), (0 : ℝ) < t n) →
      (∀ (n : ℕ), (0 : ℝ) < eta n) →
        (0 : ℝ) < C →
          (0 : ℝ) < z0 →
            (∀ᶠ (n : ℕ) in Filter.atTop, |dr n| ≤ C * eps n * s n) →
              Filter.Tendsto (fun (n : ℕ) => s n / (t n * eta n)) Filter.atTop (𝓝 z0) →
                ∃ (K : ℝ), (0 : ℝ) < K ∧ ∀ᶠ (n : ℕ) in Filter.atTop, |dr n / (t n * eta n)| ≤ K * eps n := @DominantFiveBody.nestedSource_radial_Oepsilon_from_original_bound

-- Source binding: display:774
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      ∀ (hm : ∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)),
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          (∀ (n : ℕ), DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder (x n)) →
            ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
              (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                (∀ (n : ℕ),
                    DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                  (∀ (n : ℕ), theta n (0 : DominantFiveBody.Satellite) = (0 : ℝ)) →
                    (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                      ∀ (muLimit : DominantFiveBody.MassRatio),
                        Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                          ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                            Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                                (𝓝 qLimit) →
                              ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                                Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                                  ∀ (center : DominantFiveBody.Plane),
                                    DominantFiveBody.CompleteLimitingSatelliteTriple qLimit
                                        (3 : DominantFiveBody.Satellite) center →
                                      ∀ (a b c : DominantFiveBody.TripleLabel),
                                        a < b →
                                          c ≠ a →
                                            c ≠ b →
                                              Filter.Tendsto
                                                  (fun (n : ℕ) =>
                                                    DominantFiveBody.satelliteDistance
                                                        (DominantFiveBody.satellitesRelative (x n)) (Fin.castSucc a)
                                                        (Fin.castSucc b) /
                                                      DominantFiveBody.tripleLowDiameter
                                                        (DominantFiveBody.satellitesRelative (x n)))
                                                  Filter.atTop (𝓝 (0 : ℝ)) →
                                                Nonempty
                                                  (DominantFiveBody.CapturedBranches DominantFiveBody.orderedSliceRoot
                                                    DominantFiveBody.orderedSliceNondegenerate
                                                    DominantFiveBody.orderedSliceEndpoint (fun (n : ℕ) => ⟨mu n, hm n⟩)
                                                    eps fun (n : ℕ) => DominantFiveBody.polarSlice (r n) (theta n)) := @DominantFiveBody.normalized_complete_lower_triple_nested_original_capture

-- Source binding: display:780
example : (fun (k : Fin (4 : ℕ)) (i : DominantFiveBody.Satellite) =>
    (DominantFiveBody.nestedSourceCasePermutation k : DominantFiveBody.Satellite → DominantFiveBody.Satellite) i) =
  ![![(0 : DominantFiveBody.Satellite), (1 : DominantFiveBody.Satellite), (2 : DominantFiveBody.Satellite),
      (3 : DominantFiveBody.Satellite)],
    ![(1 : DominantFiveBody.Satellite), (2 : DominantFiveBody.Satellite), (0 : DominantFiveBody.Satellite),
      (3 : DominantFiveBody.Satellite)],
    ![(1 : DominantFiveBody.Satellite), (2 : DominantFiveBody.Satellite), (3 : DominantFiveBody.Satellite),
      (0 : DominantFiveBody.Satellite)],
    ![(2 : DominantFiveBody.Satellite), (3 : DominantFiveBody.Satellite), (1 : DominantFiveBody.Satellite),
      (0 : DominantFiveBody.Satellite)]] := @DominantFiveBody.nestedSourceCasePermutation_source

-- Source binding: display:780
example : DominantFiveBody.nestedSourceCaseTable =
  ![({(1 : DominantFiveBody.Label), (2 : DominantFiveBody.Label), (3 : DominantFiveBody.Label)},
      {(1 : DominantFiveBody.Label), (2 : DominantFiveBody.Label)}, (4 : DominantFiveBody.Label), (-1 : ℝ), (1 : ℝ)),
    ({(1 : DominantFiveBody.Label), (2 : DominantFiveBody.Label), (3 : DominantFiveBody.Label)},
      {(2 : DominantFiveBody.Label), (3 : DominantFiveBody.Label)}, (4 : DominantFiveBody.Label), (-1 : ℝ), (-1 : ℝ)),
    ({(2 : DominantFiveBody.Label), (3 : DominantFiveBody.Label), (4 : DominantFiveBody.Label)},
      {(2 : DominantFiveBody.Label), (3 : DominantFiveBody.Label)}, (1 : DominantFiveBody.Label), (1 : ℝ), (1 : ℝ)),
    ({(2 : DominantFiveBody.Label), (3 : DominantFiveBody.Label), (4 : DominantFiveBody.Label)},
      {(3 : DominantFiveBody.Label), (4 : DominantFiveBody.Label)}, (1 : DominantFiveBody.Label), (1 : ℝ), (-1 : ℝ))] := @DominantFiveBody.nestedSourceCaseTable_source

-- Source binding: display:780
example : ∀ (k : Fin (4 : ℕ)),
  (⇑(DominantFiveBody.nestedSourceCasePermutation k) : DominantFiveBody.Satellite → DominantFiveBody.Satellite) ∘
      (⇑(DominantFiveBody.hullSatellitePermutation
            (DominantFiveBody.nestedBoundaryHullOrder (DominantFiveBody.nestedSourceCaseSigns k).1
              (DominantFiveBody.nestedSourceCaseSigns k).2)) :
        DominantFiveBody.Satellite → DominantFiveBody.Satellite) =
    id := @DominantFiveBody.nestedSourceCase_order_is_original

-- Source binding: prose:779
example : ∀ (eps t eta alpha : ℕ → ℝ) (y : ℕ → DominantFiveBody.NestedChartVariables) (psi omega d r : ℝ),
  Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
    Filter.Tendsto t Filter.atTop (𝓝 (0 : ℝ)) →
      Filter.Tendsto eta Filter.atTop (𝓝 (0 : ℝ)) →
        Filter.Tendsto y Filter.atTop (𝓝 (DominantFiveBody.nestedBasePoint psi omega)) →
          (0 : ℝ) < d →
            (0 : ℝ) < r →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                Dist.dist (DominantFiveBody.nestedParameter (eps n) (t n) (eta n) (alpha n))
                      (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) (alpha n)) <
                    d ∧
                  Dist.dist (y n) (DominantFiveBody.nestedBasePoint psi omega) < r := @DominantFiveBody.nestedSource_common_balls_without_alpha_limit

-- Source binding: prose:779
example : ∀ (p : ℕ → DominantFiveBody.PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → DominantFiveBody.SliceCoordinates),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.orderedSliceRoot (p n) (eps n) (y n)) →
        ∀ (muLimit thetaLimit : DominantFiveBody.MassRatio) (qLimit : DominantFiveBody.SatelliteConfiguration),
          Filter.Tendsto (fun (n : ℕ) => (↑(p n) : DominantFiveBody.MassRatio)) Filter.atTop (𝓝 muLimit) →
            Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.sliceAngles (y n)) Filter.atTop (𝓝 thetaLimit) →
              Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.sliceSatellites (y n)) Filter.atTop (𝓝 qLimit) →
                ∀ (center : DominantFiveBody.Plane),
                  DominantFiveBody.CompleteLimitingSatelliteTriple qLimit (3 : DominantFiveBody.Satellite) center →
                    ∀ (a b c : DominantFiveBody.TripleLabel),
                      a < b →
                        c ≠ a →
                          c ≠ b →
                            Filter.Tendsto
                                (fun (n : ℕ) =>
                                  DominantFiveBody.satelliteDistance (DominantFiveBody.sliceSatellites (y n))
                                      (Fin.castSucc a) (Fin.castSucc b) /
                                    DominantFiveBody.tripleLowDiameter (DominantFiveBody.sliceSatellites (y n)))
                                Filter.atTop (𝓝 (0 : ℝ)) →
                              Nonempty
                                (DominantFiveBody.CapturedBranches DominantFiveBody.orderedSliceRoot
                                  DominantFiveBody.orderedSliceNondegenerate DominantFiveBody.orderedSliceEndpoint p eps
                                  y) := @DominantFiveBody.orderedSlice_lower_nested_triple_capture

-- Source binding: prose:789
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  (0 : ℝ) < t →
    (0 : ℝ) < eta →
      DominantFiveBody.PositiveRatio (DominantFiveBody.nestedChartMass t eta alpha) →
        DominantFiveBody.NestedContinuationDomain (![(0 : ℝ), t, eta, alpha], y) →
          DominantFiveBody.nestedChartExtendedRows (0 : ℝ) t eta alpha y = (0 : DominantFiveBody.NestedChartVariables) →
            (∀ (i : DominantFiveBody.Satellite), DominantFiveBody.nestedChartRadii t eta alpha y i = (1 : ℝ)) ∧
              y (2 : Fin (7 : ℕ)) = (0 : ℝ) ∧
                y (3 : Fin (7 : ℕ)) = (0 : ℝ) ∧
                  DominantFiveBody.RelativeCollisionFree (DominantFiveBody.nestedChartPoints t eta alpha y) ∧
                    DominantFiveBody.SeparatedSemicircle (DominantFiveBody.nestedChartAngles t eta alpha y) ∧
                      ∀ (i : DominantFiveBody.Satellite),
                        DominantFiveBody.coorbitalResidual (DominantFiveBody.nestedChartMass t eta alpha)
                            (DominantFiveBody.nestedChartAngles t eta alpha y) i =
                          (0 : ℝ) := @DominantFiveBody.nestedContinuationRoot_fixed_mass_endpoint

-- Source binding: display:798
example : ∀ (eps : ℝ) (q : DominantFiveBody.Plane),
  DominantFiveBody.backgroundProbeField eps q =
    q - (‖q‖ ^ (3 : ℕ))⁻¹ • q +
        (eps / ‖DominantFiveBody.backgroundExterior eps - q‖ ^ (3 : ℕ)) •
          (DominantFiveBody.backgroundExterior eps - q) -
      (eps / DominantFiveBody.backgroundRadius eps ^ (3 : ℕ)) • DominantFiveBody.backgroundExterior eps := @DominantFiveBody.backgroundProbeField_source_formula

-- Source binding: display:798
example : ∀ (eps tau : ℝ),
  (0 : ℝ) < (1 : ℝ) + eps →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      HasFDerivAt (DominantFiveBody.backgroundProbeField eps) (DominantFiveBody.backgroundOperator eps tau)
        (DominantFiveBody.backgroundProbeCenter eps tau) := @DominantFiveBody.backgroundProbeField_hasFDerivAt

-- Source binding: prose:802
example : ∀ (eps tau : ℝ),
  (0 : ℝ) < (1 : ℝ) + eps →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      DominantFiveBody.backgroundProbeField eps (DominantFiveBody.backgroundProbeCenter eps tau) =
        (0 : DominantFiveBody.Plane) := @DominantFiveBody.backgroundProbeField_zero

-- Source binding: prose:802
example : ∀ (eps tau x y : ℝ),
  tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
    (DominantFiveBody.backgroundOperator eps tau : DominantFiveBody.Plane → DominantFiveBody.Plane)
        (x • DominantFiveBody.backgroundE0 tau + y • DominantFiveBody.quarterTurn (DominantFiveBody.backgroundE0 tau)) =
      (DominantFiveBody.backgroundMatrix eps tau (0 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) * x +
            DominantFiveBody.backgroundMatrix eps tau (0 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ)) * y) •
          DominantFiveBody.backgroundE0 tau +
        (DominantFiveBody.backgroundMatrix eps tau (1 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) * x +
            DominantFiveBody.backgroundMatrix eps tau (1 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ)) * y) •
          DominantFiveBody.quarterTurn (DominantFiveBody.backgroundE0 tau) := @DominantFiveBody.backgroundOperator_coordinates

-- Source binding: eq:bg-matrix
example : ∀ (eps tau : ℝ),
  DominantFiveBody.backgroundMatrix eps tau =
      !![(3 : ℝ) / ((1 : ℝ) + eps) * ((1 : ℝ) + eps / (4 : ℝ)),
          (3 : ℝ) / ((1 : ℝ) + eps) * (tau * √(3 : ℝ) * eps / (4 : ℝ));
        (3 : ℝ) / ((1 : ℝ) + eps) * (tau * √(3 : ℝ) * eps / (4 : ℝ)),
          (3 : ℝ) / ((1 : ℝ) + eps) * ((3 : ℝ) * eps / (4 : ℝ))] ∧
    DominantFiveBody.backgroundSlowD eps =
        (9 : ℝ) /
          ((2 : ℝ) * ((1 : ℝ) + eps) ^ (2 : ℕ) * ((1 : ℝ) + √((1 : ℝ) - (3 : ℝ) * eps / ((1 : ℝ) + eps) ^ (2 : ℕ)))) ∧
      DominantFiveBody.backgroundSlowLambda eps = eps * DominantFiveBody.backgroundSlowD eps := @DominantFiveBody.backgroundSpectrum_formula_complete

-- Source binding: eq:bg-matrix
example : ∀ (eps tau : ℝ) (v : DominantFiveBody.Plane),
  (DominantFiveBody.backgroundOperator eps tau : DominantFiveBody.Plane → DominantFiveBody.Plane) v =
    ((3 : ℝ) / ((1 : ℝ) + eps)) •
      (Inner.inner ℝ (DominantFiveBody.backgroundE0 tau) v • DominantFiveBody.backgroundE0 tau +
        eps • Inner.inner ℝ (DominantFiveBody.backgroundW0 tau) v • DominantFiveBody.backgroundW0 tau) := @DominantFiveBody.backgroundOperator_apply

-- Source binding: prose:809
example : ∀ (eps tau : ℝ), (1 : ℝ) + eps ≠ (0 : ℝ) → (DominantFiveBody.backgroundMatrix eps tau).trace = (3 : ℝ) := @DominantFiveBody.backgroundMatrix_trace

-- Source binding: prose:809
example : ∀ (eps tau x : ℝ),
  (1 : ℝ) + eps ≠ (0 : ℝ) →
    tau ^ (2 : ℕ) = (1 : ℝ) →
      (x • (1 : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ) - DominantFiveBody.backgroundMatrix eps tau).det =
        (x - DominantFiveBody.backgroundSlowLambda eps) * (x - ((3 : ℝ) - DominantFiveBody.backgroundSlowLambda eps)) := @DominantFiveBody.backgroundMatrix_characteristic_factor

-- Source binding: prose:809
example : ∀ (eps : ℝ),
  (1 : ℝ) + eps ≠ (0 : ℝ) →
    DominantFiveBody.backgroundSlowLambda eps < (3 : ℝ) - DominantFiveBody.backgroundSlowLambda eps := @DominantFiveBody.backgroundSlowLambda_lt_fast

-- Source binding: eq:slow
example : ∀ (tau : ℝ),
  DominantFiveBody.backgroundSlowD (0 : ℝ) = DominantFiveBody.tripleD0 ∧
    DominantFiveBody.backgroundSlowK (0 : ℝ) tau = (0 : ℝ) ∧
      DominantFiveBody.backgroundSlowLength (0 : ℝ) = (1 : ℝ) ∧
        DominantFiveBody.backgroundAngularScale (0 : ℝ) tau = (1 : ℝ) := @DominantFiveBody.backgroundSlow_zero_complete

-- Source binding: eq:slow
example : ∀ (eps : ℝ),
  (1 : ℝ) + eps ≠ (0 : ℝ) →
    DominantFiveBody.backgroundSlowLambda eps = (3 / 2 : ℝ) * ((1 : ℝ) - √(DominantFiveBody.backgroundDelta eps)) := @DominantFiveBody.backgroundSlowLambda_eq

-- Source binding: eq:slow
example : ∀ (eps : ℝ),
  (1 : ℝ) + eps ≠ (0 : ℝ) →
    DominantFiveBody.backgroundSlowLambda eps ^ (2 : ℕ) - (3 : ℝ) * DominantFiveBody.backgroundSlowLambda eps +
        (27 : ℝ) * eps / ((4 : ℝ) * ((1 : ℝ) + eps) ^ (2 : ℕ)) =
      (0 : ℝ) := @DominantFiveBody.backgroundSlowLambda_characteristic

-- Source binding: prose:815
example : ∀ (n : ℕ∞ω) (eps tau : ℝ),
  |eps| < (1 / 4 : ℝ) → ContDiffAt ℝ n (fun (e : ℝ) => DominantFiveBody.backgroundSlowK e tau) eps := @DominantFiveBody.backgroundSlowK_contDiffAt

-- Source binding: prose:815
example : ∀ (n : ℕ∞ω) (eps tau : ℝ),
  |eps| < (1 / 4 : ℝ) → ContDiffAt ℝ n (fun (e : ℝ) => DominantFiveBody.backgroundSlowDirection e tau) eps := @DominantFiveBody.backgroundSlowDirection_contDiffAt

-- Source binding: prose:815
example : ∀ (n : ℕ∞ω) (eps : ℝ), (1 : ℝ) + eps ≠ (0 : ℝ) → ContDiffAt ℝ n DominantFiveBody.backgroundSlowLength eps := @DominantFiveBody.backgroundSlowLength_contDiffAt

-- Source binding: prose:815
example : ∀ (n : ℕ∞ω) (eps tau : ℝ),
  |eps| < (1 / 4 : ℝ) → ContDiffAt ℝ n (fun (e : ℝ) => DominantFiveBody.backgroundAngularScale e tau) eps := @DominantFiveBody.backgroundAngularScale_contDiffAt

-- Source binding: display:816
example : ∀ (eps tau : ℝ),
  DominantFiveBody.backgroundSlowK eps tau =
      -DominantFiveBody.backgroundMatrix eps tau (0 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ)) /
        (DominantFiveBody.backgroundMatrix eps tau (0 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) -
          DominantFiveBody.backgroundSlowLambda eps) ∧
    DominantFiveBody.backgroundSlowDirection eps tau =
        (√((1 : ℝ) + DominantFiveBody.backgroundSlowK eps tau ^ (2 : ℕ)))⁻¹ •
          (DominantFiveBody.backgroundSlowK eps tau • DominantFiveBody.backgroundE0 tau +
            DominantFiveBody.quarterTurn (DominantFiveBody.backgroundE0 tau)) ∧
      DominantFiveBody.backgroundSlowLength eps =
          (DominantFiveBody.tripleD0 / DominantFiveBody.backgroundSlowD eps) ^ (1 / 3 : ℝ) ∧
        DominantFiveBody.backgroundAngularScale eps tau =
          DominantFiveBody.backgroundSlowLength eps /
            (DominantFiveBody.backgroundRadius eps * √((1 : ℝ) + DominantFiveBody.backgroundSlowK eps tau ^ (2 : ℕ))) := @DominantFiveBody.backgroundSlow_formula_complete

-- Source binding: prose:821
example : ∀ (eps tau : ℝ),
  |eps| < (1 / 4 : ℝ) →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      (DominantFiveBody.backgroundOperator eps tau : DominantFiveBody.Plane → DominantFiveBody.Plane)
          (DominantFiveBody.backgroundSlowDirection eps tau) =
        DominantFiveBody.backgroundSlowLambda eps • DominantFiveBody.backgroundSlowDirection eps tau := @DominantFiveBody.backgroundSlowDirection_eigen

-- Source binding: eq:scalar-slow
example : ∀ (omega s : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleWeights omega →
    DominantFiveBody.TripleOrdered s →
      (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual omega s i = (0 : ℝ)) →
        (∀ (i : DominantFiveBody.TripleLabel),
            DominantFiveBody.tripleD0 * s i - ∑ j ∈ Finset.univ.erase i, omega j * (s i - s j) / |s i - s j| ^ (3 : ℕ) =
              (0 : ℝ)) ∧
          (∀ (i j : DominantFiveBody.TripleLabel), i ≠ j → s i ≠ s j) ∧
            ∑ i : DominantFiveBody.TripleLabel, omega i * s i = (0 : ℝ) ∧
              ∑ i : DominantFiveBody.TripleLabel, omega i = (1 : ℝ) := @DominantFiveBody.scalarSlow_source_equations

-- Source binding: eq:scalar-slow
example : ∀ (omega : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), (0 : ℝ) < omega i) →
    ∑ i : DominantFiveBody.TripleLabel, omega i = (1 : ℝ) →
      ∃ (s : DominantFiveBody.TripleVector),
        DominantFiveBody.TripleOrdered s ∧
          (∀ (i : DominantFiveBody.TripleLabel),
              DominantFiveBody.tripleD0 * s i -
                  ∑ j ∈ Finset.univ.erase i, omega j * (s i - s j) / |s i - s j| ^ (3 : ℕ) =
                (0 : ℝ)) ∧
            (∀ (i j : DominantFiveBody.TripleLabel), i ≠ j → s i ≠ s j) ∧
              ∑ i : DominantFiveBody.TripleLabel, omega i * s i = (0 : ℝ) ∧
                ∑ i : DominantFiveBody.TripleLabel, omega i = (1 : ℝ) := @DominantFiveBody.scalarSlow_positive_seed

-- Source binding: eq:scalar-slow
example : ∀ (eta alpha psi Z z : ℝ),
  (0 : ℝ) < eta →
    eta ≤ (1 : ℝ) →
      (0 : ℝ) ≤ alpha →
        alpha ≤ (1 : ℝ) →
          |psi| = DominantFiveBody.Coorbital.h →
            DominantFiveBody.NestedChartRegular (0 : ℝ) (0 : ℝ) eta alpha (DominantFiveBody.nestedUnitPoint psi Z z) →
              DominantFiveBody.nestedChartExtendedRows (0 : ℝ) (0 : ℝ) eta alpha
                    (DominantFiveBody.nestedUnitPoint psi Z z) =
                  (0 : DominantFiveBody.NestedChartVariables) →
                ∀ (i : DominantFiveBody.TripleLabel),
                  DominantFiveBody.tripleScalarResidual (DominantFiveBody.nestedTripleWeights eta alpha)
                      ((DominantFiveBody.tripleCenteringMatrix (DominantFiveBody.nestedTripleWeights eta alpha)).mulVec
                        ![eta * z, Z - alpha * eta * z])
                      i =
                    (0 : ℝ) := @DominantFiveBody.nestedUnitPoint_scalar_root

-- Source binding: eq:vector-slow
example : ∀ (eps tau : ℝ) (omega s : DominantFiveBody.TripleVector),
  |eps| < (1 / 4 : ℝ) →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual omega s i = (0 : ℝ)) →
        ∀ (i : DominantFiveBody.TripleLabel),
          (DominantFiveBody.backgroundOperator eps tau : DominantFiveBody.Plane → DominantFiveBody.Plane)
                (DominantFiveBody.backgroundScalarLift eps tau (s i)) -
              eps •
                ∑ j ∈ Finset.univ.erase i,
                  omega j •
                    DominantFiveBody.newtonTargetField (DominantFiveBody.backgroundScalarLift eps tau (s i))
                      (DominantFiveBody.backgroundScalarLift eps tau (s j)) =
            (0 : DominantFiveBody.Plane) := @DominantFiveBody.backgroundScalarLift_vector_balance

-- Source binding: prose:831
example : ∀ (eps : ℝ),
  (1 : ℝ) + eps ≠ (0 : ℝ) →
    DominantFiveBody.backgroundSlowD eps * DominantFiveBody.backgroundSlowLength eps =
      DominantFiveBody.tripleD0 / DominantFiveBody.backgroundSlowLength eps ^ (2 : ℕ) := @DominantFiveBody.backgroundSlow_scaling

-- Source binding: prose:833
example : ∀ (R psi w z t : ℝ),
  DominantFiveBody.affinePolarPoint R psi w z t - DominantFiveBody.polarPoint R psi =
    t • DominantFiveBody.affinePolarDirection R psi w z t := @DominantFiveBody.affinePolarPoint_divided_identity

-- Source binding: prose:833
example : ∀ (R psi w z : ℝ),
  (fun (t : ℝ) =>
      DominantFiveBody.affinePolarPoint R psi w z t - DominantFiveBody.polarPoint R psi -
        t • (DominantFiveBody.polarPointDerivative (R, psi) : ℝ × ℝ → DominantFiveBody.Plane) (w, z)) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (2 : ℕ) := @DominantFiveBody.affinePolarPoint_cartesian_Osquare

-- Source binding: prose:833
example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  (fun (t : ℝ) =>
      DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc i) -
          DominantFiveBody.polarPoint (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ))) -
        t • DominantFiveBody.tripleBoundaryDisplacement alpha y i) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (2 : ℕ) := @DominantFiveBody.tripleChartPoint_cartesian_Osquare

-- Source binding: prose:833
example : ∀ (alpha : DominantFiveBody.TripleVector),
  (fun (t : ℝ) => DominantFiveBody.tripleChartMass t alpha (3 : DominantFiveBody.Satellite) - (1 : ℝ)) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (3 : ℕ) := @DominantFiveBody.tripleChart_exteriorMass_Ocube

-- Source binding: prose:833
example : ∀ (t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  DominantFiveBody.relativeAverage (DominantFiveBody.tripleChartMass t alpha)
        (DominantFiveBody.tripleChartPoints t alpha y) -
      DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ) =
    t ^ (3 : ℕ) •
      (∑ i : DominantFiveBody.TripleLabel, alpha i • DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc i) -
        DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ)) := @DominantFiveBody.tripleChart_relativeAverage_cubic_identity

-- Source binding: prose:833
example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  (fun (t : ℝ) =>
      DominantFiveBody.relativeAverage (DominantFiveBody.tripleChartMass t alpha)
          (DominantFiveBody.tripleChartPoints t alpha y) -
        DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ)) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (3 : ℕ) := @DominantFiveBody.tripleChart_relativeAverage_Ocube

-- Source binding: prose:833
example : ∀ (eps : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  (fun (t : ℝ) =>
      (eps / ((1 : ℝ) + eps)) •
        (DominantFiveBody.relativeAverage (DominantFiveBody.tripleChartMass t alpha)
            (DominantFiveBody.tripleChartPoints t alpha y) -
          DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ))) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (3 : ℕ) := @DominantFiveBody.tripleChart_reaction_Ocube

-- Source binding: prose:833
example : ∀ (eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : DominantFiveBody.TripleLabel),
  DominantFiveBody.nestedActualBoundaryClusterDisplacement eta alpha y i =
    DominantFiveBody.tripleBoundaryDisplacement (DominantFiveBody.nestedTripleWeights eta alpha)
      (DominantFiveBody.nestedToTripleVariables eta alpha y) i := @DominantFiveBody.nestedBoundaryDisplacement_to_triple

-- Source binding: prose:833
example : ∀ (eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : DominantFiveBody.TripleLabel),
  (fun (t : ℝ) =>
      DominantFiveBody.nestedChartPoints t eta alpha y (Fin.castSucc i) -
          DominantFiveBody.polarPoint (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ))) -
        t • DominantFiveBody.nestedActualBoundaryClusterDisplacement eta alpha y i) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (2 : ℕ) := @DominantFiveBody.nestedChartPoint_cartesian_Osquare

-- Source binding: prose:833
example : ∀ (eps eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  (fun (t : ℝ) =>
      (eps / ((1 : ℝ) + eps)) •
        (DominantFiveBody.relativeAverage (DominantFiveBody.nestedChartMass t eta alpha)
            (DominantFiveBody.nestedChartPoints t eta alpha y) -
          DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ))) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (3 : ℕ) := @DominantFiveBody.nestedChart_reaction_Ocube

-- Source binding: prose:833
example : ∀ (source : DominantFiveBody.Plane) (R psi w z : ℝ),
  source ≠ DominantFiveBody.polarPoint R psi →
    (fun (t : ℝ) =>
        DominantFiveBody.newtonTargetField source (DominantFiveBody.affinePolarPoint R psi w z t) -
            DominantFiveBody.newtonTargetField source (DominantFiveBody.polarPoint R psi) -
          t •
            (DominantFiveBody.newtonTargetDerivative source (DominantFiveBody.polarPoint R psi) :
                DominantFiveBody.Plane → DominantFiveBody.Plane)
              ((DominantFiveBody.polarPointDerivative (R, psi) : ℝ × ℝ → DominantFiveBody.Plane) (w, z))) =O[𝓝 (0 : ℝ)]
      fun (t : ℝ) => t ^ (2 : ℕ) := @DominantFiveBody.newtonTargetField_affinePolar_Osquare

-- Source binding: prose:833
example : ∀ (eps tau w z : ℝ),
  (0 : ℝ) < (1 : ℝ) + eps →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      (fun (t : ℝ) =>
          DominantFiveBody.backgroundProbeField eps
              (DominantFiveBody.affinePolarPoint (DominantFiveBody.backgroundRadius eps)
                (tau * DominantFiveBody.Coorbital.h) w z t) -
            t •
              (DominantFiveBody.backgroundOperator eps tau : DominantFiveBody.Plane → DominantFiveBody.Plane)
                ((DominantFiveBody.polarPointDerivative
                      (DominantFiveBody.backgroundRadius eps, tau * DominantFiveBody.Coorbital.h) :
                    ℝ × ℝ → DominantFiveBody.Plane)
                  (w, z))) =O[𝓝 (0 : ℝ)]
        fun (t : ℝ) => t ^ (2 : ℕ) := @DominantFiveBody.backgroundProbeField_affinePolar_Osquare

-- Source binding: prose:833
example : ∀ (t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  (0 : ℝ) < t →
    (∀ (j : DominantFiveBody.TripleLabel), j ≠ i → (0 : ℝ) < DominantFiveBody.tripleChartWSq t alpha y i j) →
      ∑ j ∈ Finset.univ.erase i,
          (DominantFiveBody.tripleChartMass t alpha (Fin.castSucc j) /
              DominantFiveBody.satelliteDistance (DominantFiveBody.tripleChartPoints t alpha y) (Fin.castSucc i)
                  (Fin.castSucc j) ^
                (3 : ℕ)) •
            (DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc j) -
              DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc i)) =
        t • DominantFiveBody.tripleInternalVectorQuotient t alpha y i := @DominantFiveBody.tripleInternalCartesian_scaling

-- Source binding: prose:833
example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  DominantFiveBody.tripleInternalVectorQuotient (0 : ℝ) alpha y i =
    -DominantFiveBody.tripleBoundaryInternalForce alpha y i := @DominantFiveBody.tripleInternalVectorQuotient_zero

-- Source binding: prose:833
example : ∀ (n : ℕ∞ω) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  (∀ (j : DominantFiveBody.TripleLabel), j ≠ i → (0 : ℝ) < DominantFiveBody.tripleChartWSq (0 : ℝ) alpha y i j) →
    ContDiffAt ℝ n (fun (t : ℝ) => DominantFiveBody.tripleInternalVectorQuotient t alpha y i) (0 : ℝ) := @DominantFiveBody.tripleInternalVectorQuotient_contDiffAt

-- Source binding: prose:833
example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  (∀ (j : DominantFiveBody.TripleLabel), j ≠ i → (0 : ℝ) < DominantFiveBody.tripleChartWSq (0 : ℝ) alpha y i j) →
    (fun (t : ℝ) =>
        DominantFiveBody.tripleInternalVectorQuotient t alpha y i +
          DominantFiveBody.tripleBoundaryInternalForce alpha y i) =O[𝓝 (0 : ℝ)]
      fun (t : ℝ) => t := @DominantFiveBody.tripleInternalVectorQuotient_Olinear

-- Source binding: prose:833
example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  (∀ (j : DominantFiveBody.TripleLabel), j ≠ i → (0 : ℝ) < DominantFiveBody.tripleChartWSq (0 : ℝ) alpha y i j) →
    (fun (t : ℝ) =>
        ∑ j ∈ Finset.univ.erase i,
            (DominantFiveBody.tripleChartMass t alpha (Fin.castSucc j) /
                DominantFiveBody.satelliteDistance (DominantFiveBody.tripleChartPoints t alpha y) (Fin.castSucc i)
                    (Fin.castSucc j) ^
                  (3 : ℕ)) •
              (DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc j) -
                DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc i)) +
          t • DominantFiveBody.tripleBoundaryInternalForce alpha y i) =O[𝓝[>] (0 : ℝ)]
      fun (t : ℝ) => t ^ (2 : ℕ) := @DominantFiveBody.tripleInternalCartesian_Osquare

-- Source binding: prose:833
example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  Inner.inner ℝ (DominantFiveBody.tripleBoundaryDisplacement alpha y i)
      (DominantFiveBody.polarPoint (1 : ℝ) (y (4 : Fin (7 : ℕ)))) =
    DominantFiveBody.tripleChartRadialPositions alpha y i := @DominantFiveBody.tripleBoundaryDisplacement_radial

-- Source binding: prose:833
example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  Inner.inner ℝ (DominantFiveBody.tripleBoundaryDisplacement alpha y i)
      (DominantFiveBody.quarterTurn (DominantFiveBody.polarPoint (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ))))) =
    y (1 : Fin (7 : ℕ)) ^ (2 : ℕ) * DominantFiveBody.tripleChartAngularPositions alpha y i := @DominantFiveBody.tripleBoundaryDisplacement_angular

-- Source binding: prose:833
example : ∀ (eps : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  DominantFiveBody.tripleInternalRadialReduced eps (0 : ℝ) alpha y i =
    -eps *
      Inner.inner ℝ (DominantFiveBody.tripleBoundaryInternalForce alpha y i)
        (DominantFiveBody.polarPoint (1 : ℝ) (y (4 : Fin (7 : ℕ)))) := @DominantFiveBody.tripleInternalRadialReduced_vector_projection

-- Source binding: prose:833
example : ∀ (eps : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  DominantFiveBody.tripleInternalAngularReduced eps (0 : ℝ) alpha y i =
    -Inner.inner ℝ (DominantFiveBody.tripleBoundaryInternalForce alpha y i)
        (DominantFiveBody.quarterTurn (DominantFiveBody.polarPoint (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ))))) := @DominantFiveBody.tripleInternalAngularReduced_vector_projection

-- Source binding: prose:833
example : ∀ (eps tau : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  (0 : ℝ) < (1 : ℝ) + eps →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      y (0 : Fin (7 : ℕ)) = DominantFiveBody.backgroundRadius eps →
        y (1 : Fin (7 : ℕ)) = DominantFiveBody.backgroundRadius eps →
          y (4 : Fin (7 : ℕ)) = tau * DominantFiveBody.Coorbital.h →
            ∀ (i j : DominantFiveBody.TripleLabel),
              DominantFiveBody.tripleRadialExteriorDifference eps (0 : ℝ) alpha y i j =
                Inner.inner ℝ
                  ((DominantFiveBody.backgroundOperator eps tau : DominantFiveBody.Plane → DominantFiveBody.Plane)
                    (DominantFiveBody.triplePointDirection (0 : ℝ) alpha y i j))
                  (DominantFiveBody.backgroundE0 tau) := @DominantFiveBody.tripleRadialExteriorDifference_background

-- Source binding: prose:833
example : ∀ (eps tau : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  (0 : ℝ) < (1 : ℝ) + eps →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      y (0 : Fin (7 : ℕ)) = DominantFiveBody.backgroundRadius eps →
        y (1 : Fin (7 : ℕ)) = DominantFiveBody.backgroundRadius eps →
          y (4 : Fin (7 : ℕ)) = tau * DominantFiveBody.Coorbital.h →
            ∀ (i j : DominantFiveBody.TripleLabel),
              eps * DominantFiveBody.tripleAngularExteriorDifference eps (0 : ℝ) alpha y i j =
                Inner.inner ℝ
                  ((DominantFiveBody.backgroundOperator eps tau : DominantFiveBody.Plane → DominantFiveBody.Plane)
                    (DominantFiveBody.triplePointDirection (0 : ℝ) alpha y i j))
                  (DominantFiveBody.quarterTurn (DominantFiveBody.backgroundProbeCenter eps tau)) := @DominantFiveBody.tripleAngularExteriorDifference_background

-- Source binding: prose:833
example : ∀ (eps tau : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  (0 : ℝ) < (1 : ℝ) + eps →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      y (0 : Fin (7 : ℕ)) = DominantFiveBody.backgroundRadius eps →
        y (1 : Fin (7 : ℕ)) = DominantFiveBody.backgroundRadius eps →
          y (4 : Fin (7 : ℕ)) = tau * DominantFiveBody.Coorbital.h →
            DominantFiveBody.tripleRadialMean eps (0 : ℝ) alpha y = (0 : ℝ) := @DominantFiveBody.tripleRadialMean_background_zero

-- Source binding: prose:833
example : ∀ (eps tau : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  (0 : ℝ) < (1 : ℝ) + eps →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      y (0 : Fin (7 : ℕ)) = DominantFiveBody.backgroundRadius eps →
        y (1 : Fin (7 : ℕ)) = DominantFiveBody.backgroundRadius eps →
          y (4 : Fin (7 : ℕ)) = tau * DominantFiveBody.Coorbital.h →
            DominantFiveBody.tripleAngularMean eps (0 : ℝ) alpha y = (0 : ℝ) := @DominantFiveBody.tripleAngularMean_background_zero

-- Source binding: prose:833
example : ∀ (eps : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  (0 : ℝ) < (1 : ℝ) + eps →
    y (0 : Fin (7 : ℕ)) = DominantFiveBody.backgroundRadius eps →
      DominantFiveBody.radialResidual eps (DominantFiveBody.tripleChartMass (0 : ℝ) alpha)
          (DominantFiveBody.tripleChartRadii (0 : ℝ) alpha y) (DominantFiveBody.tripleChartAngles (0 : ℝ) alpha y)
          (3 : DominantFiveBody.Satellite) =
        (0 : ℝ) := @DominantFiveBody.tripleExteriorRadialRow_background_zero

-- Source binding: prose:833
example : ∀ (eps tau : ℝ) (alpha : DominantFiveBody.TripleVector) (g : DominantFiveBody.TripleGaps),
  |eps| < (1 / 4 : ℝ) →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      (∀ (i : DominantFiveBody.TripleLabel),
          DominantFiveBody.tripleScalarResidual alpha ((DominantFiveBody.tripleCenteringMatrix alpha).mulVec g) i =
            (0 : ℝ)) →
        ∀ (i : DominantFiveBody.TripleLabel),
          (DominantFiveBody.backgroundOperator eps tau : DominantFiveBody.Plane → DominantFiveBody.Plane)
                (DominantFiveBody.tripleBoundaryDisplacement alpha (DominantFiveBody.tripleSlowPoint eps tau g) i) -
              eps • DominantFiveBody.tripleBoundaryInternalForce alpha (DominantFiveBody.tripleSlowPoint eps tau g) i =
            (0 : DominantFiveBody.Plane) := @DominantFiveBody.tripleSlowPoint_vector_balance

-- Source binding: prose:833
example : ∀ (eps tau : ℝ) (alpha : DominantFiveBody.TripleVector) (g : DominantFiveBody.TripleGaps),
  |eps| < (1 / 4 : ℝ) →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
        (∀ (i : DominantFiveBody.TripleLabel),
            DominantFiveBody.tripleScalarResidual alpha ((DominantFiveBody.tripleCenteringMatrix alpha).mulVec g) i =
              (0 : ℝ)) →
          DominantFiveBody.tripleChartExtendedRows eps (0 : ℝ) alpha (DominantFiveBody.tripleSlowPoint eps tau g) =
            (0 : DominantFiveBody.TripleChartVariables) := @DominantFiveBody.tripleSlowPoint_root

-- Source binding: prose:833
example : ∀ (eps tau eta alpha Z z : ℝ),
  |eps| < (1 / 4 : ℝ) →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      (0 : ℝ) < eta →
        z ≠ (0 : ℝ) →
          Z + ((1 : ℝ) - alpha) * eta * z ≠ (0 : ℝ) →
            Z - alpha * eta * z ≠ (0 : ℝ) →
              (∀ (i : DominantFiveBody.TripleLabel),
                  DominantFiveBody.tripleScalarResidual (DominantFiveBody.nestedTripleWeights eta alpha)
                      ((DominantFiveBody.tripleCenteringMatrix (DominantFiveBody.nestedTripleWeights eta alpha)).mulVec
                        ![eta * z, Z - alpha * eta * z])
                      i =
                    (0 : ℝ)) →
                DominantFiveBody.nestedChartExtendedRows eps (0 : ℝ) eta alpha
                    (DominantFiveBody.nestedSlowPoint eps tau Z z) =
                  (0 : DominantFiveBody.NestedChartVariables) := @DominantFiveBody.nestedSlowPoint_root

-- Source binding: prose:833
example : ∀ (t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  DominantFiveBody.tripleChartPoints t alpha y (3 : DominantFiveBody.Satellite) =
    DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ) := @DominantFiveBody.v1_tripleChartPoints_fixed_exterior

-- Source binding: prose:833
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedChartPoints t eta alpha y (3 : DominantFiveBody.Satellite) =
    DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ) := @DominantFiveBody.v1_nestedChartPoints_fixed_exterior

-- Source binding: prose:833
example : ∀ (eps t : ℝ) (mu : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration)
  (omega : DominantFiveBody.TripleVector),
  (0 : ℝ) < (1 : ℝ) + eps →
    (∀ (i : DominantFiveBody.TripleLabel), mu (Fin.castSucc i) = t ^ (3 : ℕ) * omega i) →
      q (3 : DominantFiveBody.Satellite) = DominantFiveBody.backgroundExterior eps →
        DominantFiveBody.v1FieldDefect eps mu q =
          t ^ (3 : ℕ) •
            ∑ i : DominantFiveBody.TripleLabel,
              omega i •
                ((‖q (Fin.castSucc i)‖ ^ (3 : ℕ))⁻¹ • q (Fin.castSucc i) - ((1 : ℝ) + eps)⁻¹ • q (Fin.castSucc i)) := @DominantFiveBody.v1FieldDefect_cubic_factor

-- Source binding: prose:833
example : ∀ (eps : ℝ) (omega : DominantFiveBody.TripleVector) (mu : ℝ → DominantFiveBody.MassRatio)
  (q : ℝ → DominantFiveBody.SatelliteConfiguration),
  (0 : ℝ) < (1 : ℝ) + eps →
    (∀ (t : ℝ) (i : DominantFiveBody.TripleLabel), mu t (Fin.castSucc i) = t ^ (3 : ℕ) * omega i) →
      (∀ (t : ℝ), q t (3 : DominantFiveBody.Satellite) = DominantFiveBody.backgroundExterior eps) →
        (∀ (i : DominantFiveBody.TripleLabel), ContinuousAt (fun (t : ℝ) => q t (Fin.castSucc i)) (0 : ℝ)) →
          (∀ (i : DominantFiveBody.TripleLabel), q (0 : ℝ) (Fin.castSucc i) ≠ (0 : DominantFiveBody.Plane)) →
            (fun (t : ℝ) => DominantFiveBody.v1FieldDefect eps (mu t) (q t)) =O[𝓝 (0 : ℝ)] fun (t : ℝ) => t ^ (3 : ℕ) := @DominantFiveBody.v1FieldDefect_Ocube_of_fixed_exterior

-- Source binding: prose:833
example : ∀ (eps t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  (0 : ℝ) < (1 : ℝ) + eps →
    y (0 : Fin (7 : ℕ)) = DominantFiveBody.backgroundRadius eps →
      DominantFiveBody.v1FieldDefect eps (DominantFiveBody.tripleChartMass t alpha)
          (DominantFiveBody.tripleChartPoints t alpha y) =
        t ^ (3 : ℕ) •
          ∑ i : DominantFiveBody.TripleLabel,
            alpha i •
              ((‖DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc i)‖ ^ (3 : ℕ))⁻¹ •
                  DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc i) -
                ((1 : ℝ) + eps)⁻¹ • DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc i)) := @DominantFiveBody.v1_tripleChart_fieldDefect_cubic_factor

-- Source binding: prose:833
example : ∀ (eps : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  (0 : ℝ) < (1 : ℝ) + eps →
    y (0 : Fin (7 : ℕ)) = DominantFiveBody.backgroundRadius eps →
      y (1 : Fin (7 : ℕ)) ≠ (0 : ℝ) →
        (fun (t : ℝ) =>
            DominantFiveBody.v1FieldDefect eps (DominantFiveBody.tripleChartMass t alpha)
              (DominantFiveBody.tripleChartPoints t alpha y)) =O[𝓝 (0 : ℝ)]
          fun (t : ℝ) => t ^ (3 : ℕ) := @DominantFiveBody.v1_tripleChart_fieldDefect_Ocube

-- Source binding: prose:833
example : ∀ (eps t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  (0 : ℝ) < (1 : ℝ) + eps →
    y (0 : Fin (7 : ℕ)) = DominantFiveBody.backgroundRadius eps →
      DominantFiveBody.v1FieldDefect eps (DominantFiveBody.nestedChartMass t eta alpha)
          (DominantFiveBody.nestedChartPoints t eta alpha y) =
        t ^ (3 : ℕ) •
          ∑ i : DominantFiveBody.TripleLabel,
            DominantFiveBody.nestedTripleWeights eta alpha i •
              ((‖DominantFiveBody.nestedChartPoints t eta alpha y (Fin.castSucc i)‖ ^ (3 : ℕ))⁻¹ •
                  DominantFiveBody.nestedChartPoints t eta alpha y (Fin.castSucc i) -
                ((1 : ℝ) + eps)⁻¹ • DominantFiveBody.nestedChartPoints t eta alpha y (Fin.castSucc i)) := @DominantFiveBody.v1_nestedChart_fieldDefect_cubic_factor

-- Source binding: prose:833
example : ∀ (eps eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  (0 : ℝ) < (1 : ℝ) + eps →
    y (0 : Fin (7 : ℕ)) = DominantFiveBody.backgroundRadius eps →
      y (1 : Fin (7 : ℕ)) ≠ (0 : ℝ) →
        (fun (t : ℝ) =>
            DominantFiveBody.v1FieldDefect eps (DominantFiveBody.nestedChartMass t eta alpha)
              (DominantFiveBody.nestedChartPoints t eta alpha y)) =O[𝓝 (0 : ℝ)]
          fun (t : ℝ) => t ^ (3 : ℕ) := @DominantFiveBody.v1_nestedChart_fieldDefect_Ocube

-- Source binding: prose:833
example : ∀ (eps tau : ℝ) (alpha : DominantFiveBody.TripleVector) (g : DominantFiveBody.TripleGaps),
  (0 : ℝ) < (1 : ℝ) + eps →
    (fun (t : ℝ) =>
        DominantFiveBody.v1FieldDefect eps (DominantFiveBody.tripleChartMass t alpha)
          (DominantFiveBody.tripleChartPoints t alpha (DominantFiveBody.tripleSlowPoint eps tau g))) =O[𝓝 (0 : ℝ)]
      fun (t : ℝ) => t ^ (3 : ℕ) := @DominantFiveBody.v1_tripleSlowPoint_fieldDefect_Ocube

-- Source binding: prose:833
example : ∀ (eps tau eta alpha Z z : ℝ),
  (0 : ℝ) < (1 : ℝ) + eps →
    (fun (t : ℝ) =>
        DominantFiveBody.v1FieldDefect eps (DominantFiveBody.nestedChartMass t eta alpha)
          (DominantFiveBody.nestedChartPoints t eta alpha (DominantFiveBody.nestedSlowPoint eps tau Z z))) =O[𝓝 (0 : ℝ)]
      fun (t : ℝ) => t ^ (3 : ℕ) := @DominantFiveBody.v1_nestedSlowPoint_fieldDefect_Ocube

-- Source binding: prose:833
example : ∀ (eps : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) →
    ∀ (i : DominantFiveBody.Satellite),
      DominantFiveBody.radialResidual eps mu r theta i =
        Inner.inner ℝ (DominantFiveBody.v1CorrectedVectorResidual eps mu (DominantFiveBody.polarSatellites r theta) i)
          (DominantFiveBody.polarPoint (1 : ℝ) (theta i)) := @DominantFiveBody.v1_radialResidual_corrected_projection

-- Source binding: prose:833
example : ∀ (eps : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite),
  eps * DominantFiveBody.angularResidual eps mu r theta i =
    r i *
      Inner.inner ℝ (DominantFiveBody.v1CorrectedVectorResidual eps mu (DominantFiveBody.polarSatellites r theta) i)
        (DominantFiveBody.quarterTurn (DominantFiveBody.polarPoint (1 : ℝ) (theta i))) := @DominantFiveBody.v1_epsilon_angularResidual_corrected_projection

-- Source binding: v1:boundary.off_solution_projection
example : ∀ (eps : ℝ) (mu r theta : DominantFiveBody.Satellite → ℝ),
  eps ≠ (0 : ℝ) →
    ∀ (i : DominantFiveBody.Satellite),
      DominantFiveBody.angularResidual eps mu r theta i =
        r i / eps *
          Inner.inner ℝ (DominantFiveBody.v1CorrectedVectorResidual eps mu (DominantFiveBody.polarSatellites r theta) i)
            (DominantFiveBody.quarterTurn (DominantFiveBody.polarPoint (1 : ℝ) (theta i))) := @DominantFiveBody.v1_angularResidual_corrected_projection_div

-- Source binding: eq:regular-slow
example : ∀ (alpha0 z0 : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleWeights alpha0 →
    DominantFiveBody.TripleOrdered z0 →
      (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha0 z0 i = (0 : ℝ)) →
        ∀ (tau : ℝ),
          tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
            ∀ (eta r : ℝ),
              (0 : ℝ) < eta →
                (0 : ℝ) < r →
                  ∀ (branch : DominantFiveBody.TripleChartParameters → DominantFiveBody.TripleChartVariables),
                    (∀ (q : DominantFiveBody.TripleChartParameters),
                        Dist.dist q (DominantFiveBody.tripleBoundaryParameter alpha0) < eta →
                          ∀ (y : DominantFiveBody.TripleChartVariables),
                            Dist.dist y
                                  (DominantFiveBody.tripleUnitPoint (tau * DominantFiveBody.Coorbital.h)
                                    (DominantFiveBody.tripleGapMatrix.mulVec z0)) <
                                r →
                              (DominantFiveBody.tripleChartParameterRows q y =
                                  (0 : DominantFiveBody.TripleChartVariables) ↔
                                branch q = y)) →
                      ∃ (delta : ℝ),
                        (0 : ℝ) < delta ∧
                          ∀ (eps : ℝ) (alpha : DominantFiveBody.TripleVector),
                            |eps| < delta →
                              Dist.dist alpha alpha0 < delta →
                                ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
                                  branch (DominantFiveBody.tripleParameter eps (0 : ℝ) alpha) =
                                    DominantFiveBody.tripleSlowPoint eps tau
                                      (DominantFiveBody.tripleChartAngularGaps
                                        (branch (DominantFiveBody.tripleParameter (0 : ℝ) (0 : ℝ) alpha))) := @DominantFiveBody.tripleChart_zero_face_eq_slowPoint_of_local_uniqueness

-- Source binding: eq:regular-slow
example : ∀ (eps tau : ℝ) (v : DominantFiveBody.TripleGaps),
  DominantFiveBody.tripleSlowPoint eps tau v =
    ![DominantFiveBody.backgroundRadius eps, DominantFiveBody.backgroundRadius eps,
      DominantFiveBody.backgroundRadius eps * DominantFiveBody.backgroundSlowK eps tau *
          DominantFiveBody.backgroundAngularScale eps tau *
        v (0 : Fin (2 : ℕ)),
      DominantFiveBody.backgroundRadius eps * DominantFiveBody.backgroundSlowK eps tau *
          DominantFiveBody.backgroundAngularScale eps tau *
        v (1 : Fin (2 : ℕ)),
      tau * DominantFiveBody.Coorbital.h, DominantFiveBody.backgroundAngularScale eps tau * v (0 : Fin (2 : ℕ)),
      DominantFiveBody.backgroundAngularScale eps tau * v (1 : Fin (2 : ℕ))] := @DominantFiveBody.tripleSlowPoint_source_formula

-- Source binding: prose:845
example : ∀ (eps tau s : ℝ),
  (0 : ℝ) < (1 : ℝ) + eps →
    (DominantFiveBody.backgroundRadius eps * DominantFiveBody.backgroundSlowK eps tau *
            (DominantFiveBody.backgroundAngularScale eps tau * s)) •
          DominantFiveBody.backgroundE0 tau +
        (DominantFiveBody.backgroundRadius eps * (DominantFiveBody.backgroundAngularScale eps tau * s)) •
          DominantFiveBody.quarterTurn (DominantFiveBody.backgroundE0 tau) =
      DominantFiveBody.backgroundScalarLift eps tau s := @DominantFiveBody.backgroundSlow_polar_displacement

-- Source binding: prose:845
example : ∀ (alpha0 z0 : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleWeights alpha0 →
    DominantFiveBody.TripleOrdered z0 →
      (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha0 z0 i = (0 : ℝ)) →
        ∀ (tau : ℝ),
          tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
            ∀ (eta r : ℝ),
              (0 : ℝ) < eta →
                (0 : ℝ) < r →
                  ∀ (branch : DominantFiveBody.TripleChartParameters → DominantFiveBody.TripleChartVariables),
                    (∀ (q : DominantFiveBody.TripleChartParameters),
                        Dist.dist q (DominantFiveBody.tripleBoundaryParameter alpha0) < eta →
                          ∀ (y : DominantFiveBody.TripleChartVariables),
                            Dist.dist y
                                  (DominantFiveBody.tripleUnitPoint (tau * DominantFiveBody.Coorbital.h)
                                    (DominantFiveBody.tripleGapMatrix.mulVec z0)) <
                                r →
                              (DominantFiveBody.tripleChartParameterRows q y =
                                  (0 : DominantFiveBody.TripleChartVariables) ↔
                                branch q = y)) →
                      ∃ (delta : ℝ),
                        (0 : ℝ) < delta ∧
                          ∀ (eps : ℝ) (alpha : DominantFiveBody.TripleVector),
                            |eps| < delta →
                              Dist.dist alpha alpha0 < delta →
                                ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
                                  ∀ (i : DominantFiveBody.TripleLabel),
                                    DominantFiveBody.tripleChartRadialPositions alpha
                                        (branch (DominantFiveBody.tripleParameter eps (0 : ℝ) alpha)) i =
                                      DominantFiveBody.backgroundRadius eps * DominantFiveBody.backgroundSlowK eps tau *
                                        DominantFiveBody.tripleChartAngularPositions alpha
                                          (branch (DominantFiveBody.tripleParameter eps (0 : ℝ) alpha)) i := @DominantFiveBody.tripleChart_zero_face_parallel_of_local_uniqueness

-- Source binding: display:852
example : ∀ (eta alpha Z z : ℝ),
  DominantFiveBody.nestedTripleWeights eta alpha =
      ![eta ^ (3 : ℕ) * alpha, eta ^ (3 : ℕ) * ((1 : ℝ) - alpha), (1 : ℝ) - eta ^ (3 : ℕ)] ∧
    DominantFiveBody.nestedCoordinates (1 : ℝ) eta alpha (0 : ℝ) Z z =
      ![-((1 : ℝ) - eta ^ (3 : ℕ)) * Z - ((1 : ℝ) - alpha) * eta * z, -((1 : ℝ) - eta ^ (3 : ℕ)) * Z + alpha * eta * z,
        eta ^ (3 : ℕ) * Z] := @DominantFiveBody.nestedScalarPositions_formula_complete

-- Source binding: prose:856
example : ∀ (eta alpha Z z : ℝ),
  (DominantFiveBody.tripleCenteringMatrix (DominantFiveBody.nestedTripleWeights eta alpha)).mulVec
      ![eta * z, Z - alpha * eta * z] =
    ![-((1 : ℝ) - eta ^ (3 : ℕ)) * Z - ((1 : ℝ) - alpha) * eta * z, -((1 : ℝ) - eta ^ (3 : ℕ)) * Z + alpha * eta * z,
      eta ^ (3 : ℕ) * Z] := @DominantFiveBody.nestedBoundaryScalarPositions_source_formula

-- Source binding: prose:856
example : ∀ (eta alpha Z z : ℝ),
  eta ^ (3 : ℕ) * alpha * (-((1 : ℝ) - eta ^ (3 : ℕ)) * Z - ((1 : ℝ) - alpha) * eta * z) +
        eta ^ (3 : ℕ) * ((1 : ℝ) - alpha) * (-((1 : ℝ) - eta ^ (3 : ℕ)) * Z + alpha * eta * z) +
      ((1 : ℝ) - eta ^ (3 : ℕ)) * (eta ^ (3 : ℕ) * Z) =
    (0 : ℝ) := @DominantFiveBody.nestedBoundaryScalarPositions_weighted_center

-- Source binding: prose:856
example : ∀ (alpha0 tau omega : ℝ),
  tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
    ∀ (d r : ℝ),
      (0 : ℝ) < d →
        (0 : ℝ) < r →
          ∀ (branch : DominantFiveBody.NestedChartParameters → DominantFiveBody.NestedChartVariables),
            branch (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) =
                DominantFiveBody.nestedBasePoint (tau * DominantFiveBody.Coorbital.h) omega →
              ContDiffOn ℝ ∞ branch (Metric.ball (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) d) →
                (∀ (q : DominantFiveBody.NestedChartParameters),
                    Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < d →
                      DominantFiveBody.NestedContinuationDomain (q, branch q)) →
                  (∀ (q : DominantFiveBody.NestedChartParameters),
                      Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < d →
                        DominantFiveBody.nestedChartParameterRows q (branch q) =
                          (0 : DominantFiveBody.NestedChartVariables)) →
                    (∀ (q : DominantFiveBody.NestedChartParameters),
                        Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < d →
                          ∀ (y : DominantFiveBody.NestedChartVariables),
                            Dist.dist y (DominantFiveBody.nestedBasePoint (tau * DominantFiveBody.Coorbital.h) omega) <
                                r →
                              (DominantFiveBody.nestedChartParameterRows q y =
                                  (0 : DominantFiveBody.NestedChartVariables) ↔
                                branch q = y)) →
                      ∃ (delta : ℝ),
                        (0 : ℝ) < delta ∧
                          delta ≤ d ∧
                            ∀ (eps eta alpha : ℝ),
                              Dist.dist (DominantFiveBody.nestedParameter eps (0 : ℝ) eta alpha)
                                    (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) <
                                  delta →
                                (0 : ℝ) < eta →
                                  alpha ∈ Set.Icc (0 : ℝ) (1 : ℝ) →
                                    branch (DominantFiveBody.nestedParameter eps (0 : ℝ) eta alpha) =
                                      DominantFiveBody.nestedSlowPoint eps tau
                                        (branch (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) eta alpha)
                                          (5 : Fin (7 : ℕ)))
                                        (branch (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) eta alpha)
                                          (6 : Fin (7 : ℕ))) := @DominantFiveBody.nestedChart_zero_face_eq_slowPoint_of_local_uniqueness

-- Source binding: prose:856
example : ∀ (eps tau Z z : ℝ),
  DominantFiveBody.nestedSlowPoint eps tau Z z =
    ![DominantFiveBody.backgroundRadius eps, DominantFiveBody.backgroundRadius eps,
      DominantFiveBody.backgroundRadius eps * DominantFiveBody.backgroundSlowK eps tau *
          DominantFiveBody.backgroundAngularScale eps tau *
        Z,
      DominantFiveBody.backgroundRadius eps * DominantFiveBody.backgroundSlowK eps tau *
          DominantFiveBody.backgroundAngularScale eps tau *
        z,
      tau * DominantFiveBody.Coorbital.h, DominantFiveBody.backgroundAngularScale eps tau * Z,
      DominantFiveBody.backgroundAngularScale eps tau * z] := @DominantFiveBody.nestedSlowPoint_source_formula

-- Source binding: prose:856
example : ∀ (n : ℕ∞ω) (tau : ℝ) (branch : DominantFiveBody.NestedChartParameters → DominantFiveBody.NestedChartVariables)
  (q : DominantFiveBody.NestedChartParameters),
  |q (0 : Fin (4 : ℕ))| < (1 / 4 : ℝ) →
    ContDiffAt ℝ n branch
        (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ)))) →
      ContDiffAt ℝ n (DominantFiveBody.nestedSlowRootCandidate tau branch) q := @DominantFiveBody.nestedSlowRootCandidate_contDiffAt

-- Source binding: prose:856
example : ∀ (n : ℕ∞ω) (tau : ℝ) (branch : DominantFiveBody.NestedChartParameters → DominantFiveBody.NestedChartVariables)
  (base : DominantFiveBody.NestedChartParameters) (d : ℝ),
  ContDiffOn ℝ n branch (Metric.ball base d) →
    ContDiffOn ℝ n (DominantFiveBody.nestedSlowRootCandidate tau branch)
      {q : DominantFiveBody.NestedChartParameters |
        |q (0 : Fin (4 : ℕ))| < (1 / 4 : ℝ) ∧
          Dist.dist (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))))
              base <
            d} := @DominantFiveBody.nestedSlowRootCandidate_contDiffOn

-- Source binding: eq:nest-parallel
example : ∀ (alpha0 tau omega : ℝ),
  tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
    ∀ (d r : ℝ),
      (0 : ℝ) < d →
        (0 : ℝ) < r →
          ∀ (branch : DominantFiveBody.NestedChartParameters → DominantFiveBody.NestedChartVariables),
            branch (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) =
                DominantFiveBody.nestedBasePoint (tau * DominantFiveBody.Coorbital.h) omega →
              ContDiffOn ℝ ∞ branch (Metric.ball (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) d) →
                (∀ (q : DominantFiveBody.NestedChartParameters),
                    Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < d →
                      DominantFiveBody.NestedContinuationDomain (q, branch q)) →
                  (∀ (q : DominantFiveBody.NestedChartParameters),
                      Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < d →
                        DominantFiveBody.nestedChartParameterRows q (branch q) =
                          (0 : DominantFiveBody.NestedChartVariables)) →
                    (∀ (q : DominantFiveBody.NestedChartParameters),
                        Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < d →
                          ∀ (y : DominantFiveBody.NestedChartVariables),
                            Dist.dist y (DominantFiveBody.nestedBasePoint (tau * DominantFiveBody.Coorbital.h) omega) <
                                r →
                              (DominantFiveBody.nestedChartParameterRows q y =
                                  (0 : DominantFiveBody.NestedChartVariables) ↔
                                branch q = y)) →
                      ∃ (delta : ℝ),
                        (0 : ℝ) < delta ∧
                          delta ≤ d ∧
                            ∀ (eps eta alpha : ℝ),
                              Dist.dist (DominantFiveBody.nestedParameter eps (0 : ℝ) eta alpha)
                                    (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) <
                                  delta →
                                (0 : ℝ) < eta →
                                  alpha ∈ Set.Icc (0 : ℝ) (1 : ℝ) →
                                    have y := branch (DominantFiveBody.nestedParameter eps (0 : ℝ) eta alpha);
                                    y (3 : Fin (7 : ℕ)) * y (5 : Fin (7 : ℕ)) -
                                        y (2 : Fin (7 : ℕ)) * y (6 : Fin (7 : ℕ)) =
                                      (0 : ℝ) := @DominantFiveBody.nestedChart_zero_face_parallel_of_local_uniqueness

-- Source binding: prose:864
example : ∀ (alpha0 tau omega : ℝ),
  tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
    ∀ (d r : ℝ),
      (0 : ℝ) < d →
        (0 : ℝ) < r →
          ∀ (branch : DominantFiveBody.NestedChartParameters → DominantFiveBody.NestedChartVariables),
            branch (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) =
                DominantFiveBody.nestedBasePoint (tau * DominantFiveBody.Coorbital.h) omega →
              ContDiffOn ℝ ∞ branch (Metric.ball (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) d) →
                (∀ (q : DominantFiveBody.NestedChartParameters),
                    Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < d →
                      DominantFiveBody.NestedContinuationDomain (q, branch q)) →
                  (∀ (q : DominantFiveBody.NestedChartParameters),
                      Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < d →
                        DominantFiveBody.nestedChartParameterRows q (branch q) =
                          (0 : DominantFiveBody.NestedChartVariables)) →
                    (∀ (q : DominantFiveBody.NestedChartParameters),
                        Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < d →
                          ∀ (y : DominantFiveBody.NestedChartVariables),
                            Dist.dist y (DominantFiveBody.nestedBasePoint (tau * DominantFiveBody.Coorbital.h) omega) <
                                r →
                              (DominantFiveBody.nestedChartParameterRows q y =
                                  (0 : DominantFiveBody.NestedChartVariables) ↔
                                branch q = y)) →
                      ∃ (delta : ℝ),
                        (0 : ℝ) < delta ∧
                          delta ≤ d ∧
                            ∀ (eps eta alpha : ℝ),
                              Dist.dist (DominantFiveBody.nestedParameter eps (0 : ℝ) eta alpha)
                                    (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) <
                                  delta →
                                (0 : ℝ) ≤ eta →
                                  alpha ∈ Set.Icc (0 : ℝ) (1 : ℝ) →
                                    DominantFiveBody.nestedAreaAlongRoot branch eps eta alpha (0 : ℝ) = (0 : ℝ) := @DominantFiveBody.nestedChart_zero_face_area_zero_nonnegative_eta

-- Source binding: eq:circle-area
example : ∀ (A B C : ℝ),
  A < B →
    B < C →
      C < A + Real.pi →
        DominantFiveBody.det2 (DominantFiveBody.polarPoint (1 : ℝ) B - DominantFiveBody.polarPoint (1 : ℝ) A)
              (DominantFiveBody.polarPoint (1 : ℝ) C - DominantFiveBody.polarPoint (1 : ℝ) A) =
            (4 : ℝ) * Real.sin ((B - A) / (2 : ℝ)) * Real.sin ((C - B) / (2 : ℝ)) * Real.sin ((C - A) / (2 : ℝ)) ∧
          (0 : ℝ) <
              DominantFiveBody.det2 (DominantFiveBody.polarPoint (1 : ℝ) B - DominantFiveBody.polarPoint (1 : ℝ) A)
                (DominantFiveBody.polarPoint (1 : ℝ) C - DominantFiveBody.polarPoint (1 : ℝ) A) ∧
            DominantFiveBody.det2 (DominantFiveBody.polarPoint (1 : ℝ) A) (DominantFiveBody.polarPoint (1 : ℝ) B) =
                Real.sin (B - A) ∧
              (0 : ℝ) <
                DominantFiveBody.det2 (DominantFiveBody.polarPoint (1 : ℝ) A) (DominantFiveBody.polarPoint (1 : ℝ) B) := @DominantFiveBody.circle_areas_complete

-- Source binding: prose:874
example : ∀ (rho v t a b : ℝ),
  DominantFiveBody.polarPoint (rho + t * a) (v + t * b) - DominantFiveBody.polarPoint rho v =
    t • DominantFiveBody.polarDividedEdgeIntegral rho v t a b := @DominantFiveBody.polarDividedEdgeIntegral_factor

-- Source binding: prose:874
example : ∀ (rho v a b : ℝ),
  DominantFiveBody.polarDividedEdgeIntegral rho v (0 : ℝ) a b =
    (DominantFiveBody.polarPointDerivative (rho, v) : ℝ × ℝ → DominantFiveBody.Plane) (a, b) := @DominantFiveBody.polarDividedEdgeIntegral_zero

-- Source binding: prose:874
example : ∀ (t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i j : DominantFiveBody.TripleLabel),
  DominantFiveBody.triplePointDirection t alpha y i j =
    DominantFiveBody.polarDividedEdgeIntegral (DominantFiveBody.tripleChartRadii t alpha y (Fin.castSucc i))
      (DominantFiveBody.tripleChartAngles t alpha y (Fin.castSucc i)) t
      (DominantFiveBody.tripleChartRadialPositions alpha y j - DominantFiveBody.tripleChartRadialPositions alpha y i)
      (DominantFiveBody.tripleChartAngularPositions alpha y j - DominantFiveBody.tripleChartAngularPositions alpha y i) := @DominantFiveBody.triplePointDirection_original_integral_all_scales

-- Source binding: prose:874
example : ∀ (n : ℕ∞ω) (i j : DominantFiveBody.TripleLabel),
  ContDiff ℝ n fun (v : DominantFiveBody.TripleJointVariables) =>
    DominantFiveBody.triplePointDirection (v.1 (1 : Fin (5 : ℕ))) (DominantFiveBody.tripleJointAlpha v.1) v.2 i j := @DominantFiveBody.triplePointDirection_joint_contDiff

-- Source binding: display:875
example : ∀ (t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i j : DominantFiveBody.TripleLabel),
  DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc j) -
      DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc i) =
    t • DominantFiveBody.triplePointDirection t alpha y i j := @DominantFiveBody.triplePointDirection_identity

-- Source binding: display:875
example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i j : DominantFiveBody.TripleLabel),
  DominantFiveBody.triplePointDirection (0 : ℝ) alpha y i j =
    (DominantFiveBody.tripleChartRadialPositions alpha y j - DominantFiveBody.tripleChartRadialPositions alpha y i) •
        DominantFiveBody.polarPoint (1 : ℝ) (y (4 : Fin (7 : ℕ))) +
      (y (1 : Fin (7 : ℕ)) *
          (DominantFiveBody.tripleChartAngularPositions alpha y j -
            DominantFiveBody.tripleChartAngularPositions alpha y i)) •
        DominantFiveBody.quarterTurn (DominantFiveBody.polarPoint (1 : ℝ) (y (4 : Fin (7 : ℕ)))) := @DominantFiveBody.triplePointDirection_source_at_zero

-- Source binding: prose:879
example : ∀ (alpha0 z0 : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleWeights alpha0 →
    DominantFiveBody.TripleOrdered z0 →
      (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha0 z0 i = (0 : ℝ)) →
        ∀ (tau : ℝ),
          tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
            ∀ (eta r : ℝ),
              (0 : ℝ) < eta →
                (0 : ℝ) < r →
                  ∀ (branch : DominantFiveBody.TripleChartParameters → DominantFiveBody.TripleChartVariables),
                    (∀ (q : DominantFiveBody.TripleChartParameters),
                        Dist.dist q (DominantFiveBody.tripleBoundaryParameter alpha0) < eta →
                          ∀ (y : DominantFiveBody.TripleChartVariables),
                            Dist.dist y
                                  (DominantFiveBody.tripleUnitPoint (tau * DominantFiveBody.Coorbital.h)
                                    (DominantFiveBody.tripleGapMatrix.mulVec z0)) <
                                r →
                              (DominantFiveBody.tripleChartParameterRows q y =
                                  (0 : DominantFiveBody.TripleChartVariables) ↔
                                branch q = y)) →
                      ∃ (delta : ℝ),
                        (0 : ℝ) < delta ∧
                          ∀ (eps : ℝ) (alpha : DominantFiveBody.TripleVector),
                            |eps| < delta →
                              Dist.dist alpha alpha0 < delta →
                                ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
                                  DominantFiveBody.tripleAreaAlongRoot branch eps alpha (0 : ℝ) = (0 : ℝ) := @DominantFiveBody.tripleChart_zero_face_area_zero_of_local_uniqueness

-- Source binding: prose:879
example : ∀ (branch : DominantFiveBody.TripleChartParameters → DominantFiveBody.TripleChartVariables) (eps t : ℝ)
  (alpha : DominantFiveBody.TripleVector),
  DominantFiveBody.tripleAreaAlongRoot branch eps alpha (0 : ℝ) = (0 : ℝ) →
    (∀ s ∈ Set.Icc (0 : ℝ) (1 : ℝ),
        DifferentiableAt ℝ (DominantFiveBody.tripleAreaAlongRoot branch eps alpha) (s * t)) →
      ContinuousOn (fun (s : ℝ) => deriv (DominantFiveBody.tripleAreaAlongRoot branch eps alpha) (s * t))
          (Set.Icc (0 : ℝ) (1 : ℝ)) →
        DominantFiveBody.orientedArea
            (DominantFiveBody.liftRelative
              (DominantFiveBody.tripleChartPoints t alpha (branch (DominantFiveBody.tripleParameter eps t alpha))))
            (1 : DominantFiveBody.Label) (2 : DominantFiveBody.Label) (3 : DominantFiveBody.Label) =
          t ^ (3 : ℕ) * DominantFiveBody.tripleAreaCoefficientAlongRoot branch eps t alpha := @DominantFiveBody.tripleInternalArea_factor_cubic_along_root

-- Source binding: prose:885
example : ∀ (branch : DominantFiveBody.TripleChartParameters → DominantFiveBody.TripleChartVariables) (eps t : ℝ)
  (alpha : DominantFiveBody.TripleVector),
  DifferentiableAt ℝ (DominantFiveBody.tripleAreaParameterRoot branch) (DominantFiveBody.tripleParameter eps t alpha) →
    deriv (DominantFiveBody.tripleAreaAlongRoot branch eps alpha) t =
      DominantFiveBody.tripleAreaPartialDerivative branch (DominantFiveBody.tripleParameter eps t alpha) := @DominantFiveBody.tripleAreaAlongRoot_deriv_eq_partial

-- Source binding: prose:885
example : ∀ (alpha : DominantFiveBody.TripleVector),
  ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
    ∀ (branch : ℝ → DominantFiveBody.TripleChartVariables),
      ContDiffAt ℝ (1 : ℕ∞ω) branch (0 : ℝ) →
        (∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ),
            DominantFiveBody.tripleChartExtendedRows (0 : ℝ) t alpha (branch t) =
              (0 : DominantFiveBody.TripleChartVariables)) →
          (∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ),
              ∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < DominantFiveBody.tripleChartRadii t alpha (branch t) i) →
            HasDerivAt (fun (t : ℝ) => DominantFiveBody.tripleInternalAreaQuotient t alpha (branch t))
              (branch (0 : ℝ) (5 : Fin (7 : ℕ)) * branch (0 : ℝ) (6 : Fin (7 : ℕ)) *
                  (branch (0 : ℝ) (5 : Fin (7 : ℕ)) + branch (0 : ℝ) (6 : Fin (7 : ℕ))) /
                (2 : ℝ))
              (0 : ℝ) := @DominantFiveBody.tripleAreaAlongZeroRoot_hasDerivAt

-- Source binding: display:887
example : ∀ (g : DominantFiveBody.TripleGaps),
  DominantFiveBody.tripleCircleAreaCoefficient (0 : ℝ) g =
    g (0 : Fin (2 : ℕ)) * g (1 : Fin (2 : ℕ)) * (g (0 : Fin (2 : ℕ)) + g (1 : Fin (2 : ℕ))) / (2 : ℝ) := @DominantFiveBody.tripleCircleAreaCoefficient_zero

-- Source binding: display:887
example : ∀ (g : DominantFiveBody.TripleGaps),
  (0 : ℝ) < g (0 : Fin (2 : ℕ)) →
    (0 : ℝ) < g (1 : Fin (2 : ℕ)) → (0 : ℝ) < DominantFiveBody.tripleCircleAreaCoefficient (0 : ℝ) g := @DominantFiveBody.tripleCircleAreaCoefficient_zero_pos

-- Source binding: prose:890
example : ∀ (alpha0 z0 : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleWeights alpha0 →
    DominantFiveBody.TripleOrdered z0 →
      (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha0 z0 i = (0 : ℝ)) →
        ∀ (tau : ℝ),
          tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
            ∀ (eta r : ℝ),
              (0 : ℝ) < eta →
                (0 : ℝ) < r →
                  ∀ (branch : DominantFiveBody.TripleChartParameters → DominantFiveBody.TripleChartVariables),
                    branch (DominantFiveBody.tripleBoundaryParameter alpha0) =
                        DominantFiveBody.tripleUnitPoint (tau * DominantFiveBody.Coorbital.h)
                          (DominantFiveBody.tripleGapMatrix.mulVec z0) →
                      ContDiffOn ℝ ∞ branch (Metric.ball (DominantFiveBody.tripleBoundaryParameter alpha0) eta) →
                        (∀ (q : DominantFiveBody.TripleChartParameters),
                            Dist.dist q (DominantFiveBody.tripleBoundaryParameter alpha0) < eta →
                              DominantFiveBody.tripleChartParameterRows q (branch q) =
                                (0 : DominantFiveBody.TripleChartVariables)) →
                          (∀ (q : DominantFiveBody.TripleChartParameters),
                              Dist.dist q (DominantFiveBody.tripleBoundaryParameter alpha0) < eta →
                                ∀ (i : DominantFiveBody.Satellite),
                                  (0 : ℝ) <
                                    DominantFiveBody.tripleChartRadii (q (1 : Fin (5 : ℕ)))
                                      (DominantFiveBody.tripleJointAlpha q) (branch q) i) →
                            (∀ (q : DominantFiveBody.TripleChartParameters),
                                Dist.dist q (DominantFiveBody.tripleBoundaryParameter alpha0) < eta →
                                  ∀ (y : DominantFiveBody.TripleChartVariables),
                                    Dist.dist y
                                          (DominantFiveBody.tripleUnitPoint (tau * DominantFiveBody.Coorbital.h)
                                            (DominantFiveBody.tripleGapMatrix.mulVec z0)) <
                                        r →
                                      (DominantFiveBody.tripleChartParameterRows q y =
                                          (0 : DominantFiveBody.TripleChartVariables) ↔
                                        branch q = y)) →
                              ∃ (delta : ℝ),
                                (0 : ℝ) < delta ∧
                                  delta ≤ eta ∧
                                    ∀ (eps t : ℝ) (alpha : DominantFiveBody.TripleVector),
                                      Dist.dist (DominantFiveBody.tripleParameter eps t alpha)
                                            (DominantFiveBody.tripleBoundaryParameter alpha0) <
                                          delta →
                                        ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
                                          DominantFiveBody.orientedArea
                                                (DominantFiveBody.liftRelative
                                                  (DominantFiveBody.tripleChartPoints t alpha
                                                    (branch (DominantFiveBody.tripleParameter eps t alpha))))
                                                (1 : DominantFiveBody.Label) (2 : DominantFiveBody.Label)
                                                (3 : DominantFiveBody.Label) =
                                              t ^ (3 : ℕ) *
                                                DominantFiveBody.tripleAreaCoefficientAlongRoot branch eps t alpha ∧
                                            (0 : ℝ) < DominantFiveBody.tripleAreaCoefficientAlongRoot branch eps t alpha := @DominantFiveBody.tripleChart_internal_area_positive_neighborhood

-- Source binding: prose:890
example : ∀ (alpha : DominantFiveBody.TripleVector) (psi : ℝ) (g : DominantFiveBody.TripleGaps)
  (i j : DominantFiveBody.TripleLabel),
  DominantFiveBody.tripleExternalAreaQuotient (0 : ℝ) alpha (DominantFiveBody.tripleUnitPoint psi g) i j
      (0 : DominantFiveBody.Label) =
    (DominantFiveBody.tripleCenteringMatrix alpha).mulVec g j -
      (DominantFiveBody.tripleCenteringMatrix alpha).mulVec g i := @DominantFiveBody.tripleExternalAreaQuotient_primary_boundary

-- Source binding: prose:890
example : ∀ (alpha : DominantFiveBody.TripleVector) (psi : ℝ) (g : DominantFiveBody.TripleGaps)
  (i j : DominantFiveBody.TripleLabel),
  DominantFiveBody.tripleExternalAreaQuotient (0 : ℝ) alpha (DominantFiveBody.tripleUnitPoint psi g) i j
      (4 : DominantFiveBody.Label) =
    ((DominantFiveBody.tripleCenteringMatrix alpha).mulVec g j -
        (DominantFiveBody.tripleCenteringMatrix alpha).mulVec g i) *
      ((1 : ℝ) - Real.cos psi) := @DominantFiveBody.tripleExternalAreaQuotient_exterior_boundary

-- Source binding: prose:890
example : ∀ (alpha0 z0 : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleWeights alpha0 →
    DominantFiveBody.TripleOrdered z0 →
      (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha0 z0 i = (0 : ℝ)) →
        ∀ (tau : ℝ),
          tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
            ∀ (eta r : ℝ),
              (0 : ℝ) < eta →
                (0 : ℝ) < r →
                  ∀ (branch : DominantFiveBody.TripleChartParameters → DominantFiveBody.TripleChartVariables),
                    branch (DominantFiveBody.tripleBoundaryParameter alpha0) =
                        DominantFiveBody.tripleUnitPoint (tau * DominantFiveBody.Coorbital.h)
                          (DominantFiveBody.tripleGapMatrix.mulVec z0) →
                      ContDiffOn ℝ ∞ branch (Metric.ball (DominantFiveBody.tripleBoundaryParameter alpha0) eta) →
                        (∀ (q : DominantFiveBody.TripleChartParameters),
                            Dist.dist q (DominantFiveBody.tripleBoundaryParameter alpha0) < eta →
                              DominantFiveBody.tripleChartParameterRows q (branch q) =
                                (0 : DominantFiveBody.TripleChartVariables)) →
                          (∀ (q : DominantFiveBody.TripleChartParameters),
                              Dist.dist q (DominantFiveBody.tripleBoundaryParameter alpha0) < eta →
                                ∀ (i : DominantFiveBody.Satellite),
                                  (0 : ℝ) <
                                    DominantFiveBody.tripleChartRadii (q (1 : Fin (5 : ℕ)))
                                      (DominantFiveBody.tripleJointAlpha q) (branch q) i) →
                            (∀ (q : DominantFiveBody.TripleChartParameters),
                                Dist.dist q (DominantFiveBody.tripleBoundaryParameter alpha0) < eta →
                                  ∀ (y : DominantFiveBody.TripleChartVariables),
                                    Dist.dist y
                                          (DominantFiveBody.tripleUnitPoint (tau * DominantFiveBody.Coorbital.h)
                                            (DominantFiveBody.tripleGapMatrix.mulVec z0)) <
                                        r →
                                      (DominantFiveBody.tripleChartParameterRows q y =
                                          (0 : DominantFiveBody.TripleChartVariables) ↔
                                        branch q = y)) →
                              ∃ (delta : ℝ),
                                (0 : ℝ) < delta ∧
                                  delta ≤ eta ∧
                                    ∀ (eps t : ℝ) (alpha : DominantFiveBody.TripleVector),
                                      Dist.dist (DominantFiveBody.tripleParameter eps t alpha)
                                            (DominantFiveBody.tripleBoundaryParameter alpha0) <
                                          delta →
                                        ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
                                          (0 : ℝ) < t →
                                            DominantFiveBody.StrictConvexInOrder
                                              (DominantFiveBody.tripleBoundaryHullOrder tau)
                                              (DominantFiveBody.liftRelative
                                                (DominantFiveBody.tripleChartPoints t alpha
                                                  (branch (DominantFiveBody.tripleParameter eps t alpha)))) := @DominantFiveBody.tripleChart_strictConvex_neighborhood

-- Source binding: display:895
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedChartPoints t eta alpha y (1 : DominantFiveBody.Satellite) -
      DominantFiveBody.nestedChartPoints t eta alpha y (0 : DominantFiveBody.Satellite) =
    (t * eta) • DominantFiveBody.nestedInnerDirection t eta alpha y := @DominantFiveBody.nestedInnerDirection_identity

-- Source binding: display:895
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : Fin (2 : ℕ)),
  DominantFiveBody.nestedChartPoints t eta alpha y (2 : DominantFiveBody.Satellite) -
      DominantFiveBody.nestedChartPoints t eta alpha y (Fin.castAdd (2 : ℕ) i) =
    t • DominantFiveBody.nestedOuterDirection t eta alpha y i := @DominantFiveBody.nestedOuterDirection_identity

-- Source binding: display:895
example : ∀ (t eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.orientedArea (DominantFiveBody.liftRelative (DominantFiveBody.nestedChartPoints t eta alpha y))
      (1 : DominantFiveBody.Label) (2 : DominantFiveBody.Label) (3 : DominantFiveBody.Label) =
    t ^ (2 : ℕ) * eta * DominantFiveBody.nestedInternalAreaQuotient t eta alpha y := @DominantFiveBody.nestedInternalArea_factor_square

-- Source binding: display:900
example : ∀ (eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.nestedInternalAreaQuotient (0 : ℝ) eta alpha y =
    y (1 : Fin (7 : ℕ)) * (y (3 : Fin (7 : ℕ)) * y (5 : Fin (7 : ℕ)) - y (2 : Fin (7 : ℕ)) * y (6 : Fin (7 : ℕ))) := @DominantFiveBody.nestedInternalAreaQuotient_zero_formula

-- Source binding: eq:nest-area
example : ∀ (branch : DominantFiveBody.NestedChartParameters → DominantFiveBody.NestedChartVariables) (eps t eta alpha : ℝ),
  DominantFiveBody.nestedAreaAlongRoot branch eps eta alpha (0 : ℝ) = (0 : ℝ) →
    (∀ s ∈ Set.Icc (0 : ℝ) (1 : ℝ),
        DifferentiableAt ℝ (DominantFiveBody.nestedAreaAlongRoot branch eps eta alpha) (s * t)) →
      ContinuousOn (fun (s : ℝ) => deriv (DominantFiveBody.nestedAreaAlongRoot branch eps eta alpha) (s * t))
          (Set.Icc (0 : ℝ) (1 : ℝ)) →
        DominantFiveBody.orientedArea
            (DominantFiveBody.liftRelative
              (DominantFiveBody.nestedChartPoints t eta alpha
                (branch (DominantFiveBody.nestedParameter eps t eta alpha))))
            (1 : DominantFiveBody.Label) (2 : DominantFiveBody.Label) (3 : DominantFiveBody.Label) =
          t ^ (3 : ℕ) * eta * DominantFiveBody.nestedAreaCoefficientAlongRoot branch eps t eta alpha := @DominantFiveBody.nestedInternalArea_factor_cubic_along_root

-- Source binding: prose:909
example : ∀ (branch : DominantFiveBody.NestedChartParameters → DominantFiveBody.NestedChartVariables) (eps t eta alpha : ℝ),
  DifferentiableAt ℝ (DominantFiveBody.nestedAreaParameterRoot branch)
      (DominantFiveBody.nestedParameter eps t eta alpha) →
    deriv (DominantFiveBody.nestedAreaAlongRoot branch eps eta alpha) t =
      DominantFiveBody.nestedAreaPartialDerivative branch (DominantFiveBody.nestedParameter eps t eta alpha) := @DominantFiveBody.nestedAreaAlongRoot_deriv_eq_partial

-- Source binding: prose:909
example : ∀ (eta alpha : ℝ) (branch : ℝ → DominantFiveBody.NestedChartVariables),
  ContDiffAt ℝ (1 : ℕ∞ω) branch (0 : ℝ) →
    (∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ),
        DominantFiveBody.nestedChartExtendedRows (0 : ℝ) t eta alpha (branch t) =
          (0 : DominantFiveBody.NestedChartVariables)) →
      (∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ),
          ∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < DominantFiveBody.nestedChartRadii t eta alpha (branch t) i) →
        HasDerivAt (fun (t : ℝ) => DominantFiveBody.nestedInternalAreaQuotient t eta alpha (branch t))
          (branch (0 : ℝ) (6 : Fin (7 : ℕ)) *
                (branch (0 : ℝ) (5 : Fin (7 : ℕ)) + ((1 : ℝ) - alpha) * eta * branch (0 : ℝ) (6 : Fin (7 : ℕ))) *
              (branch (0 : ℝ) (5 : Fin (7 : ℕ)) - alpha * eta * branch (0 : ℝ) (6 : Fin (7 : ℕ))) /
            (2 : ℝ))
          (0 : ℝ) := @DominantFiveBody.nestedAreaAlongZeroRoot_hasDerivAt

-- Source binding: display:910
example : ∀ (alpha Z z : ℝ),
  Z ≠ (0 : ℝ) →
    (0 : ℝ) < z →
      DominantFiveBody.nestedCircleAreaCoefficient (0 : ℝ) (0 : ℝ) alpha Z z = z * Z ^ (2 : ℕ) / (2 : ℝ) ∧
        (0 : ℝ) < DominantFiveBody.nestedCircleAreaCoefficient (0 : ℝ) (0 : ℝ) alpha Z z := @DominantFiveBody.nestedCircle_coefficient_complete

-- Source binding: prose:913
example : ∀ (x : DominantFiveBody.Configuration) (i j k : DominantFiveBody.Label),
  DominantFiveBody.orientedArea x i j k = DominantFiveBody.orientedArea x j k i := @DominantFiveBody.orientedArea_cyclic

-- Source binding: display:915
example : ∀ (alpha psi Z z tau : ℝ),
  tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
    psi = tau * DominantFiveBody.Coorbital.h →
      ∀ (i : DominantFiveBody.TripleLabel),
        DominantFiveBody.tripleMacroArea tau
            (DominantFiveBody.liftRelative
              (DominantFiveBody.nestedChartPoints (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.nestedUnitPoint psi Z z)))
            i =
          Real.sin DominantFiveBody.Coorbital.h := @DominantFiveBody.nestedMacroArea_unit_boundary

-- Source binding: display:915
example : ∀ (alpha psi Z z : ℝ) (k : DominantFiveBody.NestedEdge),
  DominantFiveBody.nestedExternalAreaQuotient (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.nestedUnitPoint psi Z z) k
      (0 : DominantFiveBody.Label) =
    DominantFiveBody.nestedEdgeBoundaryGap Z z k := @DominantFiveBody.nestedExternalAreaQuotient_primary_boundary

-- Source binding: display:915
example : ∀ (alpha psi Z z : ℝ) (k : DominantFiveBody.NestedEdge),
  DominantFiveBody.nestedExternalAreaQuotient (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.nestedUnitPoint psi Z z) k
      (4 : DominantFiveBody.Label) =
    DominantFiveBody.nestedEdgeBoundaryGap Z z k * ((1 : ℝ) - Real.cos psi) := @DominantFiveBody.nestedExternalAreaQuotient_exterior_boundary

-- Source binding: display:915
example : ∀ (omega : ℝ),
  omega = (1 : ℝ) ∨ omega = (-1 : ℝ) →
    ∀ (k : DominantFiveBody.NestedEdge),
      (0 : ℝ) <
        DominantFiveBody.nestedEdgeOrientation omega k *
          DominantFiveBody.nestedEdgeBoundaryGap (omega * DominantFiveBody.pairBoundaryScale DominantFiveBody.tripleD0)
            (DominantFiveBody.pairBoundaryScale ((3 : ℝ) * DominantFiveBody.tripleD0)) k := @DominantFiveBody.nestedEdge_signed_base_gap_pos

-- Source binding: prose:925
example : ∀ (tau omega : ℝ),
  tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
    omega = (1 : ℝ) ∨ omega = (-1 : ℝ) →
      ∃ (delta : ℝ),
        (0 : ℝ) < delta ∧
          ∀ alpha0 ∈ Set.Icc (0 : ℝ) (1 : ℝ),
            ∀ (q : DominantFiveBody.NestedChartParameters) (y : DominantFiveBody.NestedChartVariables),
              Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < delta →
                Dist.dist y (DominantFiveBody.nestedBasePoint (tau * DominantFiveBody.Coorbital.h) omega) < delta →
                  DominantFiveBody.nestedChartParameterRows q y = (0 : DominantFiveBody.NestedChartVariables) →
                    (0 : ℝ) < q (1 : Fin (4 : ℕ)) →
                      (0 : ℝ) < q (2 : Fin (4 : ℕ)) →
                        q (3 : Fin (4 : ℕ)) ∈ Set.Icc (0 : ℝ) (1 : ℝ) →
                          DominantFiveBody.NestedTenAreasPositive tau omega
                              (DominantFiveBody.liftRelative
                                (DominantFiveBody.nestedChartPoints (q (1 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))
                                  (q (3 : Fin (4 : ℕ))) y)) ∧
                            DominantFiveBody.StrictConvexInOrder (DominantFiveBody.nestedBoundaryHullOrder tau omega)
                              (DominantFiveBody.liftRelative
                                (DominantFiveBody.nestedChartPoints (q (1 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))
                                  (q (3 : Fin (4 : ℕ))) y)) := @DominantFiveBody.nestedChart_all_ten_areas_uniform_product

-- Source binding: prose:925
example : ∀ (tau omega : Real),
  Or (@Eq Real tau (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
      (@Eq Real tau (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))) →
    Or (@Eq Real omega (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
        (@Eq Real omega
          (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))) →
      ∀ (x : DominantFiveBody.Configuration),
        (∀ (k : DominantFiveBody.NestedEdge) (j : DominantFiveBody.Label),
            @Membership.mem DominantFiveBody.Label (Finset DominantFiveBody.Label)
                (@SetLike.instMembership (Finset DominantFiveBody.Label) DominantFiveBody.Label
                  (@Finset.instSetLike DominantFiveBody.Label))
                (@Insert.insert DominantFiveBody.Label (Finset DominantFiveBody.Label)
                  (@Finset.instInsert DominantFiveBody.Label
                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                  (@OfNat.ofNat DominantFiveBody.Label (nat_lit 0)
                    (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)))
                  (@Singleton.singleton DominantFiveBody.Label (Finset DominantFiveBody.Label)
                    (@Finset.instSingleton DominantFiveBody.Label)
                    (@OfNat.ofNat DominantFiveBody.Label (nat_lit 4)
                      (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 4)))))
                j →
              @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                  (DominantFiveBody.nestedEdgeOrientation omega k)
                  (DominantFiveBody.orientedArea x
                    (@Fin.succ (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (DominantFiveBody.nestedEdgeSource k))
                    (@Fin.succ (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (DominantFiveBody.nestedEdgeTarget k))
                    j))) →
          (∀ (i : DominantFiveBody.TripleLabel),
              @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                (DominantFiveBody.tripleMacroArea tau x i)) →
            @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                (DominantFiveBody.orientedArea x
                  (@OfNat.ofNat DominantFiveBody.Label (nat_lit 1)
                    (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)))
                  (@OfNat.ofNat DominantFiveBody.Label (nat_lit 2)
                    (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 2)))
                  (@OfNat.ofNat DominantFiveBody.Label (nat_lit 3)
                    (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 3)))) →
              DominantFiveBody.StrictConvexInOrder (DominantFiveBody.nestedBoundaryHullOrder tau omega) x := @DominantFiveBody.nestedStrictConvex_of_positive_areas

-- Source binding: prop:chart-interface
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      ∀ (hm : ∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)),
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
              (∀ (n : ℕ),
                  DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                (∀ (n : ℕ), theta n (0 : DominantFiveBody.Satellite) = (0 : ℝ)) →
                  (∀ (n : ℕ), DominantFiveBody.OrderedSemicircle (theta n)) →
                    ∀ (muLimit : DominantFiveBody.MassRatio),
                      Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                        ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                          Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                              (𝓝 qLimit) →
                            ∀ (thetaLimit : DominantFiveBody.Satellite → ℝ),
                              Filter.Tendsto theta Filter.atTop (𝓝 thetaLimit) →
                                Function.Injective qLimit →
                                  Nonempty
                                    (DominantFiveBody.CapturedBranches DominantFiveBody.orderedSliceRoot
                                      DominantFiveBody.orderedSliceNondegenerate DominantFiveBody.orderedSliceEndpoint
                                      (fun (n : ℕ) => ⟨mu n, hm n⟩) eps fun (n : ℕ) =>
                                      DominantFiveBody.polarSlice (r n) (theta n)) := @DominantFiveBody.normalized_noCollision_ordered_capture

-- Source binding: prop:chart-interface
example : ∀ (p : ℕ → DominantFiveBody.PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → DominantFiveBody.SliceCoordinates),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.orderedSliceRoot (p n) (eps n) (y n)) →
        ∃ (phi : ℕ → ℕ) (radius : ℝ) (Gamma : ℕ → ℝ → DominantFiveBody.SliceCoordinates),
          StrictMono phi ∧
            (0 : ℝ) < radius ∧
              (∀ (n : ℕ), eps (phi n) < radius) ∧
                (∀ (n : ℕ), ContDiffOn ℝ ∞ (Gamma n) (Set.Ico (0 : ℝ) radius)) ∧
                  (∀ (n : ℕ), Gamma n (eps (phi n)) = y (phi n)) ∧
                    (∀ (n : ℕ) (s : ℝ),
                        (0 : ℝ) < s → s < radius → DominantFiveBody.orderedSliceRoot (p (phi n)) s (Gamma n s)) ∧
                      (∀ (n : ℕ) (s : ℝ),
                          (0 : ℝ) < s →
                            s < radius → DominantFiveBody.orderedSliceNondegenerate (p (phi n)) s (Gamma n s)) ∧
                        ∀ (n : ℕ), Gamma n (0 : ℝ) = DominantFiveBody.orderedSliceEndpoint (p (phi n)) := @DominantFiveBody.orderedSlice_smooth_connection_explicit

-- Source binding: prose:947
example : ∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m →
    ∀ (σ : DominantFiveBody.HullOrder) (x : DominantFiveBody.Configuration),
      DominantFiveBody.StrictConvexCentralConfiguration m σ x →
        ∃! y : DominantFiveBody.Configuration,
          DominantFiveBody.NormalizedCentralConfiguration m y ∧
            DominantFiveBody.FirstSatelliteGauge y ∧
              DominantFiveBody.StrictConvexInOrder σ y ∧ DominantFiveBody.OrientedSimilar x y := @DominantFiveBody.strictConvexCC_existsUnique_normalized_gauged

-- Source binding: prose:947
example : ∀ (mu : DominantFiveBody.PositiveMassRatio) (eps : ℝ),
  (0 : ℝ) < eps →
    ∀ (x : DominantFiveBody.Configuration),
      DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps (↑mu : DominantFiveBody.MassRatio))
          x →
        DominantFiveBody.FirstSatelliteGauge x →
          DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder x →
            ∃ (y : DominantFiveBody.SliceCoordinates),
              DominantFiveBody.orderedSliceRoot mu eps y ∧
                DominantFiveBody.slicePhysicalConfiguration (eps, (↑mu : DominantFiveBody.MassRatio)) y = x := @DominantFiveBody.orderedSliceRoot_of_normalized_gauged

-- Source binding: prose:947
example : ∀ (mu : DominantFiveBody.PositiveMassRatio) (eps : ℝ),
  (0 : ℝ) < eps →
    ∀ (y : DominantFiveBody.SliceCoordinates),
      DominantFiveBody.orderedSliceRoot mu eps y →
        DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps (↑mu : DominantFiveBody.MassRatio))
            (DominantFiveBody.slicePhysicalConfiguration (eps, (↑mu : DominantFiveBody.MassRatio)) y) ∧
          DominantFiveBody.FirstSatelliteGauge
              (DominantFiveBody.slicePhysicalConfiguration (eps, (↑mu : DominantFiveBody.MassRatio)) y) ∧
            DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder
              (DominantFiveBody.slicePhysicalConfiguration (eps, (↑mu : DominantFiveBody.MassRatio)) y) := @DominantFiveBody.orderedSliceRoot_physical

-- Source binding: prose:947
example : ∀ (p : DominantFiveBody.ContinuationParameter) (y z : DominantFiveBody.SliceCoordinates),
  DominantFiveBody.SliceRegular p y →
    DominantFiveBody.SliceRegular p z →
      DominantFiveBody.OrderedSemicircle (DominantFiveBody.sliceAngles y) →
        DominantFiveBody.OrderedSemicircle (DominantFiveBody.sliceAngles z) →
          DominantFiveBody.slicePhysicalConfiguration p y = DominantFiveBody.slicePhysicalConfiguration p z → y = z := @DominantFiveBody.ordered_slicePhysicalConfiguration_injective

-- Source binding: prose:947
example : ∀ (mu : DominantFiveBody.PositiveMassRatio) (eps : ℝ),
  (0 : ℝ) < eps →
    ∀ (x : DominantFiveBody.Configuration),
      DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps (↑mu : DominantFiveBody.MassRatio))
          x →
        DominantFiveBody.FirstSatelliteGauge x →
          DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder x →
            ∃! y : DominantFiveBody.SliceCoordinates,
              DominantFiveBody.orderedSliceRoot mu eps y ∧
                DominantFiveBody.slicePhysicalConfiguration (eps, (↑mu : DominantFiveBody.MassRatio)) y = x := @DominantFiveBody.orderedSliceRoot_unique_coordinates_of_normalized_gauged

-- Source binding: prose:947
example : ∀ (mu : DominantFiveBody.PositiveMassRatio) (eps : ℝ),
  (0 : ℝ) < eps →
    ∀ (x : DominantFiveBody.Configuration),
      DominantFiveBody.StrictConvexCentralConfiguration (DominantFiveBody.masses eps (↑mu : DominantFiveBody.MassRatio))
          DominantFiveBody.standardHullOrder x →
        ∃! y : DominantFiveBody.SliceCoordinates,
          DominantFiveBody.orderedSliceRoot mu eps y ∧
            DominantFiveBody.OrientedSimilar x
              (DominantFiveBody.slicePhysicalConfiguration (eps, (↑mu : DominantFiveBody.MassRatio)) y) := @DominantFiveBody.orderedSliceRoot_existsUnique_orientedSimilar

-- Source binding: prose:954
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration),
  (∀ (n : ℕ), (0 : ℝ) < eps n) →
    Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
      (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
        (∀ (n : ℕ), DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
          ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
            (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
              (∀ (n : ℕ),
                  DominantFiveBody.satellitesRelative (x n) = DominantFiveBody.polarSatellites (r n) (theta n)) →
                (∀ (n : ℕ) (i j : DominantFiveBody.Satellite),
                    i < j → (0 : ℝ) < theta n j - theta n i ∧ theta n j - theta n i < Real.pi) →
                  ∀ (muLimit : DominantFiveBody.MassRatio),
                    Filter.Tendsto mu Filter.atTop (𝓝 muLimit) →
                      ∀ (qLimit : DominantFiveBody.SatelliteConfiguration),
                        Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.satellitesRelative (x n)) Filter.atTop
                            (𝓝 qLimit) →
                          ∀ (theta0 : DominantFiveBody.Satellite → ℝ),
                            Filter.Tendsto theta Filter.atTop (𝓝 theta0) →
                              Filter.Tendsto r Filter.atTop (𝓝 fun (x : DominantFiveBody.Satellite) => (1 : ℝ)) ∧
                                (∀ (i : DominantFiveBody.Satellite),
                                    qLimit i = DominantFiveBody.polarPoint (1 : ℝ) (theta0 i)) ∧
                                  Monotone theta0 ∧
                                    (0 : ℝ) <
                                        theta0 (3 : DominantFiveBody.Satellite) -
                                          theta0 (0 : DominantFiveBody.Satellite) ∧
                                      theta0 (3 : DominantFiveBody.Satellite) -
                                          theta0 (0 : DominantFiveBody.Satellite) <
                                        Real.pi := @DominantFiveBody.normalized_ordered_polar_limit_geometry

-- Source binding: prose:954
example : ∀ (q : ℕ → DominantFiveBody.SatelliteConfiguration) (a b c : DominantFiveBody.Satellite),
  a ≠ b →
    a ≠ c →
      b ≠ c →
        (∀ (n : ℕ), DominantFiveBody.RelativeCollisionFree (q n)) →
          ∃ (phi : ℕ → ℕ),
            StrictMono phi ∧
              (Filter.Tendsto
                  (fun (n : ℕ) =>
                    DominantFiveBody.tripleShortestDistance (q (phi n)) a b c /
                      DominantFiveBody.tripleLargestDistance (q (phi n)) a b c)
                  Filter.atTop (𝓝 (0 : ℝ)) ∨
                ∃ (k : ℝ),
                  (0 : ℝ) < k ∧
                    ∀ (n : ℕ),
                      k * DominantFiveBody.tripleLargestDistance (q (phi n)) a b c ≤
                          DominantFiveBody.satelliteDistance (q (phi n)) a b ∧
                        k * DominantFiveBody.tripleLargestDistance (q (phi n)) a b c ≤
                            DominantFiveBody.satelliteDistance (q (phi n)) a c ∧
                          k * DominantFiveBody.tripleLargestDistance (q (phi n)) a b c ≤
                            DominantFiveBody.satelliteDistance (q (phi n)) b c) := @DominantFiveBody.collision_free_triple_scale_subsequence

-- Source binding: prose:954
example : ∀ (q : ℕ → DominantFiveBody.SatelliteConfiguration) (a b c : DominantFiveBody.Satellite),
  ∃ (phi : ℕ → ℕ) (u : DominantFiveBody.Satellite) (v : DominantFiveBody.Satellite) (w : DominantFiveBody.Satellite),
    StrictMono phi ∧
      (u = a ∧ v = b ∧ w = c ∨ u = a ∧ v = c ∧ w = b ∨ u = b ∧ v = c ∧ w = a) ∧
        ∀ (n : ℕ),
          DominantFiveBody.satelliteDistance (q (phi n)) u v = DominantFiveBody.tripleShortestDistance (q (phi n)) a b c := @DominantFiveBody.triple_minimum_pair_subsequence

-- Source binding: prose:954
example : DominantFiveBody.ConnectionProperty DominantFiveBody.orderedSliceRoot DominantFiveBody.orderedSliceNondegenerate
  DominantFiveBody.orderedSliceEndpoint := @DominantFiveBody.orderedSlice_connection

-- Source binding: prose:954
example : ∀ (alpha0 : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleWeights alpha0 →
    ∀ (g : DominantFiveBody.TripleGaps),
      (0 : ℝ) < g (0 : Fin (2 : ℕ)) →
        (0 : ℝ) < g (1 : Fin (2 : ℕ)) →
          ∀ (tau : ℝ),
            tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
              ∀ (eps t : ℕ → ℝ) (alpha : ℕ → DominantFiveBody.TripleVector)
                (y : ℕ → DominantFiveBody.TripleChartVariables),
                Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
                  Filter.Tendsto t Filter.atTop (𝓝 (0 : ℝ)) →
                    Filter.Tendsto alpha Filter.atTop (𝓝 alpha0) →
                      Filter.Tendsto y Filter.atTop
                          (𝓝 (DominantFiveBody.tripleUnitPoint (tau * DominantFiveBody.Coorbital.h) g)) →
                        (∀ (n : ℕ),
                            DominantFiveBody.tripleChartExtendedRows (eps n) (t n) (alpha n) (y n) =
                              (0 : DominantFiveBody.TripleChartVariables)) →
                          DominantFiveBody.TripleOrdered ((DominantFiveBody.tripleCenteringMatrix alpha0).mulVec g) ∧
                            ∀ (i : DominantFiveBody.TripleLabel),
                              DominantFiveBody.tripleScalarResidual alpha0
                                  ((DominantFiveBody.tripleCenteringMatrix alpha0).mulVec g) i =
                                (0 : ℝ) := @DominantFiveBody.tripleScalar_seed_of_regular_scaled_limits

-- Source binding: prose:954
example : ∀ (alpha0 : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleWeights alpha0 →
    ∀ (g : DominantFiveBody.TripleGaps),
      (0 : ℝ) < g (0 : Fin (2 : ℕ)) →
        (0 : ℝ) < g (1 : Fin (2 : ℕ)) →
          ∀ (tau : ℝ),
            tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
              ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (r theta : ℕ → DominantFiveBody.Satellite → ℝ),
                (∀ (n : ℕ), (0 : ℝ) < eps n) →
                  (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
                    (∀ (n : ℕ) (i : DominantFiveBody.Satellite), (0 : ℝ) < r n i) →
                      (∀ (n : ℕ), theta n (3 : DominantFiveBody.Satellite) = (0 : ℝ)) →
                        (∀ (n : ℕ),
                            DominantFiveBody.RelativeCollisionFree (DominantFiveBody.polarSatellites (r n) (theta n))) →
                          (∀ (n : ℕ),
                              DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n))
                                (DominantFiveBody.centeredFromRelative (eps n) (mu n)
                                  (DominantFiveBody.polarSatellites (r n) (theta n)))) →
                            Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
                              Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.triplePhysicalScale (mu n)) Filter.atTop
                                  (𝓝 (0 : ℝ)) →
                                Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.triplePhysicalWeights (mu n))
                                    Filter.atTop (𝓝 alpha0) →
                                  Filter.Tendsto
                                      (fun (n : ℕ) =>
                                        DominantFiveBody.tripleVariablesFromPolar
                                          (DominantFiveBody.triplePhysicalScale (mu n))
                                          (DominantFiveBody.triplePhysicalWeights (mu n)) (r n) (theta n))
                                      Filter.atTop
                                      (𝓝 (DominantFiveBody.tripleUnitPoint (tau * DominantFiveBody.Coorbital.h) g)) →
                                    Nonempty
                                      (DominantFiveBody.TripleCapturedBranches eps
                                        (fun (n : ℕ) => DominantFiveBody.triplePhysicalScale (mu n))
                                        (fun (n : ℕ) => DominantFiveBody.triplePhysicalWeights (mu n))
                                        (fun (n : ℕ) =>
                                          DominantFiveBody.tripleVariablesFromPolar
                                            (DominantFiveBody.triplePhysicalScale (mu n))
                                            (DominantFiveBody.triplePhysicalWeights (mu n)) (r n) (theta n))
                                        tau) := @DominantFiveBody.triplePhysical_capture_of_regular_scaled_limits

-- Source binding: prose:954
example : ∀ (sigma : DominantFiveBody.HullOrder) (r theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.sliceAngles (DominantFiveBody.orderedPolarSlice sigma r theta) =
    fun (i : DominantFiveBody.Satellite) =>
    theta
        ((DominantFiveBody.hullSatellitePermutation sigma : DominantFiveBody.Satellite → DominantFiveBody.Satellite)
          i) -
      theta
        ((DominantFiveBody.hullSatellitePermutation sigma : DominantFiveBody.Satellite → DominantFiveBody.Satellite)
          (0 : DominantFiveBody.Satellite)) := @DominantFiveBody.orderedPolarSlice_angles

-- Source binding: prose:954
example : ∀ (sigma : DominantFiveBody.HullOrder) (r theta : DominantFiveBody.Satellite → ℝ),
  DominantFiveBody.sliceRadii (DominantFiveBody.orderedPolarSlice sigma r theta) =
    r ∘ (⇑(DominantFiveBody.hullSatellitePermutation sigma) : DominantFiveBody.Satellite → DominantFiveBody.Satellite) := @DominantFiveBody.orderedPolarSlice_radii

-- Source binding: prose:954
example : ∀ (n : ℕ∞ω) (sigma : DominantFiveBody.HullOrder),
  ContDiff ℝ n fun (p : DominantFiveBody.MassRatio × DominantFiveBody.MassRatio) =>
    DominantFiveBody.orderedPolarSlice sigma p.1 p.2 := @DominantFiveBody.orderedPolarSlice_contDiff

-- Source binding: prose:954
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (sigma : DominantFiveBody.HullOrder)
  (r theta : DominantFiveBody.Satellite → ℝ),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) →
    DominantFiveBody.slicePhysicalConfiguration
        (eps,
          mu ∘
            (⇑(DominantFiveBody.hullSatellitePermutation sigma) :
              DominantFiveBody.Satellite → DominantFiveBody.Satellite))
        (DominantFiveBody.orderedPolarSlice sigma r theta) =
      DominantFiveBody.rotateConfiguration
        (DominantFiveBody.firstSatelliteRotation
          (DominantFiveBody.centeredFromRelative eps mu (DominantFiveBody.polarSatellites r theta) ∘
            (⇑sigma.labels : DominantFiveBody.Label → DominantFiveBody.Label)))
        (DominantFiveBody.centeredFromRelative eps mu (DominantFiveBody.polarSatellites r theta) ∘
          (⇑sigma.labels : DominantFiveBody.Label → DominantFiveBody.Label)) := @DominantFiveBody.orderedPolarSlice_physical_eq_rotation

-- Source binding: prose:954
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (sigma : DominantFiveBody.HullOrder)
  (r theta : DominantFiveBody.Satellite → ℝ) (hm : DominantFiveBody.PositiveRatio mu),
  (0 : ℝ) < eps →
    (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) →
      (∀ (i j : DominantFiveBody.Satellite), |theta j - theta i| < Real.pi) →
        DominantFiveBody.StrictConvexInOrder sigma
            (DominantFiveBody.liftRelative (DominantFiveBody.polarSatellites r theta)) →
          DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu)
              (DominantFiveBody.centeredFromRelative eps mu (DominantFiveBody.polarSatellites r theta)) →
            DominantFiveBody.orderedSliceRoot
              ⟨mu ∘
                  (⇑(DominantFiveBody.hullSatellitePermutation sigma) :
                    DominantFiveBody.Satellite → DominantFiveBody.Satellite),
                DominantFiveBody.positiveRatio_satellitePermutation mu hm
                  (DominantFiveBody.hullSatellitePermutation sigma)⟩
              eps (DominantFiveBody.orderedPolarSlice sigma r theta) := @DominantFiveBody.orderedPolarSlice_root_of_normalized

-- Source binding: prose:954
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (sigma : DominantFiveBody.HullOrder)
  (r theta : DominantFiveBody.Satellite → ℝ) (hm : DominantFiveBody.PositiveRatio mu),
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < r i) →
    DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu)
        (DominantFiveBody.centeredFromRelative eps mu (DominantFiveBody.polarSatellites r theta)) →
      DominantFiveBody.ShapeHessianNondegenerate (DominantFiveBody.masses eps mu) (1 : ℝ)
          (DominantFiveBody.centeredFromRelative eps mu (DominantFiveBody.polarSatellites r theta)) →
        DominantFiveBody.orderedSliceNondegenerate
          ⟨mu ∘
              (⇑(DominantFiveBody.hullSatellitePermutation sigma) :
                DominantFiveBody.Satellite → DominantFiveBody.Satellite),
            DominantFiveBody.positiveRatio_satellitePermutation mu hm (DominantFiveBody.hullSatellitePermutation sigma)⟩
          eps (DominantFiveBody.orderedPolarSlice sigma r theta) := @DominantFiveBody.orderedPolarSlice_nondegenerate_of_normalized

-- Source binding: prose:954
example : ∀ (sigma : DominantFiveBody.HullOrder) (e : Equiv.Perm DominantFiveBody.Satellite)
  (r theta : DominantFiveBody.Satellite → ℝ) (a : ℝ),
  DominantFiveBody.hullSatellitePermutation sigma = Equiv.symm e →
    theta (0 : DominantFiveBody.Satellite) = (0 : ℝ) →
      (DominantFiveBody.orderedPolarSlice sigma (r ∘ (⇑e : DominantFiveBody.Satellite → DominantFiveBody.Satellite))
          fun (i : DominantFiveBody.Satellite) =>
          theta ((e : DominantFiveBody.Satellite → DominantFiveBody.Satellite) i) - a) =
        DominantFiveBody.polarSlice r theta := @DominantFiveBody.orderedPolarSlice_reindex_undo

-- Source binding: prose:965
example : DominantFiveBody.FixedParameterLocalExistence DominantFiveBody.orderedSliceRoot := @DominantFiveBody.orderedSlice_fixedParameterLocalExistence

-- Source binding: prose:965
example : DominantFiveBody.LocalContinuationUniqueness DominantFiveBody.orderedSliceRoot
  DominantFiveBody.orderedSliceNondegenerate DominantFiveBody.orderedSliceEndpoint := @DominantFiveBody.orderedSlice_localContinuationUniqueness

-- Source binding: prose:970
example : ∀ {P : Type u} {Y : Type v} [inst : TopologicalSpace Y] {root nondegenerate : P → ℝ → Y → Prop} {endpoint : P → Y},
  DominantFiveBody.FixedParameterLocalExistence root →
    DominantFiveBody.ConnectionProperty root nondegenerate endpoint →
      DominantFiveBody.UniformBelow fun (p : P) (ε : ℝ) => ∃ (y : Y), root p ε y := @DominantFiveBody.uniform_existence_of_connection

-- Source binding: prose:975
example : ∀ {P : Type u} {Y : Type v} [inst : TopologicalSpace Y] [T2Space Y] {root nondegenerate : P → ℝ → Y → Prop}
  {endpoint : P → Y},
  DominantFiveBody.LocalContinuationUniqueness root nondegenerate endpoint →
    DominantFiveBody.ConnectionProperty root nondegenerate endpoint →
      DominantFiveBody.UniformBelow fun (p : P) (ε : ℝ) => ∀ (y z : Y), root p ε y → root p ε z → y = z := @DominantFiveBody.uniform_uniqueness_of_connection

-- Source binding: display:980
example : ∀ (radius s : ℝ) (first second : ℝ → DominantFiveBody.SliceCoordinates),
  s ∈ DominantFiveBody.branchEqualitySet radius first second ↔ (0 : ℝ) ≤ s ∧ s < radius ∧ first s = second s := @DominantFiveBody.mem_branchEqualitySet

-- Source binding: prose:986
example : ∀ {P : Type u} {Y : Type v} [inst : TopologicalSpace Y] {root nondegenerate : P → ℝ → Y → Prop} {endpoint : P → Y},
  DominantFiveBody.ConnectionProperty root nondegenerate endpoint →
    DominantFiveBody.UniformBelow fun (p : P) (ε : ℝ) => ∀ (y : Y), root p ε y → nondegenerate p ε y := @DominantFiveBody.uniform_nondegeneracy_of_connection

-- Source binding: prose:989
example : ∀ {P : Type u} {Y : Type v} [inst : TopologicalSpace Y] [T2Space Y] {root nondegenerate : P → ℝ → Y → Prop}
  {endpoint : P → Y},
  DominantFiveBody.FixedParameterLocalExistence root →
    DominantFiveBody.LocalContinuationUniqueness root nondegenerate endpoint →
      DominantFiveBody.ConnectionProperty root nondegenerate endpoint →
        ∃ (δ : ℝ),
          (0 : ℝ) < δ ∧
            ∀ (p : P) (ε : ℝ),
              (0 : ℝ) < ε → ε < δ → (∃! y : Y, root p ε y) ∧ ∀ (y : Y), root p ε y → nondegenerate p ε y := @DominantFiveBody.main_of_chart_facts

-- Source binding: prose:989
example : (∃ (d : ℝ),
    (0 : ℝ) < d ∧
      ∀ (mu : DominantFiveBody.PositiveMassRatio) (eps : ℝ),
        (0 : ℝ) < eps →
          eps < d →
            (∃! y : DominantFiveBody.SliceCoordinates, DominantFiveBody.orderedSliceRoot mu eps y) ∧
              ∀ (y : DominantFiveBody.SliceCoordinates),
                DominantFiveBody.orderedSliceRoot mu eps y → DominantFiveBody.orderedSliceNondegenerate mu eps y) →
  DominantFiveBody.MainUniformStatement := @DominantFiveBody.main_of_orderedSlice_uniform

-- Source binding: prose:989
example : ∀ (mu : DominantFiveBody.PositiveMassRatio) (eps : ℝ),
  (0 : ℝ) < eps →
    ∀ (sigma : DominantFiveBody.HullOrder),
      (∀ (y z : DominantFiveBody.SliceCoordinates),
          DominantFiveBody.orderedSliceRoot
              ⟨(↑mu : DominantFiveBody.MassRatio) ∘
                  (⇑(DominantFiveBody.hullSatellitePermutation sigma) :
                    DominantFiveBody.Satellite → DominantFiveBody.Satellite),
                DominantFiveBody.positiveRatio_hull_reindex (↑mu : DominantFiveBody.MassRatio) sigma mu.property⟩
              eps y →
            DominantFiveBody.orderedSliceRoot
                ⟨(↑mu : DominantFiveBody.MassRatio) ∘
                    (⇑(DominantFiveBody.hullSatellitePermutation sigma) :
                      DominantFiveBody.Satellite → DominantFiveBody.Satellite),
                  DominantFiveBody.positiveRatio_hull_reindex (↑mu : DominantFiveBody.MassRatio) sigma mu.property⟩
                eps z →
              y = z) →
        ∀ (x y : DominantFiveBody.Configuration),
          DominantFiveBody.StrictConvexCentralConfiguration
              (DominantFiveBody.masses eps (↑mu : DominantFiveBody.MassRatio)) sigma x →
            DominantFiveBody.StrictConvexCentralConfiguration
                (DominantFiveBody.masses eps (↑mu : DominantFiveBody.MassRatio)) sigma y →
              DominantFiveBody.OrientedSimilar x y := @DominantFiveBody.orderedSlice_uniqueness_to_geometric

-- Source binding: prose:989
example : ∀ (mu : DominantFiveBody.PositiveMassRatio) (eps : ℝ),
  (0 : ℝ) < eps →
    ∀ (sigma : DominantFiveBody.HullOrder),
      (∀ (y : DominantFiveBody.SliceCoordinates),
          DominantFiveBody.orderedSliceRoot
              ⟨(↑mu : DominantFiveBody.MassRatio) ∘
                  (⇑(DominantFiveBody.hullSatellitePermutation sigma) :
                    DominantFiveBody.Satellite → DominantFiveBody.Satellite),
                DominantFiveBody.positiveRatio_hull_reindex (↑mu : DominantFiveBody.MassRatio) sigma mu.property⟩
              eps y →
            DominantFiveBody.orderedSliceNondegenerate
              ⟨(↑mu : DominantFiveBody.MassRatio) ∘
                  (⇑(DominantFiveBody.hullSatellitePermutation sigma) :
                    DominantFiveBody.Satellite → DominantFiveBody.Satellite),
                DominantFiveBody.positiveRatio_hull_reindex (↑mu : DominantFiveBody.MassRatio) sigma mu.property⟩
              eps y) →
        ∀ (x : DominantFiveBody.Configuration),
          DominantFiveBody.StrictConvexCentralConfiguration
              (DominantFiveBody.masses eps (↑mu : DominantFiveBody.MassRatio)) sigma x →
            DominantFiveBody.NondegenerateCentralConfiguration
              (DominantFiveBody.masses eps (↑mu : DominantFiveBody.MassRatio)) x := @DominantFiveBody.orderedSlice_nondegeneracy_to_geometric

-- Exact definition type and body: DominantFiveBody.Coorbital.h
example : ℝ := @DominantFiveBody.Coorbital.h
example : @Eq (ℝ) (@DominantFiveBody.Coorbital.h) (Real.pi / (3 : ℝ)) := rfl
#print DominantFiveBody.Coorbital.h

-- Exact definition type and body: DominantFiveBody.Coorbital.kappa
example : ℝ → ℝ := @DominantFiveBody.Coorbital.kappa
example : @Eq (ℝ → ℝ) (@DominantFiveBody.Coorbital.kappa) (fun (t : ℝ) => ((2 : ℝ) - Real.sin (t / (2 : ℝ)) ^ (2 : ℕ)) / ((8 : ℝ) * Real.sin (t / (2 : ℝ)) ^ (3 : ℕ)) + Real.cos t) := rfl
#print DominantFiveBody.Coorbital.kappa

-- Exact definition type and body: DominantFiveBody.Coorbital.kappaPrime
example : ℝ → ℝ := @DominantFiveBody.Coorbital.kappaPrime
example : @Eq (ℝ → ℝ) (@DominantFiveBody.Coorbital.kappaPrime) (fun (t : ℝ) =>
  -Real.cos (t / (2 : ℝ)) / ((16 : ℝ) * Real.sin (t / (2 : ℝ)) ^ (4 : ℕ)) *
    ((6 : ℝ) - Real.sin (t / (2 : ℝ)) ^ (2 : ℕ) + (32 : ℝ) * Real.sin (t / (2 : ℝ)) ^ (5 : ℕ))) := rfl
#print DominantFiveBody.Coorbital.kappaPrime

-- Exact definition type and body: DominantFiveBody.Coorbital.kernelF
example : ℝ → ℝ := @DominantFiveBody.Coorbital.kernelF
example : @Eq (ℝ → ℝ) (@DominantFiveBody.Coorbital.kernelF) (fun (t : ℝ) => Real.sin t * (((2 : ℝ) * Real.sin (t / (2 : ℝ)))⁻¹ ^ (3 : ℕ) - (1 : ℝ))) := rfl
#print DominantFiveBody.Coorbital.kernelF

-- Exact definition type and body: DominantFiveBody.Coorbital.pairPotential
example : ℝ → ℝ := @DominantFiveBody.Coorbital.pairPotential
example : @Eq (ℝ → ℝ) (@DominantFiveBody.Coorbital.pairPotential) (fun (t : ℝ) => ((2 : ℝ) * Real.sin (t / (2 : ℝ)))⁻¹ + (1 : ℝ) - Real.cos t) := rfl
#print DominantFiveBody.Coorbital.pairPotential

-- Exact definition type and body: DominantFiveBody.Coorbital.positiveRemainder
example : ℝ → ℝ := @DominantFiveBody.Coorbital.positiveRemainder
example : @Eq (ℝ → ℝ) (@DominantFiveBody.Coorbital.positiveRemainder) (fun (t : ℝ) => DominantFiveBody.Coorbital.kappa t - DominantFiveBody.Coorbital.slopeCoefficient t) := rfl
#print DominantFiveBody.Coorbital.positiveRemainder

-- Exact definition type and body: DominantFiveBody.Coorbital.slopeCoefficient
example : ℝ → ℝ := @DominantFiveBody.Coorbital.slopeCoefficient
example : @Eq (ℝ → ℝ) (@DominantFiveBody.Coorbital.slopeCoefficient) (fun (t : ℝ) =>
  if t < DominantFiveBody.Coorbital.h then DominantFiveBody.Coorbital.kernelF t / (DominantFiveBody.Coorbital.h - t)
  else if t = DominantFiveBody.Coorbital.h then (0 : ℝ) else DominantFiveBody.Coorbital.kernelF t / (Real.pi - t)) := rfl
#print DominantFiveBody.Coorbital.slopeCoefficient

-- Exact definition type and body: DominantFiveBody.HullOrder
example : Type := @DominantFiveBody.HullOrder
example : (labels : Equiv.Perm DominantFiveBody.Label) →
  (labels : DominantFiveBody.Label → DominantFiveBody.Label) (0 : DominantFiveBody.Label) =
      (0 : DominantFiveBody.Label) →
    DominantFiveBody.HullOrder := @DominantFiveBody.HullOrder.mk
#print DominantFiveBody.HullOrder

-- Exact definition type and body: DominantFiveBody.NormalizedCentralConfiguration
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → Prop := @DominantFiveBody.NormalizedCentralConfiguration
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → Prop) (@DominantFiveBody.NormalizedCentralConfiguration) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) =>
  DominantFiveBody.CollisionFree x ∧
    DominantFiveBody.weightedPosition m x = (0 : DominantFiveBody.Plane) ∧
      ∀ (i : DominantFiveBody.Label), DominantFiveBody.acceleration m x i = -x i) := rfl
#print DominantFiveBody.NormalizedCentralConfiguration

-- Exact definition type and body: DominantFiveBody.OrientedSimilar
example : DominantFiveBody.Configuration → DominantFiveBody.Configuration → Prop := @DominantFiveBody.OrientedSimilar
example : @Eq (DominantFiveBody.Configuration → DominantFiveBody.Configuration → Prop) (@DominantFiveBody.OrientedSimilar) (fun (x y : DominantFiveBody.Configuration) =>
  ∃ (b : DominantFiveBody.Plane) (a : ℝ) (R : DominantFiveBody.Plane ≃ₗᵢ[ℝ] DominantFiveBody.Plane),
    (0 : ℝ) < a ∧
      (LinearMap.det : (DominantFiveBody.Plane →ₗ[ℝ] DominantFiveBody.Plane) → ℝ)
            (↑R.toLinearEquiv : DominantFiveBody.Plane →ₗ[ℝ] DominantFiveBody.Plane) =
          (1 : ℝ) ∧
        ∀ (i : DominantFiveBody.Label), y i = b + a • (R : DominantFiveBody.Plane → DominantFiveBody.Plane) (x i)) := rfl
#print DominantFiveBody.OrientedSimilar

-- Exact definition type and body: DominantFiveBody.PositiveRatio
example : DominantFiveBody.MassRatio → Prop := @DominantFiveBody.PositiveRatio
example : @Eq (DominantFiveBody.MassRatio → Prop) (@DominantFiveBody.PositiveRatio) (fun (μ : DominantFiveBody.MassRatio) =>
  (∀ (i : DominantFiveBody.Satellite), (0 : ℝ) < μ i) ∧ ∑ i : DominantFiveBody.Satellite, μ i = (1 : ℝ)) := rfl
#print DominantFiveBody.PositiveRatio

-- Exact definition type and body: DominantFiveBody.acceleration
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → DominantFiveBody.Label → DominantFiveBody.Plane := @DominantFiveBody.acceleration
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → DominantFiveBody.Label → DominantFiveBody.Plane) (@DominantFiveBody.acceleration) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) (i : DominantFiveBody.Label) =>
  ∑ j ∈ Finset.univ.erase i, (m j / DominantFiveBody.pairDistance x i j ^ (3 : ℕ)) • (x j - x i)) := rfl
#print DominantFiveBody.acceleration

-- Exact definition type and body: DominantFiveBody.angularJacobian
example : (DominantFiveBody.Satellite → ℝ) →
  (DominantFiveBody.Satellite → ℝ) → Matrix DominantFiveBody.Satellite DominantFiveBody.Satellite ℝ := @DominantFiveBody.angularJacobian
example : @Eq ((DominantFiveBody.Satellite → ℝ) →
  (DominantFiveBody.Satellite → ℝ) → Matrix DominantFiveBody.Satellite DominantFiveBody.Satellite ℝ) (@DominantFiveBody.angularJacobian) (fun (mass theta : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite) =>
  if i = j then ∑ k ∈ Finset.univ.erase i, mass k * DominantFiveBody.Coorbital.kappa |theta k - theta i|
  else -mass j * DominantFiveBody.Coorbital.kappa |theta j - theta i|) := rfl
#print DominantFiveBody.angularJacobian

-- Exact definition type and body: DominantFiveBody.angularResidual
example : ℝ →
  (DominantFiveBody.Satellite → ℝ) →
    (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.angularResidual
example : @Eq (ℝ →
  (DominantFiveBody.Satellite → ℝ) →
    (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.angularResidual) (fun (ε : ℝ) (μ r θ : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) =>
  ∑ j ∈ Finset.univ.erase i,
    μ j * r i * r j * Real.sin (θ j - θ i) *
      ((DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r θ) i j ^ (3 : ℕ))⁻¹ - ((1 : ℝ) + ε)⁻¹)) := rfl
#print DominantFiveBody.angularResidual

-- Exact definition type and body: DominantFiveBody.augmentedPotential
example : DominantFiveBody.MassVector → ℝ → DominantFiveBody.Configuration → ℝ := @DominantFiveBody.augmentedPotential
example : @Eq (DominantFiveBody.MassVector → ℝ → DominantFiveBody.Configuration → ℝ) (@DominantFiveBody.augmentedPotential) (fun (m : DominantFiveBody.MassVector) (lam : ℝ) (x : DominantFiveBody.Configuration) =>
  DominantFiveBody.potential m x + lam / (2 : ℝ) * DominantFiveBody.inertia m x) := rfl
#print DominantFiveBody.augmentedPotential

-- Exact definition type and body: DominantFiveBody.branchEqualitySet
example : ℝ → (ℝ → DominantFiveBody.SliceCoordinates) → (ℝ → DominantFiveBody.SliceCoordinates) → Set ℝ := @DominantFiveBody.branchEqualitySet
example : @Eq (ℝ → (ℝ → DominantFiveBody.SliceCoordinates) → (ℝ → DominantFiveBody.SliceCoordinates) → Set ℝ) (@DominantFiveBody.branchEqualitySet) (fun (radius : ℝ) (first second : ℝ → DominantFiveBody.SliceCoordinates) =>
  {s : ℝ | s ∈ Set.Ico (0 : ℝ) radius ∧ first s = second s}) := rfl
#print DominantFiveBody.branchEqualitySet

-- Exact definition type and body: DominantFiveBody.centeredFromRelative
example : ℝ → DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Configuration := @DominantFiveBody.centeredFromRelative
example : @Eq (ℝ → DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Configuration) (@DominantFiveBody.centeredFromRelative) (fun (ε : ℝ) (μ : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration)
    (i : DominantFiveBody.Label) =>
  DominantFiveBody.liftRelative q i - (ε / ((1 : ℝ) + ε)) • DominantFiveBody.relativeAverage μ q) := rfl
#print DominantFiveBody.centeredFromRelative

-- Exact definition type and body: DominantFiveBody.centeredVariationSpace
example : DominantFiveBody.MassVector → Submodule ℝ DominantFiveBody.Configuration := @DominantFiveBody.centeredVariationSpace
example : @Eq (DominantFiveBody.MassVector → Submodule ℝ DominantFiveBody.Configuration) (@DominantFiveBody.centeredVariationSpace) (fun (m : DominantFiveBody.MassVector) => (DominantFiveBody.weightedPositionLinear m).ker) := rfl
#print DominantFiveBody.centeredVariationSpace

-- Exact definition type and body: DominantFiveBody.coorbitalDistance
example : (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.coorbitalDistance
example : @Eq ((DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.coorbitalDistance) (fun (θ : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite) =>
  ‖DominantFiveBody.point (Real.cos (θ i)) (Real.sin (θ i)) - DominantFiveBody.point (Real.cos (θ j)) (Real.sin (θ j))‖) := rfl
#print DominantFiveBody.coorbitalDistance

-- Exact definition type and body: DominantFiveBody.coorbitalFirstAngleInsertion
example : (Fin (3 : ℕ) → ℝ) →L[ℝ] DominantFiveBody.Satellite → ℝ := @DominantFiveBody.coorbitalFirstAngleInsertion
example : @Eq ((Fin (3 : ℕ) → ℝ) →L[ℝ] DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.coorbitalFirstAngleInsertion) (ContinuousLinearMap.pi fun (i : DominantFiveBody.Satellite) =>
  Fin.cases (0 : (Fin (3 : ℕ) → ℝ) →L[ℝ] ℝ) (fun (j : Fin (3 : ℕ)) => ContinuousLinearMap.proj j) i) := rfl
#print DominantFiveBody.coorbitalFirstAngleInsertion

-- Exact definition type and body: DominantFiveBody.coorbitalHessianCoefficient
example : (DominantFiveBody.Satellite → ℝ) →
  (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.coorbitalHessianCoefficient
example : @Eq ((DominantFiveBody.Satellite → ℝ) →
  (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.coorbitalHessianCoefficient) (fun (mass theta : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite) =>
  if i < j then mass i * mass j * DominantFiveBody.Coorbital.kappa (theta j - theta i)
  else if j < i then mass j * mass i * DominantFiveBody.Coorbital.kappa (theta i - theta j) else (0 : ℝ)) := rfl
#print DominantFiveBody.coorbitalHessianCoefficient

-- Exact definition type and body: DominantFiveBody.coorbitalHessianMatrix
example : (DominantFiveBody.Satellite → ℝ) →
  (DominantFiveBody.Satellite → ℝ) → Matrix DominantFiveBody.Satellite DominantFiveBody.Satellite ℝ := @DominantFiveBody.coorbitalHessianMatrix
example : @Eq ((DominantFiveBody.Satellite → ℝ) →
  (DominantFiveBody.Satellite → ℝ) → Matrix DominantFiveBody.Satellite DominantFiveBody.Satellite ℝ) (@DominantFiveBody.coorbitalHessianMatrix) (fun (mass theta : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite) =>
  DominantFiveBody.coorbitalPhysicalHessian mass theta (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))) := rfl
#print DominantFiveBody.coorbitalHessianMatrix

-- Exact definition type and body: DominantFiveBody.coorbitalKernel
example : ℝ → ℝ := @DominantFiveBody.coorbitalKernel
example : @Eq (ℝ → ℝ) (@DominantFiveBody.coorbitalKernel) (fun (t : ℝ) => if (0 : ℝ) ≤ t then DominantFiveBody.Coorbital.kernelF t else -DominantFiveBody.Coorbital.kernelF (-t)) := rfl
#print DominantFiveBody.coorbitalKernel

-- Exact definition type and body: DominantFiveBody.coorbitalMatrix
example : (DominantFiveBody.Satellite → ℝ) → Matrix DominantFiveBody.Satellite DominantFiveBody.Satellite ℝ := @DominantFiveBody.coorbitalMatrix
example : @Eq ((DominantFiveBody.Satellite → ℝ) → Matrix DominantFiveBody.Satellite DominantFiveBody.Satellite ℝ) (@DominantFiveBody.coorbitalMatrix) (fun (θ : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite) =>
  if i = j then (0 : ℝ) else DominantFiveBody.coorbitalKernel (θ j - θ i)) := rfl
#print DominantFiveBody.coorbitalMatrix

-- Exact definition type and body: DominantFiveBody.coorbitalPotential
example : (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → ℝ := @DominantFiveBody.coorbitalPotential
example : @Eq ((DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → ℝ) (@DominantFiveBody.coorbitalPotential) (fun (μ θ : DominantFiveBody.Satellite → ℝ) =>
  ∑ p ∈ DominantFiveBody.satellitePairs,
    μ p.1 * μ p.2 *
      ((DominantFiveBody.coorbitalDistance θ p.1 p.2)⁻¹ +
        DominantFiveBody.coorbitalDistance θ p.1 p.2 ^ (2 : ℕ) / (2 : ℝ))) := rfl
#print DominantFiveBody.coorbitalPotential

-- Exact definition type and body: DominantFiveBody.coorbitalResidual
example : (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.coorbitalResidual
example : @Eq ((DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.coorbitalResidual) (fun (μ θ : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) =>
  ∑ j ∈ Finset.univ.erase i, μ j * DominantFiveBody.coorbitalKernel (θ j - θ i)) := rfl
#print DominantFiveBody.coorbitalResidual

-- Exact definition type and body: DominantFiveBody.coorbitalSliceHessianMap
example : (DominantFiveBody.Satellite → ℝ) → (Fin (3 : ℕ) → ℝ) → (Fin (3 : ℕ) → ℝ) →L[ℝ] (Fin (3 : ℕ) → ℝ) →L[ℝ] ℝ := @DominantFiveBody.coorbitalSliceHessianMap
example : @Eq ((DominantFiveBody.Satellite → ℝ) → (Fin (3 : ℕ) → ℝ) → (Fin (3 : ℕ) → ℝ) →L[ℝ] (Fin (3 : ℕ) → ℝ) →L[ℝ] ℝ) (@DominantFiveBody.coorbitalSliceHessianMap) (fun (mass : DominantFiveBody.Satellite → ℝ) (z : Fin (3 : ℕ) → ℝ) =>
  ((ContinuousLinearMap.compL ℝ (Fin (3 : ℕ) → ℝ) (DominantFiveBody.Satellite → ℝ) ℝ).flip :
        ((Fin (3 : ℕ) → ℝ) →L[ℝ] DominantFiveBody.Satellite → ℝ) →
          ((DominantFiveBody.Satellite → ℝ) →L[ℝ] ℝ) →L[ℝ] (Fin (3 : ℕ) → ℝ) →L[ℝ] ℝ)
      DominantFiveBody.coorbitalFirstAngleInsertion ∘SL
    DominantFiveBody.angularHessianMap mass
        ((DominantFiveBody.coorbitalFirstAngleInsertion : (Fin (3 : ℕ) → ℝ) → DominantFiveBody.Satellite → ℝ) z) ∘SL
      DominantFiveBody.coorbitalFirstAngleInsertion) := rfl
#print DominantFiveBody.coorbitalSliceHessianMap

-- Exact definition type and body: DominantFiveBody.coorbitalSliceHessianMatrix
example : (DominantFiveBody.Satellite → ℝ) → (Fin (3 : ℕ) → ℝ) → Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) ℝ := @DominantFiveBody.coorbitalSliceHessianMatrix
example : @Eq ((DominantFiveBody.Satellite → ℝ) → (Fin (3 : ℕ) → ℝ) → Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) ℝ) (@DominantFiveBody.coorbitalSliceHessianMatrix) (fun (mass : DominantFiveBody.Satellite → ℝ) (z : Fin (3 : ℕ) → ℝ) (i j : Fin (3 : ℕ)) =>
  ((fderiv ℝ (fderiv ℝ (DominantFiveBody.coorbitalSlicePotential mass)) z :
          (Fin (3 : ℕ) → ℝ) → (Fin (3 : ℕ) → ℝ) →L[ℝ] ℝ)
        (Pi.single i (1 : ℝ)) :
      (Fin (3 : ℕ) → ℝ) → ℝ)
    (Pi.single j (1 : ℝ))) := rfl
#print DominantFiveBody.coorbitalSliceHessianMatrix

-- Exact definition type and body: DominantFiveBody.coorbitalSlicePotential
example : (DominantFiveBody.Satellite → ℝ) → (Fin (3 : ℕ) → ℝ) → ℝ := @DominantFiveBody.coorbitalSlicePotential
example : @Eq ((DominantFiveBody.Satellite → ℝ) → (Fin (3 : ℕ) → ℝ) → ℝ) (@DominantFiveBody.coorbitalSlicePotential) (fun (mass : DominantFiveBody.Satellite → ℝ) (z : Fin (3 : ℕ) → ℝ) =>
  DominantFiveBody.coorbitalPotential mass
    ((DominantFiveBody.coorbitalFirstAngleInsertion : (Fin (3 : ℕ) → ℝ) → DominantFiveBody.Satellite → ℝ) z)) := rfl
#print DominantFiveBody.coorbitalSlicePotential

-- Exact definition type and body: DominantFiveBody.coorbitalSlicePotentialDerivative
example : (DominantFiveBody.Satellite → ℝ) → (Fin (3 : ℕ) → ℝ) → (Fin (3 : ℕ) → ℝ) →L[ℝ] ℝ := @DominantFiveBody.coorbitalSlicePotentialDerivative
example : @Eq ((DominantFiveBody.Satellite → ℝ) → (Fin (3 : ℕ) → ℝ) → (Fin (3 : ℕ) → ℝ) →L[ℝ] ℝ) (@DominantFiveBody.coorbitalSlicePotentialDerivative) (fun (mass : DominantFiveBody.Satellite → ℝ) (z : Fin (3 : ℕ) → ℝ) =>
  DominantFiveBody.angularPotentialDerivative mass
      ((DominantFiveBody.coorbitalFirstAngleInsertion : (Fin (3 : ℕ) → ℝ) → DominantFiveBody.Satellite → ℝ) z) ∘SL
    DominantFiveBody.coorbitalFirstAngleInsertion) := rfl
#print DominantFiveBody.coorbitalSlicePotentialDerivative

-- Exact definition type and body: DominantFiveBody.inertia
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → ℝ := @DominantFiveBody.inertia
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → ℝ) (@DominantFiveBody.inertia) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) =>
  ∑ i : DominantFiveBody.Label, m i * ‖x i‖ ^ (2 : ℕ)) := rfl
#print DominantFiveBody.inertia

-- Exact definition type and body: DominantFiveBody.inertiaTangentSpace
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → Submodule ℝ DominantFiveBody.Configuration := @DominantFiveBody.inertiaTangentSpace
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → Submodule ℝ DominantFiveBody.Configuration) (@DominantFiveBody.inertiaTangentSpace) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) =>
  DominantFiveBody.centeredVariationSpace m ⊓ (DominantFiveBody.massInnerRight m x).ker) := rfl
#print DominantFiveBody.inertiaTangentSpace

-- Exact definition type and body: DominantFiveBody.liftRelative
example : DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Configuration := @DominantFiveBody.liftRelative
example : @Eq (DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Configuration) (@DominantFiveBody.liftRelative) (fun (q : DominantFiveBody.SatelliteConfiguration) (i : Fin ((4 : ℕ) + (1 : ℕ))) =>
  Fin.cases (0 : DominantFiveBody.Plane) q i) := rfl
#print DominantFiveBody.liftRelative

-- Exact definition type and body: DominantFiveBody.masses
example : ℝ → DominantFiveBody.MassRatio → DominantFiveBody.MassVector := @DominantFiveBody.masses
example : @Eq (ℝ → DominantFiveBody.MassRatio → DominantFiveBody.MassVector) (@DominantFiveBody.masses) (fun (ε : ℝ) (μ : DominantFiveBody.MassRatio) (i : Fin ((4 : ℕ) + (1 : ℕ))) =>
  Fin.cases (1 : ℝ) (fun (i : Fin (4 : ℕ)) => ε * μ i) i) := rfl
#print DominantFiveBody.masses

-- Exact definition type and body: DominantFiveBody.orderedPolarSlice
example : DominantFiveBody.HullOrder →
  (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.SliceCoordinates := @DominantFiveBody.orderedPolarSlice
example : @Eq (DominantFiveBody.HullOrder →
  (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.SliceCoordinates) (@DominantFiveBody.orderedPolarSlice) (fun (sigma : DominantFiveBody.HullOrder) (r theta : DominantFiveBody.Satellite → ℝ) =>
  have e := DominantFiveBody.hullSatellitePermutation sigma;
  DominantFiveBody.polarSlice (r ∘ (⇑e : DominantFiveBody.Satellite → DominantFiveBody.Satellite))
    fun (i : DominantFiveBody.Satellite) =>
    theta ((e : DominantFiveBody.Satellite → DominantFiveBody.Satellite) i) -
      theta ((e : DominantFiveBody.Satellite → DominantFiveBody.Satellite) (0 : DominantFiveBody.Satellite))) := rfl
#print DominantFiveBody.orderedPolarSlice

-- Exact definition type and body: DominantFiveBody.orderedSliceRoot
example : DominantFiveBody.PositiveMassRatio → ℝ → DominantFiveBody.SliceCoordinates → Prop := @DominantFiveBody.orderedSliceRoot
example : @Eq (DominantFiveBody.PositiveMassRatio → ℝ → DominantFiveBody.SliceCoordinates → Prop) (@DominantFiveBody.orderedSliceRoot) (fun (mu : DominantFiveBody.PositiveMassRatio) (eps : ℝ) (y : DominantFiveBody.SliceCoordinates) =>
  DominantFiveBody.SliceRegular (eps, (↑mu : DominantFiveBody.MassRatio)) y ∧
    DominantFiveBody.OrderedSemicircle (DominantFiveBody.sliceAngles y) ∧
      DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder
          (DominantFiveBody.slicePhysicalConfiguration (eps, (↑mu : DominantFiveBody.MassRatio)) y) ∧
        DominantFiveBody.reducedResidual (eps, (↑mu : DominantFiveBody.MassRatio)) y =
          (0 : DominantFiveBody.SliceCoordinates)) := rfl
#print DominantFiveBody.orderedSliceRoot

-- Exact definition type and body: DominantFiveBody.pairDistance
example : DominantFiveBody.Configuration → DominantFiveBody.Label → DominantFiveBody.Label → ℝ := @DominantFiveBody.pairDistance
example : @Eq (DominantFiveBody.Configuration → DominantFiveBody.Label → DominantFiveBody.Label → ℝ) (@DominantFiveBody.pairDistance) (fun (x : DominantFiveBody.Configuration) (i j : DominantFiveBody.Label) => ‖x i - x j‖) := rfl
#print DominantFiveBody.pairDistance

-- Exact definition type and body: DominantFiveBody.pairs
example : Finset (DominantFiveBody.Label × DominantFiveBody.Label) := @DominantFiveBody.pairs
example : @Eq (Finset (DominantFiveBody.Label × DominantFiveBody.Label)) (@DominantFiveBody.pairs) ({p : DominantFiveBody.Label × DominantFiveBody.Label | p.1 < p.2}) := rfl
#print DominantFiveBody.pairs

-- Exact definition type and body: DominantFiveBody.polarPoint
example : ℝ → ℝ → DominantFiveBody.Plane := @DominantFiveBody.polarPoint
example : @Eq (ℝ → ℝ → DominantFiveBody.Plane) (@DominantFiveBody.polarPoint) (fun (r θ : ℝ) => DominantFiveBody.point (r * Real.cos θ) (r * Real.sin θ)) := rfl
#print DominantFiveBody.polarPoint

-- Exact definition type and body: DominantFiveBody.polarSatellites
example : (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.SatelliteConfiguration := @DominantFiveBody.polarSatellites
example : @Eq ((DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.SatelliteConfiguration) (@DominantFiveBody.polarSatellites) (fun (r θ : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) => DominantFiveBody.polarPoint (r i) (θ i)) := rfl
#print DominantFiveBody.polarSatellites

-- Exact definition type and body: DominantFiveBody.potential
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → ℝ := @DominantFiveBody.potential
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → ℝ) (@DominantFiveBody.potential) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) =>
  ∑ p ∈ DominantFiveBody.pairs, m p.1 * m p.2 / DominantFiveBody.pairDistance x p.1 p.2) := rfl
#print DominantFiveBody.potential

-- Exact definition type and body: DominantFiveBody.quarterTurn
example : DominantFiveBody.Plane → DominantFiveBody.Plane := @DominantFiveBody.quarterTurn
example : @Eq (DominantFiveBody.Plane → DominantFiveBody.Plane) (@DominantFiveBody.quarterTurn) (fun (v : DominantFiveBody.Plane) => DominantFiveBody.point (-v.ofLp (1 : Fin (2 : ℕ))) (v.ofLp (0 : Fin (2 : ℕ)))) := rfl
#print DominantFiveBody.quarterTurn

-- Exact definition type and body: DominantFiveBody.radialResidual
example : ℝ →
  (DominantFiveBody.Satellite → ℝ) →
    (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.radialResidual
example : @Eq (ℝ →
  (DominantFiveBody.Satellite → ℝ) →
    (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.radialResidual) (fun (ε : ℝ) (μ r θ : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) =>
  r i - (r i ^ (2 : ℕ))⁻¹ -
      ε *
        ∑ j ∈ Finset.univ.erase i,
          μ j * (r i - r j * Real.cos (θ j - θ i)) /
            DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r θ) i j ^ (3 : ℕ) -
    ε / ((1 : ℝ) + ε) *
      Inner.inner ℝ (DominantFiveBody.relativeAverage μ (DominantFiveBody.polarSatellites r θ))
        (DominantFiveBody.polarPoint (1 : ℝ) (θ i))) := rfl
#print DominantFiveBody.radialResidual

-- Exact definition type and body: DominantFiveBody.relativeAction
example : ℝ → DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → ℝ := @DominantFiveBody.relativeAction
example : @Eq (ℝ → DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → ℝ) (@DominantFiveBody.relativeAction) (fun (eps : ℝ) (mu : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration) =>
  ∑ i : DominantFiveBody.Satellite, mu i * (‖q i‖⁻¹ + ‖q i‖ ^ (2 : ℕ) / (2 : ℝ)) +
      eps * DominantFiveBody.relativePairPotential mu q -
    eps / ((1 : ℝ) + eps) / (2 : ℝ) * ‖DominantFiveBody.relativeAverage mu q‖ ^ (2 : ℕ)) := rfl
#print DominantFiveBody.relativeAction

-- Exact definition type and body: DominantFiveBody.relativeAverage
example : DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Plane := @DominantFiveBody.relativeAverage
example : @Eq (DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Plane) (@DominantFiveBody.relativeAverage) (fun (μ : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration) =>
  ∑ i : DominantFiveBody.Satellite, μ i • q i) := rfl
#print DominantFiveBody.relativeAverage

-- Exact definition type and body: DominantFiveBody.relativeField
example : DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Plane := @DominantFiveBody.relativeField
example : @Eq (DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Plane) (@DominantFiveBody.relativeField) (fun (μ : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration) =>
  ∑ i : DominantFiveBody.Satellite, (μ i / ‖q i‖ ^ (3 : ℕ)) • q i) := rfl
#print DominantFiveBody.relativeField

-- Exact definition type and body: DominantFiveBody.satellitePairs
example : Finset (DominantFiveBody.Satellite × DominantFiveBody.Satellite) := @DominantFiveBody.satellitePairs
example : @Eq (Finset (DominantFiveBody.Satellite × DominantFiveBody.Satellite)) (@DominantFiveBody.satellitePairs) ({p : DominantFiveBody.Satellite × DominantFiveBody.Satellite | p.1 < p.2}) := rfl
#print DominantFiveBody.satellitePairs

-- Exact definition type and body: DominantFiveBody.satellitesRelative
example : DominantFiveBody.Configuration → DominantFiveBody.SatelliteConfiguration := @DominantFiveBody.satellitesRelative
example : @Eq (DominantFiveBody.Configuration → DominantFiveBody.SatelliteConfiguration) (@DominantFiveBody.satellitesRelative) (fun (x : DominantFiveBody.Configuration) (i : DominantFiveBody.Satellite) =>
  DominantFiveBody.primaryRelative x (Fin.succ i)) := rfl
#print DominantFiveBody.satellitesRelative

-- Exact definition type and body: DominantFiveBody.shapeSpace
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → Submodule ℝ DominantFiveBody.Configuration := @DominantFiveBody.shapeSpace
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → Submodule ℝ DominantFiveBody.Configuration) (@DominantFiveBody.shapeSpace) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) =>
  (DominantFiveBody.weightedPositionLinear m).ker ⊓
    ((DominantFiveBody.massInnerRight m (DominantFiveBody.centered m x)).ker ⊓
      (DominantFiveBody.massInnerRight m (DominantFiveBody.rotationDirection (DominantFiveBody.centered m x))).ker)) := rfl
#print DominantFiveBody.shapeSpace

-- Exact definition type and body: DominantFiveBody.sliceAngles
example : DominantFiveBody.SliceCoordinates → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.sliceAngles
example : @Eq (DominantFiveBody.SliceCoordinates → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.sliceAngles) (fun (y : DominantFiveBody.SliceCoordinates) (i : Fin ((3 : ℕ) + (1 : ℕ))) =>
  Fin.cases (0 : ℝ) (fun (i : Fin (3 : ℕ)) => y (Fin.natAdd (4 : ℕ) i)) i) := rfl
#print DominantFiveBody.sliceAngles

-- Exact definition type and body: DominantFiveBody.slicePhysicalConfiguration
example : DominantFiveBody.ContinuationParameter → DominantFiveBody.SliceCoordinates → DominantFiveBody.Configuration := @DominantFiveBody.slicePhysicalConfiguration
example : @Eq (DominantFiveBody.ContinuationParameter → DominantFiveBody.SliceCoordinates → DominantFiveBody.Configuration) (@DominantFiveBody.slicePhysicalConfiguration) (fun (p : DominantFiveBody.ContinuationParameter) (y : DominantFiveBody.SliceCoordinates) =>
  (DominantFiveBody.relativeCenteredContinuous p.1 p.2 :
      DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Configuration)
    (DominantFiveBody.sliceSatellites y)) := rfl
#print DominantFiveBody.slicePhysicalConfiguration

-- Exact definition type and body: DominantFiveBody.sliceRadii
example : DominantFiveBody.SliceCoordinates → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.sliceRadii
example : @Eq (DominantFiveBody.SliceCoordinates → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.sliceRadii) (fun (y : DominantFiveBody.SliceCoordinates) (i : DominantFiveBody.Satellite) => y (Fin.castAdd (3 : ℕ) i)) := rfl
#print DominantFiveBody.sliceRadii

-- Exact definition type and body: DominantFiveBody.tangentialResidual
example : (DominantFiveBody.Satellite → ℝ) →
  (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.tangentialResidual
example : @Eq ((DominantFiveBody.Satellite → ℝ) →
  (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.tangentialResidual) (fun (μ r θ : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) =>
  ∑ j ∈ Finset.univ.erase i,
    μ j * r j * Real.sin (θ j - θ i) *
      ((DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r θ) i j ^ (3 : ℕ))⁻¹ - (r j ^ (3 : ℕ))⁻¹)) := rfl
#print DominantFiveBody.tangentialResidual

-- Exact definition type and body: DominantFiveBody.v1CorrectedVectorResidual
example : ℝ →
  DominantFiveBody.MassRatio →
    DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Satellite → DominantFiveBody.Plane := @DominantFiveBody.v1CorrectedVectorResidual
example : @Eq (ℝ →
  DominantFiveBody.MassRatio →
    DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Satellite → DominantFiveBody.Plane) (@DominantFiveBody.v1CorrectedVectorResidual) (fun (eps : ℝ) (mu : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration)
    (i : DominantFiveBody.Satellite) =>
  DominantFiveBody.vectorResidual eps mu q i + eps • DominantFiveBody.v1FieldDefect eps mu q) := rfl
#print DominantFiveBody.v1CorrectedVectorResidual

-- Exact definition type and body: DominantFiveBody.v1FieldDefect
example : ℝ → DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Plane := @DominantFiveBody.v1FieldDefect
example : @Eq (ℝ → DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Plane) (@DominantFiveBody.v1FieldDefect) (fun (eps : ℝ) (mu : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration) =>
  DominantFiveBody.relativeField mu q - ((1 : ℝ) + eps)⁻¹ • DominantFiveBody.relativeAverage mu q) := rfl
#print DominantFiveBody.v1FieldDefect

-- Exact definition type and body: DominantFiveBody.vectorResidual
example : ℝ →
  DominantFiveBody.MassRatio →
    DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Satellite → DominantFiveBody.Plane := @DominantFiveBody.vectorResidual
example : @Eq (ℝ →
  DominantFiveBody.MassRatio →
    DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Satellite → DominantFiveBody.Plane) (@DominantFiveBody.vectorResidual) (fun (ε : ℝ) (μ : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration)
    (i : DominantFiveBody.Satellite) =>
  q i - (‖q i‖ ^ (3 : ℕ))⁻¹ • q i +
      ε • ∑ j ∈ Finset.univ.erase i, (μ j / DominantFiveBody.satelliteDistance q i j ^ (3 : ℕ)) • (q j - q i) -
    ε • DominantFiveBody.relativeField μ q) := rfl
#print DominantFiveBody.vectorResidual

-- Exact definition type and body: DominantFiveBody.weightedPosition
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → DominantFiveBody.Plane := @DominantFiveBody.weightedPosition
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → DominantFiveBody.Plane) (@DominantFiveBody.weightedPosition) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) => ∑ i : DominantFiveBody.Label, m i • x i) := rfl
#print DominantFiveBody.weightedPosition

#print axioms DominantFiveBody.CompactImplicit.compact_product
#print axioms DominantFiveBody.Coorbital.angularFlow_balanced
#print axioms DominantFiveBody.Coorbital.angularFlow_neg_iff
#print axioms DominantFiveBody.Coorbital.angularFlow_pos_iff
#print axioms DominantFiveBody.Coorbital.coorbital_cycle_bound
#print axioms DominantFiveBody.Coorbital.four_angular_cycle_decomposition
#print axioms DominantFiveBody.Coorbital.four_root_gaps
#print axioms DominantFiveBody.Coorbital.h
#print axioms DominantFiveBody.Coorbital.kappa
#print axioms DominantFiveBody.Coorbital.kappaPrime
#print axioms DominantFiveBody.Coorbital.kappa_h
#print axioms DominantFiveBody.Coorbital.kappa_intervalIntegrable
#print axioms DominantFiveBody.Coorbital.kernelF
#print axioms DominantFiveBody.Coorbital.kernelF_ge_neg_one
#print axioms DominantFiveBody.Coorbital.kernelF_h
#print axioms DominantFiveBody.Coorbital.kernelF_neg_on_long_arc
#print axioms DominantFiveBody.Coorbital.kernelF_pi
#print axioms DominantFiveBody.Coorbital.kernelF_pos_on_short_arc
#print axioms DominantFiveBody.Coorbital.pairPotential
#print axioms DominantFiveBody.Coorbital.positiveRemainder
#print axioms DominantFiveBody.Coorbital.positiveRemainder_pos
#print axioms DominantFiveBody.Coorbital.slopeCoefficient
#print axioms DominantFiveBody.Coorbital.strictAntiOn_kappa
#print axioms DominantFiveBody.Coorbital.three_cycle_display
#print axioms DominantFiveBody.Coorbital.three_edge_cycle_eq_zero_iff
#print axioms DominantFiveBody.Coorbital.three_root_gaps
#print axioms DominantFiveBody.Coorbital.two_cycle_display
#print axioms DominantFiveBody.Coorbital.two_denominator_cauchy_eq_iff
#print axioms DominantFiveBody.Coorbital.two_edge_cycle_eq_zero_iff
#print axioms DominantFiveBody.Coorbital.two_root_separation
#print axioms DominantFiveBody.HullOrder
#print axioms DominantFiveBody.NormalizedCentralConfiguration
#print axioms DominantFiveBody.OrientedSimilar
#print axioms DominantFiveBody.PositiveRatio
#print axioms DominantFiveBody.acceleration
#print axioms DominantFiveBody.actual_current_angular_group_representative_scaled_limit
#print axioms DominantFiveBody.actual_group_near_angular_scaled_tendsto_zero
#print axioms DominantFiveBody.affinePolarPoint_cartesian_Osquare
#print axioms DominantFiveBody.affinePolarPoint_divided_identity
#print axioms DominantFiveBody.angularChordHessian_kernel_iff
#print axioms DominantFiveBody.angularDifferential_constant
#print axioms DominantFiveBody.angularDifferential_kernel_iff_nonnegative
#print axioms DominantFiveBody.angularDifferential_recover_row
#print axioms DominantFiveBody.angularDifferential_weighted_zero
#print axioms DominantFiveBody.angularHessianMap_constant_right
#print axioms DominantFiveBody.angularJacobian
#print axioms DominantFiveBody.angularJacobian_mulVec
#print axioms DominantFiveBody.angularJacobian_zero_mass_column
#print axioms DominantFiveBody.angularJacobian_zero_support_diagonal
#print axioms DominantFiveBody.angularResidual
#print axioms DominantFiveBody.angularResidual_omitted_row
#print axioms DominantFiveBody.angular_hessian_estimate
#print axioms DominantFiveBody.augmentedPotential
#print axioms DominantFiveBody.backgroundAngularScale_contDiffAt
#print axioms DominantFiveBody.backgroundMatrix_characteristic_factor
#print axioms DominantFiveBody.backgroundMatrix_trace
#print axioms DominantFiveBody.backgroundOperator_apply
#print axioms DominantFiveBody.backgroundOperator_coordinates
#print axioms DominantFiveBody.backgroundProbeField_affinePolar_Osquare
#print axioms DominantFiveBody.backgroundProbeField_hasFDerivAt
#print axioms DominantFiveBody.backgroundProbeField_source_formula
#print axioms DominantFiveBody.backgroundProbeField_zero
#print axioms DominantFiveBody.backgroundScalarLift_vector_balance
#print axioms DominantFiveBody.backgroundSlowDirection_contDiffAt
#print axioms DominantFiveBody.backgroundSlowDirection_eigen
#print axioms DominantFiveBody.backgroundSlowK_contDiffAt
#print axioms DominantFiveBody.backgroundSlowLambda_characteristic
#print axioms DominantFiveBody.backgroundSlowLambda_eq
#print axioms DominantFiveBody.backgroundSlowLambda_lt_fast
#print axioms DominantFiveBody.backgroundSlowLength_contDiffAt
#print axioms DominantFiveBody.backgroundSlow_formula_complete
#print axioms DominantFiveBody.backgroundSlow_polar_displacement
#print axioms DominantFiveBody.backgroundSlow_scaling
#print axioms DominantFiveBody.backgroundSlow_zero_complete
#print axioms DominantFiveBody.backgroundSpectrum_formula_complete
#print axioms DominantFiveBody.branchEqualitySet
#print axioms DominantFiveBody.centeredFromRelative
#print axioms DominantFiveBody.centeredFromRelative_source_formulas
#print axioms DominantFiveBody.centeredVariationSpace
#print axioms DominantFiveBody.centered_radial_tangent_direct_sum
#print axioms DominantFiveBody.centered_radial_tangent_hessian_orthogonal
#print axioms DominantFiveBody.circle_areas_complete
#print axioms DominantFiveBody.closedCoorbital_largest_mass_gauge
#print axioms DominantFiveBody.clusterCenter_tendsto_current_weights
#print axioms DominantFiveBody.cluster_internal_force_zero
#print axioms DominantFiveBody.collision_free_triple_scale_subsequence
#print axioms DominantFiveBody.compact_positive_mass_floor
#print axioms DominantFiveBody.complete_cluster_current_center_exterior_bound
#print axioms DominantFiveBody.complete_pair_angular_prebound_before_radial_exclusion
#print axioms DominantFiveBody.complete_pair_direction_support_nonneg
#print axioms DominantFiveBody.complete_pair_exterior_angular_error_bound
#print axioms DominantFiveBody.complete_pair_exterior_difference_quotient_limit
#print axioms DominantFiveBody.complete_pair_exterior_error_bound
#print axioms DominantFiveBody.complete_pair_ordered_angles_adjacent
#print axioms DominantFiveBody.complete_pair_support_radial_expansion_littleO
#print axioms DominantFiveBody.coorbitalBaseSlice_actual_data
#print axioms DominantFiveBody.coorbitalDistance
#print axioms DominantFiveBody.coorbitalFirstAngleInsertion
#print axioms DominantFiveBody.coorbitalHessianCoefficient
#print axioms DominantFiveBody.coorbitalHessianCoefficient_of_lt
#print axioms DominantFiveBody.coorbitalHessianCoefficient_symmetric
#print axioms DominantFiveBody.coorbitalHessianMatrix
#print axioms DominantFiveBody.coorbitalHessianMatrix_diagonal
#print axioms DominantFiveBody.coorbitalHessianMatrix_offDiagonal
#print axioms DominantFiveBody.coorbitalHessianMatrix_quadratic
#print axioms DominantFiveBody.coorbitalHessianMatrix_quadratic_expanded
#print axioms DominantFiveBody.coorbitalKernel
#print axioms DominantFiveBody.coorbitalKernel_neg
#print axioms DominantFiveBody.coorbitalMassProjection_fiber_finite
#print axioms DominantFiveBody.coorbitalMassProjection_isCoveringMapOn
#print axioms DominantFiveBody.coorbitalMassProjection_isLocalHomeomorphOn
#print axioms DominantFiveBody.coorbitalMassProjection_isProperMap
#print axioms DominantFiveBody.coorbitalMatrix
#print axioms DominantFiveBody.coorbitalPhysicalHessian_pair_formula
#print axioms DominantFiveBody.coorbitalPhysicalHessian_self
#print axioms DominantFiveBody.coorbitalPotential
#print axioms DominantFiveBody.coorbitalPotential_coordinate_derivative
#print axioms DominantFiveBody.coorbitalPotential_eq_angularPotential
#print axioms DominantFiveBody.coorbitalResidual
#print axioms DominantFiveBody.coorbitalResidual_eq_matrix_sum
#print axioms DominantFiveBody.coorbitalResidual_hasFDerivAt
#print axioms DominantFiveBody.coorbitalSliceHessianMap
#print axioms DominantFiveBody.coorbitalSliceHessianMatrix
#print axioms DominantFiveBody.coorbitalSliceHessianMatrix_eq_submatrix
#print axioms DominantFiveBody.coorbitalSliceHessian_quadratic_zero_first
#print axioms DominantFiveBody.coorbitalSlicePotential
#print axioms DominantFiveBody.coorbitalSlicePotentialDerivative
#print axioms DominantFiveBody.coorbitalSlicePotential_hessian_pullback
#print axioms DominantFiveBody.coorbitalVirial_pair_with_mass_floor
#print axioms DominantFiveBody.coorbitalVirial_zero
#print axioms DominantFiveBody.coorbital_closed_mass_jacobian_complete
#print axioms DominantFiveBody.coorbital_compact_physical_continuation
#print axioms DominantFiveBody.coorbital_cut
#print axioms DominantFiveBody.coorbital_global_complete
#print axioms DominantFiveBody.coorbital_negative_terms_lower_bound
#print axioms DominantFiveBody.coorbital_recover_positive_mass_row
#print axioms DominantFiveBody.coorbital_roots_uniform_pair_separation
#print axioms DominantFiveBody.coorbital_three_source_kernel_not_all_zero_at_missing_source
#print axioms DominantFiveBody.coorbital_three_source_kernel_vector_by_rank
#print axioms DominantFiveBody.coorbital_three_source_ranks_and_kernel_dimensions
#print axioms DominantFiveBody.coorbital_weightedResidual_zero
#print axioms DominantFiveBody.coordinate_row_transform_fderiv_at_root
#print axioms DominantFiveBody.coordinate_row_transform_isInvertible_iff
#print axioms DominantFiveBody.current_group_near_angular_scaled_abs_bound
#print axioms DominantFiveBody.deletedAngularJacobian_inverse_uniform_on_closed_roots
#print axioms DominantFiveBody.deletedAngularJacobian_isUnit_nonnegative
#print axioms DominantFiveBody.deletedAngularJacobian_isUnit_positive
#print axioms DominantFiveBody.dominant_normalized_diameter_le
#print axioms DominantFiveBody.dominant_ordered_polar_gap_limsup
#print axioms DominantFiveBody.dominant_primary_relative_radii_uniform
#print axioms DominantFiveBody.dominant_primary_relative_radius_lower
#print axioms DominantFiveBody.dominant_projectedClusterGap_source
#print axioms DominantFiveBody.dominant_strictConvex_uniform_polar_span
#print axioms DominantFiveBody.dominant_uniform_geometry_complete
#print axioms DominantFiveBody.equalMass_coorbital_existsUnique
#print axioms DominantFiveBody.equalMass_root_reversal_symmetry
#print axioms DominantFiveBody.equal_scaled_class_cross_separation
#print axioms DominantFiveBody.finite_exterior_scaled_difference_bound
#print axioms DominantFiveBody.finrank_shapeSpace
#print axioms DominantFiveBody.five_projection_large_gap
#print axioms DominantFiveBody.fixedAngleDeletedJacobian_isInvertible_iff_shape
#print axioms DominantFiveBody.fixedAngleDeletedResidual_same_eq
#print axioms DominantFiveBody.fixedAngle_zero_source_full_block
#print axioms DominantFiveBody.fullAngularMatrix_cross_distance_abs_bound
#print axioms DominantFiveBody.fullAngularMatrix_det_zero_of_root
#print axioms DominantFiveBody.fullAngularMatrix_pi_det
#print axioms DominantFiveBody.fullAngularMatrix_pi_determinant_limit
#print axioms DominantFiveBody.fullAngularMatrix_pi_entries
#print axioms DominantFiveBody.fullAngularMatrix_source_entries
#print axioms DominantFiveBody.full_angular_cut
#print axioms DominantFiveBody.full_angular_cut_limit_gap_le
#print axioms DominantFiveBody.hadamard_target_difference
#print axioms DominantFiveBody.inertia
#print axioms DominantFiveBody.inertiaTangentSpace
#print axioms DominantFiveBody.inertia_centeredFromRelative
#print axioms DominantFiveBody.kappaPrime_h_source
#print axioms DominantFiveBody.kernelF_angle_mul_tendsto_atTop
#print axioms DominantFiveBody.liftRelative
#print axioms DominantFiveBody.low_triple_scale_cases
#print axioms DominantFiveBody.lower_triple_scaled_positions_compact_subsequence
#print axioms DominantFiveBody.main_of_chart_facts
#print axioms DominantFiveBody.main_of_orderedSlice_uniform
#print axioms DominantFiveBody.main_uniform
#print axioms DominantFiveBody.main_uniform_unnormalized
#print axioms DominantFiveBody.masses
#print axioms DominantFiveBody.mem_branchEqualitySet
#print axioms DominantFiveBody.nestedAngularBoundaryMatrix_source
#print axioms DominantFiveBody.nestedAngularExterior_recovery
#print axioms DominantFiveBody.nestedAngularInnerDifference_at_boundary
#print axioms DominantFiveBody.nestedAngularMean_at_boundary
#print axioms DominantFiveBody.nestedAngularOuterDifference_at_boundary
#print axioms DominantFiveBody.nestedAngularRows_source_complete
#print axioms DominantFiveBody.nestedAreaAlongRoot_deriv_eq_partial
#print axioms DominantFiveBody.nestedAreaAlongZeroRoot_hasDerivAt
#print axioms DominantFiveBody.nestedBasePoint_formula_complete
#print axioms DominantFiveBody.nestedBasePoint_regular
#print axioms DominantFiveBody.nestedBoundaryDerivativeMatrix_det
#print axioms DominantFiveBody.nestedBoundaryDerivativeMatrix_triangular_diagonal
#print axioms DominantFiveBody.nestedBoundaryDisplacement_to_triple
#print axioms DominantFiveBody.nestedBoundaryKernel_fderiv_apply
#print axioms DominantFiveBody.nestedBoundaryKernel_original_derivatives
#print axioms DominantFiveBody.nestedBoundaryKernels_source_complete
#print axioms DominantFiveBody.nestedBoundaryScalarPositions_source_formula
#print axioms DominantFiveBody.nestedBoundaryScalarPositions_weighted_center
#print axioms DominantFiveBody.nestedChartExtendedRows_base_root
#print axioms DominantFiveBody.nestedChartExtendedRows_eq_physical
#print axioms DominantFiveBody.nestedChartExtendedRows_joint_analyticAt
#print axioms DominantFiveBody.nestedChartExtendedRows_joint_contDiffAt
#print axioms DominantFiveBody.nestedChartExtendedRows_zero_iff_normalized
#print axioms DominantFiveBody.nestedChartJacobian_boundary_alpha_independent
#print axioms DominantFiveBody.nestedChartJacobian_boundary_isInvertible
#print axioms DominantFiveBody.nestedChartJacobian_unit_radial
#print axioms DominantFiveBody.nestedChartJacobian_unit_radial_difference
#print axioms DominantFiveBody.nestedChartPhysicalRows_zero_iff
#print axioms DominantFiveBody.nestedChartPoint_cartesian_Osquare
#print axioms DominantFiveBody.nestedChart_all_ten_areas_uniform_product
#print axioms DominantFiveBody.nestedChart_compact_boundary_continuation
#print axioms DominantFiveBody.nestedChart_convex_physical_continuation
#print axioms DominantFiveBody.nestedChart_coordinates_complete
#print axioms DominantFiveBody.nestedChart_radial_uniform_epsilon_bound
#print axioms DominantFiveBody.nestedChart_reaction_Ocube
#print axioms DominantFiveBody.nestedChart_zero_eps_all_scale_faces
#print axioms DominantFiveBody.nestedChart_zero_face_area_zero_nonnegative_eta
#print axioms DominantFiveBody.nestedChart_zero_face_eq_slowPoint_of_local_uniqueness
#print axioms DominantFiveBody.nestedChart_zero_face_parallel_of_local_uniqueness
#print axioms DominantFiveBody.nestedCircle_coefficient_complete
#print axioms DominantFiveBody.nestedContinuationRoot_fixed_mass_endpoint
#print axioms DominantFiveBody.nestedEdge_signed_base_gap_pos
#print axioms DominantFiveBody.nestedExternalAreaQuotient_exterior_boundary
#print axioms DominantFiveBody.nestedExternalAreaQuotient_primary_boundary
#print axioms DominantFiveBody.nestedGaps_formula_complete
#print axioms DominantFiveBody.nestedInnerDirection_identity
#print axioms DominantFiveBody.nestedInnerJOverT_joint_contDiffAt
#print axioms DominantFiveBody.nestedInnerJ_factor
#print axioms DominantFiveBody.nestedInnerJ_formula_complete
#print axioms DominantFiveBody.nestedInnerM_at_boundary
#print axioms DominantFiveBody.nestedInnerM_formula
#print axioms DominantFiveBody.nestedInnerN_source_formula
#print axioms DominantFiveBody.nestedInnerO_source_formula
#print axioms DominantFiveBody.nestedInnerWSq_formula
#print axioms DominantFiveBody.nestedInner_distance
#print axioms DominantFiveBody.nestedInternalAreaQuotient_zero_formula
#print axioms DominantFiveBody.nestedInternalArea_factor_cubic_along_root
#print axioms DominantFiveBody.nestedInternalArea_factor_square
#print axioms DominantFiveBody.nestedMacroArea_unit_boundary
#print axioms DominantFiveBody.nestedOriginalScalarPath_endpoints
#print axioms DominantFiveBody.nestedOriginalScalarPath_positive_common_tube
#print axioms DominantFiveBody.nestedOuterDirection_identity
#print axioms DominantFiveBody.nestedOuterL_formula
#print axioms DominantFiveBody.nestedOuterL_original_integral
#print axioms DominantFiveBody.nestedOuterN_formula
#print axioms DominantFiveBody.nestedOuterN_original_integral
#print axioms DominantFiveBody.nestedOuterO_formula
#print axioms DominantFiveBody.nestedOuterWSq_formula
#print axioms DominantFiveBody.nestedOuter_distance
#print axioms DominantFiveBody.nestedRadialExterior_recovery
#print axioms DominantFiveBody.nestedRadialInnerDifference_at_boundary
#print axioms DominantFiveBody.nestedRadialMean_at_boundary
#print axioms DominantFiveBody.nestedRadialOuterDifference_at_boundary
#print axioms DominantFiveBody.nestedRadialRows_source_complete
#print axioms DominantFiveBody.nestedRows_formula_complete
#print axioms DominantFiveBody.nestedRows_recovery
#print axioms DominantFiveBody.nestedScalarAngularKernel_formula
#print axioms DominantFiveBody.nestedScalarAngularKernel_substitution
#print axioms DominantFiveBody.nestedScalarFields_at_actual_targets
#print axioms DominantFiveBody.nestedScalarH_source_formula
#print axioms DominantFiveBody.nestedScalarK_source_formula
#print axioms DominantFiveBody.nestedScalarPositions_formula_complete
#print axioms DominantFiveBody.nestedScalarRadialKernel_formula
#print axioms DominantFiveBody.nestedScalarRadialKernel_substitution
#print axioms DominantFiveBody.nestedSlowPoint_root
#print axioms DominantFiveBody.nestedSlowPoint_source_formula
#print axioms DominantFiveBody.nestedSlowRootCandidate_contDiffAt
#print axioms DominantFiveBody.nestedSlowRootCandidate_contDiffOn
#print axioms DominantFiveBody.nestedSourceCasePermutation_source
#print axioms DominantFiveBody.nestedSourceCaseTable_source
#print axioms DominantFiveBody.nestedSourceCase_order_is_original
#print axioms DominantFiveBody.nestedSource_common_balls_without_alpha_limit
#print axioms DominantFiveBody.nestedSource_individual_inverse_limits
#print axioms DominantFiveBody.nestedSource_radial_Oepsilon_from_original_bound
#print axioms DominantFiveBody.nestedStrictConvex_of_positive_areas
#print axioms DominantFiveBody.nestedToFixedSlice_full_abs_det
#print axioms DominantFiveBody.nestedToFixedSlice_full_det
#print axioms DominantFiveBody.nestedToFixedSlice_full_matrix
#print axioms DominantFiveBody.nestedUnitPoint_scalar_root
#print axioms DominantFiveBody.nested_cross_distance_diameter_ratios
#print axioms DominantFiveBody.nested_kernel_integral_shift
#print axioms DominantFiveBody.nested_precise_two_cube_limits_of_selected
#print axioms DominantFiveBody.newtonTargetDerivative_operator_norm_bound
#print axioms DominantFiveBody.newtonTargetField_affinePolar_Osquare
#print axioms DominantFiveBody.noCollision_actual_sequence_capture_of_regular_limit
#print axioms DominantFiveBody.noCollision_physical_local_continuation
#print axioms DominantFiveBody.no_coorbital_root_at_semicircle_boundary
#print axioms DominantFiveBody.no_full_angular_sequence_at_pi_by_determinant
#print axioms DominantFiveBody.no_full_angular_unit_root_at_pi
#print axioms DominantFiveBody.no_one_source_coorbital_root
#print axioms DominantFiveBody.no_primary_complete_collision
#print axioms DominantFiveBody.normalizedCC_of_reducedResidual_zero
#print axioms DominantFiveBody.normalized_centeredFromRelative_iff_vectorRoot
#print axioms DominantFiveBody.normalized_cluster_exterior_average
#print axioms DominantFiveBody.normalized_cluster_virial
#print axioms DominantFiveBody.normalized_cluster_virial_le
#print axioms DominantFiveBody.normalized_complete_lower_triple_full_rectangle_derivatives_uniform
#print axioms DominantFiveBody.normalized_complete_lower_triple_initial_scales
#print axioms DominantFiveBody.normalized_complete_lower_triple_mass_vanishes
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_directions
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_macro_mass_cube_limit
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_original_capture
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_precise_scales
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_radial_bound
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_radial_limits
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_rectangle_controls
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_rectangle_individual_limits
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_rectangle_near_display_bound
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_rectangle_near_display_rhs_vanishes
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_rectangle_near_geometry_uniform
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_scale_complete
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_segment_derivative_bound
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_segment_scaled_geometry_uniform
#print axioms DominantFiveBody.normalized_complete_lower_triple_original_angular_scaled_zero_cube_impossible
#print axioms DominantFiveBody.normalized_complete_lower_triple_original_group_geometry
#print axioms DominantFiveBody.normalized_complete_lower_triple_original_group_geometry_of_scaled_limits
#print axioms DominantFiveBody.normalized_complete_lower_triple_original_group_mass_lower
#print axioms DominantFiveBody.normalized_complete_lower_triple_original_group_zero_cube_impossible
#print axioms DominantFiveBody.normalized_complete_lower_triple_original_initial_estimates
#print axioms DominantFiveBody.normalized_complete_lower_triple_regular_actual_capture
#print axioms DominantFiveBody.normalized_complete_pair_actual_capture
#print axioms DominantFiveBody.normalized_complete_pair_actual_chart_limits
#print axioms DominantFiveBody.normalized_complete_pair_direction_alternative
#print axioms DominantFiveBody.normalized_complete_pair_left_outward_radial_impossible
#print axioms DominantFiveBody.normalized_complete_pair_mass_cube_limit
#print axioms DominantFiveBody.normalized_complete_pair_radial_bound_of_tangential
#print axioms DominantFiveBody.normalized_complete_pair_right_inward_radial_impossible
#print axioms DominantFiveBody.normalized_complete_pair_scale_complete
#print axioms DominantFiveBody.normalized_complete_pair_selected_tangential
#print axioms DominantFiveBody.normalized_complete_pair_tangential_difference_positive
#print axioms DominantFiveBody.normalized_complete_pair_tangential_mass_scale
#print axioms DominantFiveBody.normalized_complete_pairs_cannot_coexist
#print axioms DominantFiveBody.normalized_complete_triple_limiting_exterior
#print axioms DominantFiveBody.normalized_complete_upper_triple_initial_scales
#print axioms DominantFiveBody.normalized_complete_upper_triple_mass_vanishes
#print axioms DominantFiveBody.normalized_complete_upper_triple_nested_rectangle_controls
#print axioms DominantFiveBody.normalized_complete_upper_triple_nested_rectangle_individual_limits
#print axioms DominantFiveBody.normalized_complete_upper_triple_nested_rectangle_near_display_bound
#print axioms DominantFiveBody.normalized_complete_upper_triple_nested_rectangle_near_display_rhs_vanishes
#print axioms DominantFiveBody.normalized_complete_upper_triple_nested_rectangle_near_geometry_uniform
#print axioms DominantFiveBody.normalized_complete_upper_triple_nested_scale_complete
#print axioms DominantFiveBody.normalized_complete_upper_triple_nested_segment_scaled_geometry_uniform
#print axioms DominantFiveBody.normalized_complete_upper_triple_original_group_complete_geometry
#print axioms DominantFiveBody.normalized_complete_upper_triple_regular_actual_capture
#print axioms DominantFiveBody.normalized_nested_macro_average
#print axioms DominantFiveBody.normalized_nested_macro_mass_cube_limit_of_first_order_geometry
#print axioms DominantFiveBody.normalized_noCollision_ordered_capture
#print axioms DominantFiveBody.normalized_of_vectorResidual_zero
#print axioms DominantFiveBody.normalized_ordered_collision_classes_exhaustive
#print axioms DominantFiveBody.normalized_ordered_polar_limit_geometry
#print axioms DominantFiveBody.normalized_pairDistance_cube_le
#print axioms DominantFiveBody.normalized_pair_midpoint_identity
#print axioms DominantFiveBody.normalized_pair_vector_difference
#print axioms DominantFiveBody.normalized_polar_gauge_angular_rows
#print axioms DominantFiveBody.normalized_projection_gap_cube_le
#print axioms DominantFiveBody.normalized_strictConvex_ordered_angular_rep
#print axioms DominantFiveBody.orderedPolarSlice
#print axioms DominantFiveBody.orderedPolarSlice_angles
#print axioms DominantFiveBody.orderedPolarSlice_contDiff
#print axioms DominantFiveBody.orderedPolarSlice_nondegenerate_of_normalized
#print axioms DominantFiveBody.orderedPolarSlice_physical_eq_rotation
#print axioms DominantFiveBody.orderedPolarSlice_radii
#print axioms DominantFiveBody.orderedPolarSlice_reindex_undo
#print axioms DominantFiveBody.orderedPolarSlice_root_of_normalized
#print axioms DominantFiveBody.orderedSliceRoot
#print axioms DominantFiveBody.orderedSliceRoot_existsUnique_orientedSimilar
#print axioms DominantFiveBody.orderedSliceRoot_of_normalized_gauged
#print axioms DominantFiveBody.orderedSliceRoot_physical
#print axioms DominantFiveBody.orderedSliceRoot_unique_coordinates_of_normalized_gauged
#print axioms DominantFiveBody.orderedSlice_connection
#print axioms DominantFiveBody.orderedSlice_fixedParameterLocalExistence
#print axioms DominantFiveBody.orderedSlice_localContinuationUniqueness
#print axioms DominantFiveBody.orderedSlice_lower_nested_triple_capture
#print axioms DominantFiveBody.orderedSlice_nondegeneracy_to_geometric
#print axioms DominantFiveBody.orderedSlice_smooth_connection_explicit
#print axioms DominantFiveBody.orderedSlice_uniqueness_to_geometric
#print axioms DominantFiveBody.ordered_full_angular_limit_consecutive_gap_le
#print axioms DominantFiveBody.ordered_full_angular_limit_span_lt_pi
#print axioms DominantFiveBody.ordered_full_angular_limit_span_pos
#print axioms DominantFiveBody.ordered_slicePhysicalConfiguration_injective
#print axioms DominantFiveBody.orientedArea_cyclic
#print axioms DominantFiveBody.pairAngularDifference_at_boundary
#print axioms DominantFiveBody.pairAngularExterior_joint_contDiffAt
#print axioms DominantFiveBody.pairAngularMean_at_boundary
#print axioms DominantFiveBody.pairAreaQuotient_joint_contDiff
#print axioms DominantFiveBody.pairArea_factor
#print axioms DominantFiveBody.pairChartExtendedRows_eq_physical
#print axioms DominantFiveBody.pairChartExtendedRows_joint_analyticAt
#print axioms DominantFiveBody.pairChartExtendedRows_joint_contDiffAt
#print axioms DominantFiveBody.pairChartJacobian_boundary_isInvertible
#print axioms DominantFiveBody.pairChartJacobian_exterior_source_a0
#print axioms DominantFiveBody.pairChartJacobian_unit_difference
#print axioms DominantFiveBody.pairChartJacobian_unit_exterior
#print axioms DominantFiveBody.pairChartJacobian_unit_mean
#print axioms DominantFiveBody.pairChartJacobian_unit_radial
#print axioms DominantFiveBody.pairChartJacobian_unit_radial_difference
#print axioms DominantFiveBody.pairChartPhysicalRows_zero_iff
#print axioms DominantFiveBody.pairChartRows_half_interval_choice
#print axioms DominantFiveBody.pairChartWSq_formula_complete
#print axioms DominantFiveBody.pairChart_boundary_radial
#print axioms DominantFiveBody.pairChart_compact_boundary_continuation
#print axioms DominantFiveBody.pairChart_compact_physical_continuation
#print axioms DominantFiveBody.pairChart_coordinates_complete
#print axioms DominantFiveBody.pairChart_distance_sq
#print axioms DominantFiveBody.pairChart_omitted_mass_lower_fixed_anchor
#print axioms DominantFiveBody.pairChart_zero_eps_all_scale_faces
#print axioms DominantFiveBody.pairCoordinateMatrix_det
#print axioms DominantFiveBody.pairDistance
#print axioms DominantFiveBody.pairExteriorAngular_source_derivatives
#print axioms DominantFiveBody.pairExteriorField_fderiv_norm_bound
#print axioms DominantFiveBody.pairExteriorField_fderiv_norm_bound_two_sources
#print axioms DominantFiveBody.pairExteriorField_hasFDerivAt
#print axioms DominantFiveBody.pairExteriorField_joint_contDiffAt
#print axioms DominantFiveBody.pairExteriorFields_source_formulas
#print axioms DominantFiveBody.pairExterior_joint_neighborhood_derivative_bounds
#print axioms DominantFiveBody.pairExterior_moving_neighborhood_derivative_bounds
#print axioms DominantFiveBody.pairInternal_weighted_radial_source
#print axioms DominantFiveBody.pairRadialDifference_at_boundary
#print axioms DominantFiveBody.pairRadialExterior_joint_contDiffAt
#print axioms DominantFiveBody.pairRadialMean_at_boundary
#print axioms DominantFiveBody.pairRadial_root_compact_uniform_bound
#print axioms DominantFiveBody.pairRadial_root_exact_factor
#print axioms DominantFiveBody.pairRows_recovery
#print axioms DominantFiveBody.pairSourceA0_abs_lower
#print axioms DominantFiveBody.pair_areas_boundary_complete
#print axioms DominantFiveBody.pair_tangential_coefficient_lower
#print axioms DominantFiveBody.pairs
#print axioms DominantFiveBody.physicalHessian_radial_of_normalizedCC
#print axioms DominantFiveBody.physicalPairExteriorAngularAngularDerivative_eq_selected
#print axioms DominantFiveBody.physicalPairExteriorAngularRadialDerivative_eq_selected
#print axioms DominantFiveBody.physicalSourceAngularField_joint_contDiffAt
#print axioms DominantFiveBody.physicalSourceAngularRadialDerivative_near_display_bound
#print axioms DominantFiveBody.physicalSourceFullAngularField_hasDerivAt_angle
#print axioms DominantFiveBody.physicalSourceFullAngularField_hasDerivAt_radius
#print axioms DominantFiveBody.physicalSourceFullAngularField_left_difference_control
#print axioms DominantFiveBody.physicalSourceFullAngularField_moving_secant_limit
#print axioms DominantFiveBody.physicalSourceFullAngularField_near_scaled_limit
#print axioms DominantFiveBody.physical_current_group_full_angular_average
#print axioms DominantFiveBody.physical_current_group_projection_average
#print axioms DominantFiveBody.physical_nested_group_radial_projections_tendsto
#print axioms DominantFiveBody.physical_nested_macro_average
#print axioms DominantFiveBody.physical_nested_pair_exterior_secant_limit
#print axioms DominantFiveBody.physical_nested_pair_mass_cube_limit_of_tangential
#print axioms DominantFiveBody.physical_nested_pair_selected_tangential
#print axioms DominantFiveBody.physical_nested_pair_unselected_precise_scales
#print axioms DominantFiveBody.physical_nested_polar_rectangle_derivatives_individually_uniform
#print axioms DominantFiveBody.physical_pair_direction_alternative_of_exterior_vanishes
#print axioms DominantFiveBody.physical_pair_direction_polar_ratio_limits
#print axioms DominantFiveBody.physical_pair_left_endpoint_difference_control
#print axioms DominantFiveBody.physical_pair_left_endpoint_rectangular_controls
#print axioms DominantFiveBody.physical_pair_radial_bound_of_exterior_secant_limit
#print axioms DominantFiveBody.physical_pair_radial_subsequence_source_package
#print axioms DominantFiveBody.physical_pair_right_endpoint_difference_control
#print axioms DominantFiveBody.physical_pair_segment_near_distance_uniform
#print axioms DominantFiveBody.physical_pair_segment_scaled_displacement_uniform
#print axioms DominantFiveBody.physical_pair_weighted_full_angular_average
#print axioms DominantFiveBody.physical_triple_equal_scaled_groups_primary_projection_limit
#print axioms DominantFiveBody.physical_triple_equal_scaled_groups_primary_vector_limit
#print axioms DominantFiveBody.physical_triple_extreme_angular_identity
#print axioms DominantFiveBody.physical_triple_extreme_mass_width_bound
#print axioms DominantFiveBody.physical_triple_extreme_source_signs
#print axioms DominantFiveBody.physical_triple_original_angular_groups_zero_cube_impossible
#print axioms DominantFiveBody.physical_triple_scaled_groups_radial_projection_limit
#print axioms DominantFiveBody.physical_triple_weighted_full_angular_average
#print axioms DominantFiveBody.physical_two_current_groups_projection_difference
#print axioms DominantFiveBody.polarAction_fderiv_apply
#print axioms DominantFiveBody.polarDividedEdgeIntegral_factor
#print axioms DominantFiveBody.polarDividedEdgeIntegral_zero
#print axioms DominantFiveBody.polarPoint
#print axioms DominantFiveBody.polarSatellites
#print axioms DominantFiveBody.polar_distance_sq
#print axioms DominantFiveBody.polar_scaled_distance_square
#print axioms DominantFiveBody.polar_scaled_radius_difference_tendsto_zero
#print axioms DominantFiveBody.polar_support_radial_drop_le
#print axioms DominantFiveBody.polar_support_radial_expansion_exact
#print axioms DominantFiveBody.polar_support_radial_expansion_remainder_bound
#print axioms DominantFiveBody.positive_two_scale_fraction_identity
#print axioms DominantFiveBody.potential
#print axioms DominantFiveBody.primary_cluster_cube_lower
#print axioms DominantFiveBody.primary_cluster_inertia_upper
#print axioms DominantFiveBody.primary_cluster_potential_lower
#print axioms DominantFiveBody.quarterTurn
#print axioms DominantFiveBody.radialResidual
#print axioms DominantFiveBody.reducedAngularJacobian_zero_eq
#print axioms DominantFiveBody.reducedAngularJacobian_zero_full_matrix
#print axioms DominantFiveBody.reducedAngularJacobian_zero_isInvertible
#print axioms DominantFiveBody.reducedJacobian_at_closed_separated_root_isInvertible
#print axioms DominantFiveBody.reducedJacobian_at_coorbital_root_isInvertible
#print axioms DominantFiveBody.reducedJacobian_zero_radial_block
#print axioms DominantFiveBody.reducedPolarResiduals_zero_iff_vectorRoot
#print axioms DominantFiveBody.regularTripleBoundaryM_source_formula
#print axioms DominantFiveBody.regularTripleScalarH_source_formula
#print axioms DominantFiveBody.relativeAction
#print axioms DominantFiveBody.relativeActionVectorGradient_eq_CF
#print axioms DominantFiveBody.relativeAction_critical_iff_vectorRoot
#print axioms DominantFiveBody.relativeAction_eq_augmentedPotential_div
#print axioms DominantFiveBody.relativeAverage
#print axioms DominantFiveBody.relativeCenteredEquiv
#print axioms DominantFiveBody.relativeField
#print axioms DominantFiveBody.relativeField_eq_scaledAverage_of_vectorRoot
#print axioms DominantFiveBody.relativeMassMatrix_posDef
#print axioms DominantFiveBody.rotationSliceHessian_nondegenerate_iff_shape
#print axioms DominantFiveBody.satelliteGroupNearProjection_abs_bound
#print axioms DominantFiveBody.satellitePairs
#print axioms DominantFiveBody.satellite_complete_cluster_limit_unit
#print axioms DominantFiveBody.satellite_group_internal_projection_zero
#print axioms DominantFiveBody.satellitesRelative
#print axioms DominantFiveBody.scalarSlow_positive_seed
#print axioms DominantFiveBody.scalarSlow_source_equations
#print axioms DominantFiveBody.sectionThree_solution_field_and_tangential_identity
#print axioms DominantFiveBody.shapeSpace
#print axioms DominantFiveBody.signedProbe_hasDerivAt
#print axioms DominantFiveBody.signedProbe_inner_deriv_neg
#print axioms DominantFiveBody.signedProbe_reflection
#print axioms DominantFiveBody.sinc_source_extension
#print axioms DominantFiveBody.singleScaleAngularTerm_contDiffAt
#print axioms DominantFiveBody.singleScaleAngularTerm_eq_physical
#print axioms DominantFiveBody.singleScaleChi_complete
#print axioms DominantFiveBody.singleScaleRadialTerm_contDiffAt
#print axioms DominantFiveBody.singleScaleRadialTerm_eq_physical
#print axioms DominantFiveBody.singleScaleWSq_formula_complete
#print axioms DominantFiveBody.singleScaleWeightedRadialPair_pair_sum
#print axioms DominantFiveBody.singleScale_distance
#print axioms DominantFiveBody.singleScale_distance_sq
#print axioms DominantFiveBody.singleScale_internal_weighted_angular_sum
#print axioms DominantFiveBody.singleScale_pair_weighted_radial_sum
#print axioms DominantFiveBody.singleScale_three_weighted_radial_sum
#print axioms DominantFiveBody.sliceAction_second_fderiv
#print axioms DominantFiveBody.sliceAction_second_fderiv_isInvertible_iff_reducedJacobian
#print axioms DominantFiveBody.sliceAngles
#print axioms DominantFiveBody.sliceMassWeights_pos
#print axioms DominantFiveBody.slicePhysicalConfiguration
#print axioms DominantFiveBody.sliceRadii
#print axioms DominantFiveBody.sliceWeightedMetric_apply
#print axioms DominantFiveBody.source_angle_domain
#print axioms DominantFiveBody.source_integral_comparisons
#print axioms DominantFiveBody.source_masses
#print axioms DominantFiveBody.source_scalar_derivatives
#print axioms DominantFiveBody.strictConvexCC_existsUnique_normalized_gauged
#print axioms DominantFiveBody.strictConvexInOrder_exists_ordered_polar
#print axioms DominantFiveBody.strictConvex_primaryRelative_all_edges
#print axioms DominantFiveBody.tangentialResidual
#print axioms DominantFiveBody.tangentialResidual_zero_of_normalized
#print axioms DominantFiveBody.three_radii_spread_le_width
#print axioms DominantFiveBody.three_source_probe_remainder_lower_bound
#print axioms DominantFiveBody.three_source_support_kernel
#print axioms DominantFiveBody.tripleAngularCoefficient_lower
#print axioms DominantFiveBody.tripleAngularDifference_boundary_eq_LM
#print axioms DominantFiveBody.tripleAngularDifference_unit_scalar
#print axioms DominantFiveBody.tripleAngularExteriorDifference_background
#print axioms DominantFiveBody.tripleAngularExterior_joint_contDiffAt
#print axioms DominantFiveBody.tripleAngularMean_background_zero
#print axioms DominantFiveBody.tripleAngularMean_boundary_source_H
#print axioms DominantFiveBody.tripleAreaAlongRoot_deriv_eq_partial
#print axioms DominantFiveBody.tripleAreaAlongZeroRoot_hasDerivAt
#print axioms DominantFiveBody.tripleBoundaryDisplacement_angular
#print axioms DominantFiveBody.tripleBoundaryDisplacement_radial
#print axioms DominantFiveBody.tripleChartExtendedRows_eq_physical
#print axioms DominantFiveBody.tripleChartExtendedRows_joint_analyticAt
#print axioms DominantFiveBody.tripleChartExtendedRows_joint_contDiffAt
#print axioms DominantFiveBody.tripleChartExtendedRows_unit_root
#print axioms DominantFiveBody.tripleChartExtendedRows_zero_iff_normalized
#print axioms DominantFiveBody.tripleChartJacobian_unit_difference
#print axioms DominantFiveBody.tripleChartJacobian_unit_mean
#print axioms DominantFiveBody.tripleChartJacobian_unit_radial
#print axioms DominantFiveBody.tripleChartJacobian_unit_radial_difference
#print axioms DominantFiveBody.tripleChartPoint_cartesian_Osquare
#print axioms DominantFiveBody.tripleChart_boundary_continuation_of_scalar_root
#print axioms DominantFiveBody.tripleChart_boundary_radial
#print axioms DominantFiveBody.tripleChart_convex_physical_continuation
#print axioms DominantFiveBody.tripleChart_coordinates_complete
#print axioms DominantFiveBody.tripleChart_exteriorMass_Ocube
#print axioms DominantFiveBody.tripleChart_internal_area_positive_neighborhood
#print axioms DominantFiveBody.tripleChart_radial_uniform_epsilon_bound
#print axioms DominantFiveBody.tripleChart_reaction_Ocube
#print axioms DominantFiveBody.tripleChart_relativeAverage_Ocube
#print axioms DominantFiveBody.tripleChart_relativeAverage_cubic_identity
#print axioms DominantFiveBody.tripleChart_strictConvex_neighborhood
#print axioms DominantFiveBody.tripleChart_zero_eps_all_scale_faces
#print axioms DominantFiveBody.tripleChart_zero_face_area_zero_of_local_uniqueness
#print axioms DominantFiveBody.tripleChart_zero_face_eq_slowPoint_of_local_uniqueness
#print axioms DominantFiveBody.tripleChart_zero_face_parallel_of_local_uniqueness
#print axioms DominantFiveBody.tripleCircleAreaCoefficient_zero
#print axioms DominantFiveBody.tripleCircleAreaCoefficient_zero_pos
#print axioms DominantFiveBody.tripleExteriorJ_source_formula
#print axioms DominantFiveBody.tripleExteriorRadialRow_background_zero
#print axioms DominantFiveBody.tripleExternalAreaQuotient_exterior_boundary
#print axioms DominantFiveBody.tripleExternalAreaQuotient_primary_boundary
#print axioms DominantFiveBody.tripleIntegratedJacobian_entries
#print axioms DominantFiveBody.tripleIntegratedJacobian_lower_norm_bound
#print axioms DominantFiveBody.tripleInternalAngularReduced_vector_projection
#print axioms DominantFiveBody.tripleInternalAngular_eq_physical
#print axioms DominantFiveBody.tripleInternalAngular_source_formula
#print axioms DominantFiveBody.tripleInternalArea_factor_cubic_along_root
#print axioms DominantFiveBody.tripleInternalCartesian_Osquare
#print axioms DominantFiveBody.tripleInternalCartesian_scaling
#print axioms DominantFiveBody.tripleInternalRadialReduced_vector_projection
#print axioms DominantFiveBody.tripleInternalRadial_eq_physical
#print axioms DominantFiveBody.tripleInternalRadial_source_formula
#print axioms DominantFiveBody.tripleInternalVectorQuotient_Olinear
#print axioms DominantFiveBody.tripleInternalVectorQuotient_contDiffAt
#print axioms DominantFiveBody.tripleInternalVectorQuotient_zero
#print axioms DominantFiveBody.tripleInternal_weighted_angular_zero
#print axioms DominantFiveBody.tripleInternal_weighted_radial_upper_sum
#print axioms DominantFiveBody.tripleOrderedSegment_ordered
#print axioms DominantFiveBody.triplePhysical_capture_of_regular_scaled_limits
#print axioms DominantFiveBody.triplePointDirection_identity
#print axioms DominantFiveBody.triplePointDirection_joint_contDiff
#print axioms DominantFiveBody.triplePointDirection_original_integral_all_scales
#print axioms DominantFiveBody.triplePointDirection_source_at_zero
#print axioms DominantFiveBody.tripleRadialDifference_at_boundary
#print axioms DominantFiveBody.tripleRadialExteriorDifference_background
#print axioms DominantFiveBody.tripleRadialExterior_joint_contDiffAt
#print axioms DominantFiveBody.tripleRadialMean_at_boundary
#print axioms DominantFiveBody.tripleRadialMean_background_zero
#print axioms DominantFiveBody.tripleReducedDifferential_matrix
#print axioms DominantFiveBody.tripleReducedJacobian_det_ne_zero
#print axioms DominantFiveBody.tripleReducedJacobian_formula_complete
#print axioms DominantFiveBody.tripleRows_recovery
#print axioms DominantFiveBody.tripleRows_zero_iff
#print axioms DominantFiveBody.tripleScalarJacobian_lower_norm_bound
#print axioms DominantFiveBody.tripleScalarJacobian_strict_row_dominance
#print axioms DominantFiveBody.tripleScalarPotential_critical_iff_root
#print axioms DominantFiveBody.tripleScalarPotential_divided_gradient
#print axioms DominantFiveBody.tripleScalarPotential_exists_minimizer
#print axioms DominantFiveBody.tripleScalarPotential_isProperMap
#print axioms DominantFiveBody.tripleScalarPotential_source_formula
#print axioms DominantFiveBody.tripleScalarPotential_strictConvexOn
#print axioms DominantFiveBody.tripleScalarResidual_hasFDerivAt
#print axioms DominantFiveBody.tripleScalarResidual_ordered_segment_integral
#print axioms DominantFiveBody.tripleScalar_J_entries_complete
#print axioms DominantFiveBody.tripleScalar_centered_gap_root_recovery
#print axioms DominantFiveBody.tripleScalar_matrices_complete
#print axioms DominantFiveBody.tripleScalar_potential_root_existsUnique_centered
#print axioms DominantFiveBody.tripleScalar_root_unique_by_integratedJacobian
#print axioms DominantFiveBody.tripleScalar_root_weighted_center
#print axioms DominantFiveBody.tripleScalar_seed_of_regular_scaled_limits
#print axioms DominantFiveBody.tripleSlowPoint_root
#print axioms DominantFiveBody.tripleSlowPoint_source_formula
#print axioms DominantFiveBody.tripleSlowPoint_vector_balance
#print axioms DominantFiveBody.triple_mass_cube_upper_of_extreme_rows
#print axioms DominantFiveBody.triple_minimum_pair_subsequence
#print axioms DominantFiveBody.twoSourceFunction_endpoint
#print axioms DominantFiveBody.twoSourceFunction_root_strict_secant
#print axioms DominantFiveBody.twoSourceFunction_second_deriv_pos
#print axioms DominantFiveBody.twoSourcePolarAngular_fderiv_apply
#print axioms DominantFiveBody.twoSourcePolarAngular_source_formula
#print axioms DominantFiveBody.twoSourceProbe
#print axioms DominantFiveBody.two_source_probe_diagonal_pos
#print axioms DominantFiveBody.two_source_separation
#print axioms DominantFiveBody.uniform_existence_of_connection
#print axioms DominantFiveBody.uniform_nondegeneracy_of_connection
#print axioms DominantFiveBody.uniform_uniqueness_of_connection
#print axioms DominantFiveBody.unit_satellites_strictConvex_iff_open_semicircle
#print axioms DominantFiveBody.v1CorrectedVectorResidual
#print axioms DominantFiveBody.v1FieldDefect
#print axioms DominantFiveBody.v1FieldDefect_Ocube_of_fixed_exterior
#print axioms DominantFiveBody.v1FieldDefect_cubic_factor
#print axioms DominantFiveBody.v1_angularResidual_corrected_projection_div
#print axioms DominantFiveBody.v1_epsilon_angularResidual_corrected_projection
#print axioms DominantFiveBody.v1_nestedChartPoints_fixed_exterior
#print axioms DominantFiveBody.v1_nestedChart_fieldDefect_Ocube
#print axioms DominantFiveBody.v1_nestedChart_fieldDefect_cubic_factor
#print axioms DominantFiveBody.v1_nestedSlowPoint_fieldDefect_Ocube
#print axioms DominantFiveBody.v1_radialResidual_corrected_projection
#print axioms DominantFiveBody.v1_tripleChartPoints_fixed_exterior
#print axioms DominantFiveBody.v1_tripleChart_fieldDefect_Ocube
#print axioms DominantFiveBody.v1_tripleChart_fieldDefect_cubic_factor
#print axioms DominantFiveBody.v1_tripleSlowPoint_fieldDefect_Ocube
#print axioms DominantFiveBody.vectorResidual
#print axioms DominantFiveBody.vectorResidual_tangential
#print axioms DominantFiveBody.weightedPosition
#print axioms DominantFiveBody.weighted_angularResidual_zero
