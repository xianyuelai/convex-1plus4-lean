import DominantFiveBody.TripleConvexContinuation
import DominantFiveBody.NestedContinuation

/-! Literal nonzero physical angular gaps at the fixed-mass zero endpoints
in Proposition 7.1. The separated-angle hypotheses are supplied by the
actual endpoint recovery theorems, including all four original labels. -/
noncomputable section
open scoped BigOperators
namespace DominantFiveBody

theorem separated_angle_gap_ne_zero (theta : Satellite → ℝ)
    (hsep : SeparatedSemicircle theta) (i j : Satellite) (hij : i ≠ j) :
    theta j-theta i≠0 := sub_ne_zero.mpr (hsep i j hij).1.symm

theorem pairChart_endpoint_gap_nonzero (t alpha : ℝ) (y : PairChartVariables)
    (hsep : SeparatedSemicircle (pairChartAngles t alpha y)) :
    pairChartAngles t alpha y 1-pairChartAngles t alpha y 0=t*y 6 ∧ t*y 6≠0 := by
  have he : pairChartAngles t alpha y 1-pairChartAngles t alpha y 0=t*y 6 := by
    simp only [pairChartAngles,Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  exact ⟨he,he ▸ separated_angle_gap_ne_zero _ hsep 0 1 (by decide)⟩

theorem tripleChart_endpoint_gaps_nonzero (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ha : ∑ i,alpha i=1)
    (hsep : SeparatedSemicircle (tripleChartAngles t alpha y)) :
    ∀ k : Fin 2,
      tripleChartAngles t alpha y k.succ.castSucc-
        tripleChartAngles t alpha y k.castSucc.castSucc=t*tripleChartAngularGaps y k ∧
      t*tripleChartAngularGaps y k≠0 := by
  intro k
  have he : tripleChartAngles t alpha y k.succ.castSucc-
      tripleChartAngles t alpha y k.castSucc.castSucc=t*tripleChartAngularGaps y k := by
    fin_cases k
    · change (y 4+t*tripleChartAngularPositions alpha y 1)-
        (y 4+t*tripleChartAngularPositions alpha y 0)=t*tripleChartAngularGaps y 0
      have hh := tripleAngularPositions_gap alpha y ha (0 : Fin 2)
      change tripleChartAngularPositions alpha y 1-tripleChartAngularPositions alpha y 0=
        tripleChartAngularGaps y 0 at hh
      calc
        _=t*(tripleChartAngularPositions alpha y 1-tripleChartAngularPositions alpha y 0) := by ring
        _=t*tripleChartAngularGaps y 0 := congrArg (fun a : ℝ => t*a) hh
    · change (y 4+t*tripleChartAngularPositions alpha y 2)-
        (y 4+t*tripleChartAngularPositions alpha y 1)=t*tripleChartAngularGaps y 1
      have hh := tripleAngularPositions_gap alpha y ha (1 : Fin 2)
      change tripleChartAngularPositions alpha y 2-tripleChartAngularPositions alpha y 1=
        tripleChartAngularGaps y 1 at hh
      calc
        _=t*(tripleChartAngularPositions alpha y 2-tripleChartAngularPositions alpha y 1) := by ring
        _=t*tripleChartAngularGaps y 1 := congrArg (fun a : ℝ => t*a) hh
  refine ⟨he,he ▸ separated_angle_gap_ne_zero _ hsep _ _ ?_⟩
  fin_cases k <;> decide

theorem nestedChart_endpoint_gaps_nonzero (t eta alpha : ℝ) (y : NestedChartVariables)
    (hsep : SeparatedSemicircle (nestedChartAngles t eta alpha y)) :
    nestedChartAngles t eta alpha y 1-nestedChartAngles t eta alpha y 0=t*eta*y 6 ∧
      t*eta*y 6≠0 ∧
      (∀ i : Fin 2,nestedChartAngles t eta alpha y 2-
        nestedChartAngles t eta alpha y (i.castAdd 2)=t*nestedOuterAngularGaps eta alpha y i ∧
        t*nestedOuterAngularGaps eta alpha y i≠0) := by
  have hi : nestedChartAngles t eta alpha y 1-nestedChartAngles t eta alpha y 0=t*eta*y 6 := by
    simp only [nestedChartAngles,nestedCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  refine ⟨hi,hi ▸ separated_angle_gap_ne_zero _ hsep 0 1 (by decide),?_⟩
  intro i
  have he := (nestedOuter_gaps t eta alpha y i).2
  refine ⟨he,he ▸ separated_angle_gap_ne_zero _ hsep _ _ ?_⟩
  fin_cases i <;> decide

end DominantFiveBody
