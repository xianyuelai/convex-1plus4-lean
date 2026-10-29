import DominantFiveBody.TripleBoundary
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Original line-segment construction of the regular chart's divided
edges, separately from the earlier closed sinc formula. -/
noncomputable section
namespace DominantFiveBody
set_option maxHeartbeats 800000

def polarDividedEdgeIntegral (rho v t a b : ℝ) : Plane :=
  ∫ s in (0 : ℝ)..1,
    polarPointDerivative (rho + s * (t * a), v + s * (t * b)) (a, b)

theorem polarDividedEdgeIntegral_factor (rho v t a b : ℝ) :
    polarPoint (rho + t * a) (v + t * b) - polarPoint rho v =
      t • polarDividedEdgeIntegral rho v t a b := by
  let path : ℝ → ℝ × ℝ := fun s => (rho + s * (t * a), v + s * (t * b))
  let f : ℝ → Plane := fun s => polarPoint (path s).1 (path s).2
  let g : ℝ → Plane := fun s => polarPointDerivative (path s) (a, b)
  have hpath : Continuous path := by fun_prop
  have hc : Continuous g := by
    unfold g polarPointDerivative
    change Continuous (fun s => a • polarPoint 1 (path s).2 +
      b • quarterTurn (polarPoint (path s).1 (path s).2))
    exact ((continuous_const : Continuous (fun _ : ℝ => a)).smul ((polarPoint_contDiff 0).continuous.comp
      (continuous_const.prodMk hpath.snd))).add
      ((continuous_const : Continuous (fun _ : ℝ => b)).smul (quarterTurnLinear.toContinuousLinearMap.continuous.comp
        ((polarPoint_contDiff 0).continuous.comp hpath)))
  have hd (s : ℝ) : HasDerivAt f (t • g s) s := by
    have hp : HasDerivAt path (t * a, t * b) s := by
      have hp1 : HasDerivAt (fun r : ℝ => rho + r * (t * a)) (t * a) s := by
        simpa using ((hasDerivAt_id s).mul_const (t * a)).const_add rho
      have hp2 : HasDerivAt (fun r : ℝ => v + r * (t * b)) (t * b) s := by
        simpa using ((hasDerivAt_id s).mul_const (t * b)).const_add v
      exact HasDerivAt.prodMk hp1 hp2
    have he := (polarPoint_hasFDerivAt (path s)).comp_hasDerivAt s hp
    convert! he using 1
    change t • polarPointDerivative (path s) (a, b) =
      polarPointDerivative (path s) (t * a, t * b)
    rw [polarPointDerivative_apply, polarPointDerivative_apply]
    module
  have hcg : Continuous (fun s : ℝ => t • g s) :=
    (continuous_const : Continuous (fun _ : ℝ => t)).smul hc
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) (hcg.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_smul] at hFTC
  simpa [f, path, g, polarDividedEdgeIntegral] using hFTC.symm

theorem polarDividedEdgeIntegral_zero (rho v a b : ℝ) :
    polarDividedEdgeIntegral rho v 0 a b = polarPointDerivative (rho, v) (a, b) := by
  simp [polarDividedEdgeIntegral]

theorem triplePointDirection_original_integral (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i j : TripleLabel) (ht : t ≠ 0) :
    triplePointDirection t alpha y i j =
      polarDividedEdgeIntegral
        (tripleChartRadii t alpha y i.castSucc) (tripleChartAngles t alpha y i.castSucc) t
        (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i)
        (tripleChartAngularPositions alpha y j - tripleChartAngularPositions alpha y i) := by
  have hr : tripleChartRadii t alpha y j.castSucc = tripleChartRadii t alpha y i.castSucc +
      t * (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i) := by
    fin_cases i <;> fin_cases j <;> simp [tripleChartRadii, tripleChartRadialPositions] <;> ring
  have hv : tripleChartAngles t alpha y j.castSucc = tripleChartAngles t alpha y i.castSucc +
      t * (tripleChartAngularPositions alpha y j - tripleChartAngularPositions alpha y i) := by
    fin_cases i <;> fin_cases j <;> simp [tripleChartAngles, tripleChartAngularPositions] <;> ring
  have hintegral := polarDividedEdgeIntegral_factor
    (tripleChartRadii t alpha y i.castSucc) (tripleChartAngles t alpha y i.castSucc) t
    (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i)
    (tripleChartAngularPositions alpha y j - tripleChartAngularPositions alpha y i)
  rw [← hr, ← hv] at hintegral
  have hid := triplePointDirection_identity t alpha y i j
  have he : t • triplePointDirection t alpha y i j = t • polarDividedEdgeIntegral
      (tripleChartRadii t alpha y i.castSucc) (tripleChartAngles t alpha y i.castSucc) t
      (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i)
      (tripleChartAngularPositions alpha y j - tripleChartAngularPositions alpha y i) :=
    hid.symm.trans hintegral
  have hinv := congrArg (fun p : Plane => t⁻¹ • p) he
  simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using hinv

theorem triplePointDirection_original_integral_all_scales (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i j : TripleLabel) :
    triplePointDirection t alpha y i j =
      polarDividedEdgeIntegral
        (tripleChartRadii t alpha y i.castSucc) (tripleChartAngles t alpha y i.castSucc) t
        (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i)
        (tripleChartAngularPositions alpha y j - tripleChartAngularPositions alpha y i) := by
  by_cases ht : t = 0
  · subst t
    rw [polarDividedEdgeIntegral_zero, triplePointDirection_at_zero]
    fin_cases i <;> simp [tripleChartRadii, tripleChartAngles]
  · exact triplePointDirection_original_integral t alpha y i j ht

theorem triplePointDirection_source_at_zero (alpha : TripleVector)
    (y : TripleChartVariables) (i j : TripleLabel) :
    triplePointDirection 0 alpha y i j =
      (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i) •
        polarPoint 1 (y 4) +
      (y 1 * (tripleChartAngularPositions alpha y j - tripleChartAngularPositions alpha y i)) •
        quarterTurn (polarPoint 1 (y 4)) := by
  rw [triplePointDirection_at_zero, polarPointDerivative_apply, polarPoint_rotation_smul,
    smul_smul]
  module

end DominantFiveBody
