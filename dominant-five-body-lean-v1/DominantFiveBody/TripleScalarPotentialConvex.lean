import DominantFiveBody.TripleScalarPotential
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-! The original strict-convexity proof: a positive quadratic term and
three convex inverse positive gaps on the actual ordered chamber. -/
noncomputable section
open scoped BigOperators
open Set
namespace DominantFiveBody

def tripleQuadraticPotential (alpha z : TripleVector) : ℝ :=
  tripleD0/2*(∑ i,alpha i*z i^2)

theorem tripleQuadraticPotential_strictJensen (alpha x y : TripleVector)
    (ha : ∀ i,0<alpha i) (hxy : x≠y) (a b : ℝ)
    (ha0 : 0<a) (hb0 : 0<b) (hab : a+b=1) :
    tripleQuadraticPotential alpha (a • x+b • y)<
      a*tripleQuadraticPotential alpha x+b*tripleQuadraticPotential alpha y := by
  obtain ⟨i,hi⟩ : ∃ i,x i≠y i := by
    by_contra hn
    apply hxy
    funext i
    exact Classical.byContradiction (fun hi => hn ⟨i,hi⟩)
  have hS : 0<∑ j,alpha j*(x j-y j)^2 :=
    Finset.sum_pos' (fun j _ => mul_nonneg (ha j).le (sq_nonneg _))
      ⟨i,Finset.mem_univ i,mul_pos (ha i) (sq_pos_of_ne_zero (sub_ne_zero.mpr hi))⟩
  have hb : b=1-a := by linarith
  have he : a*tripleQuadraticPotential alpha x+b*tripleQuadraticPotential alpha y-
      tripleQuadraticPotential alpha (a • x+b • y)=
      (tripleD0/2)*a*b*(∑ j,alpha j*(x j-y j)^2) := by
    simp only [tripleQuadraticPotential,Fin.sum_univ_three,Pi.add_apply,Pi.smul_apply,
      smul_eq_mul,hb]
    ring
  have hp : 0<(tripleD0/2)*a*b*(∑ j,alpha j*(x j-y j)^2) :=
    mul_pos (mul_pos (mul_pos (div_pos tripleD0_pos (by norm_num)) ha0) hb0) hS
  linarith

theorem inverse_positive_gap_convex (x y a b : ℝ) (hx : 0<x) (hy : 0<y)
    (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    (a*x+b*y)⁻¹≤a*x⁻¹+b*y⁻¹ := by
  have hc : ConvexOn ℝ (Ioi (0 : ℝ)) (fun t : ℝ => t⁻¹) := by
    simpa only [zpow_neg_one] using
      (strictConvexOn_zpow (m := (-1 : ℤ)) (by norm_num) (by norm_num)).convexOn
  simpa only [smul_eq_mul] using hc.2 hx hy ha hb hab

theorem tripleScalarPotential_strictConvexOn (alpha : TripleVector)
    (ha : ∀ i,0<alpha i) : StrictConvexOn ℝ tripleScalarChamber (tripleScalarPotential alpha) := by
  refine ⟨tripleScalarChamber_convex,?_⟩
  intro x hx y hy hxy a b ha0 hb0 hab
  have hmix : TripleOrdered (a • x+b • y) :=
    tripleScalarChamber_convex hx hy ha0.le hb0.le hab
  have hQ := tripleQuadraticPotential_strictJensen alpha x y ha hxy a b ha0 hb0 hab
  have hpair (i j : TripleLabel) (hij : i<j) :
      alpha i*alpha j/((a • x+b • y) j-(a • x+b • y) i)≤
        a*(alpha i*alpha j/(x j-x i))+b*(alpha i*alpha j/(y j-y i)) := by
    have hc := inverse_positive_gap_convex (x j-x i) (y j-y i) a b
      (sub_pos.mpr (hx i j hij)) (sub_pos.mpr (hy i j hij)) ha0.le hb0.le hab
    have hm := mul_le_mul_of_nonneg_left hc (mul_nonneg (ha i).le (ha j).le)
    have he : (a • x+b • y) j-(a • x+b • y) i=a*(x j-x i)+b*(y j-y i) := by
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [he]
    simp only [div_eq_mul_inv] at *
    nlinarith
  rw [tripleScalarPotential_ordered_formula alpha _ hmix,
    tripleScalarPotential_ordered_formula alpha x hx,tripleScalarPotential_ordered_formula alpha y hy]
  change tripleQuadraticPotential alpha (a • x+b • y)+_ <
    a*(tripleQuadraticPotential alpha x+_)+b*(tripleQuadraticPotential alpha y+_)
  linarith [hpair 0 1 (by decide),hpair 0 2 (by decide),hpair 1 2 (by decide)]

end DominantFiveBody
