import DominantFiveBody.TripleScalarSeed
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! The original positive-weight scalar potential of Section 5.3.
Its absolute-distance terms are the three unordered source pairs. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody

def tripleScalarPotential (alpha z : TripleVector) : ℝ :=
  tripleD0/2*(∑ i,alpha i*z i^2)+
    (alpha 0*alpha 1/|z 0-z 1|+alpha 0*alpha 2/|z 0-z 2|+
      alpha 1*alpha 2/|z 1-z 2|)

def tripleScalarChamber : Set TripleVector := {z | TripleOrdered z}

def tripleScalarPairs : Finset (TripleLabel × TripleLabel) := Finset.univ.filter (fun p => p.1<p.2)

theorem tripleScalarPotential_source_formula (alpha z : TripleVector) :
    tripleScalarPotential alpha z=tripleD0/2*(∑ i,alpha i*z i^2)+
      ∑ p ∈ tripleScalarPairs,alpha p.1*alpha p.2/|z p.1-z p.2| := by
  simp [tripleScalarPotential,tripleScalarPairs,Finset.sum_filter,Fintype.sum_prod_type,Fin.sum_univ_three]

theorem tripleOrdered_iff_adjacent (z : TripleVector) :
    TripleOrdered z ↔ z 0<z 1 ∧ z 1<z 2 := by
  constructor
  · intro hz
    exact ⟨hz 0 1 (by decide),hz 1 2 (by decide)⟩
  · rintro ⟨h01,h12⟩
    have h02 := h01.trans h12
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem tripleScalarChamber_isOpen : IsOpen tripleScalarChamber := by
  have h0 : IsOpen {z : TripleVector | z 0<z 1} :=
    isOpen_lt (continuous_apply 0) (continuous_apply 1)
  have h1 : IsOpen {z : TripleVector | z 1<z 2} :=
    isOpen_lt (continuous_apply 1) (continuous_apply 2)
  convert h0.inter h1 using 1
  ext z
  exact tripleOrdered_iff_adjacent z

theorem tripleScalarChamber_convex : Convex ℝ tripleScalarChamber := by
  intro x hx y hy a b ha hb hab i j hij
  have hxij : 0<x j-x i := sub_pos.mpr (hx i j hij)
  have hyij : 0<y j-y i := sub_pos.mpr (hy i j hij)
  change a*x i+b*y i<a*x j+b*y j
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    simpa only [ha0,hb1,zero_mul,one_mul,zero_add] using hy i j hij
  · have hpos : 0<a*(x j-x i)+b*(y j-y i) :=
      add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hxij)
        (mul_nonneg hb hyij.le)
    nlinarith

theorem tripleScalarPotential_ordered_formula (alpha z : TripleVector) (hz : TripleOrdered z) :
    tripleScalarPotential alpha z=tripleD0/2*(∑ i,alpha i*z i^2)+
      (alpha 0*alpha 1/(z 1-z 0)+alpha 0*alpha 2/(z 2-z 0)+
        alpha 1*alpha 2/(z 2-z 1)) := by
  unfold tripleScalarPotential
  rw [abs_sub_comm (z 0) (z 1),abs_sub_comm (z 0) (z 2),abs_sub_comm (z 1) (z 2),
    abs_of_pos (sub_pos.mpr (hz 0 1 (by decide))),
    abs_of_pos (sub_pos.mpr (hz 0 2 (by decide))),
    abs_of_pos (sub_pos.mpr (hz 1 2 (by decide)))]

theorem tripleScalarPotential_nonneg (alpha z : TripleVector) (ha : ∀ i,0≤alpha i) :
    0≤tripleScalarPotential alpha z := by
  unfold tripleScalarPotential
  have hsum : 0≤∑ i,alpha i*z i^2 := Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (sq_nonneg _))
  have hD := tripleD0_pos
  exact add_nonneg (mul_nonneg (div_nonneg hD.le (by norm_num)) hsum)
    (add_nonneg (add_nonneg (div_nonneg (mul_nonneg (ha 0) (ha 1)) (abs_nonneg _))
      (div_nonneg (mul_nonneg (ha 0) (ha 2)) (abs_nonneg _)))
      (div_nonneg (mul_nonneg (ha 1) (ha 2)) (abs_nonneg _)))

end DominantFiveBody
