import DominantFiveBody.TripleScalarPotentialConvex
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! Actual properness of the original scalar potential: every sublevel
is compact inside the open ordered chamber, bounded both at infinity
and away from every original pair collision. -/
noncomputable section
open scoped BigOperators
open Set Filter Topology
namespace DominantFiveBody

theorem tripleScalarPotential_continuousAt (alpha z : TripleVector)
    (hz : TripleOrdered z) : ContinuousAt (tripleScalarPotential alpha) z := by
  have hpair (i j : TripleLabel) (hij : i<j) :
      ContinuousAt (fun w : TripleVector => alpha i*alpha j/|w i-w j|) z :=
    continuousAt_const.div (((continuous_apply i).continuousAt.sub
      (continuous_apply j).continuousAt).abs) (abs_ne_zero.mpr (ne_of_lt (sub_neg.mpr (hz i j hij))))
  have hQ : ContinuousAt (fun w : TripleVector => tripleD0/2*(∑ i,alpha i*w i^2)) z := by
    simp only [Fin.sum_univ_three]
    fun_prop
  exact hQ.add (((hpair 0 1 (by decide)).add (hpair 0 2 (by decide))).add (hpair 1 2 (by decide)))

theorem tripleScalarPotential_quadratic_term_le (alpha z : TripleVector)
    (ha : ∀ i,0≤alpha i) (i : TripleLabel) :
    tripleD0/2*(alpha i*z i^2)≤tripleScalarPotential alpha z := by
  have hsum : alpha i*z i^2≤∑ j,alpha j*z j^2 :=
    Finset.single_le_sum (fun j _ => mul_nonneg (ha j) (sq_nonneg _)) (Finset.mem_univ i)
  have hQ : tripleD0/2*(alpha i*z i^2)≤tripleD0/2*(∑ j,alpha j*z j^2) :=
    mul_le_mul_of_nonneg_left hsum (div_nonneg tripleD0_pos.le (by norm_num))
  have h01 : 0≤alpha 0*alpha 1/|z 0-z 1| := div_nonneg (mul_nonneg (ha 0) (ha 1)) (abs_nonneg _)
  have h02 : 0≤alpha 0*alpha 2/|z 0-z 2| := div_nonneg (mul_nonneg (ha 0) (ha 2)) (abs_nonneg _)
  have h12 : 0≤alpha 1*alpha 2/|z 1-z 2| := div_nonneg (mul_nonneg (ha 1) (ha 2)) (abs_nonneg _)
  unfold tripleScalarPotential
  linarith

theorem tripleScalarPotential_pair_term_le (alpha z : TripleVector)
    (ha : ∀ i,0≤alpha i) (i j : TripleLabel) (hij : i<j) :
    alpha i*alpha j/|z i-z j|≤tripleScalarPotential alpha z := by
  have hQ : 0≤tripleD0/2*(∑ j,alpha j*z j^2) :=
    mul_nonneg (div_nonneg tripleD0_pos.le (by norm_num))
      (Finset.sum_nonneg (fun j _ => mul_nonneg (ha j) (sq_nonneg _)))
  have h01 : 0≤alpha 0*alpha 1/|z 0-z 1| := div_nonneg (mul_nonneg (ha 0) (ha 1)) (abs_nonneg _)
  have h02 : 0≤alpha 0*alpha 2/|z 0-z 2| := div_nonneg (mul_nonneg (ha 0) (ha 2)) (abs_nonneg _)
  have h12 : 0≤alpha 1*alpha 2/|z 1-z 2| := div_nonneg (mul_nonneg (ha 1) (ha 2)) (abs_nonneg _)
  have h01le : alpha 0*alpha 1/|z 0-z 1|≤tripleScalarPotential alpha z := by unfold tripleScalarPotential; linarith
  have h02le : alpha 0*alpha 2/|z 0-z 2|≤tripleScalarPotential alpha z := by unfold tripleScalarPotential; linarith
  have h12le : alpha 1*alpha 2/|z 1-z 2|≤tripleScalarPotential alpha z := by unfold tripleScalarPotential; linarith
  fin_cases i <;> fin_cases j
  all_goals first | exact h01le | exact h02le | exact h12le | exact (not_lt_of_ge (by decide) hij).elim

theorem tripleScalarPotential_sublevel_coordinate_bounds (alpha z : TripleVector)
    (ha : ∀ i,0<alpha i) (C : ℝ) (hC : 0<C)
    (hlevel : tripleScalarPotential alpha z≤C) :
    ∀ i,|z i|≤1+2*C/(tripleD0*alpha i) := by
  intro i
  have hterm := (tripleScalarPotential_quadratic_term_le alpha z (fun j => (ha j).le) i).trans hlevel
  have hden : 0<tripleD0*alpha i := mul_pos tripleD0_pos (ha i)
  have hsq : z i^2≤2*C/(tripleD0*alpha i) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  have hB : 0≤2*C/(tripleD0*alpha i) := div_nonneg (by positivity) hden.le
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (z i-1),sq_nonneg (z i+1)]

theorem tripleScalarPotential_sublevel_gap_bounds (alpha z : TripleVector)
    (ha : ∀ i,0<alpha i) (hz : TripleOrdered z) (C : ℝ) (hC : 0<C)
    (hlevel : tripleScalarPotential alpha z≤C) :
    ∀ i j,i<j → alpha i*alpha j/C≤z j-z i := by
  intro i j hij
  have hterm := (tripleScalarPotential_pair_term_le alpha z (fun k => (ha k).le) i j hij).trans hlevel
  rw [abs_sub_comm (z i) (z j),abs_of_pos (sub_pos.mpr (hz i j hij))] at hterm
  exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using (div_le_iff₀ (sub_pos.mpr (hz i j hij))).mp hterm)

def tripleScalarSeparationSet (alpha : TripleVector) (C : ℝ) : Set TripleVector :=
  {z | ∀ i j,i<j → alpha i*alpha j/C≤z j-z i}

theorem tripleScalarSeparationSet_isClosed (alpha : TripleVector) (C : ℝ) :
    IsClosed (tripleScalarSeparationSet alpha C) := by
  simp only [tripleScalarSeparationSet,Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const
    ((continuous_apply j : Continuous (fun z : TripleVector => z j)).sub (continuous_apply i))

theorem tripleScalarSeparationSet_subset_chamber (alpha : TripleVector)
    (ha : ∀ i,0<alpha i) (C : ℝ) (hC : 0<C) :
    tripleScalarSeparationSet alpha C⊆tripleScalarChamber := by
  intro z hz i j hij
  exact sub_pos.mp ((div_pos (mul_pos (ha i) (ha j)) hC).trans_le (hz i j hij))

theorem tripleScalarPotential_compact_sublevel (alpha : TripleVector)
    (ha : ∀ i,0<alpha i) (c : ℝ) :
    IsCompact {z : TripleVector | TripleOrdered z ∧ tripleScalarPotential alpha z≤c} := by
  let C := max c 1
  have hC : 0<C := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) (le_max_right _ _)
  have hcC : c≤C := le_max_left _ _
  let S : Set TripleVector := {z | TripleOrdered z ∧ tripleScalarPotential alpha z≤c}
  let K := tripleScalarSeparationSet alpha C
  have hSK : S⊆K := by
    intro z hz
    exact tripleScalarPotential_sublevel_gap_bounds alpha z ha hz.1 C hC (hz.2.trans hcC)
  have hKch : K⊆tripleScalarChamber := tripleScalarSeparationSet_subset_chamber alpha ha C hC
  have hcont : ContinuousOn (tripleScalarPotential alpha) K :=
    fun z hz => (tripleScalarPotential_continuousAt alpha z (hKch hz)).continuousWithinAt
  have hclosed : IsClosed S := by
    have he : S=K∩(tripleScalarPotential alpha) ⁻¹' Iic c := by
      ext z
      exact ⟨fun hz => ⟨hSK hz,hz.2⟩,fun hz => ⟨hKch hz.1,hz.2⟩⟩
    rw [he]
    exact hcont.preimage_isClosed_of_isClosed (tripleScalarSeparationSet_isClosed alpha C) isClosed_Iic
  have hbox : IsCompact (Set.univ.pi (fun i : TripleLabel =>
      Icc (-(1+2*C/(tripleD0*alpha i))) (1+2*C/(tripleD0*alpha i)))) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset hclosed
  intro z hz i _
  exact abs_le.mp (tripleScalarPotential_sublevel_coordinate_bounds alpha z ha C hC (hz.2.trans hcC) i)

theorem tripleScalarPotential_isProperMap (alpha : TripleVector)
    (ha : ∀ i,0<alpha i) :
    IsProperMap (fun z : {z : TripleVector // TripleOrdered z} => tripleScalarPotential alpha z.val) := by
  let f := fun z : {z : TripleVector // TripleOrdered z} => tripleScalarPotential alpha z.val
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (tripleScalarPotential_continuousAt alpha z.val z.property).comp
      continuous_subtype_val.continuousAt
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hf,?_⟩
  intro K hK
  obtain ⟨c,hc⟩ := hK.bddAbove
  have hsublevel : IsCompact {z : {z : TripleVector // TripleOrdered z} | f z≤c} := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    convert tripleScalarPotential_compact_sublevel alpha ha c using 1
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.property,hw⟩
    · rintro ⟨hz,hv⟩
      exact ⟨⟨z,hz⟩,hv,rfl⟩
  exact hsublevel.of_isClosed_subset (hK.isClosed.preimage hf)
    (fun z hz => hc hz)

end DominantFiveBody
