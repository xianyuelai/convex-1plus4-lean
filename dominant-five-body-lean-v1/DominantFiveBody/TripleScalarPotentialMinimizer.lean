import DominantFiveBody.TripleScalarPotentialProper
import DominantFiveBody.TripleScalarPotentialGradient
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap

/-! The original scalar-potential route to existence and uniqueness:
properness gives a minimizer; the true derivative gives its equations;
strict convexity gives uniqueness of the resulting ordered root. -/
noncomputable section
open scoped BigOperators
open Set Filter Topology
namespace DominantFiveBody

theorem tripleScalarPotential_exists_minimizer (alpha : TripleVector)
    (ha : ∀ i,0<alpha i) :
    ∃ z : TripleVector,TripleOrdered z ∧ IsMinOn (tripleScalarPotential alpha) tripleScalarChamber z := by
  let z0 : TripleVector := ![-1,0,1]
  have hz0 : TripleOrdered z0 := (tripleOrdered_iff_adjacent z0).mpr
    ⟨by change (-1 : ℝ)<0; norm_num,by change (0 : ℝ)<1; norm_num⟩
  let S : Set TripleVector := {z | TripleOrdered z ∧
    tripleScalarPotential alpha z≤tripleScalarPotential alpha z0}
  have hcompact : IsCompact S := tripleScalarPotential_compact_sublevel alpha ha _
  have hnonempty : S.Nonempty := ⟨z0,hz0,le_rfl⟩
  have hcontinuous : ContinuousOn (tripleScalarPotential alpha) S :=
    fun z hz => (tripleScalarPotential_continuousAt alpha z hz.1).continuousWithinAt
  obtain ⟨z,hz,hmin⟩ := hcompact.exists_isMinOn hnonempty hcontinuous
  refine ⟨z,hz.1,?_⟩
  intro y hy
  by_cases hv : tripleScalarPotential alpha y≤tripleScalarPotential alpha z0
  · exact hmin ⟨hy,hv⟩
  · exact hz.2.trans (le_of_lt (lt_of_not_ge hv))

theorem tripleScalarPotential_critical_isMinOn (alpha z : TripleVector)
    (ha : ∀ i,0<alpha i) (hz : TripleOrdered z)
    (hcritical : fderiv ℝ (tripleScalarPotential alpha) z=0) :
    IsMinOn (tripleScalarPotential alpha) tripleScalarChamber z := by
  intro y hy
  let L : ℝ →ᵃ[ℝ] TripleVector := AffineMap.lineMap z y
  have hconv := ((tripleScalarPotential_strictConvexOn alpha ha).convexOn.comp_affineMap L).subset
    (tripleScalarChamber_convex.mapsTo_lineMap hz hy) (convex_Icc (0 : ℝ) 1)
  have hd0 : HasFDerivAt (tripleScalarPotential alpha) (0 : TripleVector →L[ℝ] ℝ) z := by
    simpa only [hcritical] using (tripleScalarPotential_hasFDerivAt alpha z hz).differentiableAt.hasFDerivAt
  have hd : HasDerivAt ((tripleScalarPotential alpha) ∘ L) 0 0 := by
    have hbase : HasFDerivAt (tripleScalarPotential alpha) (0 : TripleVector →L[ℝ] ℝ) (L 0) := by
      simpa only [L,AffineMap.lineMap_apply_zero] using hd0
    simpa only [zero_apply] using hbase.comp_hasDerivAt 0
      (AffineMap.hasDerivAt_lineMap (a := z) (b := y) (x := (0 : ℝ)))
  have hs := hconv.le_slope_of_hasDerivAt (x := (0 : ℝ)) (y := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hd
  have hvalue : 0≤tripleScalarPotential alpha y-tripleScalarPotential alpha z := by
    simpa [slope,L] using hs
  exact sub_nonneg.mp hvalue

theorem tripleScalar_potential_root_existsUnique (alpha : TripleVector)
    (ha : ∀ i,0<alpha i) :
    ∃! z : TripleVector,TripleOrdered z ∧ ∀ i,tripleScalarResidual alpha z i=0 := by
  obtain ⟨z,hz,hmin⟩ := tripleScalarPotential_exists_minimizer alpha ha
  have hcritical : fderiv ℝ (tripleScalarPotential alpha) z=0 :=
    (hmin.isLocalMin (tripleScalarChamber_isOpen.mem_nhds hz)).fderiv_eq_zero
  have hroot := (tripleScalarPotential_critical_iff_root alpha z ha hz).mp hcritical
  refine ⟨z,⟨hz,hroot⟩,?_⟩
  intro y hy
  have hminy := tripleScalarPotential_critical_isMinOn alpha y ha hy.1
    ((tripleScalarPotential_critical_iff_root alpha y ha hy.1).mpr hy.2)
  exact (tripleScalarPotential_strictConvexOn alpha ha).eq_of_isMinOn hminy hmin hy.1 hz

theorem tripleScalar_potential_root_existsUnique_centered (alpha : TripleVector)
    (ha : ∀ i,0<alpha i) :
    ∃! z : TripleVector,TripleOrdered z ∧ (∀ i,tripleScalarResidual alpha z i=0) ∧
      ∑ i,alpha i*z i=0 := by
  obtain ⟨z,hz,hunique⟩ := tripleScalar_potential_root_existsUnique alpha ha
  refine ⟨z,⟨hz.1,hz.2,tripleScalar_root_weighted_center alpha z hz.2⟩,?_⟩
  intro y hy
  exact hunique y ⟨hy.1,hy.2.1⟩

end DominantFiveBody
