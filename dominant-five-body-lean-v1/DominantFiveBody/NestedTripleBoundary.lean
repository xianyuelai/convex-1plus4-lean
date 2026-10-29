import DominantFiveBody.NestedTripleCoordinates

/-! # The actual nested and regular boundary systems agree

The equality is first proved on physical positive scales, then passed to
zero scale using the established joint smooth extensions. Positive eta
is fixed during this argument; individual mass fractions may be zero.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1000000

theorem nestedToTriple_extendedRows_at_zero (eps eta alpha : ℝ) (y : NestedChartVariables)
    (he : 0<eta) (hreg : NestedChartRegular eps 0 eta alpha y) :
    tripleChartExtendedRows eps 0 (nestedTripleWeights eta alpha) (nestedToTripleVariables eta alpha y)=
      nestedToTripleVariables eta alpha (nestedChartExtendedRows eps 0 eta alpha y) := by
  let a := nestedTripleWeights eta alpha
  let z := nestedToTripleVariables eta alpha y
  let pn (s : ℝ) : NestedJointVariables := ((![eps,s,eta,alpha] : Fin 4 → ℝ),y)
  let pt (s : ℝ) : TripleJointVariables := ((![eps,s,a 0,a 1,a 2] : Fin 5 → ℝ),z)
  have hpa (s : ℝ) : tripleJointAlpha (pt s).1=a := by ext i; fin_cases i <;> rfl
  have hcn : Continuous pn := by unfold pn; fun_prop
  have hct : Continuous pt := by unfold pt; fun_prop
  have htr := nestedToTriple_regular_zero eps eta alpha y he.ne' hreg
  have hnr : ∀ᶠ s in 𝓝 (0 : ℝ),NestedChartRegular eps s eta alpha y :=
    hcn.continuousAt.eventually (nestedChartRegular_isOpen.mem_nhds hreg)
  have htrp : TripleChartRegular ((pt 0).1 0) ((pt 0).1 1) (tripleJointAlpha (pt 0).1) (pt 0).2 := by
    simpa only [hpa,pt,Matrix.cons_val_zero,Matrix.cons_val_one] using htr
  have htrnear : ∀ᶠ s in 𝓝 (0 : ℝ),TripleChartRegular eps s a z := by
    have hh := hct.continuousAt.eventually (tripleChartRegular_isOpen.mem_nhds htrp)
    simpa only [hpa,pt,Matrix.cons_val_zero,Matrix.cons_val_one] using hh
  have htcont : ContinuousAt (fun s : ℝ => tripleChartExtendedRows eps s a z) 0 := by
    have hh := (tripleChartExtendedRows_joint_contDiffAt 0 (pt 0) htrp).continuousAt.comp hct.continuousAt
    simpa only [Function.comp_def,hpa,pt,Matrix.cons_val_zero,Matrix.cons_val_one] using hh
  have hncont : ContinuousAt (fun s : ℝ => nestedChartExtendedRows eps s eta alpha y) 0 := by
    exact (nestedChartExtendedRows_joint_contDiffAt 0 (pn 0) hreg).continuousAt.comp hcn.continuousAt
  have hmap := (nestedToTripleVariables_contDiff 0 eta alpha).continuous.continuousAt.comp hncont
  have heq : (fun s : ℝ => tripleChartExtendedRows eps s a z) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun s => nestedToTripleVariables eta alpha (nestedChartExtendedRows eps s eta alpha y)) := by
    have hnr' : ∀ᶠ s in 𝓝[>] (0 : ℝ),NestedChartRegular eps s eta alpha y :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hnr
    have htr' : ∀ᶠ s in 𝓝[>] (0 : ℝ),TripleChartRegular eps s a z :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds htrnear
    filter_upwards [hnr',htr',self_mem_nhdsWithin] with s hn ht hs
    have hspos : 0<s := hs
    rw [tripleChartExtendedRows_eq_physical eps s a z hspos ht.1 ht.2.2.1
      (fun i => ht.2.1 i.castSucc) ht.2.2.2]
    rw [nestedChartExtendedRows_eq_physical eps s eta alpha y hspos he hn.1 hn.2.1
      hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2]
    exact nestedToTriple_physicalRows eps s eta alpha y hspos.ne' he.ne'
  exact tendsto_nhds_unique (htcont.mono_left nhdsWithin_le_nhds)
    ((hmap.mono_left nhdsWithin_le_nhds).congr' heq.symm)

theorem nestedToTriple_boundary_root_iff (eps eta alpha : ℝ) (y : NestedChartVariables)
    (he : 0<eta) (hreg : NestedChartRegular eps 0 eta alpha y) :
    nestedChartExtendedRows eps 0 eta alpha y=0 ↔
      tripleChartExtendedRows eps 0 (nestedTripleWeights eta alpha)
        (nestedToTripleVariables eta alpha y)=0 := by
  rw [nestedToTriple_extendedRows_at_zero eps eta alpha y he hreg]
  constructor
  · intro hh
    rw [hh,nestedToTripleVariables_zero]
  · intro hh
    apply nestedToTripleVariables_injective eta alpha he.ne'
    simpa only [nestedToTripleVariables_zero] using hh

end DominantFiveBody
