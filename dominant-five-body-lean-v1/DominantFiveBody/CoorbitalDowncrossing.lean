import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Filter Set Topology

namespace DominantFiveBody

theorem negative_derivative_zero_right {f : ℝ → ℝ} {x b d : ℝ}
    (hd : HasDerivAt f d x) (hdneg : d < 0) (hx : f x = 0) (hxb : x < b) :
    ∃ y, y ∈ Ioo x b ∧ f y < 0 := by
  have hs : ∀ᶠ y in 𝓝[>] x, slope f x y < 0 :=
    (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)).eventually (Iio_mem_nhds hdneg)
  have hb : ∀ᶠ y in 𝓝[>] x, y < b :=
    (show ∀ᶠ y in 𝓝 x, y < b from Iio_mem_nhds hxb).filter_mono nhdsWithin_le_nhds
  have hxnear : ∀ᶠ y in 𝓝[>] x, x < y := self_mem_nhdsWithin
  obtain ⟨y, hy⟩ := (hs.and (hxnear.and hb)).exists
  refine ⟨y, ⟨hy.2.1, hy.2.2⟩, ?_⟩
  rw [slope_def_field, hx, sub_zero] at hy
  simpa using (div_lt_iff₀ (sub_pos.mpr hy.2.1)).mp hy.1

theorem negative_derivative_zero_left {f : ℝ → ℝ} {a x d : ℝ}
    (hd : HasDerivAt f d x) (hdneg : d < 0) (hx : f x = 0) (hax : a < x) :
    ∃ y, y ∈ Ioo a x ∧ 0 < f y := by
  have hs : ∀ᶠ y in 𝓝[<] x, slope f x y < 0 :=
    (hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE x)).eventually (Iio_mem_nhds hdneg)
  have ha : ∀ᶠ y in 𝓝[<] x, a < y :=
    (show ∀ᶠ y in 𝓝 x, a < y from Ioi_mem_nhds hax).filter_mono nhdsWithin_le_nhds
  have hxnear : ∀ᶠ y in 𝓝[<] x, y < x := self_mem_nhdsWithin
  obtain ⟨y, hy⟩ := (hs.and (ha.and hxnear)).exists
  refine ⟨y, ⟨hy.2.1, hy.2.2⟩, ?_⟩
  rw [slope_def_field, hx, sub_zero] at hy
  simpa using (div_lt_iff_of_neg (sub_neg.mpr hy.2.2)).mp hy.1

/-- A continuous scalar function whose every zero is a strict downcrossing
has at most one zero on an interval. No sign of its derivative away from
the zero set is required. -/
theorem downcrossing_zero_unique {f : ℝ → ℝ} {l r : ℝ}
    (hc : ContinuousOn f (Ioo l r))
    (hd : ∀ x ∈ Ioo l r, f x = 0 → ∃ d < 0, HasDerivAt f d x)
    {a b : ℝ} (ha : a ∈ Ioo l r) (hb : b ∈ Ioo l r)
    (hfa : f a = 0) (hfb : f b = 0) : a = b := by
  suffices hnot : ∀ a ∈ Ioo l r, ∀ b ∈ Ioo l r, f a = 0 → f b = 0 → ¬a < b by
    exact le_antisymm (le_of_not_gt (hnot b hb a ha hfb hfa))
      (le_of_not_gt (hnot a ha b hb hfa hfb))
  intro a ha b hb hfa hfb hab
  obtain ⟨da, hda, hda'⟩ := hd a ha hfa
  obtain ⟨c, hcinterval, hfc⟩ := negative_derivative_zero_right hda' hda hfa hab
  have hcb : c ≤ b := hcinterval.2.le
  have hsub : Icc c b ⊆ Ioo l r := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_trans ha.1 hcinterval.1) hx.1,
      lt_of_le_of_lt hx.2 hb.2⟩
  have hcont : ContinuousOn f (Icc c b) := hc.mono hsub
  let Z : Set ℝ := Icc c b ∩ f ⁻¹' {0}
  have hZclosed : IsClosed Z := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZcompact : IsCompact Z := isCompact_Icc.of_isClosed_subset hZclosed inter_subset_left
  have hZnonempty : Z.Nonempty := ⟨b, ⟨⟨hcb, le_rfl⟩, hfb⟩⟩
  obtain ⟨z, hz, hzleast⟩ := hZcompact.exists_isLeast hZnonempty
  have hcz : c < z := lt_of_le_of_ne hz.1.1 (by
    intro heq
    have : f c = 0 := heq ▸ hz.2
    linarith)
  obtain ⟨dz, hdz, hdz'⟩ := hd z (hsub hz.1) hz.2
  obtain ⟨y, hy, hfy⟩ := negative_derivative_zero_left hdz' hdz hz.2 hcz
  have hcy : c ≤ y := hy.1.le
  have hcont' : ContinuousOn f (Icc c y) := hcont.mono (by
    intro x hx; exact ⟨hx.1, le_trans hx.2 (le_trans hy.2.le hz.1.2)⟩)
  obtain ⟨w, hw, hfw⟩ := intermediate_value_Icc hcy hcont' ⟨hfc.le, hfy.le⟩
  have hwZ : w ∈ Z := ⟨⟨hw.1, le_trans hw.2 (le_trans hy.2.le hz.1.2)⟩, hfw⟩
  have hzw : z ≤ w := hzleast hwZ
  linarith [hw.2, hy.2]

end DominantFiveBody
