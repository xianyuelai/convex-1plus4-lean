import DominantFiveBody.CompactContinuation

/-!
# The manuscript's compact implicit function lemma

This module is independent of the equations of any collision chart.
`F` is an actual smooth map on an open domain, not an assumed solution
oracle. Finite-dimensional square derivatives are actual Fréchet
derivatives. The proof supplies the common products, root radius, inverse
bound and smooth gluing required in Lemma 3.2.
-/

noncomputable section
open scoped ContDiff
open Filter Set Topology

namespace DominantFiveBody.CompactImplicit

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] {n : ℕ}

abbrev Unknown (n : ℕ) := Fin n → ℝ

def jacobian (F : P → Unknown n → Unknown n) (p : P) (y : Unknown n) :
    Unknown n →L[ℝ] Unknown n := fderiv ℝ (F p) y

omit [CompleteSpace P] in
theorem jacobian_eq_partial (F : P → Unknown n → Unknown n) (p : P) (y : Unknown n)
    (hf : ContDiffAt ℝ 1 (Function.uncurry F) (p, y)) :
    jacobian F p y = (fderiv ℝ (Function.uncurry F) (p, y)).comp
      (ContinuousLinearMap.inr ℝ P (Unknown n)) := by
  have hd := hf.differentiableAt (by norm_num)
  have hh : HasFDerivAt (fun z : Unknown n => (p, z))
      (ContinuousLinearMap.inr ℝ P (Unknown n)) y := by
    convert! (hasFDerivAt_const p y).prodMk (hasFDerivAt_id y) using 1
  exact (hd.hasFDerivAt.comp y hh).fderiv

omit [CompleteSpace P] in
theorem jacobian_joint_continuousAt (F : P → Unknown n → Unknown n) (p : P)
    (y : Unknown n) (hf : ContDiffAt ℝ 1 (Function.uncurry F) (p, y)) :
    ContinuousAt (fun a : P × Unknown n => jacobian F a.1 a.2) (p, y) := by
  let f : (P × Unknown n) → Unknown n → Unknown n := fun z v => F z.1 v
  have hp : ContDiff ℝ 1 (fun z : (P × Unknown n) × Unknown n => (z.1.1, z.2)) := by
    fun_prop
  have h : ContDiffAt ℝ 1 (Function.uncurry f) ((p, y), y) := by
    convert! hf.comp ((p, y), y) hp.contDiffAt using 1
  exact (h.fderiv (contDiffAt_snd : ContDiffAt ℝ 0
    (fun z : P × Unknown n => z.2) (p, y)) (by norm_num)).continuousAt

theorem local_implicitFunction (F : P → Unknown n → Unknown n) (p : P) (y : Unknown n)
    (hf : ContDiffAt ℝ ∞ (Function.uncurry F) (p, y)) (hroot : F p y = 0)
    (hJ : (jacobian F p y).IsInvertible) :
    ∃ ψ : P → Unknown n, ψ p = y ∧ ContDiffAt ℝ ∞ ψ p ∧
      (∀ᶠ q in 𝓝 p, F q (ψ q) = 0) ∧
      (∀ᶠ a : P × Unknown n in 𝓝 (p, y), F a.1 a.2 = 0 ↔ ψ a.1 = a.2) := by
  have hpartial : (fderiv ℝ (Function.uncurry F) (p, y) ∘L
      ContinuousLinearMap.inr ℝ P (Unknown n)).IsInvertible := by
    rwa [← jacobian_eq_partial F p y (hf.of_le (by norm_num))]
  let ψ := hf.implicitFunction (by simp) hpartial
  refine ⟨ψ, hf.implicitFunction_apply_self (by simp) hpartial,
    hf.contDiffAt_implicitFunction (by simp) hpartial, ?_, ?_⟩
  · simpa only [Function.uncurry, hroot] using hf.eventually_apply_implicitFunction (by simp) hpartial
  · simpa only [Function.uncurry, hroot] using hf.eventually_apply_eq_iff_implicitFunction (by simp) hpartial

theorem local_rectangle (F : P → Unknown n → Unknown n) (p : P) (y : Unknown n)
    (hf : ContDiffAt ℝ ∞ (Function.uncurry F) (p, y)) (hroot : F p y = 0)
    (hJ : (jacobian F p y).IsInvertible) :
    ∃ ψ : P → Unknown n, ∃ η ζ : ℝ, 0 < η ∧ 0 < ζ ∧ ψ p = y ∧
      ContDiffAt ℝ ∞ ψ p ∧ ∀ q, dist q p < η →
        dist (ψ q) y < ζ ∧ F q (ψ q) = 0 ∧
        (∀ z, dist z y < ζ → (F q z = 0 ↔ ψ q = z)) := by
  obtain ⟨ψ, hbase, hsmooth, hroots, huniq⟩ := local_implicitFunction F p y hf hroot hJ
  obtain ⟨a, ha, hrootNear⟩ := Metric.eventually_nhds_iff.mp hroots
  obtain ⟨b, hb, huniqNear⟩ := Metric.eventually_nhds_iff.mp huniq
  have hψnear : ∀ᶠ q in 𝓝 p, dist (ψ q) y < b := by
    have h := hsmooth.continuousAt.tendsto.eventually (Metric.ball_mem_nhds (ψ p) hb)
    simpa only [Metric.mem_ball, hbase] using h
  obtain ⟨c, hc, hψNear⟩ := Metric.eventually_nhds_iff.mp hψnear
  refine ⟨ψ, min a (min b c), b, lt_min ha (lt_min hb hc), hb, hbase, hsmooth, ?_⟩
  intro q hq
  refine ⟨hψNear (lt_of_lt_of_le hq ((min_le_right _ _).trans (min_le_right _ _))),
    hrootNear (lt_of_lt_of_le hq (min_le_left _ _)), ?_⟩
  intro z hz
  apply huniqNear (y := (q, z))
  simpa only [Prod.dist_eq] using
    (max_lt (lt_of_lt_of_le hq ((min_le_right _ _).trans (min_le_left _ _))) hz)

omit [CompleteSpace P] in
theorem inverse_joint_continuousAt (F : P → Unknown n → Unknown n) (p : P) (y : Unknown n)
    (hf : ContDiffAt ℝ 1 (Function.uncurry F) (p, y))
    (hJ : (jacobian F p y).IsInvertible) :
    ContinuousAt (fun a : P × Unknown n => (jacobian F a.1 a.2).inverse) (p, y) := by
  exact ContinuousAt.comp (f := fun a : P × Unknown n => jacobian F a.1 a.2)
    (x := (p, y)) (hJ.contDiffAt_map_inverse (𝕜 := ℝ) (n := 0)).continuousAt
    (jacobian_joint_continuousAt F p y hf)

omit [CompleteSpace P] in
theorem compact_inverse_tube (F : P → Unknown n → Unknown n) (D K : Set (P × Unknown n))
    (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ (Function.uncurry F) D) (hK : IsCompact K)
    (hdata : ∀ a ∈ K, a ∈ D ∧ (jacobian F a.1 a.2).IsInvertible) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ a ∈ K, ∀ z : P × Unknown n,
      dist z a < δ → z ∈ D ∧ (jacobian F z.1 z.2).IsInvertible ∧
        ‖(jacobian F z.1 z.2).inverse‖ ≤ C := by
  have hdiff (a : P × Unknown n) (ha : a ∈ D) :
      ContDiffAt ℝ ∞ (Function.uncurry F) a :=
    (hF a ha).contDiffAt (hD.mem_nhds ha)
  have hcont : ContinuousOn (fun a : P × Unknown n => (jacobian F a.1 a.2).inverse) K := by
    intro a ha
    exact (inverse_joint_continuousAt F a.1 a.2
      ((hdiff a (hdata a ha).1).of_le (by norm_num)) (hdata a ha).2).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcont.norm
  let C : ℝ := max B 1 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right B 1]
  let U : Set (P × Unknown n) := {z | z ∈ D ∧ (jacobian F z.1 z.2).IsInvertible ∧
    ‖(jacobian F z.1 z.2).inverse‖ ≤ C}
  have hU : ∀ a ∈ K, U ∈ 𝓝 a := by
    intro a ha
    obtain ⟨haD, hJ⟩ := hdata a ha
    have hf := (hdiff a haD).of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)
    have hbase : ‖(jacobian F a.1 a.2).inverse‖ < C := by
      have hb := hB (Set.mem_image_of_mem _ ha)
      dsimp [C]
      linarith [le_max_left B 1]
    have hnorm : ∀ᶠ z : P × Unknown n in 𝓝 a, ‖(jacobian F z.1 z.2).inverse‖ < C :=
      (inverse_joint_continuousAt F a.1 a.2 hf hJ).norm.tendsto.eventually
        ((isOpen_lt continuous_id continuous_const).mem_nhds hbase)
    have hInv : ∀ᶠ z : P × Unknown n in 𝓝 a, (jacobian F z.1 z.2).IsInvertible :=
      (jacobian_joint_continuousAt F a.1 a.2 hf).tendsto.eventually
        (isOpen_euclidean_clm_isInvertible.mem_nhds hJ)
    filter_upwards [hD.mem_nhds haD, hInv, hnorm] with z hz hJz hNz
    exact ⟨hz, hJz, hNz.le⟩
  obtain ⟨δ, hδ, htube⟩ := compact_uniform_neighborhood K U hK hU
  exact ⟨δ, C, hδ, hC, htube⟩

theorem compact_uniform_uniqueness (F : P → Unknown n → Unknown n)
    (K : Set (P × Unknown n)) (hK : IsCompact K)
    (hdata : ∀ a ∈ K, ContDiffAt ℝ ∞ (Function.uncurry F) a ∧ F a.1 a.2 = 0 ∧
      (jacobian F a.1 a.2).IsInvertible) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ K, ∀ q v w,
      dist q a.1 < r → dist v a.2 < r → dist w a.2 < r → F q v = 0 → F q w = 0 → v = w := by
  classical
  have hlocal (a : K) := local_rectangle F a.1.1 a.1.2
    (hdata a.1 a.2).1 (hdata a.1 a.2).2.1 (hdata a.1 a.2).2.2
  choose ψ η ζ hη hζ hbase hsmooth hrows using hlocal
  let U (a : K) : Set (P × Unknown n) :=
    {z | dist z.1 a.1.1 < η a ∧ dist z.2 a.1.2 < ζ a}
  have hopen (a : K) : IsOpen (U a) :=
    (isOpen_lt (continuous_fst.dist continuous_const) continuous_const).inter
      (isOpen_lt (continuous_snd.dist continuous_const) continuous_const)
  have hcover : K ⊆ ⋃ a : K, U a := by
    intro a ha
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, by simpa [U] using And.intro (hη ⟨a, ha⟩) (hζ ⟨a, ha⟩)⟩
  obtain ⟨r, hr, hballs⟩ := lebesgue_number_lemma_of_metric hK hopen hcover
  refine ⟨r, hr, ?_⟩
  intro a ha q v w hq hv hw hrv hrw
  obtain ⟨b, hb⟩ := hballs a ha
  have hvb : (q, v) ∈ U b := hb (by simpa only [Metric.mem_ball, Prod.dist_eq] using max_lt hq hv)
  have hwb : (q, w) ∈ U b := hb (by simpa only [Metric.mem_ball, Prod.dist_eq] using max_lt hq hw)
  exact ((hrows b q hvb.1).2.2 v hvb.2 |>.mp hrv).symm.trans
    ((hrows b q hwb.1).2.2 w hwb.2 |>.mp hrw)

theorem eventually_exists_near (F : P → Unknown n → Unknown n) (p : P) (y : Unknown n)
    (hf : ContDiffAt ℝ ∞ (Function.uncurry F) (p, y)) (hroot : F p y = 0)
    (hJ : (jacobian F p y).IsInvertible) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ a : P × Unknown n in 𝓝 (p, y), ∃ x, dist x a.2 < r ∧ F a.1 x = 0 := by
  obtain ⟨ψ, hbase, hsmooth, hroots, _⟩ := local_implicitFunction F p y hf hroot hJ
  have hψ : ∀ᶠ a : P × Unknown n in 𝓝 (p, y), dist (ψ a.1) y < r / 2 := by
    have hc : ContinuousAt (fun a : P × Unknown n => ψ a.1) (p, y) :=
      ContinuousAt.comp (f := Prod.fst) (x := (p, y)) hsmooth.continuousAt continuousAt_fst
    have h := hc.tendsto.eventually (Metric.ball_mem_nhds (ψ p) (by linarith : 0 < r / 2))
    simpa only [Metric.mem_ball, hbase] using h
  have hy : ∀ᶠ a : P × Unknown n in 𝓝 (p, y), dist a.2 y < r / 2 :=
    (continuous_snd.continuousAt (x := (p, y))).tendsto.eventually
      (Metric.ball_mem_nhds y (by linarith : 0 < r / 2))
  have hz : ∀ᶠ a : P × Unknown n in 𝓝 (p, y), F a.1 (ψ a.1) = 0 :=
    (continuous_fst.continuousAt (x := (p, y))).tendsto.eventually hroots
  filter_upwards [hψ, hy, hz] with a hψ hy hz
  refine ⟨ψ a.1, ?_, hz⟩
  have ht := dist_triangle (ψ a.1) y a.2
  rw [dist_comm y a.2] at ht
  linarith

/-- Original Lemma 3.2 with proved compact uniformization and gluing.
The only input is the actual smooth equation on an open domain containing
a compact set of actual regular roots. -/
theorem compact_product (F : P → Unknown n → Unknown n) (D K : Set (P × Unknown n))
    (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ (Function.uncurry F) D) (hK : IsCompact K)
    (hdata : ∀ a ∈ K, a ∈ D ∧ F a.1 a.2 = 0 ∧ (jacobian F a.1 a.2).IsInvertible)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ η r C : ℝ, 0 < η ∧ 0 < r ∧ 0 < C ∧ r ≤ τ ∧ η ≤ r ∧
      ∀ a ∈ K, ∃ ψ : P → Unknown n, ψ a.1 = a.2 ∧
        ContDiffOn ℝ ∞ ψ (Metric.ball a.1 η) ∧ ∀ q, dist q a.1 < η →
          dist (ψ q) a.2 < r / 2 ∧ (q, ψ q) ∈ D ∧ (jacobian F q (ψ q)).IsInvertible ∧
          ‖(jacobian F q (ψ q)).inverse‖ ≤ C ∧ F q (ψ q) = 0 ∧
          (∀ z, dist z a.2 < r → (F q z = 0 ↔ ψ q = z)) := by
  classical
  have hdiff (a : P × Unknown n) (ha : a ∈ D) :
      ContDiffAt ℝ ∞ (Function.uncurry F) a := (hF a ha).contDiffAt (hD.mem_nhds ha)
  obtain ⟨u, hu, huniq⟩ := compact_uniform_uniqueness F K hK
    (fun a ha => ⟨hdiff a (hdata a ha).1, (hdata a ha).2⟩)
  obtain ⟨d, C, hd, hC, hinverse⟩ := compact_inverse_tube F D K hD hF hK
    (fun a ha => ⟨(hdata a ha).1, (hdata a ha).2.2⟩)
  let r : ℝ := min (min u d) τ
  have hr : 0 < r := lt_min (lt_min hu hd) hτ
  have hru : r ≤ u := (min_le_left (min u d) τ).trans (min_le_left u d)
  have hrd : r ≤ d := (min_le_left (min u d) τ).trans (min_le_right u d)
  let U : Set (P × Unknown n) := {b | ∃ x, dist x b.2 < r / 2 ∧ F b.1 x = 0}
  have hU : ∀ a ∈ K, U ∈ 𝓝 a := by
    intro a ha
    exact eventually_exists_near F a.1 a.2 (hdiff a (hdata a ha).1)
      (hdata a ha).2.1 (hdata a ha).2.2 (r / 2) (by linarith)
  obtain ⟨b, hb, hexists⟩ := compact_uniform_neighborhood K U hK hU
  let η : ℝ := min b r
  have hη : 0 < η := lt_min hb hr
  refine ⟨η, r, C, hη, hr, hC, min_le_right _ _, min_le_right _ _, ?_⟩
  intro a ha
  let ψ : P → Unknown n := fun q =>
    if h : ∃ x, dist x a.2 < r / 2 ∧ F q x = 0 then Classical.choose h else a.2
  have hψ (q : P) (hq : dist q a.1 < η) : dist (ψ q) a.2 < r / 2 ∧ F q (ψ q) = 0 := by
    have hdist : dist (q, a.2) a < b := by
      rw [Prod.dist_eq, dist_self]
      exact max_lt (lt_of_lt_of_le hq (min_le_left b r)) hb
    have he : ∃ x, dist x a.2 < r / 2 ∧ F q x = 0 := hexists a ha (q, a.2) hdist
    simpa only [ψ, dif_pos he] using Classical.choose_spec he
  have hq_u (q : P) (hq : dist q a.1 < η) : dist q a.1 < u :=
    lt_of_lt_of_le hq ((min_le_right b r).trans hru)
  have hnear (q : P) (hq : dist q a.1 < η) : (q, ψ q) ∈ D ∧
      (jacobian F q (ψ q)).IsInvertible ∧ ‖(jacobian F q (ψ q)).inverse‖ ≤ C := by
    apply hinverse a ha (q, ψ q)
    rw [Prod.dist_eq]
    exact max_lt (lt_of_lt_of_le hq ((min_le_right b r).trans hrd))
      (lt_of_lt_of_le (lt_trans (hψ q hq).1 (by linarith : r / 2 < r)) hrd)
  have hψunique (q : P) (hq : dist q a.1 < η) (z : Unknown n)
      (hz : dist z a.2 < r) (hrootz : F q z = 0) : ψ q = z := by
    exact huniq a ha q (ψ q) z (hq_u q hq)
      (lt_of_lt_of_le (lt_trans (hψ q hq).1 (by linarith : r / 2 < r)) hru)
      (lt_of_lt_of_le hz hru) (hψ q hq).2 hrootz
  refine ⟨ψ, hψunique a.1 (by simpa using hη) a.2 (by simpa using hr) (hdata a ha).2.1,
    ?_, ?_⟩
  · intro q hq
    obtain ⟨φ, hφbase, hφsmooth, hφroot, _⟩ := local_implicitFunction F q (ψ q)
      (hdiff (q, ψ q) (hnear q hq).1) (hψ q hq).2 (hnear q hq).2.1
    have hparam : ∀ᶠ t in 𝓝 q, dist t a.1 < η :=
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const).mem_nhds hq
    have hφnear : ∀ᶠ t in 𝓝 q, dist (φ t) a.2 < r := by
      have hdist : dist (φ q) a.2 < r := by
        rw [hφbase]
        linarith [(hψ q hq).1]
      exact hφsmooth.continuousAt.tendsto.eventually
        ((isOpen_lt (continuous_id.dist continuous_const) continuous_const).mem_nhds hdist)
    have heq : ψ =ᶠ[𝓝 q] φ := by
      filter_upwards [hparam, hφnear, hφroot] with t ht hd hr
      exact hψunique t ht (φ t) hd hr
    exact (hφsmooth.congr_of_eventuallyEq heq).contDiffWithinAt
  · intro q hq
    refine ⟨(hψ q hq).1, (hnear q hq).1, (hnear q hq).2.1,
      (hnear q hq).2.2, (hψ q hq).2, ?_⟩
    intro z hz
    exact ⟨hψunique q hq z hz, fun he => he ▸ (hψ q hq).2⟩

end DominantFiveBody.CompactImplicit
