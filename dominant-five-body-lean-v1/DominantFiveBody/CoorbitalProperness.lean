import DominantFiveBody.CoorbitalCompactness
import DominantFiveBody.BoundaryJacobian
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Actual properness of the coorbital mass projection

The manuscript's Theorem `thm:coorbital`. The auxiliary clipped kernel is
used only to express compact closed sets away from collisions; its equality
with the actual equations on every admissible root is proved explicitly.
-/

noncomputable section
open scoped BigOperators
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

theorem kernelF_continuousAt_closed_semicircle {t : ℝ} (ht : 0 < t)
    (htpi : t ≤ Real.pi) : ContinuousAt kernelF t := by
  have hs : Real.sin (t / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  unfold kernelF
  fun_prop (disch := positivity)

/-- A continuous extension on the compact collision-free angle box. This
is an auxiliary function, and never replaces the physical kernel at roots. -/
def compactKernel (d t : ℝ) : ℝ := kernelF (min Real.pi (max d t))

theorem compactKernel_continuous (d : ℝ) (hd : 0 < d) (hdpi : d ≤ Real.pi) :
    Continuous (compactKernel d) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have htpos : 0 < min Real.pi (max d t) :=
    lt_min (lt_of_lt_of_le hd hdpi) (lt_of_lt_of_le hd (le_max_left _ _))
  exact (kernelF_continuousAt_closed_semicircle htpos (min_le_left _ _)).comp
    (f := fun t : ℝ => min Real.pi (max d t)) (x := t) (by fun_prop)

theorem compactKernel_eq (d t : ℝ) (hdt : d ≤ t) (htpi : t ≤ Real.pi) :
    compactKernel d t = kernelF t := by
  simp only [compactKernel, max_eq_right hdt, min_eq_right htpi]

def compactAngularEquation (d : ℝ) (mass theta : Satellite → ℝ) (i : Satellite) : ℝ :=
  ∑ j, if i < j then mass j * compactKernel d (theta j - theta i)
    else if j < i then -(mass j * compactKernel d (theta i - theta j)) else 0

theorem compactAngularEquation_continuous (d : ℝ) (hd : 0 < d) (hdpi : d ≤ Real.pi)
    (i : Satellite) : Continuous (fun z : (Satellite → ℝ) × (Satellite → ℝ) =>
      compactAngularEquation d z.1 z.2 i) := by
  classical
  unfold compactAngularEquation
  apply continuous_finsetSum
  intro j _
  split_ifs
  · exact (by fun_prop : Continuous
      (fun z : (Satellite → ℝ) × (Satellite → ℝ) => z.1 j)).mul
        ((compactKernel_continuous d hd hdpi).comp (by fun_prop))
  · exact ((by fun_prop : Continuous
      (fun z : (Satellite → ℝ) × (Satellite → ℝ) => z.1 j)).mul
        ((compactKernel_continuous d hd hdpi).comp (by fun_prop))).neg
  · exact continuous_const

theorem compactAngularEquation_eq (d : ℝ) (mass theta : Satellite → ℝ)
    (hgaps : ∀ i j, i < j → d ≤ theta j - theta i ∧ theta j - theta i ≤ Real.pi)
    (hpos : ∀ i j, i < j → 0 < theta j - theta i) (i : Satellite) :
    compactAngularEquation d mass theta i = angularEquation mass theta i := by
  classical
  unfold compactAngularEquation angularEquation
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · rw [if_pos hij, compactKernel_eq d _ (hgaps i j hij).1 (hgaps i j hij).2,
      coorbitalKernel_eq_positive_formula _ (hpos i j hij).le]
  · rw [if_neg hij]
    by_cases hji : j < i
    · rw [if_pos hji, compactKernel_eq d _ (hgaps j i hji).1 (hgaps j i hji).2]
      have heq : theta j - theta i = -(theta i - theta j) := by ring
      rw [heq, coorbitalKernel_neg,
        coorbitalKernel_eq_positive_formula _ (hpos j i hji).le]
      ring
    · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      simp [coorbitalKernel, kernelF]

/-- The exact boundary contradiction from the manuscript: when all three
gaps are at most h and their sum is π, the first row is a strictly negative
nonzero multiple of f(2h). -/
theorem no_coorbital_root_at_semicircle_boundary (mass theta : Satellite → ℝ)
    (hmass : ∀ i, 0 < mass i)
    (hgaps : theta 1 - theta 0 ≤ h ∧ theta 2 - theta 1 ≤ h ∧ theta 3 - theta 2 ≤ h)
    (hspan : theta 3 - theta 0 = Real.pi)
    (hroot : ∀ i, angularEquation mass theta i = 0) : False := by
  have hthree : 3 * h = Real.pi := by unfold h; ring
  have h01 : theta 1 - theta 0 = h := by linarith [hgaps.1, hgaps.2.1, hgaps.2.2]
  have h02 : theta 2 - theta 0 = 2 * h := by linarith [hgaps.1, hgaps.2.1, hgaps.2.2]
  have hh : 0 < h := by unfold h; positivity
  have hf : kernelF (2 * h) < 0 := kernelF_neg_on_long_arc (by linarith) (by linarith)
  have heq := hroot 0
  unfold angularEquation at heq
  rw [Fin.sum_univ_four] at heq
  have hz : coorbitalKernel 0 = 0 := by simp [coorbitalKernel, kernelF]
  simp only [sub_self, hz, mul_zero, zero_add] at heq
  change mass 1 * coorbitalKernel (theta 1 - theta 0) +
    mass 2 * coorbitalKernel (theta 2 - theta 0) +
    mass 3 * coorbitalKernel (theta 3 - theta 0) = 0 at heq
  rw [h01, h02, hspan, coorbitalKernel_eq_positive_formula h hh.le,
    coorbitalKernel_eq_positive_formula (2 * h) (by positivity),
    coorbitalKernel_eq_positive_formula Real.pi Real.pi_pos.le,
    kernelF_h, kernelF_pi, mul_zero, mul_zero, zero_add, add_zero] at heq
  exact (ne_of_lt (mul_neg_of_pos_of_neg (hmass 2) hf)) heq

def compactCoorbitalRootRegion (K : Set (Satellite → ℝ)) (d : ℝ) :
    Set ((Satellite → ℝ) × (Satellite → ℝ)) :=
  {z | z.1 ∈ K ∧ z.2 0 = 0 ∧
    (∀ i j, i < j → d ≤ z.2 j - z.2 i) ∧
    (∀ i : Fin 3, z.2 i.succ - z.2 i.castSucc ≤ h) ∧
    z.2 3 ≤ Real.pi ∧ (∀ i, compactAngularEquation d z.1 z.2 i = 0)}

theorem compactCoorbitalRootRegion_isClosed (K : Set (Satellite → ℝ)) (d : ℝ)
    (hK : IsClosed K) (hd : 0 < d) (hdpi : d ≤ Real.pi) :
    IsClosed (compactCoorbitalRootRegion K d) := by
  classical
  unfold compactCoorbitalRootRegion
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (hK.preimage continuous_fst).inter ((isClosed_eq (by fun_prop) continuous_const).inter
    ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const (by fun_prop)).inter
    ((isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const).inter
    ((isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_iInter fun i => isClosed_eq
      (compactAngularEquation_continuous d hd hdpi i) continuous_const)))))

theorem compactCoorbitalRootRegion_isCompact (K : Set (Satellite → ℝ)) (d : ℝ)
    (hK : IsCompact K) (hd : 0 < d) (hdpi : d ≤ Real.pi) :
    IsCompact (compactCoorbitalRootRegion K d) := by
  have hangle : IsCompact {t : Satellite → ℝ | ∀ i, t i ∈ Set.Icc (0 : ℝ) Real.pi} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply (hK.prod hangle).of_isClosed_subset
    (compactCoorbitalRootRegion_isClosed K d hK.isClosed hd hdpi)
  intro z hz
  obtain ⟨hm, ha, hg, _, hl, _⟩ := hz
  refine ⟨hm, ?_⟩
  intro i
  by_cases hi : i = 0
  · subst i
    exact ⟨by rw [ha], by rw [ha]; exact Real.pi_pos.le⟩
  · have h0i : (0 : Satellite) < i := lt_of_le_of_ne (Fin.zero_le i) (Ne.symm hi)
    have hlow : 0 ≤ z.2 i := by have ht := hg 0 i h0i; rw [ha, sub_zero] at ht; linarith
    have hupper : z.2 i ≤ Real.pi := by
      by_cases hithree : i = 3
      · subst i; exact hl
      · have hi3 : i < (3 : Satellite) := lt_of_le_of_ne (Fin.le_last i) hithree
        have ht := hg i 3 hi3
        linarith
    exact ⟨hlow, hupper⟩

theorem compactCoorbitalRootRegion_span_lt_pi
    (K : Set (Satellite → ℝ)) (d : ℝ) (hd : 0 < d)
    (hmass : ∀ m ∈ K, ∀ i, 0 < m i) (z : (Satellite → ℝ) × (Satellite → ℝ))
    (hz : z ∈ compactCoorbitalRootRegion K d) : z.2 3 < Real.pi := by
  obtain ⟨hm, ha, hg, hcons, hl, hr⟩ := hz
  have hpairUpper : ∀ i j : Satellite, i < j → z.2 j - z.2 i ≤ Real.pi := by
    intro i j hij
    have hlow (i : Satellite) : 0 ≤ z.2 i := by
      by_cases hi : i = 0
      · subst i; rw [ha]
      · have hi0 : (0 : Satellite) < i := lt_of_le_of_ne (Fin.zero_le i) (Ne.symm hi)
        have ht := hg 0 i hi0
        rw [ha, sub_zero] at ht
        linarith
    have hupp (j : Satellite) : z.2 j ≤ Real.pi := by
      by_cases hj : j = 3
      · subst j; exact hl
      · have hj3 : j < (3 : Satellite) := lt_of_le_of_ne (Fin.le_last j) hj
        have ht := hg j 3 hj3
        linarith
    linarith [hlow i, hupp j]
  have hroot : ∀ i, angularEquation z.1 z.2 i = 0 := by
    intro i
    rw [← compactAngularEquation_eq d z.1 z.2
      (fun i j hij => ⟨hg i j hij, hpairUpper i j hij⟩)
      (fun i j hij => lt_of_lt_of_le hd (hg i j hij))]
    exact hr i
  rcases lt_or_eq_of_le hl with hlt | heq
  · exact hlt
  · exfalso
    apply no_coorbital_root_at_semicircle_boundary z.1 z.2 (hmass z.1 hm)
      ⟨hcons 0, hcons 1, hcons 2⟩ (by rw [ha, sub_zero]; exact heq) hroot

def coorbitalRootsOver (K : Set (Satellite → ℝ)) :
    Set ((Satellite → ℝ) × (Satellite → ℝ)) :=
  {z | z.1 ∈ K ∧ CoorbitalAngleDomain z.2 ∧ (∀ i, coorbitalResidual z.1 z.2 i = 0)}

theorem compact_positive_mass_floor (K : Set (Satellite → ℝ))
    (hK : IsCompact K) (hpositive : ∀ m ∈ K, ∀ i, 0 < m i) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ m ∈ K, ∀ i, alpha ≤ m i := by
  let massMin : (Satellite → ℝ) → ℝ := fun m => min (min (m 0) (m 1)) (min (m 2) (m 3))
  have hc : Continuous massMin := by dsimp [massMin]; fun_prop
  have hp : ∀ m ∈ K, 0 < massMin m := by
    intro m hm
    exact lt_min (lt_min (hpositive m hm 0) (hpositive m hm 1))
      (lt_min (hpositive m hm 2) (hpositive m hm 3))
  obtain ⟨alpha, ha, hfloor⟩ := hK.exists_forall_le' hc.continuousOn hp
  refine ⟨alpha, ha, ?_⟩
  intro m hm i
  have hmin : massMin m ≤ m i := by
    fin_cases i
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_right _ _)
  exact le_trans (hfloor m hm) hmin

theorem coorbitalRootsOver_eq_compactRegion (K : Set (Satellite → ℝ)) (d : ℝ)
    (hd : 0 < d) (hpositive : ∀ m ∈ K, PositiveRatio m)
    (hseparation : ∀ z ∈ coorbitalRootsOver K, ∀ i j, i < j → d ≤ z.2 j - z.2 i) :
    coorbitalRootsOver K = compactCoorbitalRootRegion K d := by
  ext z
  constructor
  · intro hz
    obtain ⟨hm, ht, hr⟩ := hz
    have harc := orderedSemicircle_of_coorbitalAngleDomain z.2 ht
    have hroot : ∀ i, angularEquation z.1 z.2 i = 0 := by
      intro i; rw [angularEquation_eq_residual]; exact hr i
    have hgaps := four_root_gaps z.1 z.2 (hpositive z.1 hm).1 harc hroot
    refine ⟨hm, ht.1, hseparation z ⟨hm, ht, hr⟩, ?_, ht.2.2.le, ?_⟩
    · intro i
      fin_cases i
      · exact hgaps.1.le
      · exact hgaps.2.1.le
      · exact hgaps.2.2.1.le
    · intro i
      rw [compactAngularEquation_eq d z.1 z.2
        (fun a b hab => ⟨hseparation z ⟨hm, ht, hr⟩ a b hab, (harc a b hab).2.le⟩)
        (fun a b hab => (harc a b hab).1)]
      exact hroot i
  · intro hz
    have hspan := compactCoorbitalRootRegion_span_lt_pi K d hd
      (fun m hm => (hpositive m hm).1) z hz
    obtain ⟨hm, ha, hg, _, _, hr⟩ := hz
    have hstrict : ∀ i j, i < j → z.2 i < z.2 j := by
      intro i j hij
      exact sub_pos.mp (lt_of_lt_of_le hd (hg i j hij))
    have ht : CoorbitalAngleDomain z.2 := ⟨ha, hstrict, hspan⟩
    have harc := orderedSemicircle_of_coorbitalAngleDomain z.2 ht
    refine ⟨hm, ht, ?_⟩
    intro i
    rw [← angularEquation_eq_residual, ← compactAngularEquation_eq d z.1 z.2
      (fun a b hab => ⟨hg a b hab, (harc a b hab).2.le⟩)
      (fun a b hab => (harc a b hab).1)]
    exact hr i

/-- The actual preimage of every compact positive-mass base is compact.
The pair margin and exclusion of span π have both been proved from roots. -/
theorem coorbitalRootsOver_isCompact (K : Set (Satellite → ℝ))
    (hK : IsCompact K) (hpositive : ∀ m ∈ K, PositiveRatio m) :
    IsCompact (coorbitalRootsOver K) := by
  obtain ⟨alpha, ha, hfloor⟩ := compact_positive_mass_floor K hK
    (fun m hm => (hpositive m hm).1)
  obtain ⟨d, hd, hsep⟩ := coorbital_roots_uniform_pair_separation alpha ha
  let delta := min d h
  have hdeltapos : 0 < delta := lt_min hd (by unfold h; positivity)
  have hdeltapi : delta ≤ Real.pi := by
    exact le_trans (min_le_right _ _) (by unfold h; linarith [Real.pi_pos])
  have hseparation : ∀ z ∈ coorbitalRootsOver K, ∀ i j, i < j → delta ≤ z.2 j - z.2 i := by
    intro z hz i j hij
    obtain ⟨hm, ht, hr⟩ := hz
    exact le_trans (min_le_left _ _) (hsep z.1 z.2 (hpositive z.1 hm) (hfloor z.1 hm)
      (orderedSemicircle_of_coorbitalAngleDomain z.2 ht)
      (fun i => (angularEquation_eq_residual z.1 z.2 i).trans (hr i)) i j hij)
  rw [coorbitalRootsOver_eq_compactRegion K delta hdeltapos hpositive hseparation]
  exact compactCoorbitalRootRegion_isCompact K delta hK hdeltapos hdeltapi

theorem coorbitalRootsOver_uniform_span_margin (K : Set (Satellite → ℝ))
    (hK : IsCompact K) (hpositive : ∀ m ∈ K, PositiveRatio m) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ z ∈ coorbitalRootsOver K, z.2 3 ≤ Real.pi - eta := by
  have hcompact := coorbitalRootsOver_isCompact K hK hpositive
  obtain ⟨eta, he, hbound⟩ := hcompact.exists_forall_le'
    (show ContinuousOn (fun z : (Satellite → ℝ) × (Satellite → ℝ) => Real.pi - z.2 3)
      (coorbitalRootsOver K) by fun_prop)
    (fun z hz => sub_pos.mpr hz.2.1.2.2)
  exact ⟨eta, he, fun z hz => by have hb := hbound z hz; linarith⟩

abbrev CoorbitalMassSpace := {m : Satellite → ℝ // PositiveRatio m}

abbrev CoorbitalRootSpace :=
  {z : (Satellite → ℝ) × (Satellite → ℝ) //
    PositiveRatio z.1 ∧ CoorbitalAngleDomain z.2 ∧
      (∀ i, coorbitalResidual z.1 z.2 i = 0)}

def coorbitalMassProjection (z : CoorbitalRootSpace) : CoorbitalMassSpace :=
  ⟨z.val.1, z.property.1⟩

theorem coorbitalMassProjection_continuous : Continuous coorbitalMassProjection := by
  unfold coorbitalMassProjection
  fun_prop

/-- The mass projection of the actual zero set is proper, rather than
an abstract map with properness supplied as a premise. -/
theorem coorbitalMassProjection_isProperMap : IsProperMap coorbitalMassProjection := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨coorbitalMassProjection_continuous, ?_⟩
  intro K hK
  let base : Set (Satellite → ℝ) := Subtype.val '' K
  have hbase : IsCompact base := hK.image continuous_subtype_val
  have hpositive : ∀ m ∈ base, PositiveRatio m := by
    intro m hm
    obtain ⟨m', _, rfl⟩ := hm
    exact m'.property
  apply Subtype.isCompact_iff.mpr
  have heq : (Subtype.val '' (coorbitalMassProjection ⁻¹' K) :
      Set ((Satellite → ℝ) × (Satellite → ℝ))) = coorbitalRootsOver base := by
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨coorbitalMassProjection r, hr, rfl⟩, r.property.2⟩
    · intro hz
      obtain ⟨hm, ht, hroot⟩ := hz
      obtain ⟨m, hm, hmeq⟩ := hm
      let r : CoorbitalRootSpace := ⟨z, ⟨by rw [← hmeq]; exact m.property, ht, hroot⟩⟩
      refine ⟨r, ?_, rfl⟩
      have hproj : coorbitalMassProjection r = m := Subtype.ext hmeq.symm
      change coorbitalMassProjection r ∈ K
      rwa [hproj]
  rw [heq]
  exact coorbitalRootsOver_isCompact base hbase hpositive

end DominantFiveBody
