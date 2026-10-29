import DominantFiveBody.CompactImplicit
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Quantitative dependence of actual roots on independent parameters.
This supplies the uniform O(epsilon) estimates in the collision charts. -/
noncomputable section
open scoped BigOperators ContDiff NNReal
open Filter Set Topology
namespace DominantFiveBody.CompactImplicit

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] {n : ℕ}

theorem compact_root_lipschitz (F : P → Unknown n → Unknown n)
    (K : Set (P × Unknown n)) (hK : IsCompact K)
    (hdata : ∀ a ∈ K, ContDiffAt ℝ ∞ (Function.uncurry F) a ∧ F a.1 a.2 = 0 ∧
      (jacobian F a.1 a.2).IsInvertible) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ a ∈ K, ∀ p q v w,
      dist p a.1 < r → dist q a.1 < r → dist v a.2 < r → dist w a.2 < r →
      F p v = 0 → F q w = 0 → dist v w ≤ C * dist p q := by
  classical
  have hlocal (a : K) : ∃ ψ : P → Unknown n, ∃ η ζ : ℝ, ∃ L : ℝ≥0,
      0 < η ∧ 0 < ζ ∧ LipschitzOnWith L ψ (Metric.ball a.1.1 η) ∧
      ∀ q, dist q a.1.1 < η → ∀ z, dist z a.1.2 < ζ → (F q z = 0 ↔ ψ q = z) := by
    obtain ⟨ψ, η, ζ, hη, hζ, _, hs, hrows⟩ := local_rectangle F a.1.1 a.1.2
      (hdata a.1 a.2).1 (hdata a.1 a.2).2.1 (hdata a.1 a.2).2.2
    obtain ⟨L, U, hU, hL⟩ := (hs.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    obtain ⟨c, hc, hball⟩ := Metric.mem_nhds_iff.mp hU
    refine ⟨ψ, min η c, ζ, L, lt_min hη hc, hζ, hL.mono ?_, ?_⟩
    · exact (Metric.ball_subset_ball (min_le_right η c)).trans hball
    · intro q hq z hz
      exact (hrows q (lt_of_lt_of_le hq (min_le_left η c))).2.2 z hz
  choose ψ η ζ L hη hζ hL hrows using hlocal
  let U (a : K) : Set (P × Unknown n) :=
    {z | dist z.1 a.1.1 < η a ∧ dist z.2 a.1.2 < ζ a}
  have hopen (a : K) : IsOpen (U a) :=
    (isOpen_lt (continuous_fst.dist continuous_const) continuous_const).inter
      (isOpen_lt (continuous_snd.dist continuous_const) continuous_const)
  have hcover : K ⊆ ⋃ a : K, U a := by
    intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩, by simpa [U] using And.intro (hη ⟨a,ha⟩) (hζ ⟨a,ha⟩)⟩
  obtain ⟨T,hT⟩ := hK.elim_finite_subcover U hopen hcover
  let I := {a : K // a ∈ T}
  have hcover' : K ⊆ ⋃ a : I, U a.1 := by
    intro a ha
    obtain ⟨b,hb,hab⟩ := mem_iUnion₂.mp (hT ha)
    exact mem_iUnion.mpr ⟨⟨b,hb⟩,hab⟩
  obtain ⟨r,hr,hballs⟩ := lebesgue_number_lemma_of_metric hK (fun a : I => hopen a.1) hcover'
  let C : ℝ := 1 + ∑ b ∈ T, (L b : ℝ)
  have hsum : 0 ≤ ∑ b ∈ T, (L b : ℝ) := Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _)
  refine ⟨r,C,hr,by dsimp [C]; linarith,?_⟩
  intro a ha p q v w hp hq hv hw hrv hrw
  obtain ⟨b,hb⟩ := hballs a ha
  have hpv : (p,v) ∈ U b.1 := hb (by simpa only [Metric.mem_ball,Prod.dist_eq] using max_lt hp hv)
  have hqw : (q,w) ∈ U b.1 := hb (by simpa only [Metric.mem_ball,Prod.dist_eq] using max_lt hq hw)
  have hψp := (hrows b.1 p hpv.1 v hpv.2).mp hrv
  have hψq := (hrows b.1 q hqw.1 w hqw.2).mp hrw
  have hbound := (hL b.1).dist_le_mul p hpv.1 q hqw.1
  rw [hψp,hψq] at hbound
  have hLC : (L b.1 : ℝ) ≤ C := by
    have hsingle := Finset.single_le_sum (fun c (_ : c ∈ T) => NNReal.coe_nonneg (L c)) b.2
    dsimp [C]
    linarith
  exact hbound.trans (mul_le_mul_of_nonneg_right hLC dist_nonneg)

end DominantFiveBody.CompactImplicit
