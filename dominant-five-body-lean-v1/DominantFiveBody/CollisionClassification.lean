import DominantFiveBody.CollisionPairScales

/-! # Exhaustive limiting collision classes for actual ordered roots

The geometric limits are consequences of Proposition 4.1. The finite
classification distinguishes a separated limit, one complete pair, and
an endpoint complete triple. The two-pair case is eliminated by the
actual scale theorem, before any regularized chart is invoked.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1000000

def CompleteLimitingSatelliteTriple (q : SatelliteConfiguration) (p : Satellite) (c : Plane) : Prop :=
  ∀ i,q i=c ↔ i≠p

theorem normalized_ordered_polar_limit_geometry
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration) (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (𝓝 theta0)) :
    Tendsto r atTop (𝓝 (fun _ => (1 : ℝ))) ∧
      (∀ i,qLimit i=polarPoint 1 (theta0 i)) ∧ Monotone theta0 ∧
      0<theta0 3-theta0 0 ∧ theta0 3-theta0 0<Real.pi := by
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (𝓝 1) := by
    convert! dominant_satellite_radius_tendsto eps mu x heps hepst hm hx i using 1
    funext n
    rw [hpolar n]
    simp only [polarSatellites,polarPoint_norm,abs_of_pos (hr n i)]
  have hrt : Tendsto r atTop (𝓝 (fun _ => (1 : ℝ))) := tendsto_pi_nhds.mpr hrat
  have hT (n : ℕ) := (polarResiduals_zero_of_normalized (eps n) (mu n) (x n) (hx n)
    (hm n) (heps n) (r n) (theta n) (hr n) (hpolar n)).2
  refine ⟨hrt,?_,ordered_angle_limits_monotone theta horder theta0 hthetat,?_,?_⟩
  · intro i
    have hqi : Tendsto (fun n => satellitesRelative (x n) i) atTop (𝓝 (qLimit i)) := by
      exact (continuous_apply i).continuousAt.tendsto.comp hqt
    have hti : Tendsto (fun n => theta n i) atTop (𝓝 (theta0 i)) :=
      (continuous_apply i).continuousAt.tendsto.comp hthetat
    have hp : Tendsto (fun n => polarPoint (r n i) (theta n i)) atTop (𝓝 (polarPoint 1 (theta0 i))) :=
      (polarPoint_contDiff 0).continuous.continuousAt.tendsto.comp ((hrat i).prodMk_nhds hti)
    have hp' : Tendsto (fun n => satellitesRelative (x n) i) atTop (𝓝 (polarPoint 1 (theta0 i))) := by
      simpa only [hpolar,polarSatellites] using hp
    exact tendsto_nhds_unique hqi hp'
  · exact ordered_full_angular_limit_span_pos eps heps mu r theta (fun n => (hm n).1) hr hT
      horder (fun _ => 1) theta0 (fun _ => rfl) hrt hthetat
  · exact ordered_full_angular_limit_span_lt_pi eps heps hepst mu r theta (fun n => (hm n).1)
      (fun n => (hm n).2) hr hT horder muLimit (fun _ => 1) theta0 (fun _ => rfl) hmt hrt hthetat

theorem unit_ordered_limit_equal_iff (q : SatelliteConfiguration) (theta : Satellite → ℝ)
    (hpolar : ∀ i,q i=polarPoint 1 (theta i)) (hmono : Monotone theta)
    (hspan : theta 3-theta 0<Real.pi) (i j : Satellite) :
    q i=q j ↔ theta i=theta j := by
  have hpi : |theta j-theta i|<Real.pi := by
    have hi0 := hmono (Fin.zero_le i)
    have hj0 := hmono (Fin.zero_le j)
    have hi3 := hmono (Fin.le_last i)
    have hj3 := hmono (Fin.le_last j)
    change theta i≤theta 3 at hi3
    change theta j≤theta 3 at hj3
    rw [abs_lt]
    constructor <;> linarith
  rw [hpolar i,hpolar j]
  constructor
  · intro hh
    by_contra hn
    exact polarUnit_ne_of_angle_ne (theta i) (theta j) hn hpi hh
  · intro hh
    rw [hh]

theorem ordered_four_collision_classes (q : SatelliteConfiguration) (theta : Satellite → ℝ)
    (heq : ∀ i j,q i=q j ↔ theta i=theta j) (hmono : Monotone theta)
    (hspan : theta 0<theta 3) :
    Function.Injective q ∨
      (∃ a b : Satellite,a<b ∧ CompleteLimitingSatellitePair q a b (q a)) ∨
      (∃ p : Satellite,(p=0 ∨ p=3) ∧ ∃ c,CompleteLimitingSatelliteTriple q p c) ∨
      (CompleteLimitingSatellitePair q 0 1 (q 0) ∧ CompleteLimitingSatellitePair q 2 3 (q 2)) := by
  rcases (hmono (show (0 : Satellite)≤1 by decide)).lt_or_eq with h01|h01
  all_goals rcases (hmono (show (1 : Satellite)≤2 by decide)).lt_or_eq with h12|h12
  all_goals rcases (hmono (show (2 : Satellite)≤3 by decide)).lt_or_eq with h23|h23
  · left
    intro i j hij
    have hh := (heq i j).mp hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; dsimp at hh; linarith)
  · right; left
    refine ⟨2,3,by decide,?_⟩
    intro j
    rw [heq]
    fin_cases j <;> simp_all
    all_goals linarith
  · right; left
    refine ⟨1,2,by decide,?_⟩
    intro j
    rw [heq]
    fin_cases j <;> simp_all
    all_goals linarith
  · right; right; left
    refine ⟨0,Or.inl rfl,q 1,?_⟩
    intro j
    rw [heq]
    fin_cases j <;> simp_all
    all_goals linarith
  · right; left
    refine ⟨0,1,by decide,?_⟩
    intro j
    rw [heq]
    fin_cases j <;> simp_all
    all_goals linarith
  · right; right; right
    constructor
    · intro j
      rw [heq]
      fin_cases j <;> simp_all
      all_goals linarith
    · intro j
      rw [heq]
      fin_cases j <;> simp_all
      all_goals linarith
  · right; right; left
    refine ⟨3,Or.inr rfl,q 0,?_⟩
    intro j
    rw [heq]
    fin_cases j <;> simp_all
    all_goals linarith
  · exfalso
    linarith

theorem normalized_ordered_collision_classes_exhaustive
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration) (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (𝓝 theta0)) :
    Function.Injective qLimit ∨
      (∃ a b : Satellite,a<b ∧ CompleteLimitingSatellitePair qLimit a b (qLimit a)) ∨
      (∃ p : Satellite,(p=0 ∨ p=3) ∧ ∃ c,CompleteLimitingSatelliteTriple qLimit p c) := by
  obtain ⟨_,hqp,hmono,hspan0,hspanpi⟩ := normalized_ordered_polar_limit_geometry
    eps mu x heps hepst hm hx r theta hr hpolar horder muLimit hmt qLimit hqt theta0 hthetat
  have heq := unit_ordered_limit_equal_iff qLimit theta0 hqp hmono hspanpi
  rcases ordered_four_collision_classes qLimit theta0 heq hmono (sub_pos.mp hspan0) with hcf|hp|ht|hpairs
  · exact Or.inl hcf
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr ht)
  · have hneq : qLimit 0≠qLimit 2 := by
      intro hh
      have hj := (hpairs.1 2).mp hh.symm
      exact (by decide : ¬((2 : Satellite)=0 ∨ (2 : Satellite)=1)) hj
    exact (normalized_complete_pairs_cannot_coexist eps mu x heps hepst hm hx hconv
      r theta hr hpolar horder muLimit hmt qLimit hqt 0 1 2 3 (by decide) (by decide)
      (qLimit 0) (qLimit 2) hneq hpairs.1 hpairs.2 theta0 hthetat).elim

end DominantFiveBody
