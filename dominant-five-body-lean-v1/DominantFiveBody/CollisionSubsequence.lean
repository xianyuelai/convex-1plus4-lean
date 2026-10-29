import DominantFiveBody.CollisionClassification
import Mathlib.Data.Fintype.Pigeonhole

/-! # Actual compact subsequences and the regular/nested triple split

No chart membership enters compactness or the scale-ratio alternative.
The first selection jointly treats mass fractions and physical angles;
the second separates a uniformly comparable triple from a nested pair.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem ordered_mass_angle_compact_subsequence (mu theta : ℕ → Satellite → ℝ)
    (hm : ∀ n,PositiveRatio (mu n)) (hzero : ∀ n,theta n 0=0)
    (horder : ∀ n i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi) :
    ∃ (phi : ℕ → ℕ) (muLimit thetaLimit : Satellite → ℝ),StrictMono phi ∧
      Tendsto (mu ∘ phi) atTop (𝓝 muLimit) ∧ Tendsto (theta ∘ phi) atTop (𝓝 thetaLimit) ∧
      (∀ i,0≤muLimit i) ∧ ∑ i,muLimit i=1 := by
  obtain ⟨thetaLimit,phi1,hphi1,htheta⟩ := ordered_angles_compact_subsequence theta hzero horder
  have hb : ∀ n,mu (phi1 n)∈Metric.closedBall (0 : MassRatio) 1 := by
    intro n
    rw [Metric.mem_closedBall,dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ)≤1)).mpr
    intro i
    rw [Real.norm_eq_abs,abs_of_pos ((hm (phi1 n)).1 i),← (hm (phi1 n)).2]
    exact Finset.single_le_sum (fun j _ => ((hm (phi1 n)).1 j).le) (Finset.mem_univ i)
  obtain ⟨muLimit,_,phi2,hphi2,hmu⟩ := (isCompact_closedBall (0 : MassRatio) 1).tendsto_subseq hb
  let phi := phi1 ∘ phi2
  have hmLim : Tendsto (mu ∘ phi) atTop (𝓝 muLimit) := hmu
  refine ⟨phi,muLimit,thetaLimit,hphi1.comp hphi2,hmLim,htheta.comp hphi2.tendsto_atTop,?_,?_⟩
  · intro i
    exact ge_of_tendsto ((continuous_apply i).continuousAt.tendsto.comp hmLim)
      (Filter.Eventually.of_forall (fun n => ((hm (phi n)).1 i).le))
  · have hc : Continuous (fun m : MassRatio => ∑ i,m i) := by fun_prop
    have hsum := hc.continuousAt.tendsto.comp hmLim
    have heq : (fun n => ∑ i,mu (phi n) i)=(fun _ : ℕ => (1 : ℝ)) :=
      funext (fun n => (hm (phi n)).2)
    change Tendsto (fun n => ∑ i,mu (phi n) i) atTop (𝓝 (∑ i,muLimit i)) at hsum
    rw [heq] at hsum
    exact tendsto_nhds_unique hsum tendsto_const_nhds

theorem normalized_ordered_collision_subsequence
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (hzero : ∀ n,theta n 0=0)
    (horder : ∀ n i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi) :
    ∃ (phi : ℕ → ℕ) (muLimit thetaLimit : Satellite → ℝ),StrictMono phi ∧
      Tendsto (mu ∘ phi) atTop (𝓝 muLimit) ∧ Tendsto (theta ∘ phi) atTop (𝓝 thetaLimit) ∧
      (∀ i,0≤muLimit i) ∧ (∑ i,muLimit i=1) ∧
      let qLimit := polarSatellites (fun _ => 1) thetaLimit
      Tendsto (fun n => satellitesRelative (x (phi n))) atTop (𝓝 qLimit) ∧
      (Function.Injective qLimit ∨
        (∃ a b : Satellite,a<b ∧ CompleteLimitingSatellitePair qLimit a b (qLimit a)) ∨
        (∃ p : Satellite,(p=0 ∨ p=3) ∧ ∃ c,CompleteLimitingSatelliteTriple qLimit p c)) := by
  obtain ⟨phi,muLimit,thetaLimit,hphi,hmu,htheta,hmnonneg,hmsum⟩ :=
    ordered_mass_angle_compact_subsequence mu theta hm hzero horder
  let qLimit := polarSatellites (fun _ => 1) thetaLimit
  have hq : Tendsto (fun n => satellitesRelative (x (phi n))) atTop (𝓝 qLimit) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hrat : Tendsto (fun n => r (phi n) i) atTop (𝓝 1) := by
      have hh := (dominant_satellite_radius_tendsto eps mu x heps hepst hm hx i).comp hphi.tendsto_atTop
      simpa only [Function.comp_def,hpolar,polarSatellites,polarPoint_norm,
        abs_of_pos (hr _ _)] using hh
    have hthetaI : Tendsto (fun n => theta (phi n) i) atTop (𝓝 (thetaLimit i)) :=
      (continuous_apply i).continuousAt.tendsto.comp htheta
    have hh := (polarPoint_contDiff 0).continuous.continuousAt.tendsto.comp
      (hrat.prodMk_nhds hthetaI)
    simpa only [Function.comp_def,hpolar,polarSatellites,qLimit] using hh
  refine ⟨phi,muLimit,thetaLimit,hphi,hmu,htheta,hmnonneg,hmsum,hq,?_⟩
  exact normalized_ordered_collision_classes_exhaustive (eps ∘ phi) (mu ∘ phi) (x ∘ phi)
    (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop) (fun n => hm (phi n))
    (fun n => hx (phi n)) (fun n => hconv (phi n)) (r ∘ phi) (theta ∘ phi)
    (fun n => hr (phi n)) (fun n => hpolar (phi n)) (fun n => horder (phi n))
    muLimit hmu qLimit hq thetaLimit htheta

def tripleShortestDistance (q : SatelliteConfiguration) (a b c : Satellite) : ℝ :=
  min (satelliteDistance q a b) (min (satelliteDistance q a c) (satelliteDistance q b c))

def tripleLargestDistance (q : SatelliteConfiguration) (a b c : Satellite) : ℝ :=
  max (satelliteDistance q a b) (max (satelliteDistance q a c) (satelliteDistance q b c))

theorem tripleDistances_bounds (q : SatelliteConfiguration) (a b c : Satellite)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) (hq : RelativeCollisionFree q) :
    0<tripleShortestDistance q a b c ∧
      tripleShortestDistance q a b c≤tripleLargestDistance q a b c := by
  have hp (i j : Satellite) (hij : i≠j) : 0<satelliteDistance q i j :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (hq.2 i j hij))
  refine ⟨lt_min (hp a b hab) (lt_min (hp a c hac) (hp b c hbc)),?_⟩
  exact (min_le_left _ _).trans (le_max_left _ _)

theorem positive_scale_ratio_subsequence (s d : ℕ → ℝ)
    (hs : ∀ n,0<s n) (hsd : ∀ n,s n≤d n) :
    ∃ (phi : ℕ → ℕ) (L : ℝ),StrictMono phi ∧ L∈Icc (0 : ℝ) 1 ∧
      Tendsto (fun n => s (phi n)/d (phi n)) atTop (𝓝 L) ∧
      (L=0 ∨ (0<L ∧ ∃ k : ℝ,0<k ∧ ∀ n,k≤s (phi n)/d (phi n))) := by
  have hbound (n : ℕ) : s n/d n∈Icc (0 : ℝ) 1 := by
    have hd := lt_of_lt_of_le (hs n) (hsd n)
    exact ⟨(div_pos (hs n) hd).le,(div_le_one hd).mpr (hsd n)⟩
  obtain ⟨L,hL,phi,hphi,hlim⟩ := isCompact_Icc.isSeqCompact hbound
  rcases hL.1.eq_or_lt with hL0|hLp
  · exact ⟨phi,L,hphi,hL,hlim,Or.inl hL0.symm⟩
  · have hn : ∀ᶠ n in atTop,L/2<s (phi n)/d (phi n) :=
      hlim.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hn
    let psi (n : ℕ) := phi (N+n)
    have hshift : StrictMono (fun n : ℕ => N+n) := fun _ _ hij => Nat.add_lt_add_left hij N
    refine ⟨psi,L,hphi.comp hshift,hL,hlim.comp hshift.tendsto_atTop,Or.inr ⟨hLp,L/2,by positivity,?_⟩⟩
    intro n
    exact (hN (N+n) (Nat.le_add_right N n)).le

/-- The physical shortest/diameter ratio yields the two triple regimes
on an actual subsequence; the comparable regime has a single positive
lower bound for all its pair distances. -/
theorem collision_free_triple_scale_subsequence (q : ℕ → SatelliteConfiguration)
    (a b c : Satellite) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hq : ∀ n,RelativeCollisionFree (q n)) :
    ∃ phi : ℕ → ℕ,StrictMono phi ∧
      (Tendsto (fun n => tripleShortestDistance (q (phi n)) a b c/
        tripleLargestDistance (q (phi n)) a b c) atTop (𝓝 0) ∨
      ∃ k : ℝ,0<k ∧ ∀ n,
        k*tripleLargestDistance (q (phi n)) a b c≤satelliteDistance (q (phi n)) a b ∧
        k*tripleLargestDistance (q (phi n)) a b c≤satelliteDistance (q (phi n)) a c ∧
        k*tripleLargestDistance (q (phi n)) a b c≤satelliteDistance (q (phi n)) b c) := by
  have hb (n : ℕ) := tripleDistances_bounds (q n) a b c hab hac hbc (hq n)
  obtain ⟨phi,L,hphi,_,hlim,hcase⟩ := positive_scale_ratio_subsequence
    (fun n => tripleShortestDistance (q n) a b c) (fun n => tripleLargestDistance (q n) a b c)
    (fun n => (hb n).1) (fun n => (hb n).2)
  refine ⟨phi,hphi,?_⟩
  rcases hcase with rfl|⟨_,k,hk,hbound⟩
  · exact Or.inl hlim
  · right
    refine ⟨k,hk,?_⟩
    intro n
    have hd := lt_of_lt_of_le (hb (phi n)).1 (hb (phi n)).2
    have hbnd := (le_div_iff₀ hd).mp (hbound n)
    exact ⟨hbnd.trans (min_le_left _ _),
      hbnd.trans ((min_le_right _ _).trans (min_le_left _ _)),
      hbnd.trans ((min_le_right _ _).trans (min_le_right _ _))⟩

/-- The minimum-distance pair can be fixed on a true subsequence.
The remaining label is kept explicit, with no collision-chart input. -/
theorem triple_minimum_pair_subsequence (q : ℕ → SatelliteConfiguration)
    (a b c : Satellite) :
    ∃ (phi : ℕ → ℕ) (u v w : Satellite),StrictMono phi ∧
      ((u=a ∧ v=b ∧ w=c) ∨ (u=a ∧ v=c ∧ w=b) ∨ (u=b ∧ v=c ∧ w=a)) ∧
      ∀ n,satelliteDistance (q (phi n)) u v=tripleShortestDistance (q (phi n)) a b c := by
  classical
  have hex (n : ℕ) : ∃ k : Fin 3,
      (![satelliteDistance (q n) a b,satelliteDistance (q n) a c,satelliteDistance (q n) b c] : Fin 3 → ℝ) k=
        tripleShortestDistance (q n) a b c := by
    by_cases h1 : satelliteDistance (q n) a b≤min (satelliteDistance (q n) a c) (satelliteDistance (q n) b c)
    · exact ⟨0,(min_eq_left h1).symm⟩
    · by_cases h2 : satelliteDistance (q n) a c≤satelliteDistance (q n) b c
      · exact ⟨1,by rw [tripleShortestDistance,min_eq_right (le_of_not_ge h1),min_eq_left h2]; rfl⟩
      · exact ⟨2,by rw [tripleShortestDistance,min_eq_right (le_of_not_ge h1),
          min_eq_right (le_of_not_ge h2)]; rfl⟩
  choose k hk using hex
  obtain ⟨j,hj⟩ := Finite.exists_infinite_fiber k
  obtain ⟨phi,hphi,hval⟩ := Nat.exists_strictMono_subsequence (P := fun n => k n=j) (by
    intro N
    obtain ⟨n,hn,hN⟩ := (Set.infinite_coe_iff.mp hj).exists_gt N
    exact ⟨n,hN,hn⟩)
  have he (n : ℕ) := hk (phi n)
  simp only [hval] at he
  fin_cases j
  · exact ⟨phi,a,b,c,hphi,Or.inl ⟨rfl,rfl,rfl⟩,he⟩
  · exact ⟨phi,a,c,b,hphi,Or.inr (Or.inl ⟨rfl,rfl,rfl⟩),he⟩
  · exact ⟨phi,b,c,a,hphi,Or.inr (Or.inr ⟨rfl,rfl,rfl⟩),he⟩

end DominantFiveBody
