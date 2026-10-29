import DominantFiveBody.PairAreas

/-! # Strict convexity in each actual directed order near a complete pair -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

theorem increasingTriple_fin_five (i j k : Label) (hij : i<j) (hjk : j<k) :
    (i=0 ∧ j=1 ∧ k=2) ∨ (i=0 ∧ j=1 ∧ k=3) ∨ (i=0 ∧ j=1 ∧ k=4) ∨
    (i=0 ∧ j=2 ∧ k=3) ∨ (i=0 ∧ j=2 ∧ k=4) ∨ (i=0 ∧ j=3 ∧ k=4) ∨
    (i=1 ∧ j=2 ∧ k=3) ∨ (i=1 ∧ j=2 ∧ k=4) ∨ (i=1 ∧ j=3 ∧ k=4) ∨
    (i=2 ∧ j=3 ∧ k=4) := by
  revert i j k
  decide

def pairMiddleOrder : HullOrder where
  labels :=
    { toFun := ![0,3,1,2,4]
      invFun := ![0,2,3,1,4]
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by intro i; fin_cases i <;> rfl }
  primary_first := rfl

def pairRightOrder : HullOrder where
  labels :=
    { toFun := ![0,3,4,1,2]
      invFun := ![0,3,4,1,2]
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by intro i; fin_cases i <;> rfl }
  primary_first := rfl

def PairCyclicTriple (i j k : Label) : Prop :=
  ∃ l∈({0,3,4} : Finset Label),
    (i=1 ∧ j=2 ∧ k=l) ∨ (i=2 ∧ j=l ∧ k=1) ∨ (i=l ∧ j=1 ∧ k=2)

theorem PairCyclicTriple.area_pos (x : Configuration) (i j k : Label)
    (h : PairCyclicTriple i j k)
    (hpair : ∀ l∈({0,3,4} : Finset Label), 0<orientedArea x 1 2 l) :
    0<orientedArea x i j k := by
  rcases h with ⟨l,hl,h | h | h⟩
  · rcases h with ⟨hi,hj,hk⟩
    rw [hi,hj,hk]
    exact hpair l hl
  · rcases h with ⟨hi,hj,hk⟩
    rw [hi,hj,hk]
    rw [←orientedArea_cyclic x 1 2 l]
    exact hpair l hl
  · rcases h with ⟨hi,hj,hk⟩
    rw [hi,hj,hk]
    rw [orientedArea_cyclic x l 1 2]
    exact hpair l hl

theorem strictConvex_of_ordered_triple_areas (sigma : HullOrder) (x : Configuration)
    (h : ∀ i j k : Label, i<j → j<k →
      0<orientedArea x (sigma.labels i) (sigma.labels j) (sigma.labels k)) :
    StrictConvexInOrder sigma x := by
  have hs := standardStrictConvex_of_increasing_triples (x ∘ sigma.labels) h
  simpa only [StrictConvexInOrder,standardHullOrder,Equiv.refl_apply,orientedArea,Function.comp_apply] using hs

theorem pairChartArea_joint_continuous (i j k : Label) :
    Continuous (fun v : PairJointVariables =>
      orientedArea (liftRelative (pairChartPoints (v.1 1) (v.1 3) v.2)) i j k) :=
  (orientedArea_continuous i j k).comp (liftRelative_continuous.comp
    (continuous_pi (fun l => (pairChartPoints_joint_contDiff 0 l).continuous)))

theorem pairStrictConvex_neighborhood_of_boundary (sigma : HullOrder) (p alpha omega psi z : ℝ)
    (hz : 0<z) (hpsi0 : psi≠0) (hpsiw : psi≠omega)
    (hpi0 : |psi|<Real.pi) (hpiw : |psi-omega|<Real.pi)
    (hbase : ∀ i j k : Label, i<j → j<k →
      PairCyclicTriple (sigma.labels i) (sigma.labels j) (sigma.labels k) ∨
      0<orientedArea (liftRelative (pairChartPoints 0 alpha (pairUnitPoint omega psi z)))
        (sigma.labels i) (sigma.labels j) (sigma.labels k)) :
    ∀ᶠ v : PairJointVariables in 𝓝 ((![0,0,p,alpha] : Fin 4 → ℝ),pairUnitPoint omega psi z),
      0<v.1 1 → StrictConvexInOrder sigma (liftRelative (pairChartPoints (v.1 1) (v.1 3) v.2)) := by
  have hpair := pairArea_positive_neighborhood p alpha omega psi z hz hpsi0 hpsiw hpi0 hpiw
  have htrip : ∀ᶠ v : PairJointVariables in 𝓝 ((![0,0,p,alpha] : Fin 4 → ℝ),pairUnitPoint omega psi z),
      ∀ i j k : Label, i<j → j<k → 0<v.1 1 →
        0<orientedArea (liftRelative (pairChartPoints (v.1 1) (v.1 3) v.2))
          (sigma.labels i) (sigma.labels j) (sigma.labels k) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro k
    by_cases hij : i<j
    · by_cases hjk : j<k
      · rcases hbase i j k hij hjk with hcyc | hpos
        · filter_upwards [hpair] with v hv
          intro _ _ ht
          exact hcyc.area_pos _ _ _ _ (fun l hl => hv l hl ht)
        · have he := (pairChartArea_joint_continuous (sigma.labels i) (sigma.labels j) (sigma.labels k)).continuousAt
            (x := ((![0,0,p,alpha] : Fin 4 → ℝ),pairUnitPoint omega psi z))
          have hp := he.eventually (Ioi_mem_nhds hpos)
          filter_upwards [hp] with v hv
          exact fun _ _ _ => hv
      · exact Filter.Eventually.of_forall (fun _ _ hk => (hjk hk).elim)
    · exact Filter.Eventually.of_forall (fun _ hi => (hij hi).elim)
  filter_upwards [htrip] with v hv
  intro ht
  exact strictConvex_of_ordered_triple_areas sigma _ (fun i j k hij hjk => hv i j k hij hjk ht)

theorem pairBoundary_left_triples (alpha omega psi z : ℝ)
    (hpsi : psi<0) (homega : 0<omega) (hspan : omega-psi<Real.pi) :
    ∀ i j k : Label, i<j → j<k →
      PairCyclicTriple i j k ∨
      0<orientedArea (liftRelative (pairChartPoints 0 alpha (pairUnitPoint omega psi z))) i j k := by
  have h0c : 0<det2 (polarPoint 1 psi) (polarPoint 1 0) := by
    rw [unit_polar_det]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h0d : 0<det2 (polarPoint 1 psi) (polarPoint 1 omega) := by
    rw [unit_polar_det]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) hspan
  have hcd : 0<det2 (polarPoint 1 0) (polarPoint 1 omega) := by
    rw [unit_polar_det]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hacd := unit_polar_triangle_det_pos psi 0 omega (by linarith) (by linarith) hspan
  intro i j k hij hjk
  rcases increasingTriple_fin_five i j k hij hjk with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
  all_goals rcases ht with ⟨rfl,rfl,rfl⟩
  all_goals simp only [pairChartPoints_at_zero]
  all_goals first
    | exact Or.inl ⟨0,by decide,by decide⟩
    | exact Or.inl ⟨3,by decide,by decide⟩
    | exact Or.inl ⟨4,by decide,by decide⟩
    | solve | right; change 0<det2 (polarPoint 1 psi-0) (polarPoint 1 0-0); simpa using h0c
    | solve | right; change 0<det2 (polarPoint 1 psi-0) (polarPoint 1 omega-0); simpa using h0d
    | solve | right; change 0<det2 (polarPoint 1 0-0) (polarPoint 1 omega-0); simpa using hcd
    | solve | right; exact hacd

theorem pairBoundary_middle_triples (alpha omega psi z : ℝ)
    (hpsi : 0<psi) (hpsiw : psi<omega) (hspan : omega<Real.pi) :
    ∀ i j k : Label, i<j → j<k →
      PairCyclicTriple (pairMiddleOrder.labels i) (pairMiddleOrder.labels j) (pairMiddleOrder.labels k) ∨
      0<orientedArea (liftRelative (pairChartPoints 0 alpha (pairUnitPoint omega psi z)))
        (pairMiddleOrder.labels i) (pairMiddleOrder.labels j) (pairMiddleOrder.labels k) := by
  have h0c : 0<det2 (polarPoint 1 0) (polarPoint 1 psi) := by
    rw [unit_polar_det]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h0d : 0<det2 (polarPoint 1 psi) (polarPoint 1 omega) := by
    rw [unit_polar_det]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcd : 0<det2 (polarPoint 1 0) (polarPoint 1 omega) := by
    rw [unit_polar_det]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcad := unit_polar_triangle_det_pos 0 psi omega (by linarith) (by linarith) (by simpa using hspan)
  intro i j k hij hjk
  rcases increasingTriple_fin_five i j k hij hjk with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
  all_goals rcases ht with ⟨rfl,rfl,rfl⟩
  all_goals simp only [pairChartPoints_at_zero]
  all_goals first
    | exact Or.inl ⟨0,by decide,by decide⟩
    | exact Or.inl ⟨3,by decide,by decide⟩
    | exact Or.inl ⟨4,by decide,by decide⟩
    | solve | right; change 0<det2 (polarPoint 1 0-0) (polarPoint 1 psi-0); simpa using h0c
    | solve | right; change 0<det2 (polarPoint 1 psi-0) (polarPoint 1 omega-0); simpa using h0d
    | solve | right; change 0<det2 (polarPoint 1 0-0) (polarPoint 1 omega-0); simpa using hcd
    | solve | right; exact hcad

theorem pairBoundary_right_triples (alpha omega psi z : ℝ)
    (homega : 0<omega) (hpsiw : omega<psi) (hspan : psi<Real.pi) :
    ∀ i j k : Label, i<j → j<k →
      PairCyclicTriple (pairRightOrder.labels i) (pairRightOrder.labels j) (pairRightOrder.labels k) ∨
      0<orientedArea (liftRelative (pairChartPoints 0 alpha (pairUnitPoint omega psi z)))
        (pairRightOrder.labels i) (pairRightOrder.labels j) (pairRightOrder.labels k) := by
  have h0c : 0<det2 (polarPoint 1 0) (polarPoint 1 psi) := by
    rw [unit_polar_det]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h0d : 0<det2 (polarPoint 1 omega) (polarPoint 1 psi) := by
    rw [unit_polar_det]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcd : 0<det2 (polarPoint 1 0) (polarPoint 1 omega) := by
    rw [unit_polar_det]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcda := unit_polar_triangle_det_pos 0 omega psi (by linarith) (by linarith) (by simpa using hspan)
  intro i j k hij hjk
  rcases increasingTriple_fin_five i j k hij hjk with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
  all_goals rcases ht with ⟨rfl,rfl,rfl⟩
  all_goals simp only [pairChartPoints_at_zero]
  all_goals first
    | exact Or.inl ⟨0,by decide,by decide⟩
    | exact Or.inl ⟨3,by decide,by decide⟩
    | exact Or.inl ⟨4,by decide,by decide⟩
    | solve | right; change 0<det2 (polarPoint 1 0-0) (polarPoint 1 psi-0); simpa using h0c
    | solve | right; change 0<det2 (polarPoint 1 omega-0) (polarPoint 1 psi-0); simpa using h0d
    | solve | right; change 0<det2 (polarPoint 1 0-0) (polarPoint 1 omega-0); simpa using hcd
    | solve | right; exact hcda

def pairBoundaryHullOrder (psi : ℝ) : HullOrder :=
  if psi<0 then standardHullOrder else if psi<Coorbital.h then pairMiddleOrder else pairRightOrder

theorem pairBoundary_hull_triples (alpha psi z : ℝ)
    (hpsi0 : psi≠0) (hpsih : psi≠Coorbital.h) (hspan : twoSourceSpan psi<Real.pi) :
    ∀ i j k : Label, i<j → j<k →
      PairCyclicTriple ((pairBoundaryHullOrder psi).labels i) ((pairBoundaryHullOrder psi).labels j)
        ((pairBoundaryHullOrder psi).labels k) ∨
      0<orientedArea (liftRelative (pairChartPoints 0 alpha (pairUnitPoint Coorbital.h psi z)))
        ((pairBoundaryHullOrder psi).labels i) ((pairBoundaryHullOrder psi).labels j)
        ((pairBoundaryHullOrder psi).labels k) := by
  have hhpos : 0<Coorbital.h := by unfold Coorbital.h; positivity
  have hhpi : Coorbital.h<Real.pi := by unfold Coorbital.h; linarith [Real.pi_pos]
  have hsep := probe_separations_lt_pi hspan
  unfold pairBoundaryHullOrder
  split_ifs with hneg hmid
  · exact pairBoundary_left_triples alpha Coorbital.h psi z hneg hhpos
      (by simpa only [abs_of_neg (by linarith : psi-Coorbital.h<0),neg_sub] using hsep.2)
  · exact pairBoundary_middle_triples alpha Coorbital.h psi z
      (lt_of_le_of_ne (le_of_not_gt hneg) hpsi0.symm) hmid hhpi
  · exact pairBoundary_right_triples alpha Coorbital.h psi z hhpos
      (lt_of_le_of_ne (le_of_not_gt hmid) hpsih.symm)
      (by simpa only [abs_of_nonneg (le_of_not_gt hneg)] using hsep.1)

theorem pairChart_boundary_strictConvex_neighborhood (p alpha psi z : ℝ)
    (hz : 0<z) (hpsi0 : psi≠0) (hpsih : psi≠Coorbital.h) (hspan : twoSourceSpan psi<Real.pi) :
    ∀ᶠ v : PairJointVariables in 𝓝 ((![0,0,p,alpha] : Fin 4 → ℝ),pairUnitPoint Coorbital.h psi z),
      0<v.1 1 → StrictConvexInOrder (pairBoundaryHullOrder psi)
        (liftRelative (pairChartPoints (v.1 1) (v.1 3) v.2)) := by
  have hsep := probe_separations_lt_pi hspan
  exact pairStrictConvex_neighborhood_of_boundary (pairBoundaryHullOrder psi)
    p alpha Coorbital.h psi z hz hpsi0 hpsih hsep.1 hsep.2
    (pairBoundary_hull_triples alpha psi z hpsi0 hpsih hspan)

end DominantFiveBody
