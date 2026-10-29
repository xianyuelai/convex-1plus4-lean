import DominantFiveBody.CycleEstimate

/-! Explicit supported simple-cycle decomposition for the actual four-body
angular circulation, and the two stages of the displayed cycle inequality. -/
noncomputable section
namespace DominantFiveBody.Coorbital

theorem balanced_four_cycle_decomposition (A B C D E F : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hF : F≤0)
    (h0 : A+D+F=0) (h1 : -A+B+E=0) (h2 : -D-B+C=0) :
    ∃ p q r s t : ℝ, 0≤p ∧ 0≤q ∧ 0≤r ∧ 0≤s ∧ 0≤t ∧
      A=p+s+t ∧ B=p+q+t ∧ C=q+r+t ∧ D=r-p ∧ E=s-q ∧ F=-(r+s+t) ∧
      (0<p → D<0) ∧ (0<q → E<0) ∧ (0<r → 0<D) ∧ (0<s → 0<E) := by
  rcases le_or_gt 0 D with hd | hd <;> rcases le_or_gt 0 E with he | he
  · refine ⟨0,0,D,E,B,by positivity,by positivity,hd,he,hB,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro hh) <;> linarith
  · refine ⟨0,-E,D,0,A,by positivity,by linarith,hd,by positivity,hA,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro hh) <;> linarith
  · refine ⟨-D,0,0,E,C,by linarith,by positivity,by positivity,he,hC,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro hh) <;> linarith
  · refine ⟨-D,-E,0,0,-F,by linarith,by linarith,by positivity,by positivity,by linarith,
      ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro hh) <;> linarith

theorem four_angular_cycle_decomposition (mass theta : Fin 4 → ℝ)
    (hm : ∀ i,0<mass i)
    (ha : ∀ i j,i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi)
    (hr : ∀ i,angularEquation mass theta i=0) :
    ∃ p q r s t : ℝ, 0≤p ∧ 0≤q ∧ 0≤r ∧ 0≤s ∧ 0≤t ∧
      angularFlow mass theta 0 1=p+s+t ∧
      angularFlow mass theta 1 2=p+q+t ∧
      angularFlow mass theta 2 3=q+r+t ∧
      angularFlow mass theta 0 2=r-p ∧
      angularFlow mass theta 1 3=s-q ∧
      angularFlow mass theta 0 3=-(r+s+t) ∧
      (0<p → angularFlow mass theta 0 2<0) ∧
      (0<q → angularFlow mass theta 1 3<0) ∧
      (0<r → 0<angularFlow mass theta 0 2) ∧
      (0<s → 0<angularFlow mass theta 1 3) := by
  obtain ⟨h01,h12,h23,h03⟩ := four_root_gaps mass theta hm ha hr
  obtain ⟨hb0,hb1,hb2⟩ := four_flow_balance mass theta hr
  exact balanced_four_cycle_decomposition _ _ _ _ _ _
    (angularFlow_pos mass theta hm 0 1 (ha 0 1 (by decide)).1 h01).le
    (angularFlow_pos mass theta hm 1 2 (ha 1 2 (by decide)).1 h12).le
    (angularFlow_pos mass theta hm 2 3 (ha 2 3 (by decide)).1 h23).le
    (angularFlow_neg mass theta hm 0 3 (ha 0 3 (by decide)).1 h03
      (ha 0 3 (by decide)).2).le hb0 hb1 hb2

theorem two_cycle_display (s t u v : ℝ) (hs : s<h) (ht : t<h) (_hspan : s+t<Real.pi) :
    (u+v)^2/(2*h-(s+t))-(u+v)^2/(Real.pi-(s+t)) ≤
      u^2/(h-s)+v^2/(h-t)-(u+v)^2/(Real.pi-(s+t)) ∧
    0≤(u+v)^2/(2*h-(s+t))-(u+v)^2/(Real.pi-(s+t)) := by
  have hab : (h-s)+(h-t)=2*h-(s+t) := by ring
  have hcs := two_denominator_cauchy (h-s) (h-t) u v (by linarith) (by linarith)
  rw [hab] at hcs
  have hb : 0<2*h-(s+t) := by linarith
  have hd : 2*h-(s+t)≤Real.pi-(s+t) := by unfold h; linarith [Real.pi_pos]
  have hcmp := div_le_div_of_nonneg_left (sq_nonneg (u+v)) hb hd
  exact ⟨by linarith,by linarith⟩

theorem three_cycle_display (s t r u v w : ℝ) (hs : s<h) (ht : t<h) (hr : r<h) :
    (u+v+w)^2/(3*h-(s+t+r))-(u+v+w)^2/(Real.pi-(s+t+r)) ≤
      u^2/(h-s)+v^2/(h-t)+w^2/(h-r)-(u+v+w)^2/(Real.pi-(s+t+r)) ∧
    0≤(u+v+w)^2/(3*h-(s+t+r))-(u+v+w)^2/(Real.pi-(s+t+r)) := by
  have heq : 3*h=Real.pi := by unfold h; ring
  rw [heq,sub_self]
  exact ⟨three_edge_cycle_nonneg s t r u v w hs ht hr (by rw [←heq]; linarith),le_rfl⟩

end DominantFiveBody.Coorbital
