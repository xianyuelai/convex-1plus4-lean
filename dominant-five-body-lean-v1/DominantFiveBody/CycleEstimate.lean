import DominantFiveBody.CoorbitalModel
import DominantFiveBody.WeightedHessian

/-!
# The actual finite circulation estimate in Lemma 2.1

For at most four vertices, we use an explicit decomposition into supported
triangles and the ordered quadrilateral. This is a finite proof of the same
balanced-flow argument, not an assumption of its conclusion.
-/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody.Coorbital

def angularEquation {n : ℕ} (mass theta : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, mass j * coorbitalKernel (theta j - theta i)

def angularFlow {n : ℕ} (mass theta : Fin n → ℝ) (i j : Fin n) : ℝ :=
  mass i * mass j * coorbitalKernel (theta j - theta i)

/-- In the four-source model, keeping a zero diagonal or erasing it gives
exactly the same physical divided equations. -/
theorem angularEquation_eq_coorbitalResidual (mass theta : Satellite → ℝ) (i : Satellite) :
    angularEquation mass theta i = coorbitalResidual mass theta i := by
  simp [angularEquation, coorbitalResidual, Finset.sum_erase_eq_sub]

@[simp] theorem angularFlow_self {n : ℕ} (mass theta : Fin n → ℝ) (i : Fin n) :
    angularFlow mass theta i i = 0 := by simp [angularFlow]

theorem angularFlow_reverse {n : ℕ} (mass theta : Fin n → ℝ) (i j : Fin n) :
    angularFlow mass theta j i = -angularFlow mass theta i j := by
  unfold angularFlow
  rw [show theta i - theta j = -(theta j - theta i) by ring, coorbitalKernel_neg]
  ring

/-- Actual angular equations imply vertex balance, without any mass division. -/
theorem angularFlow_balanced {n : ℕ} (mass theta : Fin n → ℝ)
    (hroot : ∀ i, angularEquation mass theta i = 0) (i : Fin n) :
    (∑ j, angularFlow mass theta i j) = 0 := by
  simpa only [angularFlow, angularEquation, Finset.mul_sum, mul_assoc, mul_zero]
    using congrArg (fun x => mass i * x) (hroot i)

theorem kernelF_nonneg_of_le_h {t : ℝ} (ht : 0 < t) (hth : t ≤ h) :
    0 ≤ kernelF t := by
  rcases lt_or_eq_of_le hth with hlt | heq
  · exact (kernelF_pos_on_short_arc ht hlt).le
  · rw [heq, kernelF_h]

theorem kernelF_nonpos_of_h_le {t : ℝ} (hht : h ≤ t) (htpi : t < Real.pi) :
    kernelF t ≤ 0 := by
  rcases lt_or_eq_of_le hht with hlt | heq
  · exact (kernelF_neg_on_long_arc hlt htpi).le
  · rw [← heq, kernelF_h]

theorem angularFlow_positive_formula {n : ℕ} (mass theta : Fin n → ℝ)
    (i j : Fin n) (ht : 0 < theta j - theta i) :
    angularFlow mass theta i j = mass i * mass j * kernelF (theta j - theta i) := by
  rw [angularFlow, coorbitalKernel_eq_positive_formula _ ht.le]

theorem angularFlow_pos {n : ℕ} (mass theta : Fin n → ℝ)
    (hm : ∀ i, 0 < mass i) (i j : Fin n)
    (ht : 0 < theta j - theta i) (hth : theta j - theta i < h) :
    0 < angularFlow mass theta i j := by
  rw [angularFlow_positive_formula mass theta i j ht]
  exact mul_pos (mul_pos (hm i) (hm j)) (kernelF_pos_on_short_arc ht hth)

theorem angularFlow_neg {n : ℕ} (mass theta : Fin n → ℝ)
    (hm : ∀ i, 0 < mass i) (i j : Fin n)
    (ht : 0 < theta j - theta i) (hht : h < theta j - theta i)
    (htpi : theta j - theta i < Real.pi) :
    angularFlow mass theta i j < 0 := by
  rw [angularFlow_positive_formula mass theta i j ht]
  exact mul_neg_of_pos_of_neg (mul_pos (hm i) (hm j)) (kernelF_neg_on_long_arc hht htpi)

theorem angularFlow_nonneg {n : ℕ} (mass theta : Fin n → ℝ)
    (hm : ∀ i, 0 < mass i) (i j : Fin n)
    (ht : 0 < theta j - theta i) (hth : theta j - theta i ≤ h) :
    0 ≤ angularFlow mass theta i j := by
  rw [angularFlow_positive_formula mass theta i j ht]
  exact mul_nonneg (mul_pos (hm i) (hm j)).le (kernelF_nonneg_of_le_h ht hth)

theorem angularFlow_nonpos {n : ℕ} (mass theta : Fin n → ℝ)
    (hm : ∀ i, 0 < mass i) (i j : Fin n)
    (ht : 0 < theta j - theta i) (hht : h ≤ theta j - theta i)
    (htpi : theta j - theta i < Real.pi) :
    angularFlow mass theta i j ≤ 0 := by
  rw [angularFlow_positive_formula mass theta i j ht]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_pos (hm i) (hm j)).le
    (kernelF_nonpos_of_h_le hht htpi)

/-- Weighted Cauchy--Schwarz for the two right edges of a triangle.
All three denominators are proved positive before clearing them. -/
theorem two_denominator_cauchy (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (u + v) ^ 2 / (a + b) ≤ u ^ 2 / a + v ^ 2 / b := by
  have hab : 0 < a + b := add_pos ha hb
  apply (div_le_iff₀ hab).mpr
  field_simp
  nlinarith [sq_nonneg (b * u - a * v)]

theorem two_denominator_cauchy_gap (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b) :
    u^2/a + v^2/b - (u+v)^2/(a+b) = (b*u-a*v)^2/(a*b*(a+b)) := by
  field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt (add_pos ha hb)]
  ring

/-- The equality condition in the weighted Cauchy step is exact. -/
theorem two_denominator_cauchy_eq_iff (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (u+v)^2/(a+b) = u^2/a + v^2/b ↔ b*u = a*v := by
  have hgap := two_denominator_cauchy_gap a b u v ha hb
  have hd : a*b*(a+b) ≠ 0 := ne_of_gt (mul_pos (mul_pos ha hb) (add_pos ha hb))
  constructor
  · intro heq
    have hs : (b*u-a*v)^2/(a*b*(a+b)) = 0 := by linarith
    have hs' : (b*u-a*v)^2 = 0 := (div_eq_zero_iff.mp hs).resolve_right hd
    nlinarith
  · intro heq
    have hs : (b*u-a*v)^2/(a*b*(a+b)) = 0 := by simp [sub_eq_zero.mpr heq]
    linarith

/-- The length restriction in `lem:cycle` gives the nonnegative triangle form. -/
theorem two_edge_cycle_nonneg (s t u v : ℝ)
    (hs : s < h) (ht : t < h) (hspan : s + t < Real.pi) :
    0 ≤ u ^ 2 / (h - s) + v ^ 2 / (h - t) - (u + v) ^ 2 / (Real.pi - (s + t)) := by
  have ha : 0 < h - s := sub_pos.mpr hs
  have hb : 0 < h - t := sub_pos.mpr ht
  have hc : 0 < Real.pi - (s + t) := sub_pos.mpr hspan
  have habc : (h - s) + (h - t) ≤ Real.pi - (s + t) := by
    unfold h
    linarith [Real.pi_pos]
  have hfirst := two_denominator_cauchy (h - s) (h - t) u v ha hb
  have hsecond := div_le_div_of_nonneg_left (sq_nonneg (u + v)) (add_pos ha hb) habc
  linarith

/-- A supported three-edge cycle has equality only when all increments vanish:
`2h < π` makes its denominator comparison strict. -/
theorem two_edge_cycle_eq_zero_iff (s t u v : ℝ)
    (hs : s < h) (ht : t < h) (hspan : s+t < Real.pi) :
    u^2/(h-s) + v^2/(h-t) - (u+v)^2/(Real.pi-(s+t)) = 0 ↔ u=0 ∧ v=0 := by
  have ha : 0 < h-s := sub_pos.mpr hs
  have hb : 0 < h-t := sub_pos.mpr ht
  have hc : 0 < Real.pi-(s+t) := sub_pos.mpr hspan
  have hden : (h-s)+(h-t) < Real.pi-(s+t) := by unfold h; linarith [Real.pi_pos]
  constructor
  · intro heq
    have hfirst := two_denominator_cauchy (h-s) (h-t) u v ha hb
    have huv : u+v=0 := by
      by_contra hne
      have hsq : 0 < (u+v)^2 := sq_pos_of_ne_zero hne
      have hstrict := div_lt_div_of_pos_left hsq (add_pos ha hb) hden
      linarith
    have hterms : u^2/(h-s)+v^2/(h-t)=0 := by rw [huv] at heq; simpa using heq
    have hu : u^2/(h-s)=0 := le_antisymm
      (by linarith [div_nonneg (sq_nonneg v) hb.le]) (div_nonneg (sq_nonneg u) ha.le)
    have hu' : u^2=0 := (div_eq_zero_iff.mp hu).resolve_right (ne_of_gt ha)
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨rfl,rfl⟩
    simp

/-- The three right edges of the ordered quadrilateral use `3h=π` exactly. -/
theorem three_edge_cycle_nonneg (s t r u v w : ℝ)
    (hs : s < h) (ht : t < h) (hr : r < h) (_hspan : s + t + r < Real.pi) :
    0 ≤ u ^ 2 / (h - s) + v ^ 2 / (h - t) + w ^ 2 / (h - r) -
      (u + v + w) ^ 2 / (Real.pi - (s + t + r)) := by
  have ha : 0 < h - s := sub_pos.mpr hs
  have hb : 0 < h - t := sub_pos.mpr ht
  have hc : 0 < h - r := sub_pos.mpr hr
  have hfirst := two_denominator_cauchy (h - s) (h - t) u v ha hb
  have hsecond := two_denominator_cauchy ((h - s) + (h - t)) (h - r) (u + v) w
    (add_pos ha hb) hc
  have hden : (h - s) + (h - t) + (h - r) = Real.pi - (s + t + r) := by
    unfold h
    ring
  rw [hden] at hsecond
  linarith

/-- For a four-edge cycle, equality means that all rightward increments
have the same increment-to-deficit ratio. -/
theorem three_edge_cycle_eq_zero_iff (s t r u v w : ℝ)
    (hs : s<h) (ht : t<h) (hr : r<h) :
    u^2/(h-s)+v^2/(h-t)+w^2/(h-r) -
      (u+v+w)^2/(Real.pi-(s+t+r)) = 0 ↔
      (h-t)*u=(h-s)*v ∧ (h-r)*(u+v)=((h-s)+(h-t))*w := by
  have ha : 0<h-s := sub_pos.mpr hs
  have hb : 0<h-t := sub_pos.mpr ht
  have hc : 0<h-r := sub_pos.mpr hr
  have hab := add_pos ha hb
  have hden : (h-s)+(h-t)+(h-r)=Real.pi-(s+t+r) := by unfold h; ring
  have hnonneg1 := two_denominator_cauchy (h-s) (h-t) u v ha hb
  have hnonneg2 := two_denominator_cauchy ((h-s)+(h-t)) (h-r) (u+v) w hab hc
  have heq1 := two_denominator_cauchy_eq_iff (h-s) (h-t) u v ha hb
  have heq2 := two_denominator_cauchy_eq_iff ((h-s)+(h-t)) (h-r) (u+v) w hab hc
  rw [← hden]
  constructor
  · intro heq
    have h1 : (u+v)^2/((h-s)+(h-t))=u^2/(h-s)+v^2/(h-t) := by linarith
    have h2 : ((u+v)+w)^2/(((h-s)+(h-t))+(h-r))=
        (u+v)^2/((h-s)+(h-t))+w^2/(h-r) := by linarith
    exact ⟨heq1.mp h1, heq2.mp h2⟩
  · rintro ⟨h1,h2⟩
    have H1 := heq1.mpr h1
    have H2 := heq2.mpr h2
    linarith

/-- The six physical flows obey the three cut balances. -/
theorem four_flow_balance (mass theta : Fin 4 → ℝ)
    (hroot : ∀ i, angularEquation mass theta i = 0) :
    angularFlow mass theta 0 1 + angularFlow mass theta 0 2 +
      angularFlow mass theta 0 3 = 0 ∧
    -angularFlow mass theta 0 1 + angularFlow mass theta 1 2 +
      angularFlow mass theta 1 3 = 0 ∧
    -angularFlow mass theta 0 2 - angularFlow mass theta 1 2 +
      angularFlow mass theta 2 3 = 0 := by
  have h0 := angularFlow_balanced mass theta hroot 0
  have h1 := angularFlow_balanced mass theta hroot 1
  have h2 := angularFlow_balanced mass theta hroot 2
  simp only [Fin.sum_univ_four, angularFlow_self, zero_add, add_zero] at h0 h1 h2
  rw [angularFlow_reverse mass theta 0 1] at h1
  rw [angularFlow_reverse mass theta 0 2, angularFlow_reverse mass theta 1 2] at h2
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Root equations give the length restriction, rather than assuming it for
the proposed cycle decomposition. -/
theorem four_root_gaps (mass theta : Fin 4 → ℝ)
    (hm : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, angularEquation mass theta i = 0) :
    theta 1 - theta 0 < h ∧ theta 2 - theta 1 < h ∧
    theta 3 - theta 2 < h ∧ h < theta 3 - theta 0 := by
  obtain ⟨h0,h1,h2⟩ := four_flow_balance mass theta hroot
  have h01 := harc 0 1 (by decide)
  have h02 := harc 0 2 (by decide)
  have h03 := harc 0 3 (by decide)
  have h12 := harc 1 2 (by decide)
  have h13 := harc 1 3 (by decide)
  have h23 := harc 2 3 (by decide)
  have ha : theta 1 - theta 0 < h := by
    by_contra hh
    have ha := angularFlow_nonpos mass theta hm 0 1 h01.1 (by linarith) h01.2
    have hd := angularFlow_neg mass theta hm 0 2 h02.1 (by linarith) h02.2
    have hf := angularFlow_neg mass theta hm 0 3 h03.1 (by linarith) h03.2
    linarith
  have hb : theta 2 - theta 1 < h := by
    by_contra hh
    have hb := angularFlow_nonpos mass theta hm 1 2 h12.1 (by linarith) h12.2
    have hd := angularFlow_neg mass theta hm 0 2 h02.1 (by linarith) h02.2
    have he := angularFlow_neg mass theta hm 1 3 h13.1 (by linarith) h13.2
    have hf := angularFlow_neg mass theta hm 0 3 h03.1 (by linarith) h03.2
    linarith
  have hc : theta 3 - theta 2 < h := by
    by_contra hh
    have hc := angularFlow_nonpos mass theta hm 2 3 h23.1 (by linarith) h23.2
    have he := angularFlow_neg mass theta hm 1 3 h13.1 (by linarith) h13.2
    have hf := angularFlow_neg mass theta hm 0 3 h03.1 (by linarith) h03.2
    linarith
  have hL : h < theta 3 - theta 0 := by
    by_contra hh
    have ha := angularFlow_pos mass theta hm 0 1 h01.1 ha
    have hd := angularFlow_nonneg mass theta hm 0 2 h02.1 (by linarith)
    have hf := angularFlow_nonneg mass theta hm 0 3 h03.1 (by linarith)
    linarith
  exact ⟨ha,hb,hc,hL⟩

/-- The signed finite decomposition, including zero diagonal flows. Each
inequality is required only when that supported cycle has positive flow. -/
theorem balanced_four_energy_nonneg
    (A B C D E F x01 x12 x23 x02 x13 x03 : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hF : F ≤ 0)
    (h0 : A + D + F = 0) (h1 : -A + B + E = 0) (h2 : -D - B + C = 0)
    (h012 : D < 0 → 0 ≤ x01 + x12 - x02)
    (h123 : E < 0 → 0 ≤ x12 + x23 - x13)
    (h023 : 0 < D → 0 ≤ x02 + x23 - x03)
    (h013 : 0 < E → 0 ≤ x01 + x13 - x03)
    (h0123 : 0 ≤ x01 + x12 + x23 - x03) :
    0 ≤ A*x01 + B*x12 + C*x23 + D*x02 + E*x13 + F*x03 := by
  have hDpos : 0 ≤ D → 0 ≤ D * (x02 + x23 - x03) := by
    intro hD
    rcases lt_or_eq_of_le hD with h | h
    · exact mul_nonneg h.le (h023 h)
    · rw [← h, zero_mul]
  have hEpos : 0 ≤ E → 0 ≤ E * (x01 + x13 - x03) := by
    intro hE
    rcases lt_or_eq_of_le hE with h | h
    · exact mul_nonneg h.le (h013 h)
    · rw [← h, zero_mul]
  rcases le_or_gt 0 D with hD | hD <;> rcases le_or_gt 0 E with hE | hE
  · have h := add_nonneg (add_nonneg (hDpos hD) (hEpos hE)) (mul_nonneg hB h0123)
    have heq : A*x01 + B*x12 + C*x23 + D*x02 + E*x13 + F*x03 =
        D*(x02+x23-x03) + E*(x01+x13-x03) + B*(x01+x12+x23-x03) := by
      have : A = B+E := by linarith
      have : C = D+B := by linarith
      have : F = -(B+E+D) := by linarith
      rw [‹A = B+E›, ‹C = D+B›, ‹F = -(B+E+D)›]; ring
    rwa [heq]
  · have h := add_nonneg (add_nonneg (hDpos hD)
      (mul_nonneg (neg_nonneg.mpr hE.le) (h123 hE))) (mul_nonneg hA h0123)
    have heq : A*x01 + B*x12 + C*x23 + D*x02 + E*x13 + F*x03 =
        D*(x02+x23-x03) + (-E)*(x12+x23-x13) + A*(x01+x12+x23-x03) := by
      have : B = A-E := by linarith
      have : C = D+A-E := by linarith
      have : F = -(A+D) := by linarith
      rw [‹B = A-E›, ‹C = D+A-E›, ‹F = -(A+D)›]; ring
    rwa [heq]
  · have h := add_nonneg (add_nonneg (mul_nonneg (neg_nonneg.mpr hD.le) (h012 hD))
      (hEpos hE)) (mul_nonneg hC h0123)
    have heq : A*x01 + B*x12 + C*x23 + D*x02 + E*x13 + F*x03 =
        (-D)*(x01+x12-x02) + E*(x01+x13-x03) + C*(x01+x12+x23-x03) := by
      have : B = C-D := by linarith
      have : A = C-D+E := by linarith
      have : F = -(C+E) := by linarith
      rw [‹A = C-D+E›, ‹B = C-D›, ‹F = -(C+E)›]; ring
    rwa [heq]
  · have h := add_nonneg (add_nonneg (mul_nonneg (neg_nonneg.mpr hD.le) (h012 hD))
      (mul_nonneg (neg_nonneg.mpr hE.le) (h123 hE))) (mul_nonneg (neg_nonneg.mpr hF) h0123)
    have heq : A*x01 + B*x12 + C*x23 + D*x02 + E*x13 + F*x03 =
        (-D)*(x01+x12-x02) + (-E)*(x12+x23-x13) + (-F)*(x01+x12+x23-x03) := by
      have : A = -D-F := by linarith
      have : B = -D-F-E := by linarith
      have : C = -F-E := by linarith
      rw [‹A = -D-F›, ‹B = -D-F-E›, ‹C = -F-E›]; ring
    rwa [heq]

/-- The relevant denominator is selected by the physical kernel sign. -/
def cycleDenominator (t : ℝ) : ℝ := if t < h then h-t else Real.pi-t

theorem slopeCoefficient_eq_kernel_div (t : ℝ) :
    slopeCoefficient t = kernelF t / cycleDenominator t := by
  unfold slopeCoefficient cycleDenominator
  split_ifs with hlt heq
  · rfl
  · rw [heq, kernelF_h, zero_div]
  · rfl

def coorbitalSlopeForm {n : ℕ} (mass theta u : Fin n → ℝ) : ℝ :=
  weightedAngleForm mass (fun i j => slopeCoefficient (theta j - theta i)) u

theorem coorbitalSlopeForm_eq_flow {n : ℕ} (mass theta u : Fin n → ℝ)
    (harc : ∀ i j, i < j → 0 < theta j-theta i) :
    coorbitalSlopeForm mass theta u = pairForm
      (fun i j => angularFlow mass theta i j / cycleDenominator (theta j-theta i)) u := by
  unfold coorbitalSlopeForm weightedAngleForm pairForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · dsimp only
    rw [slopeCoefficient_eq_kernel_div,
      angularFlow_positive_formula mass theta i j (harc i j hij)]
    ring
  · rfl

theorem coorbitalKappaForm_sub_remainder {n : ℕ} (mass theta u : Fin n → ℝ) :
    coorbitalKappaForm mass theta u - coorbitalRemainderForm mass theta u =
      coorbitalSlopeForm mass theta u := by
  unfold coorbitalKappaForm coorbitalRemainderForm coorbitalSlopeForm
    weightedAngleForm pairForm positiveRemainder
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

theorem angularFlow_pos_iff {n : ℕ} (mass theta : Fin n → ℝ)
    (hm : ∀ i, 0 < mass i) (i j : Fin n)
    (ht : 0 < theta j-theta i) (htpi : theta j-theta i < Real.pi) :
    0 < angularFlow mass theta i j ↔ theta j-theta i < h := by
  constructor
  · intro hf
    by_contra hh
    have := angularFlow_nonpos mass theta hm i j ht (le_of_not_gt hh) htpi
    linarith
  · exact angularFlow_pos mass theta hm i j ht

theorem angularFlow_neg_iff {n : ℕ} (mass theta : Fin n → ℝ)
    (hm : ∀ i, 0 < mass i) (i j : Fin n)
    (ht : 0 < theta j-theta i) (htpi : theta j-theta i < Real.pi) :
    angularFlow mass theta i j < 0 ↔ h < theta j-theta i := by
  constructor
  · intro hf
    by_contra hh
    have := angularFlow_nonneg mass theta hm i j ht (le_of_not_gt hh)
    linarith
  · intro hh
    exact angularFlow_neg mass theta hm i j ht hh htpi

theorem triangle_cycle_nonneg (a b c x y z : ℝ)
    (hab : b-a < h) (hbc : c-b < h) (hac : c-a < Real.pi) :
    0 ≤ (y-x)^2/(h-(b-a)) + (z-y)^2/(h-(c-b)) -
      (z-x)^2/(Real.pi-(c-a)) := by
  convert two_edge_cycle_nonneg (b-a) (c-b) (y-x) (z-y) hab hbc
    (by linarith) using 1; ring

theorem quadrilateral_cycle_nonneg (a b c d x y z w : ℝ)
    (hab : b-a < h) (hbc : c-b < h) (hcd : d-c < h) (had : d-a < Real.pi) :
    0 ≤ (y-x)^2/(h-(b-a)) + (z-y)^2/(h-(c-b)) +
      (w-z)^2/(h-(d-c)) - (w-x)^2/(Real.pi-(d-a)) := by
  convert three_edge_cycle_nonneg (b-a) (c-b) (d-c) (y-x) (z-y) (w-z)
    hab hbc hcd (by linarith) using 1; ring

set_option maxHeartbeats 800000 in
/-- The real four-satellite circulation estimate. No cycle bound or positive
weight conclusion is supplied as an input. -/
theorem four_coorbitalSlopeForm_nonneg (mass theta u : Fin 4 → ℝ)
    (hm : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j-theta i ∧ theta j-theta i < Real.pi)
    (hroot : ∀ i, angularEquation mass theta i = 0) :
    0 ≤ coorbitalSlopeForm mass theta u := by
  obtain ⟨ha,hb,hc,hL⟩ := four_root_gaps mass theta hm harc hroot
  obtain ⟨h0,h1,h2⟩ := four_flow_balance mass theta hroot
  have h01 := harc 0 1 (by decide)
  have h02 := harc 0 2 (by decide)
  have h03 := harc 0 3 (by decide)
  have h12 := harc 1 2 (by decide)
  have h13 := harc 1 3 (by decide)
  have h23 := harc 2 3 (by decide)
  have hDpos := angularFlow_pos_iff mass theta hm 0 2 h02.1 h02.2
  have hEpos := angularFlow_pos_iff mass theta hm 1 3 h13.1 h13.2
  have hDneg := angularFlow_neg_iff mass theta hm 0 2 h02.1 h02.2
  have hEneg := angularFlow_neg_iff mass theta hm 1 3 h13.1 h13.2
  have hden01 : cycleDenominator (theta 1-theta 0) = h-(theta 1-theta 0) := by
    simp [cycleDenominator, ha]
  have hden12 : cycleDenominator (theta 2-theta 1) = h-(theta 2-theta 1) := by
    simp [cycleDenominator, hb]
  have hden23 : cycleDenominator (theta 3-theta 2) = h-(theta 3-theta 2) := by
    simp [cycleDenominator, hc]
  have hden03 : cycleDenominator (theta 3-theta 0) = Real.pi-(theta 3-theta 0) := by
    simp [cycleDenominator, not_lt.mpr hL.le]
  have H := balanced_four_energy_nonneg
    (angularFlow mass theta 0 1) (angularFlow mass theta 1 2)
    (angularFlow mass theta 2 3) (angularFlow mass theta 0 2)
    (angularFlow mass theta 1 3) (angularFlow mass theta 0 3)
    ((u 1-u 0)^2/(h-(theta 1-theta 0)))
    ((u 2-u 1)^2/(h-(theta 2-theta 1)))
    ((u 3-u 2)^2/(h-(theta 3-theta 2)))
    ((u 2-u 0)^2/cycleDenominator (theta 2-theta 0))
    ((u 3-u 1)^2/cycleDenominator (theta 3-theta 1))
    ((u 3-u 0)^2/(Real.pi-(theta 3-theta 0)))
    (angularFlow_pos mass theta hm 0 1 h01.1 ha).le
    (angularFlow_pos mass theta hm 1 2 h12.1 hb).le
    (angularFlow_pos mass theta hm 2 3 h23.1 hc).le
    (angularFlow_neg mass theta hm 0 3 h03.1 hL h03.2).le h0 h1 h2
    (by
      intro hd
      have hh := hDneg.mp hd
      simp only [cycleDenominator, if_neg (not_lt.mpr hh.le)]
      exact triangle_cycle_nonneg (theta 0) (theta 1) (theta 2) (u 0) (u 1) (u 2)
        ha hb h02.2)
    (by
      intro he
      have hh := hEneg.mp he
      simp only [cycleDenominator, if_neg (not_lt.mpr hh.le)]
      exact triangle_cycle_nonneg (theta 1) (theta 2) (theta 3) (u 1) (u 2) (u 3)
        hb hc h13.2)
    (by
      intro hd
      have hh := hDpos.mp hd
      simp only [cycleDenominator, if_pos hh]
      exact triangle_cycle_nonneg (theta 0) (theta 2) (theta 3) (u 0) (u 2) (u 3)
        hh hc h03.2)
    (by
      intro he
      have hh := hEpos.mp he
      simp only [cycleDenominator, if_pos hh]
      exact triangle_cycle_nonneg (theta 0) (theta 1) (theta 3) (u 0) (u 1) (u 3)
        ha hh h03.2)
    (quadrilateral_cycle_nonneg (theta 0) (theta 1) (theta 2) (theta 3)
      (u 0) (u 1) (u 2) (u 3) ha hb hc h03.2)
  rw [coorbitalSlopeForm_eq_flow mass theta u (fun i j hij => (harc i j hij).1)]
  simp only [pairForm, Fin.sum_univ_four]
  simp only [Fin.reduceLT, if_true, if_false, zero_add, add_zero]
  rw [hden01, hden12, hden23, hden03]
  convert H using 1; ring


theorem three_flow_balance (mass theta : Fin 3 → ℝ)
    (hroot : ∀ i, angularEquation mass theta i = 0) :
    angularFlow mass theta 0 1 + angularFlow mass theta 0 2 = 0 ∧
    angularFlow mass theta 1 2 = angularFlow mass theta 0 1 := by
  have h0 := angularFlow_balanced mass theta hroot 0
  have h1 := angularFlow_balanced mass theta hroot 1
  simp only [Fin.sum_univ_three, angularFlow_self, zero_add, add_zero] at h0 h1
  rw [angularFlow_reverse mass theta 0 1] at h1
  exact ⟨h0, by linarith⟩

theorem three_root_gaps (mass theta : Fin 3 → ℝ)
    (hm : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j-theta i ∧ theta j-theta i < Real.pi)
    (hroot : ∀ i, angularEquation mass theta i = 0) :
    theta 1-theta 0 < h ∧ theta 2-theta 1 < h ∧ h < theta 2-theta 0 := by
  obtain ⟨h0,h1⟩ := three_flow_balance mass theta hroot
  have h01 := harc 0 1 (by decide)
  have h02 := harc 0 2 (by decide)
  have h12 := harc 1 2 (by decide)
  have ha : theta 1-theta 0 < h := by
    by_contra hh
    have ha := angularFlow_nonpos mass theta hm 0 1 h01.1 (le_of_not_gt hh) h01.2
    have hd := angularFlow_neg mass theta hm 0 2 h02.1 (by linarith) h02.2
    linarith
  have hA := angularFlow_pos mass theta hm 0 1 h01.1 ha
  have hb : theta 2-theta 1 < h :=
    (angularFlow_pos_iff mass theta hm 1 2 h12.1 h12.2).mp (by linarith)
  have hL : h < theta 2-theta 0 :=
    (angularFlow_neg_iff mass theta hm 0 2 h02.1 h02.2).mp (by linarith)
  exact ⟨ha,hb,hL⟩

theorem three_coorbitalSlopeForm_nonneg (mass theta u : Fin 3 → ℝ)
    (hm : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j-theta i ∧ theta j-theta i < Real.pi)
    (hroot : ∀ i, angularEquation mass theta i = 0) :
    0 ≤ coorbitalSlopeForm mass theta u := by
  obtain ⟨ha,hb,hL⟩ := three_root_gaps mass theta hm harc hroot
  obtain ⟨h0,h1⟩ := three_flow_balance mass theta hroot
  have H := mul_nonneg (angularFlow_pos mass theta hm 0 1 (harc 0 1 (by decide)).1 ha).le
    (triangle_cycle_nonneg (theta 0) (theta 1) (theta 2) (u 0) (u 1) (u 2)
      ha hb (harc 0 2 (by decide)).2)
  have h02 : angularFlow mass theta 0 2 = -angularFlow mass theta 0 1 := by linarith
  rw [coorbitalSlopeForm_eq_flow mass theta u (fun i j hij => (harc i j hij).1)]
  simp only [pairForm, Fin.sum_univ_three, Fin.reduceLT, if_true, if_false,
    zero_add, add_zero]
  simp only [cycleDenominator, if_pos ha, if_pos hb, if_neg (not_lt.mpr hL.le), h02, h1]
  convert! H using 1; ring

theorem two_root_separation (mass theta : Fin 2 → ℝ)
    (hm : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j-theta i ∧ theta j-theta i < Real.pi)
    (hroot : ∀ i, angularEquation mass theta i = 0) :
    theta 1-theta 0 = h := by
  have he := hroot 0
  have h01 := harc 0 1 (by decide)
  simp only [angularEquation, Fin.sum_univ_two, sub_self, coorbitalKernel_zero,
    mul_zero, zero_add] at he
  rw [coorbitalKernel_eq_positive_formula _ h01.1.le] at he
  exact (kernelF_eq_zero_iff h01.1 h01.2).mp
    ((mul_eq_zero.mp he).resolve_left (ne_of_gt (hm 1)))

theorem two_coorbitalSlopeForm_nonneg (mass theta u : Fin 2 → ℝ)
    (hm : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j-theta i ∧ theta j-theta i < Real.pi)
    (hroot : ∀ i, angularEquation mass theta i = 0) :
    0 ≤ coorbitalSlopeForm mass theta u := by
  have hh := two_root_separation mass theta hm harc hroot
  simp [coorbitalSlopeForm, weightedAngleForm, pairForm, Fin.sum_univ_two,
    hh, slopeCoefficient]

/-- Equation (2.5), for every satellite count admitted by Lemma 2.1. -/
theorem coorbital_cycle_bound {n : ℕ} (hn₂ : 2 ≤ n) (hn₄ : n ≤ 4)
    (mass theta u : Fin n → ℝ)
    (hm : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j-theta i ∧ theta j-theta i < Real.pi)
    (hroot : ∀ i, angularEquation mass theta i = 0) :
    coorbitalRemainderForm mass theta u ≤ coorbitalKappaForm mass theta u := by
  have H : 0 ≤ coorbitalSlopeForm mass theta u := by
    interval_cases n
    · exact two_coorbitalSlopeForm_nonneg mass theta u hm harc hroot
    · exact three_coorbitalSlopeForm_nonneg mass theta u hm harc hroot
    · exact four_coorbitalSlopeForm_nonneg mass theta u hm harc hroot
  rw [← coorbitalKappaForm_sub_remainder] at H
  linarith

/-- The kernel equations themselves imply strict positivity off rotation. -/
theorem coorbitalKappaForm_pos_at_root {n : ℕ} (hn₂ : 2 ≤ n) (hn₄ : n ≤ 4)
    (mass theta u : Fin n → ℝ)
    (hm : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j-theta i ∧ theta j-theta i < Real.pi)
    (hroot : ∀ i, angularEquation mass theta i = 0)
    (hu : ¬∀ i j, u i = u j) : 0 < coorbitalKappaForm mass theta u :=
  coorbitalKappaForm_pos_of_cycle_bound mass theta u hm harc
    (coorbital_cycle_bound hn₂ hn₄ mass theta u hm harc hroot) hu

theorem coorbitalKappaForm_pos_on_slice_at_root {n : ℕ} (hn₂ : 2 ≤ n) (hn₄ : n ≤ 4)
    (mass theta u : Fin n → ℝ) (p : Fin n)
    (hm : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j-theta i ∧ theta j-theta i < Real.pi)
    (hroot : ∀ i, angularEquation mass theta i = 0) (hp : u p = 0) (hu : u ≠ 0) :
    0 < coorbitalKappaForm mass theta u :=
  coorbitalKappaForm_pos_on_rotation_slice mass theta u p hm harc
    (coorbital_cycle_bound hn₂ hn₄ mass theta u hm harc hroot) hp hu

end DominantFiveBody.Coorbital







