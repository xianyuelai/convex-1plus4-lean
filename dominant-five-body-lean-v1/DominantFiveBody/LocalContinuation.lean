import DominantFiveBody.Residuals
import DominantFiveBody.PotentialDerivatives
import DominantFiveBody.BoundaryJacobian
import DominantFiveBody.CoorbitalHessian
import DominantFiveBody.RelativeAction
import DominantFiveBody.HessianCorrespondence
import DominantFiveBody.PolarCoordinates
import DominantFiveBody.ResidualEquivalence
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The actual seven equations and their parameter implicit function theorem

Source: §3 `eq:R`, `eq:T`, `lem:product`, `prop:local`.
The first angle and the first angular row have the same label. Four radial
rows and three divided angular rows are retained. Parameters are independent
ambient coordinates `(ε, μ)`; positivity/sum constraints are subsequently
imposed on physical applications, never on the smooth extension itself.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

abbrev SliceCoordinates := Fin 7 → ℝ
abbrev ContinuationParameter := ℝ × MassRatio

def sliceRadii (y : SliceCoordinates) : Satellite → ℝ := fun i => y (i.castAdd 3)

/-- The first satellite angle is fixed to zero; the remaining angles are
the last three unknowns, in their original label order. -/
def sliceAngles (y : SliceCoordinates) : Satellite → ℝ :=
  Fin.cases 0 (fun i : Fin 3 => y (i.natAdd 4))

/-- The actual seven divided equations of §3. No satellite mass is divided
out at a zero value: the explicit `Residuals.lean` expressions are retained. -/
def reducedResidual (p : ContinuationParameter) (y : SliceCoordinates) : SliceCoordinates :=
  Fin.append (radialResidual p.1 p.2 (sliceRadii y) (sliceAngles y))
    (fun i : Fin 3 => angularResidual p.1 p.2 (sliceRadii y) (sliceAngles y) i.succ)

def sliceSatellites (y : SliceCoordinates) : SatelliteConfiguration :=
  polarSatellites (sliceRadii y) (sliceAngles y)

/-- The actual denominator hypotheses for the smooth seven-equation map. -/
def SliceRegular (p : ContinuationParameter) (y : SliceCoordinates) : Prop :=
  -1 < p.1 ∧ (∀ i, 0 < sliceRadii y i) ∧
    (∀ i j, i ≠ j → sliceSatellites y i ≠ sliceSatellites y j)

theorem sliceRadii_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun y : SliceCoordinates => sliceRadii y i) := by
  unfold sliceRadii
  fun_prop

theorem sliceAngles_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun y : SliceCoordinates => sliceAngles y i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [sliceAngles, Fin.cases_zero]
    exact contDiff_const
  · simp only [sliceAngles, Fin.cases_succ]
    fun_prop

theorem polarPoint_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun z : ℝ × ℝ => polarPoint z.1 z.2) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff ℝ n (fun z : ℝ × ℝ => z.1 * Real.cos z.2)
    fun_prop
  · change ContDiff ℝ n (fun z : ℝ × ℝ => z.1 * Real.sin z.2)
    fun_prop

theorem sliceSatellites_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun y : SliceCoordinates => sliceSatellites y i) := by
  exact (polarPoint_contDiff n).comp ((sliceRadii_contDiff n i).prodMk (sliceAngles_contDiff n i))

/-- The real pair distance is smooth at every noncollision seven-coordinate
base point, jointly in the independent parameters and unknowns. -/
theorem sliceSatelliteDistance_contDiffAt (n : ℕ∞ω) (p : ContinuationParameter)
    (y : SliceCoordinates) (hreg : SliceRegular p y) (i j : Satellite) (hij : i ≠ j) :
    ContDiffAt ℝ n (fun z : ContinuationParameter × SliceCoordinates =>
      satelliteDistance (sliceSatellites z.2) i j) (p, y) := by
  have hsnd : ContDiff ℝ n (fun z : ContinuationParameter × SliceCoordinates => z.2) := contDiff_snd
  have hi := (sliceSatellites_contDiff n i).comp hsnd
  have hj := (sliceSatellites_contDiff n j).comp hsnd
  exact (hi.sub hj).contDiffAt.norm ℝ (sub_ne_zero.mpr (hreg.2.2 i j hij))

/-- Joint smoothness of the *actual* divided radial rows. -/
theorem radialResidual_joint_contDiffAt (n : ℕ∞ω) (p : ContinuationParameter)
    (y : SliceCoordinates) (hreg : SliceRegular p y) (i : Satellite) :
    ContDiffAt ℝ n (fun z : ContinuationParameter × SliceCoordinates =>
      radialResidual z.1.1 z.1.2 (sliceRadii z.2) (sliceAngles z.2) i) (p, y) := by
  have hsnd : ContDiff ℝ n (fun z : ContinuationParameter × SliceCoordinates => z.2) := contDiff_snd
  have hr (j : Satellite) := ((sliceRadii_contDiff n j).comp hsnd).contDiffAt (x := (p, y))
  have hθ (j : Satellite) := ((sliceAngles_contDiff n j).comp hsnd).contDiffAt (x := (p, y))
  have hq (j : Satellite) := ((sliceSatellites_contDiff n j).comp hsnd).contDiffAt (x := (p, y))
  have hε : ContDiffAt ℝ n (fun z : ContinuationParameter × SliceCoordinates => z.1.1) (p, y) := by
    fun_prop
  have hμ (j : Satellite) :
      ContDiffAt ℝ n (fun z : ContinuationParameter × SliceCoordinates => z.1.2 j) (p, y) := by
    fun_prop
  have hsum : ContDiffAt ℝ n (fun z : ContinuationParameter × SliceCoordinates =>
      ∑ j ∈ Finset.univ.erase i,
        z.1.2 j * (sliceRadii z.2 i - sliceRadii z.2 j *
          Real.cos (sliceAngles z.2 j - sliceAngles z.2 i)) /
          satelliteDistance (sliceSatellites z.2) i j ^ 3) (p, y) := by
    apply ContDiffAt.sum
    intro j hj
    have hne : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    exact ((hμ j).mul ((hr i).sub ((hr j).mul (((hθ j).sub (hθ i)).cos)))).div
      ((sliceSatelliteDistance_contDiffAt n p y hreg i j hne).pow 3)
      (pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hreg.2.2 i j hne))))
  have hX : ContDiffAt ℝ n (fun z : ContinuationParameter × SliceCoordinates =>
      relativeAverage z.1.2 (sliceSatellites z.2)) (p, y) := by
    unfold relativeAverage
    apply ContDiffAt.sum
    intro j _
    exact (hμ j).smul (hq j)
  have he : ContDiffAt ℝ n (fun z : ContinuationParameter × SliceCoordinates =>
      polarPoint 1 (sliceAngles z.2 i)) (p, y) :=
    (polarPoint_contDiff n).contDiffAt.comp _ (contDiffAt_const.prodMk (hθ i))
  have hg := (hr i).sub (((hr i).pow 2).inv (pow_ne_zero 2 (ne_of_gt (hreg.2.1 i))))
  exact (hg.sub (hε.mul hsum)).sub
    ((hε.div (contDiffAt_const.add hε) (ne_of_gt (parameter_denominator_pos _ hreg.1))).mul
      (hX.inner ℝ he))

/-- Joint smoothness of all actual divided angular rows, including ε=0. -/
theorem angularResidual_joint_contDiffAt (n : ℕ∞ω) (p : ContinuationParameter)
    (y : SliceCoordinates) (hreg : SliceRegular p y) (i : Satellite) :
    ContDiffAt ℝ n (fun z : ContinuationParameter × SliceCoordinates =>
      angularResidual z.1.1 z.1.2 (sliceRadii z.2) (sliceAngles z.2) i) (p, y) := by
  have hsnd : ContDiff ℝ n (fun z : ContinuationParameter × SliceCoordinates => z.2) := contDiff_snd
  have hr (j : Satellite) := ((sliceRadii_contDiff n j).comp hsnd).contDiffAt (x := (p, y))
  have hθ (j : Satellite) := ((sliceAngles_contDiff n j).comp hsnd).contDiffAt (x := (p, y))
  have hε : ContDiffAt ℝ n (fun z : ContinuationParameter × SliceCoordinates => z.1.1) (p, y) := by
    fun_prop
  have hμ (j : Satellite) :
      ContDiffAt ℝ n (fun z : ContinuationParameter × SliceCoordinates => z.1.2 j) (p, y) := by
    fun_prop
  unfold angularResidual
  apply ContDiffAt.sum
  intro j hj
  have hne : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
  exact ((((hμ j).mul (hr i)).mul (hr j)).mul (((hθ j).sub (hθ i)).sin)).mul
    ((((sliceSatelliteDistance_contDiffAt n p y hreg i j hne).pow 3).inv
      (pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hreg.2.2 i j hne))))).sub
      ((contDiffAt_const.add hε).inv (ne_of_gt (parameter_denominator_pos _ hreg.1))))

/-- §3 `prop:local`: joint smoothness of the concrete seven-equation map
on an independent ambient parameter neighborhood, including zero ε. -/
theorem reducedResidual_joint_contDiffAt (n : ℕ∞ω) (p : ContinuationParameter)
    (y : SliceCoordinates) (hreg : SliceRegular p y) :
    ContDiffAt ℝ n (fun z : ContinuationParameter × SliceCoordinates => reducedResidual z.1 z.2)
      (p, y) := by
  apply contDiffAt_pi.mpr
  intro i
  refine Fin.addCases (motive := fun k => ContDiffAt ℝ n
    (fun z : ContinuationParameter × SliceCoordinates => reducedResidual z.1 z.2 k) (p, y))
    (fun j : Fin 4 => ?_) (fun j : Fin 3 => ?_) i
  · simpa only [reducedResidual, Fin.append_left] using radialResidual_joint_contDiffAt n p y hreg j
  · simpa only [reducedResidual, Fin.append_right] using angularResidual_joint_contDiffAt n p y hreg j.succ

/-- The actual seven-by-seven derivative, not a Hessian definition. -/
def reducedJacobian (p : ContinuationParameter) (y : SliceCoordinates) :
    SliceCoordinates →L[ℝ] SliceCoordinates :=
  fderiv ℝ (reducedResidual p) y

theorem reducedJacobian_eq_partial (p : ContinuationParameter) (y : SliceCoordinates)
    (hreg : SliceRegular p y) :
    reducedJacobian p y =
      (fderiv ℝ (fun z : ContinuationParameter × SliceCoordinates => reducedResidual z.1 z.2) (p, y)).comp
        (ContinuousLinearMap.inr ℝ ContinuationParameter SliceCoordinates) := by
  have hf := (reducedResidual_joint_contDiffAt 1 p y hreg).differentiableAt (by norm_num)
  have hh : HasFDerivAt (fun z : SliceCoordinates => (p, z))
      (ContinuousLinearMap.inr ℝ ContinuationParameter SliceCoordinates) y := by
    convert! (hasFDerivAt_const p y).prodMk (hasFDerivAt_id y) using 1
  exact (hf.hasFDerivAt.comp y hh).fderiv

theorem radialResidual_at_zero (μ r θ : Satellite → ℝ) (i : Satellite) :
    radialResidual 0 μ r θ i = r i - (r i ^ 2)⁻¹ := by
  simp [radialResidual]

/-- The first four equations really have derivative `3I` at unit radii,
including zero angular columns. This calculation differentiates the
explicit physical divided equation at ε=0. -/
theorem radialResidual_zero_hasFDerivAt (μ : MassRatio) (y : SliceCoordinates)
    (i : Satellite) (hi : sliceRadii y i = 1) :
    HasFDerivAt (fun z : SliceCoordinates =>
      radialResidual 0 μ (sliceRadii z) (sliceAngles z) i)
      (3 • (ContinuousLinearMap.proj (i.castAdd 3) : SliceCoordinates →L[ℝ] ℝ)) y := by
  let L : SliceCoordinates →L[ℝ] ℝ := ContinuousLinearMap.proj (i.castAdd 3)
  have hL : HasFDerivAt (fun z : SliceCoordinates => sliceRadii z i) L y := L.hasFDerivAt
  have hnon : sliceRadii y i ^ 2 ≠ 0 := by rw [hi]; norm_num
  have h := hL.sub ((hasDerivAt_inv hnon).comp_hasFDerivAt y (hL.pow 2))
  convert! h using 1
  · funext z
    exact radialResidual_at_zero μ (sliceRadii z) (sliceAngles z) i
  · ext v
    simp [L, hi, smul_apply, smul_eq_mul]
    ring

/-- Actual upper block of the seven-row Jacobian at ε=0. -/
theorem reducedJacobian_zero_radial_block (μ : MassRatio) (y : SliceCoordinates)
    (hreg : SliceRegular (0, μ) y) (hunit : ∀ i, sliceRadii y i = 1)
    (v : SliceCoordinates) (i : Satellite) :
    reducedJacobian (0, μ) y v (i.castAdd 3) = 3 * sliceRadii v i := by
  have hc : ContDiff ℝ 1 (fun z : SliceCoordinates => (((0 : ℝ), μ), z)) :=
    contDiff_const.prodMk contDiff_id
  have hd : HasFDerivAt (reducedResidual (0, μ)) (reducedJacobian (0, μ) y) y :=
    ((reducedResidual_joint_contDiffAt 1 (0, μ) y hreg).comp y hc.contDiffAt).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hp := (ContinuousLinearMap.proj (i.castAdd 3) : SliceCoordinates →L[ℝ] ℝ).hasFDerivAt.comp y hd
  have hp' : HasFDerivAt (fun z : SliceCoordinates =>
      radialResidual 0 μ (sliceRadii z) (sliceAngles z) i)
      ((ContinuousLinearMap.proj (i.castAdd 3) : SliceCoordinates →L[ℝ] ℝ).comp
        (reducedJacobian (0, μ) y)) y := by
    convert! hp using 1
    funext z
    simp [reducedResidual]
  have he := hp'.unique (radialResidual_zero_hasFDerivAt μ y i (hunit i))
  have hv := congrArg (fun L : SliceCoordinates →L[ℝ] ℝ => L v) he
  simpa [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, sliceRadii] using hv

/-- Insert the three free-angle variations after four zero radial
variations. This is the genuine inclusion used for the lower right block. -/
def sliceAngleInjection : (Fin 3 → ℝ) →L[ℝ] SliceCoordinates :=
  ContinuousLinearMap.pi (fun k => Fin.addCases
    (fun _ : Fin 4 => 0) (fun i : Fin 3 => ContinuousLinearMap.proj i) k)

def sliceFreeAngleProjection : SliceCoordinates →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (i.natAdd 4))

@[simp] theorem sliceAngleInjection_radial (a : Fin 3 → ℝ) (i : Satellite) :
    sliceAngleInjection a (i.castAdd 3) = 0 := by
  simp [sliceAngleInjection]

@[simp] theorem sliceAngleInjection_angular (a : Fin 3 → ℝ) (i : Fin 3) :
    sliceAngleInjection a (i.natAdd 4) = a i := by
  simp [sliceAngleInjection]

@[simp] theorem sliceFreeAngleProjection_apply (v : SliceCoordinates) (i : Fin 3) :
    sliceFreeAngleProjection v i = v (i.natAdd 4) := rfl

def reducedAngularJacobian (p : ContinuationParameter) (y : SliceCoordinates) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  sliceFreeAngleProjection.comp ((reducedJacobian p y).comp sliceAngleInjection)

theorem euclidean_clm_isInvertible_of_injective {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (hi : Function.Injective A) : A.IsInvertible := by
  have hs : Function.Surjective A.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := A.toLinearMap) rfl).mp hi
  let e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    LinearEquiv.ofBijective A.toLinearMap ⟨hi, hs⟩
  let e' : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    { e with
      continuous_toFun := A.continuous
      continuous_invFun := LinearMap.continuous_of_finiteDimensional
        (𝕜 := ℝ) (E := Fin n → ℝ) (F' := Fin n → ℝ) e.symm.toLinearMap }
  exact ⟨e', rfl⟩

/-- The actual seven-row derivative has the paper's block-triangular
invertibility at ε=0. The radial block is proved above; the sole remaining
input is invertibility of the *actual* three-by-three angular block. -/
theorem reducedJacobian_zero_isInvertible_of_angular (μ : MassRatio) (y : SliceCoordinates)
    (hreg : SliceRegular (0, μ) y) (hunit : ∀ i, sliceRadii y i = 1)
    (ha : (reducedAngularJacobian (0, μ) y).IsInvertible) :
    (reducedJacobian (0, μ) y).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  have hk : (∀ v, reducedJacobian (0, μ) y v = 0 → v = 0) →
      Function.Injective (reducedJacobian (0, μ) y) := by
    convert! (LinearMap.ker_eq_bot' (f := (reducedJacobian (0, μ) y).toLinearMap)).symm.trans
      (LinearMap.ker_eq_bot (f := (reducedJacobian (0, μ) y).toLinearMap)) |>.mp using 1
  apply hk
  intro v hv
  have hrad (i : Satellite) : sliceRadii v i = 0 := by
    have h := congrArg (fun z : SliceCoordinates => z (i.castAdd 3)) hv
    rw [reducedJacobian_zero_radial_block μ y hreg hunit v i] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hvinj : sliceAngleInjection (sliceFreeAngleProjection v) = v := by
    funext k
    refine Fin.addCases (motive := fun k =>
      sliceAngleInjection (sliceFreeAngleProjection v) k = v k)
      (fun i : Fin 4 => ?_) (fun i : Fin 3 => ?_) k
    · simpa only [sliceAngleInjection_radial, sliceRadii] using (hrad i).symm
    · simp
  have hang : reducedAngularJacobian (0, μ) y (sliceFreeAngleProjection v) = 0 := by
    simp only [reducedAngularJacobian, ContinuousLinearMap.comp_apply, hvinj, hv, map_zero]
  have hangle : sliceFreeAngleProjection v = 0 :=
    ha.injective (by simpa only [map_zero] using hang)
  rw [← hvinj, hangle, map_zero]

theorem coorbitalKernel_eq_unit_chord (θ : Satellite → ℝ) (harc : OrderedSemicircle θ)
    (i j : Satellite) (hij : i ≠ j) :
    coorbitalKernel (θ j - θ i) = Real.sin (θ j - θ i) *
      ((coorbitalDistance θ i j ^ 3)⁻¹ - 1) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hc := unit_circle_chord (θ i) (θ j) (harc i j hlt).1 (harc i j hlt).2
    rw [coorbitalKernel_eq_positive_formula _ (harc i j hlt).1.le]
    simp only [Coorbital.kernelF, coorbitalDistance, hc, inv_pow]
  · have hc := unit_circle_chord (θ j) (θ i) (harc j i hgt).1 (harc j i hgt).2
    have ht : θ j - θ i = -(θ i - θ j) := by ring
    rw [ht, coorbitalKernel_neg,
      coorbitalKernel_eq_positive_formula _ (harc j i hgt).1.le, Real.sin_neg]
    have hdist : coorbitalDistance θ i j = 2 * Real.sin ((θ i - θ j) / 2) := by
      rw [coorbitalDistance, norm_sub_rev]
      exact hc
    rw [hdist]
    simp only [Coorbital.kernelF, inv_pow, neg_mul]

/-- At unit radii and ε=0 the explicit angular divided equations coincide
with the paper's signed coorbital equations, including negative angle
differences. The chord denominator and odd extension are both checked. -/
theorem angularResidual_zero_unit (μ θ : Satellite → ℝ)
    (harc : OrderedSemicircle θ) (i : Satellite) :
    angularResidual 0 μ (fun _ => 1) θ i = coorbitalResidual μ θ i := by
  unfold angularResidual coorbitalResidual
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
  rw [coorbitalKernel_eq_unit_chord θ harc i j hij]
  have hc : satelliteDistance (polarSatellites (fun _ => 1) θ) i j =
      coorbitalDistance θ i j := by
    simp [satelliteDistance, polarSatellites, polarPoint, coorbitalDistance]
  rw [hc]
  norm_num
  ring

def coorbitalAngleInjection : (Fin 3 → ℝ) →L[ℝ] (Satellite → ℝ) :=
  ContinuousLinearMap.pi (fun i => Fin.cases 0
    (fun j : Fin 3 => ContinuousLinearMap.proj j) i)

def sliceAnglesLinear : SliceCoordinates →L[ℝ] (Satellite → ℝ) :=
  coorbitalAngleInjection.comp sliceFreeAngleProjection

def coorbitalFreeRows : (Satellite → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i.succ)

@[simp] theorem coorbitalAngleInjection_zero (a : Fin 3 → ℝ) :
    coorbitalAngleInjection a 0 = 0 := by simp [coorbitalAngleInjection]

@[simp] theorem coorbitalAngleInjection_succ (a : Fin 3 → ℝ) (i : Fin 3) :
    coorbitalAngleInjection a i.succ = a i := by simp [coorbitalAngleInjection]

@[simp] theorem sliceAnglesLinear_apply (y : SliceCoordinates) :
    sliceAnglesLinear y = sliceAngles y := by
  funext i
  refine Fin.cases ?_ (fun j : Fin 3 => ?_) i <;>
    simp [sliceAnglesLinear, sliceAngles]

theorem sliceAnglesLinear_comp_injection :
    sliceAnglesLinear.comp sliceAngleInjection = coorbitalAngleInjection := by
  ext a i
  refine Fin.cases ?_ (fun j : Fin 3 => ?_) i <;>
    simp [sliceAnglesLinear, coorbitalAngleInjection, sliceFreeAngleProjection]

theorem slice_separatedSemicircle_of_ordered (θ : Satellite → ℝ)
    (harc : OrderedSemicircle θ) : SeparatedSemicircle θ := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · obtain ⟨hpos, hpi⟩ := harc i j hlt
    exact ⟨ne_of_lt (sub_pos.mp hpos), by rwa [abs_of_pos hpos]⟩
  · obtain ⟨hpos, hpi⟩ := harc j i hgt
    exact ⟨ne_of_gt (sub_pos.mp hpos), by rw [abs_sub_comm, abs_of_pos hpos]; exact hpi⟩

/-- The lower right block is the derivative of the actual signed
coorbital residual restricted to the fixed-first-angle slice. The proof
uses an equality on a neighborhood, not merely equality at the root. -/
theorem reducedAngularJacobian_zero_eq (μ : MassRatio) (y : SliceCoordinates)
    (hreg : SliceRegular (0, μ) y) (hunit : ∀ i, sliceRadii y i = 1)
    (harc : OrderedSemicircle (sliceAngles y)) :
    reducedAngularJacobian (0, μ) y = coorbitalFreeRows.comp
      ((angularDifferential μ (sliceAngles y)).comp coorbitalAngleInjection) := by
  have hc : ContDiff ℝ 1 (fun z : SliceCoordinates => (((0 : ℝ), μ), z)) :=
    contDiff_const.prodMk contDiff_id
  have hd : HasFDerivAt (reducedResidual (0, μ)) (reducedJacobian (0, μ) y) y :=
    ((reducedResidual_joint_contDiffAt 1 (0, μ) y hreg).comp y hc.contDiffAt).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hinj : HasFDerivAt (fun a : Fin 3 → ℝ => y + sliceAngleInjection a)
      sliceAngleInjection 0 := by
    simpa using (hasFDerivAt_const y (0 : Fin 3 → ℝ)).add sliceAngleInjection.hasFDerivAt
  have hactual : HasFDerivAt (fun a : Fin 3 → ℝ =>
      sliceFreeAngleProjection (reducedResidual (0, μ) (y + sliceAngleInjection a)))
      (reducedAngularJacobian (0, μ) y) 0 := by
    have hd' : HasFDerivAt (reducedResidual (0, μ)) (reducedJacobian (0, μ) y)
        (y + sliceAngleInjection 0) := by simpa only [map_zero, add_zero] using hd
    convert! sliceFreeAngleProjection.hasFDerivAt.comp 0 (hd'.comp 0 hinj) using 1
  have hangles : HasFDerivAt (fun a : Fin 3 → ℝ =>
      sliceAngles (y + sliceAngleInjection a)) coorbitalAngleInjection 0 := by
    convert! sliceAnglesLinear.hasFDerivAt.comp 0 hinj using 1
    · funext a; exact (sliceAnglesLinear_apply _).symm
    · exact sliceAnglesLinear_comp_injection.symm
  have hco := coorbitalResidual_hasFDerivAt μ (sliceAngles y)
    (slice_separatedSemicircle_of_ordered (sliceAngles y) harc)
  have hco' : HasFDerivAt (fun a : Fin 3 → ℝ =>
      coorbitalFreeRows (fun i => coorbitalResidual μ (sliceAngles (y + sliceAngleInjection a)) i))
      (coorbitalFreeRows.comp ((angularDifferential μ (sliceAngles y)).comp coorbitalAngleInjection)) 0 := by
    have hcoAt : HasFDerivAt (fun angles i => coorbitalResidual μ angles i)
        (angularDifferential μ (sliceAngles y))
        (sliceAngles (y + sliceAngleInjection 0)) := by
      simpa only [map_zero, add_zero] using hco
    convert! coorbitalFreeRows.hasFDerivAt.comp 0 (hcoAt.comp 0 hangles) using 1
  have hnear : ∀ᶠ a : Fin 3 → ℝ in 𝓝 0,
      OrderedSemicircle (sliceAngles (y + sliceAngleInjection a)) := by
    have hbase : OrderedSemicircle (sliceAngles (y + sliceAngleInjection 0)) := by
      simpa only [map_zero, add_zero] using harc
    have h := hangles.continuousAt.tendsto.eventually
      ((isOpen_orderedSemicircle 4).mem_nhds hbase)
    simpa only [map_zero, add_zero] using h
  have heq : (fun a : Fin 3 → ℝ =>
      sliceFreeAngleProjection (reducedResidual (0, μ) (y + sliceAngleInjection a))) =ᶠ[𝓝 0]
      (fun a => coorbitalFreeRows
        (fun i => coorbitalResidual μ (sliceAngles (y + sliceAngleInjection a)) i)) := by
    filter_upwards [hnear] with a ha
    have hr : sliceRadii (y + sliceAngleInjection a) = fun _ => 1 := by
      funext i
      simp [sliceRadii, ← hunit i]
    funext i
    simp only [sliceFreeAngleProjection_apply, reducedResidual, Fin.append_right,
      hr, coorbitalFreeRows, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
    exact angularResidual_zero_unit μ _ ha i.succ
  exact hactual.unique (hco'.congr_of_eventuallyEq heq)

/-- At every strictly positive coorbital root the lower angular block of
the actual seven equations is invertible. The previously proved cycle
estimate supplies its exact constant rotation kernel. -/
theorem reducedAngularJacobian_zero_isInvertible (μ : MassRatio) (y : SliceCoordinates)
    (hreg : SliceRegular (0, μ) y) (hunit : ∀ i, sliceRadii y i = 1)
    (hμ : ∀ i, 0 < μ i) (harc : OrderedSemicircle (sliceAngles y))
    (hroot : ∀ i, coorbitalResidual μ (sliceAngles y) i = 0) :
    (reducedAngularJacobian (0, μ) y).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  have hk : (∀ a, reducedAngularJacobian (0, μ) y a = 0 → a = 0) →
      Function.Injective (reducedAngularJacobian (0, μ) y) := by
    convert! (LinearMap.ker_eq_bot' (f := (reducedAngularJacobian (0, μ) y).toLinearMap)).symm.trans
      (LinearMap.ker_eq_bot (f := (reducedAngularJacobian (0, μ) y).toLinearMap)) |>.mp using 1
  apply hk
  intro a ha
  rw [reducedAngularJacobian_zero_eq μ y hreg hunit harc] at ha
  let u := coorbitalAngleInjection a
  have hrows (j : Fin 3) : angularDifferential μ (sliceAngles y) u j.succ = 0 := by
    have h := congrFun ha j
    simpa [coorbitalFreeRows, u] using h
  have hothers : ∀ i : Satellite, i ≠ 0 → angularDifferential μ (sliceAngles y) u i = 0 := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    simpa only [Fin.succAbove_zero] using hrows j
  have hzero : angularDifferential μ (sliceAngles y) u = 0 := by
    funext i
    by_cases hi : i = 0
    · subst i
      exact angularDifferential_recover_row μ (sliceAngles y) u 0 (hμ 0) hothers
    · exact hothers i hi
  have hconstant := (angularDifferential_kernel_iff_positive μ (sliceAngles y) u hμ harc hroot).mp hzero
  funext j
  have h := hconstant j.succ 0
  simpa [u] using h

theorem coorbitalDistance_pos_of_ordered (θ : Satellite → ℝ)
    (harc : OrderedSemicircle θ) (i j : Satellite) (hij : i ≠ j) :
    0 < coorbitalDistance θ i j := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [coorbitalDistance, unit_circle_chord (θ i) (θ j) (harc i j hlt).1 (harc i j hlt).2]
    exact mul_pos (by norm_num) (Coorbital.sin_half_pos (harc i j hlt).1 (harc i j hlt).2)
  · rw [coorbitalDistance, norm_sub_rev,
      unit_circle_chord (θ j) (θ i) (harc j i hgt).1 (harc j i hgt).2]
    exact mul_pos (by norm_num) (Coorbital.sin_half_pos (harc j i hgt).1 (harc j i hgt).2)

theorem sliceRegular_at_coorbital (μ : MassRatio) (y : SliceCoordinates)
    (hunit : ∀ i, sliceRadii y i = 1) (harc : OrderedSemicircle (sliceAngles y)) :
    SliceRegular (0, μ) y := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro i; rw [hunit i]; norm_num
  · intro i j hij
    have hp := coorbitalDistance_pos_of_ordered (sliceAngles y) harc i j hij
    have heq : coorbitalDistance (sliceAngles y) i j = ‖sliceSatellites y i - sliceSatellites y j‖ := by
      simp [coorbitalDistance, sliceSatellites, polarSatellites, polarPoint, hunit]
    rw [heq] at hp
    intro he
    simp [he] at hp

theorem reducedResidual_at_coorbital_root (μ : MassRatio) (y : SliceCoordinates)
    (hunit : ∀ i, sliceRadii y i = 1) (harc : OrderedSemicircle (sliceAngles y))
    (hroot : ∀ i, coorbitalResidual μ (sliceAngles y) i = 0) :
    reducedResidual (0, μ) y = 0 := by
  have hr : sliceRadii y = fun _ => 1 := funext hunit
  funext k
  refine Fin.addCases (motive := fun k => reducedResidual (0, μ) y k = 0)
    (fun i : Fin 4 => ?_) (fun i : Fin 3 => ?_) k
  · simp [reducedResidual, radialResidual, hunit]
  · simpa only [reducedResidual, Fin.append_right, hr,
      angularResidual_zero_unit μ (sliceAngles y) harc i.succ] using hroot i.succ

/-- The base Jacobian hypothesis is fully discharged for actual positive
coorbital roots: four unit radii, three free angles and exactly the paper's
divided equations. No Hessian or invertibility condition remains assumed. -/
theorem reducedJacobian_at_coorbital_root_isInvertible (μ : MassRatio) (y : SliceCoordinates)
    (hunit : ∀ i, sliceRadii y i = 1) (hμ : ∀ i, 0 < μ i)
    (harc : OrderedSemicircle (sliceAngles y))
    (hroot : ∀ i, coorbitalResidual μ (sliceAngles y) i = 0) :
    (reducedJacobian (0, μ) y).IsInvertible := by
  have hreg := sliceRegular_at_coorbital μ y hunit harc
  exact reducedJacobian_zero_isInvertible_of_angular μ y hreg hunit
    (reducedAngularJacobian_zero_isInvertible μ y hreg hunit hμ harc hroot)

/-- The actual-parameter IFT for the paper's seven equations. Inputs are
the explicitly defined residual root and its actual invertible Jacobian.
The missing coorbital/geometric work must supply that invertibility; this
does not assert it for every mass vector. -/
theorem reducedResidual_local_implicitFunction (p : ContinuationParameter)
    (y : SliceCoordinates) (hreg : SliceRegular p y)
    (hroot : reducedResidual p y = 0) (hJ : (reducedJacobian p y).IsInvertible) :
    ∃ ψ : ContinuationParameter → SliceCoordinates,
      ψ p = y ∧ ContDiffAt ℝ ∞ ψ p ∧
      (∀ᶠ q in 𝓝 p, reducedResidual q (ψ q) = 0) ∧
      (∀ᶠ z : ContinuationParameter × SliceCoordinates in 𝓝 (p, y),
        reducedResidual z.1 z.2 = 0 ↔ ψ z.1 = z.2) := by
  let cdf := reducedResidual_joint_contDiffAt ∞ p y hreg
  have hpartial : (fderiv ℝ (fun z : ContinuationParameter × SliceCoordinates =>
      reducedResidual z.1 z.2) (p, y) ∘L ContinuousLinearMap.inr ℝ ContinuationParameter SliceCoordinates).IsInvertible := by
    rwa [← reducedJacobian_eq_partial p y hreg]
  let ψ := cdf.implicitFunction (by simp) hpartial
  refine ⟨ψ, cdf.implicitFunction_apply_self (by simp) hpartial,
    cdf.contDiffAt_implicitFunction (by simp) hpartial, ?_, ?_⟩
  · simpa only [hroot] using cdf.eventually_apply_implicitFunction (by simp) hpartial
  · simpa only [hroot] using cdf.eventually_apply_eq_iff_implicitFunction (by simp) hpartial

/-- §3 `lem:product`, the single-base step: an actual invertible seven-row
root admits an independent ε-by-mass parameter product and one fixed root
ball. No relation such as ε=o(t) is imposed. Compact-base uniformization
still requires the finite-cover argument across the selected base family. -/
theorem reducedResidual_local_product (p : ContinuationParameter)
    (y : SliceCoordinates) (hreg : SliceRegular p y)
    (hroot : reducedResidual p y = 0) (hJ : (reducedJacobian p y).IsInvertible) :
    ∃ ψ : ContinuationParameter → SliceCoordinates, ∃ η ζ : ℝ,
      0 < η ∧ 0 < ζ ∧ ψ p = y ∧ ContDiffAt ℝ ∞ ψ p ∧
      ∀ ε μ, dist ε p.1 < η → dist μ p.2 < η →
        dist (ψ (ε, μ)) y < ζ ∧ reducedResidual (ε, μ) (ψ (ε, μ)) = 0 ∧
          (∀ z, dist z y < ζ → (reducedResidual (ε, μ) z = 0 ↔ ψ (ε, μ) = z)) := by
  obtain ⟨ψ, hbase, hsmooth, hroots, huniq⟩ :=
    reducedResidual_local_implicitFunction p y hreg hroot hJ
  obtain ⟨a, ha, hrootNear⟩ := Metric.eventually_nhds_iff.mp hroots
  obtain ⟨b, hb, huniqNear⟩ := Metric.eventually_nhds_iff.mp huniq
  have hψnear : ∀ᶠ q in 𝓝 p, dist (ψ q) y < b := by
    have h := hsmooth.continuousAt.tendsto.eventually (Metric.ball_mem_nhds (ψ p) hb)
    simpa only [Metric.mem_ball, hbase] using h
  obtain ⟨c, hc, hψNear⟩ := Metric.eventually_nhds_iff.mp hψnear
  let η : ℝ := min a (min b c)
  refine ⟨ψ, η, b, lt_min ha (lt_min hb hc), hb, hbase, hsmooth, ?_⟩
  intro ε μ hε hμ
  have hq : dist (ε, μ) p < η := by
    simpa only [Prod.dist_eq] using max_lt hε hμ
  have hqa : dist (ε, μ) p < a := lt_of_lt_of_le hq (min_le_left _ _)
  have hqb : dist (ε, μ) p < b :=
    lt_of_lt_of_le hq ((min_le_right _ _).trans (min_le_left _ _))
  have hqc : dist (ε, μ) p < c :=
    lt_of_lt_of_le hq ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨hψNear hqc, hrootNear hqa, ?_⟩
  intro z hz
  apply huniqNear (y := ((ε, μ), z))
  simpa only [Prod.dist_eq] using max_lt hqb hz

/-- The genuine local continuation at every positive-mass coorbital root.
The actual seven-equation base Jacobian has been proved invertible above;
no nondegeneracy, Hessian or inverse is assumed in this statement.
The mass neighborhood is ambient and independent of the ε interval. -/
theorem coorbital_root_local_continuation (μ : MassRatio) (y : SliceCoordinates)
    (hunit : ∀ i, sliceRadii y i = 1) (hμ : PositiveRatio μ)
    (hdomain : CoorbitalAngleDomain (sliceAngles y))
    (hroot : ∀ i, coorbitalResidual μ (sliceAngles y) i = 0) :
    ∃ ψ : ContinuationParameter → SliceCoordinates, ∃ η ζ : ℝ,
      0 < η ∧ 0 < ζ ∧ ψ (0, μ) = y ∧ ContDiffAt ℝ ∞ ψ (0, μ) ∧
      ∀ ε ν, |ε| < η → dist ν μ < η →
        dist (ψ (ε, ν)) y < ζ ∧ reducedResidual (ε, ν) (ψ (ε, ν)) = 0 ∧
          (∀ z, dist z y < ζ → (reducedResidual (ε, ν) z = 0 ↔ ψ (ε, ν) = z)) := by
  have harc := orderedSemicircle_of_coorbitalAngleDomain (sliceAngles y) hdomain
  have hreg := sliceRegular_at_coorbital μ y hunit harc
  have hz := reducedResidual_at_coorbital_root μ y hunit harc hroot
  have hJ := reducedJacobian_at_coorbital_root_isInvertible μ y hunit hμ.1 harc hroot
  obtain ⟨ψ, η, ζ, hη, hζ, hbase, hsmooth, hlocal⟩ :=
    reducedResidual_local_product (0, μ) y hreg hz hJ
  refine ⟨ψ, η, ζ, hη, hζ, hbase, hsmooth, ?_⟩
  intro ε ν hε hν
  apply hlocal ε ν ?_ hν
  simpa only [Real.dist_eq, sub_zero] using hε

def sliceRadiiLinear : SliceCoordinates →L[ℝ] (Satellite → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (i.castAdd 3))

@[simp] theorem sliceRadiiLinear_apply (y : SliceCoordinates) :
    sliceRadiiLinear y = sliceRadii y := rfl

def slicePolarCoordinates : SliceCoordinates →L[ℝ] PolarCoordinates :=
  sliceRadiiLinear.prod sliceAnglesLinear

@[simp] theorem slicePolarCoordinates_apply (y : SliceCoordinates) :
    slicePolarCoordinates y = (sliceRadii y, sliceAngles y) := by
  simp [slicePolarCoordinates]

def sliceAction (p : ContinuationParameter) (y : SliceCoordinates) : ℝ :=
  polarAction p.1 p.2 (slicePolarCoordinates y)

def sliceMassWeights (p : ContinuationParameter) : SliceCoordinates :=
  Fin.append p.2 (fun i : Fin 3 => p.1 * p.2 i.succ)

def sliceWeightedMetric (p : ContinuationParameter) :
    SliceCoordinates →L[ℝ] SliceCoordinates →L[ℝ] ℝ :=
  ∑ i, sliceMassWeights p i •
    ((ContinuousLinearMap.proj i : SliceCoordinates →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj i : SliceCoordinates →L[ℝ] ℝ))

theorem sliceWeightedMetric_apply (p : ContinuationParameter) (u v : SliceCoordinates) :
    sliceWeightedMetric p u v = ∑ i, sliceMassWeights p i * u i * v i := by
  simp only [sliceWeightedMetric, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sliceSatellites_relativeCollisionFree (p : ContinuationParameter) (y : SliceCoordinates)
    (hreg : SliceRegular p y) : RelativeCollisionFree (sliceSatellites y) := by
  refine ⟨?_, hreg.2.2⟩
  intro i
  apply norm_ne_zero_iff.mp
  change ‖polarPoint (sliceRadii y i) (sliceAngles y i)‖ ≠ 0
  rw [polarPoint_norm, abs_of_pos (hreg.2.1 i)]
  exact ne_of_gt (hreg.2.1 i)

theorem isOpen_sliceRegular (p : ContinuationParameter) :
    IsOpen {y : SliceCoordinates | SliceRegular p y} := by
  simp only [SliceRegular, Set.ofPred_and]
  apply IsOpen.inter
  · exact isOpen_lt continuous_const continuous_const
  · apply IsOpen.inter
    · simp only [Set.ofPred_forall]
      apply isOpen_iInter_of_finite
      intro i
      exact isOpen_lt continuous_const (sliceRadii_contDiff 0 i).continuous
    · simp only [Set.ofPred_forall]
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro j
      apply isOpen_iInter_of_finite
      intro _
      exact (isClosed_eq (sliceSatellites_contDiff 0 i).continuous
        (sliceSatellites_contDiff 0 j).continuous).isOpen_compl

/-- Actual first differential of the action on the fixed-first-angle
seven-coordinate slice: precisely the positive diagonal weighted residual.
This follows from the full physical polar differential, including its ε
angular factor, rather than defining the action through the residual. -/
theorem sliceAction_hasFDerivAt (p : ContinuationParameter) (y : SliceCoordinates)
    (hreg : SliceRegular p y) :
    HasFDerivAt (sliceAction p)
      (sliceWeightedMetric p (reducedResidual p y)) y := by
  have hq : RelativeCollisionFree (polarCoordinateMap (slicePolarCoordinates y)) := by
    simpa only [slicePolarCoordinates_apply, polarCoordinateMap, sliceSatellites] using
      sliceSatellites_relativeCollisionFree p y hreg
  have hr : ∀ i, 0 < (slicePolarCoordinates y).1 i := by
    simpa only [slicePolarCoordinates_apply] using hreg.2.1
  have hd := (polarAction_hasFDerivAt p.1 p.2 (slicePolarCoordinates y) hq).comp y
    slicePolarCoordinates.hasFDerivAt
  apply hd.congr_fderiv
  ext v
  rw [ContinuousLinearMap.comp_apply, polarActionDerivative_apply _ _ _ _ hr,
    sliceWeightedMetric_apply]
  simp only [slicePolarCoordinates_apply]
  have hang : (∑ i : Satellite, p.1 * p.2 i *
      angularResidual p.1 p.2 (sliceRadii y) (sliceAngles y) i * sliceAngles v i) =
      ∑ j : Fin 3, p.1 * p.2 j.succ *
        angularResidual p.1 p.2 (sliceRadii y) (sliceAngles y) j.succ * v (j.natAdd 4) := by
    rw [Fin.sum_univ_succ]
    simp [sliceAngles]
  rw [hang]
  rw [Fin.sum_univ_add (a := 4) (b := 3)]
  simp only [sliceMassWeights, reducedResidual, Fin.append_left, Fin.append_right, sliceRadii]

theorem sliceAction_fderiv (p : ContinuationParameter) (y : SliceCoordinates)
    (hreg : SliceRegular p y) :
    fderiv ℝ (sliceAction p) y = sliceWeightedMetric p (reducedResidual p y) :=
  (sliceAction_hasFDerivAt p y hreg).fderiv

/-- The nested, actual second Fréchet differential of Φ on the fixed-angle
slice is the actual residual Jacobian followed by the diagonal row metric.
The first differential is identified throughout a neighborhood before
taking its derivative. -/
theorem sliceAction_second_fderiv (p : ContinuationParameter) (y : SliceCoordinates)
    (hreg : SliceRegular p y) :
    fderiv ℝ (fderiv ℝ (sliceAction p)) y =
      (sliceWeightedMetric p).comp (reducedJacobian p y) := by
  have hc : ContDiff ℝ 1 (fun z : SliceCoordinates => (p, z)) :=
    contDiff_const.prodMk contDiff_id
  have hd : HasFDerivAt (reducedResidual p) (reducedJacobian p y) y :=
    ((reducedResidual_joint_contDiffAt 1 p y hreg).comp y hc.contDiffAt).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hg := (sliceWeightedMetric p).hasFDerivAt.comp y hd
  have hnear : ∀ᶠ z in 𝓝 y, SliceRegular p z := (isOpen_sliceRegular p).mem_nhds hreg
  have heq : fderiv ℝ (sliceAction p) =ᶠ[𝓝 y]
      (fun z => sliceWeightedMetric p (reducedResidual p z)) :=
    hnear.mono (fun z hz => sliceAction_fderiv p z hz)
  exact (hg.congr_of_eventuallyEq heq).fderiv

theorem sliceMassWeights_pos (p : ContinuationParameter) (hε : 0 < p.1)
    (hμ : ∀ i, 0 < p.2 i) (k : Fin 7) : 0 < sliceMassWeights p k := by
  refine Fin.addCases (motive := fun k => 0 < sliceMassWeights p k)
    (fun i : Fin 4 => ?_) (fun i : Fin 3 => ?_) k
  · simpa only [sliceMassWeights, Fin.append_left] using hμ i
  · simpa only [sliceMassWeights, Fin.append_right] using mul_pos hε (hμ i.succ)

/-- All seven row factors are nonzero for actual positive ε and positive
masses. The diagonal bilinear pairing is consequently an isomorphism to
the continuous dual, proved by evaluating it on the coordinate vectors. -/
theorem sliceWeightedMetric_isInvertible (p : ContinuationParameter) (hε : 0 < p.1)
    (hμ : ∀ i, 0 < p.2 i) : (sliceWeightedMetric p).IsInvertible := by
  let _ : FiniteDimensional ℝ (SliceCoordinates →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap : (SliceCoordinates →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      (SliceCoordinates →L[ℝ] ℝ)).finiteDimensional
  have hdim : Module.finrank ℝ SliceCoordinates =
      Module.finrank ℝ (SliceCoordinates →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap : (SliceCoordinates →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      (SliceCoordinates →L[ℝ] ℝ)).finrank_eq]
    exact Subspace.dual_finrank_eq.symm
  apply clm_isInvertible_of_injective_of_finrank_eq _ ?_ hdim
  have hk : (∀ u, sliceWeightedMetric p u = 0 → u = 0) →
      Function.Injective (sliceWeightedMetric p) := by
    convert! (LinearMap.ker_eq_bot' (f := (sliceWeightedMetric p).toLinearMap)).symm.trans
      (LinearMap.ker_eq_bot (f := (sliceWeightedMetric p).toLinearMap)) |>.mp using 1
  apply hk
  intro u hu
  funext k
  have h := congrArg (fun L : SliceCoordinates →L[ℝ] ℝ => L (Pi.single k 1)) hu
  have hz : sliceMassWeights p k * u k = 0 := by
    simpa [sliceWeightedMetric_apply, Pi.single_apply] using h
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (sliceMassWeights_pos p hε hμ k))

/-- Actual fixed-angle action Hessian iff actual seven-row Jacobian for
positive ε and positive masses. Its Hessian is the nested derivative of
the action, and the independent geometric shape conversion is recorded in
`HessianCorrespondence.lean`. -/
theorem sliceAction_second_fderiv_isInvertible_iff_reducedJacobian
    (p : ContinuationParameter) (y : SliceCoordinates) (hreg : SliceRegular p y)
    (hε : 0 < p.1) (hμ : ∀ i, 0 < p.2 i) :
    (fderiv ℝ (fderiv ℝ (sliceAction p)) y).IsInvertible ↔
      (reducedJacobian p y).IsInvertible := by
  obtain ⟨e, he⟩ := sliceWeightedMetric_isInvertible p hε hμ
  rw [sliceAction_second_fderiv p y hreg, ← he]
  exact ContinuousLinearMap.isInvertible_equiv_comp

/-- Nonnegative closed-simplex version of the actual base Jacobian.
Only the omitted row's mass is required to be positive. All zero masses
remain in the three divided angular rows; the kernel theorem for those
true rows supplies invertibility. -/
theorem reducedAngularJacobian_zero_isInvertible_nonnegative (μ : MassRatio)
    (y : SliceCoordinates) (hreg : SliceRegular (0, μ) y)
    (hunit : ∀ i, sliceRadii y i = 1) (hμ : ∀ i, 0 ≤ μ i)
    (hsum : ∑ i, μ i = 1) (hμ₀ : 0 < μ 0)
    (harc : OrderedSemicircle (sliceAngles y))
    (hroot : ∀ i, coorbitalResidual μ (sliceAngles y) i = 0) :
    (reducedAngularJacobian (0, μ) y).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  have hk : (∀ a, reducedAngularJacobian (0, μ) y a = 0 → a = 0) →
      Function.Injective (reducedAngularJacobian (0, μ) y) := by
    convert! (LinearMap.ker_eq_bot' (f := (reducedAngularJacobian (0, μ) y).toLinearMap)).symm.trans
      (LinearMap.ker_eq_bot (f := (reducedAngularJacobian (0, μ) y).toLinearMap)) |>.mp using 1
  apply hk
  intro a ha
  rw [reducedAngularJacobian_zero_eq μ y hreg hunit harc] at ha
  let u := coorbitalAngleInjection a
  have hrows (j : Fin 3) : angularDifferential μ (sliceAngles y) u j.succ = 0 := by
    have h := congrFun ha j
    simpa [coorbitalFreeRows, u] using h
  have hothers : ∀ i : Satellite, i ≠ 0 → angularDifferential μ (sliceAngles y) u i = 0 := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    simpa only [Fin.succAbove_zero] using hrows j
  have hzero : angularDifferential μ (sliceAngles y) u = 0 := by
    funext i
    by_cases hi : i = 0
    · subst i
      exact angularDifferential_recover_row μ (sliceAngles y) u 0 hμ₀ hothers
    · exact hothers i hi
  have hconstant := (angularDifferential_kernel_iff_nonnegative μ (sliceAngles y) u hμ hsum
    (slice_separatedSemicircle_of_ordered (sliceAngles y) harc) harc hroot).mp hzero
  funext j
  have h := hconstant j.succ 0
  simpa [u] using h

theorem reducedJacobian_at_closed_coorbital_root_isInvertible (μ : MassRatio)
    (y : SliceCoordinates) (hunit : ∀ i, sliceRadii y i = 1)
    (hμ : ∀ i, 0 ≤ μ i) (hsum : ∑ i, μ i = 1) (hμ₀ : 0 < μ 0)
    (harc : OrderedSemicircle (sliceAngles y))
    (hroot : ∀ i, coorbitalResidual μ (sliceAngles y) i = 0) :
    (reducedJacobian (0, μ) y).IsInvertible := by
  have hreg := sliceRegular_at_coorbital μ y hunit harc
  exact reducedJacobian_zero_isInvertible_of_angular μ y hreg hunit
    (reducedAngularJacobian_zero_isInvertible_nonnegative μ y hreg hunit hμ hsum hμ₀ harc hroot)

/-- §5.1 local no-collision continuation on the closed nonnegative mass
simplex, fixing and omitting the positive first mass. The ambient mass
coordinates in the product are independent of ε and may cross zero. -/
theorem closed_coorbital_root_local_continuation (μ : MassRatio) (y : SliceCoordinates)
    (hunit : ∀ i, sliceRadii y i = 1) (hμ : ∀ i, 0 ≤ μ i)
    (hsum : ∑ i, μ i = 1) (hμ₀ : 0 < μ 0)
    (hdomain : CoorbitalAngleDomain (sliceAngles y))
    (hroot : ∀ i, coorbitalResidual μ (sliceAngles y) i = 0) :
    ∃ ψ : ContinuationParameter → SliceCoordinates, ∃ η ζ : ℝ,
      0 < η ∧ 0 < ζ ∧ ψ (0, μ) = y ∧ ContDiffAt ℝ ∞ ψ (0, μ) ∧
      ∀ ε ν, |ε| < η → dist ν μ < η →
        dist (ψ (ε, ν)) y < ζ ∧ reducedResidual (ε, ν) (ψ (ε, ν)) = 0 ∧
          (∀ z, dist z y < ζ → (reducedResidual (ε, ν) z = 0 ↔ ψ (ε, ν) = z)) := by
  have harc := orderedSemicircle_of_coorbitalAngleDomain (sliceAngles y) hdomain
  have hreg := sliceRegular_at_coorbital μ y hunit harc
  have hz := reducedResidual_at_coorbital_root μ y hunit harc hroot
  have hJ := reducedJacobian_at_closed_coorbital_root_isInvertible μ y hunit hμ hsum hμ₀ harc hroot
  obtain ⟨ψ, η, ζ, hη, hζ, hbase, hsmooth, hlocal⟩ :=
    reducedResidual_local_product (0, μ) y hreg hz hJ
  refine ⟨ψ, η, ζ, hη, hζ, hbase, hsmooth, ?_⟩
  intro ε ν hε hν
  apply hlocal ε ν ?_ hν
  simpa only [Real.dist_eq, sub_zero] using hε

/-- The bilinear kernel condition for the genuine nested action
differential on the actual fixed-angle coordinate slice. -/
def SliceActionHessianNondegenerate (p : ContinuationParameter) (y : SliceCoordinates) : Prop :=
  ∀ v : SliceCoordinates,
    (∀ w : SliceCoordinates, fderiv ℝ (fderiv ℝ (sliceAction p)) y v w = 0) → v = 0

theorem sliceActionHessianNondegenerate_iff_isInvertible
    (p : ContinuationParameter) (y : SliceCoordinates) :
    SliceActionHessianNondegenerate p y ↔
      (fderiv ℝ (fderiv ℝ (sliceAction p)) y).IsInvertible := by
  let H := fderiv ℝ (fderiv ℝ (sliceAction p)) y
  constructor
  · intro hn
    let _ : FiniteDimensional ℝ (SliceCoordinates →L[ℝ] ℝ) :=
      (LinearMap.toContinuousLinearMap : (SliceCoordinates →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
        (SliceCoordinates →L[ℝ] ℝ)).finiteDimensional
    have hdim : Module.finrank ℝ SliceCoordinates =
        Module.finrank ℝ (SliceCoordinates →L[ℝ] ℝ) := by
      rw [← (LinearMap.toContinuousLinearMap : (SliceCoordinates →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
        (SliceCoordinates →L[ℝ] ℝ)).finrank_eq]
      exact Subspace.dual_finrank_eq.symm
    apply clm_isInvertible_of_injective_of_finrank_eq H ?_ hdim
    have hk : (∀ v, H v = 0 → v = 0) → Function.Injective H := by
      convert! (LinearMap.ker_eq_bot' (f := H.toLinearMap)).symm.trans
        (LinearMap.ker_eq_bot (f := H.toLinearMap)) |>.mp using 1
    apply hk
    intro v hv
    apply hn v
    intro w
    have h := congrArg (fun L : SliceCoordinates →L[ℝ] ℝ => L w) hv
    exact h
  · intro hi v hk
    have hv : H v = H 0 := by
      ext w
      simpa only [map_zero, zero_apply] using hk w
    exact hi.injective hv

theorem sliceActionHessianNondegenerate_iff_reducedJacobian
    (p : ContinuationParameter) (y : SliceCoordinates) (hreg : SliceRegular p y)
    (hε : 0 < p.1) (hμ : ∀ i, 0 < p.2 i) :
    SliceActionHessianNondegenerate p y ↔ (reducedJacobian p y).IsInvertible :=
  (sliceActionHessianNondegenerate_iff_isInvertible p y).trans
    (sliceAction_second_fderiv_isInvertible_iff_reducedJacobian p y hreg hε hμ)

def slicePolarInverse : PolarCoordinates →L[ℝ] SliceCoordinates :=
  ContinuousLinearMap.pi (fun k => Fin.addCases
    (fun i : Fin 4 => polarRadialProjection i)
    (fun i : Fin 3 => polarAngularProjection i.succ) k)

theorem slicePolarInverse_left (v : SliceCoordinates) :
    slicePolarInverse (slicePolarCoordinates v) = v := by
  funext k
  refine Fin.addCases (motive := fun k => slicePolarInverse (slicePolarCoordinates v) k = v k)
    (fun i : Fin 4 => ?_) (fun i : Fin 3 => ?_) k <;>
    simp [slicePolarInverse, slicePolarCoordinates_apply, polarRadialProjection,
      polarAngularProjection, sliceRadii, sliceAngles]

theorem slicePolarInverse_right (v : PolarCoordinates) (hv : v.2 0 = 0) :
    slicePolarCoordinates (slicePolarInverse v) = v := by
  rw [slicePolarCoordinates_apply]
  apply Prod.ext
  · funext i
    simp [sliceRadii, slicePolarInverse, polarRadialProjection]
  · funext i
    refine Fin.cases ?_ (fun j : Fin 3 => ?_) i <;>
      simp [sliceAngles, slicePolarInverse, polarAngularProjection, hv]

def slicePhysicalConfiguration (p : ContinuationParameter) (y : SliceCoordinates) : Configuration :=
  relativeCenteredContinuous p.1 p.2 (sliceSatellites y)

def sliceConfigurationDerivative (p : ContinuationParameter) (y : SliceCoordinates) :
    SliceCoordinates →L[ℝ] Configuration :=
  (relativeCenteredContinuous p.1 p.2).comp
    ((polarCoordinateDerivative (slicePolarCoordinates y)).comp slicePolarCoordinates)

theorem slicePhysicalConfiguration_hasFDerivAt (p : ContinuationParameter) (y : SliceCoordinates) :
    HasFDerivAt (slicePhysicalConfiguration p) (sliceConfigurationDerivative p y) y := by
  have h := (relativeCenteredContinuous p.1 p.2).hasFDerivAt.comp y
    ((polarCoordinateMap_hasFDerivAt (slicePolarCoordinates y)).comp y slicePolarCoordinates.hasFDerivAt)
  convert! h using 1
  funext z
  simp only [Function.comp_apply, slicePhysicalConfiguration, slicePolarCoordinates_apply,
    polarCoordinateMap, sliceSatellites]

theorem slicePhysicalConfiguration_contDiff (n : ℕ∞ω) (p : ContinuationParameter) :
    ContDiff ℝ n (slicePhysicalConfiguration p) := by
  exact (relativeCenteredContinuous p.1 p.2).contDiff.comp
    (contDiff_pi.mpr (fun i => sliceSatellites_contDiff n i))

theorem sliceAction_eq_scaled_physical (p : ContinuationParameter)
    (hsum : ∑ i, p.2 i = 1) (heps : p.1 ≠ 0) (hden : 1 + p.1 ≠ 0) :
    sliceAction p = p.1⁻¹ • (augmentedPotential (masses p.1 p.2) 1 ∘ slicePhysicalConfiguration p) := by
  funext y
  rw [sliceAction, polarAction, relativeAction_eq_augmentedPotential_div p.1 p.2 hsum heps hden]
  simp only [slicePolarCoordinates_apply, polarCoordinateMap, slicePhysicalConfiguration,
    relativeCenteredContinuous_apply, sliceSatellites, Pi.smul_apply, Function.comp_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The actual action Hessian is ε⁻¹ times the physical Hessian pulled back
through the actual centered polar derivative at a genuine CC. Both the
global action identity and the critical second-derivative chain rule have
been proved before applying this statement. -/
theorem sliceActionHessian_physical_pullback (p : ContinuationParameter) (y : SliceCoordinates)
    (hsum : ∑ i, p.2 i = 1) (heps : p.1 ≠ 0) (hden : 1 + p.1 ≠ 0)
    (hx : NormalizedCentralConfiguration (masses p.1 p.2) (slicePhysicalConfiguration p y))
    (v w : SliceCoordinates) :
    fderiv ℝ (fderiv ℝ (sliceAction p)) y v w = p.1⁻¹ *
      physicalHessian (masses p.1 p.2) 1 (slicePhysicalConfiguration p y)
        (sliceConfigurationDerivative p y v) (sliceConfigurationDerivative p y w) := by
  rw [sliceAction_eq_scaled_physical p hsum heps hden, fderiv_const_smul_field]
  have hscale : fderiv ℝ (p.1⁻¹ • fderiv ℝ
      (augmentedPotential (masses p.1 p.2) 1 ∘ slicePhysicalConfiguration p)) =
      p.1⁻¹ • fderiv ℝ (fderiv ℝ
        (augmentedPotential (masses p.1 p.2) 1 ∘ slicePhysicalConfiguration p)) := by
    convert! fderiv_const_smul_field (𝕜 := ℝ) p.1⁻¹
  rw [hscale]
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
  rw [physicalHessian_comp_at_normalizedCC (masses p.1 p.2)
    (slicePhysicalConfiguration p) y (slicePhysicalConfiguration_contDiff 2 p).contDiffAt hx]
  rw [(slicePhysicalConfiguration_hasFDerivAt p y).fderiv]

def sliceCenteredDerivative (p : ContinuationParameter) (y : SliceCoordinates)
    (hsum : ∑ i, p.2 i = 1) (hden : 1 + p.1 ≠ 0) :
    SliceCoordinates →L[ℝ] centeredVariationSpace (masses p.1 p.2) :=
  (relativeCenteredEquiv p.1 p.2 hsum hden).toContinuousLinearMap.comp
    ((polarCoordinateDerivative (slicePolarCoordinates y)).comp slicePolarCoordinates)

@[simp] theorem sliceCenteredDerivative_apply (p : ContinuationParameter) (y : SliceCoordinates)
    (hsum : ∑ i, p.2 i = 1) (hden : 1 + p.1 ≠ 0) (v : SliceCoordinates) :
    (sliceCenteredDerivative p y hsum hden v : Configuration) = sliceConfigurationDerivative p y v := by
  simp only [sliceCenteredDerivative, sliceConfigurationDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, relativeCenteredEquiv_apply, relativeCenteredContinuous_apply]

@[simp] theorem relativeCenteredEquiv_symm_apply (ε : ℝ) (μ : MassRatio)
    (hsum : ∑ i, μ i = 1) (hden : 1 + ε ≠ 0) (v : centeredVariationSpace (masses ε μ)) :
    (relativeCenteredEquiv ε μ hsum hden).symm v = satellitesRelative v := rfl

/-- The true polar first-angle transverse functional on centered variations.
It is measured in primary-relative variations, and is not mass orthogonality. -/
def sliceTransverseConstraint (p : ContinuationParameter) (y : SliceCoordinates)
    (hsum : ∑ i, p.2 i = 1) (hden : 1 + p.1 ≠ 0) :
    centeredVariationSpace (masses p.1 p.2) →L[ℝ] ℝ :=
  (innerSL ℝ (quarterTurn (sliceSatellites y 0))).comp
    ((ContinuousLinearMap.proj 0 : SatelliteConfiguration →L[ℝ] Plane).comp
      (relativeCenteredEquiv p.1 p.2 hsum hden).symm.toContinuousLinearMap)

theorem sliceCenteredDerivative_transverse (p : ContinuationParameter) (y : SliceCoordinates)
    (hsum : ∑ i, p.2 i = 1) (hden : 1 + p.1 ≠ 0) (v : SliceCoordinates) :
    sliceTransverseConstraint p y hsum hden (sliceCenteredDerivative p y hsum hden v) = 0 := by
  change inner ℝ (quarterTurn (sliceSatellites y 0))
    ((relativeCenteredEquiv p.1 p.2 hsum hden).symm
      ((relativeCenteredEquiv p.1 p.2 hsum hden)
        (polarCoordinateDerivative (slicePolarCoordinates y) (slicePolarCoordinates v))) 0) = 0
  rw [ContinuousLinearEquiv.symm_apply_apply, real_inner_comm, polarCoordinateDerivative_apply,
    slicePolarCoordinates_apply, slicePolarCoordinates_apply]
  simp [sliceAngles, sliceSatellites, polarSatellites, real_inner_smul_left,
    polarPoint_inner_rotation]

def sliceTransverseEquiv (p : ContinuationParameter) (y : SliceCoordinates)
    (hsum : ∑ i, p.2 i = 1) (hden : 1 + p.1 ≠ 0)
    (hr : ∀ i, sliceRadii y i ≠ 0) :
    SliceCoordinates ≃L[ℝ] (sliceTransverseConstraint p y hsum hden).toLinearMap.ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((sliceCenteredDerivative p y hsum hden).codRestrict
      (sliceTransverseConstraint p y hsum hden).toLinearMap.ker
      (fun v => sliceCenteredDerivative_transverse p y hsum hden v))
    (slicePolarInverse.comp ((polarCoordinateInverse (slicePolarCoordinates y)).comp
      ((relativeCenteredEquiv p.1 p.2 hsum hden).symm.toContinuousLinearMap.comp
        (sliceTransverseConstraint p y hsum hden).toLinearMap.ker.subtypeL)))
    (by
      intro v
      change slicePolarInverse (polarCoordinateInverse (slicePolarCoordinates y)
        ((relativeCenteredEquiv p.1 p.2 hsum hden).symm
          ((relativeCenteredEquiv p.1 p.2 hsum hden)
            (polarCoordinateDerivative (slicePolarCoordinates y) (slicePolarCoordinates v))))) = v
      rw [ContinuousLinearEquiv.symm_apply_apply,
        polarCoordinateInverse_left _ _ (by simpa only [slicePolarCoordinates_apply] using hr),
        slicePolarInverse_left])
    (by
      intro v
      let a := polarCoordinateInverse (slicePolarCoordinates y)
        ((relativeCenteredEquiv p.1 p.2 hsum hden).symm v)
      have ha : a.2 0 = 0 := by
        have hv : sliceTransverseConstraint p y hsum hden v = 0 := v.property
        change inner ℝ (quarterTurn (sliceSatellites y 0))
          ((relativeCenteredEquiv p.1 p.2 hsum hden).symm v 0) = 0 at hv
        simp only [a, polarCoordinateInverse_apply, slicePolarCoordinates_apply]
        change (sliceRadii y 0 ^ 2)⁻¹ *
          inner ℝ ((relativeCenteredEquiv p.1 p.2 hsum hden).symm v 0)
            (quarterTurn (sliceSatellites y 0)) = 0
        rw [real_inner_comm, hv, mul_zero]
      apply Subtype.ext
      change (relativeCenteredEquiv p.1 p.2 hsum hden)
        (polarCoordinateDerivative (slicePolarCoordinates y)
          (slicePolarCoordinates (slicePolarInverse a))) = v
      rw [slicePolarInverse_right a ha]
      dsimp only [a]
      rw [polarCoordinateInverse_right _ _ (by simpa only [slicePolarCoordinates_apply] using hr),
        ContinuousLinearEquiv.apply_symm_apply])

@[simp] theorem sliceTransverseEquiv_apply (p : ContinuationParameter) (y : SliceCoordinates)
    (hsum : ∑ i, p.2 i = 1) (hden : 1 + p.1 ≠ 0)
    (hr : ∀ i, sliceRadii y i ≠ 0) (v : SliceCoordinates) :
    (sliceTransverseEquiv p y hsum hden hr v : centeredVariationSpace (masses p.1 p.2)) =
      sliceCenteredDerivative p y hsum hden v := rfl

theorem satellitesRelative_rotationDirection (x : Configuration) :
    satellitesRelative (rotationDirection x) = fun i => quarterTurn (satellitesRelative x i) := by
  funext i
  simp only [satellitesRelative, primaryRelative, rotationDirection, ← quarterTurn_sub]

theorem slicePhysicalConfiguration_satellitesRelative (p : ContinuationParameter) (y : SliceCoordinates) :
    satellitesRelative (slicePhysicalConfiguration p y) = sliceSatellites y := by
  rw [slicePhysicalConfiguration, relativeCenteredContinuous_apply,
    satellitesRelative_centeredFromRelative]

/-- The actual first-angle slice is transverse to rotation because its
functional on the rotation direction is the squared primary-relative
radius, rather than an assumed nonzero coordinate coefficient. -/
theorem sliceTransverseConstraint_rotation_value (p : ContinuationParameter) (y : SliceCoordinates)
    (hsum : ∑ i, p.2 i = 1) (hden : 1 + p.1 ≠ 0)
    (hx : NormalizedCentralConfiguration (masses p.1 p.2) (slicePhysicalConfiguration p y)) :
    sliceTransverseConstraint p y hsum hden
      (centeredRotationVector (masses p.1 p.2) (slicePhysicalConfiguration p y) hx) =
        sliceRadii y 0 ^ 2 := by
  change inner ℝ (quarterTurn (sliceSatellites y 0))
    ((relativeCenteredEquiv p.1 p.2 hsum hden).symm
      (centeredRotationVector (masses p.1 p.2) (slicePhysicalConfiguration p y) hx) 0) = _
  rw [relativeCenteredEquiv_symm_apply]
  change inner ℝ (quarterTurn (sliceSatellites y 0))
    (satellitesRelative (rotationDirection (slicePhysicalConfiguration p y)) 0) = _
  rw [satellitesRelative_rotationDirection, slicePhysicalConfiguration_satellitesRelative,
    quarterTurn_inner_quarterTurn, real_inner_self_eq_norm_sq]
  exact polarPoint_norm_sq _ _

theorem sliceActionHessianNondegenerate_iff_transverse (p : ContinuationParameter)
    (y : SliceCoordinates) (hsum : ∑ i, p.2 i = 1) (heps : p.1 ≠ 0)
    (hden : 1 + p.1 ≠ 0) (hr : ∀ i, sliceRadii y i ≠ 0)
    (hx : NormalizedCentralConfiguration (masses p.1 p.2) (slicePhysicalConfiguration p y)) :
    SliceActionHessianNondegenerate p y ↔
      BilinearNondegenerateOn
        (centeredHessianOperator (masses p.1 p.2) 1 (slicePhysicalConfiguration p y))
        (sliceTransverseConstraint p y hsum hden).toLinearMap.ker := by
  let T := sliceTransverseEquiv p y hsum hden hr
  have hpull (v w : SliceCoordinates) : fderiv ℝ (fderiv ℝ (sliceAction p)) y v w =
      p.1⁻¹ * centeredHessianOperator (masses p.1 p.2) 1 (slicePhysicalConfiguration p y)
        (T v) (T w) := by
    simpa only [T, centeredHessianOperator_apply, sliceTransverseEquiv_apply,
      sliceCenteredDerivative_apply, physicalHessian_eq_map _ _ _ hx.1] using
      sliceActionHessian_physical_pullback p y hsum heps hden hx v w
  constructor
  · intro hn v hv hk
    let vS : (sliceTransverseConstraint p y hsum hden).toLinearMap.ker := ⟨v, hv⟩
    have hz : T.symm vS = 0 := by
      apply hn
      intro w
      rw [hpull, ContinuousLinearEquiv.apply_symm_apply]
      rw [hk (T w) (T w).property, mul_zero]
    have hzS : vS = 0 := T.symm.injective (by simpa only [map_zero] using hz)
    exact congrArg Subtype.val hzS
  · intro hn v hk
    have hv : (T v : centeredVariationSpace (masses p.1 p.2)) = 0 := by
      apply hn (T v) (T v).property
      intro w hw
      let wS : (sliceTransverseConstraint p y hsum hden).toLinearMap.ker := ⟨w, hw⟩
      have h := hk (T.symm wS)
      rw [hpull, ContinuousLinearEquiv.apply_symm_apply] at h
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero heps)
    have hzS : T v = 0 := Subtype.ext hv
    exact T.injective (by simpa only [map_zero] using hzS)

/-- Complete actual Jacobian/shape-Hessian bridge at genuine normalized
roots: true divided rows, true coordinate differential, true action
Hessian, actual transverse rotation slice and the original six-dimensional
physical shape space are all linked by proved equalities. -/
theorem reducedJacobian_isInvertible_iff_shape_at_normalizedCC
    (p : ContinuationParameter) (y : SliceCoordinates) (hreg : SliceRegular p y)
    (hε : 0 < p.1) (hμ : PositiveRatio p.2)
    (hx : NormalizedCentralConfiguration (masses p.1 p.2) (slicePhysicalConfiguration p y)) :
    (reducedJacobian p y).IsInvertible ↔
      ShapeHessianNondegenerate (masses p.1 p.2) 1 (slicePhysicalConfiguration p y) := by
  have hden : 1 + p.1 ≠ 0 := parameter_denominator_ne_zero p.1 hreg.1
  have hr : ∀ i, sliceRadii y i ≠ 0 := fun i => ne_of_gt (hreg.2.1 i)
  have hL : sliceTransverseConstraint p y hμ.2 hden
      (centeredRotationVector (masses p.1 p.2) (slicePhysicalConfiguration p y) hx) ≠ 0 := by
    rw [sliceTransverseConstraint_rotation_value p y hμ.2 hden hx]
    exact pow_ne_zero 2 (hr 0)
  exact (sliceActionHessianNondegenerate_iff_reducedJacobian p y hreg hε hμ.1).symm.trans
    ((sliceActionHessianNondegenerate_iff_transverse p y hμ.2 (ne_of_gt hε) hden hr hx).trans
      (transverseCenteredHessian_nondegenerate_iff_shape (masses p.1 p.2)
        (masses_positive p.1 p.2 hε hμ) (slicePhysicalConfiguration p y) hx
        (sliceTransverseConstraint p y hμ.2 hden) hL))

theorem normalizedCC_of_reducedResidual_zero (p : ContinuationParameter) (y : SliceCoordinates)
    (hreg : SliceRegular p y) (hε : 0 < p.1) (hμ : PositiveRatio p.2)
    (hroot : reducedResidual p y = 0) :
    NormalizedCentralConfiguration (masses p.1 p.2) (slicePhysicalConfiguration p y) := by
  have hR (i : Satellite) : radialResidual p.1 p.2 (sliceRadii y) (sliceAngles y) i = 0 := by
    have h := congrFun hroot (i.castAdd 3)
    simpa only [reducedResidual, Fin.append_left, Pi.zero_apply] using h
  have hT (i : Satellite) (hi : i ≠ 0) :
      angularResidual p.1 p.2 (sliceRadii y) (sliceAngles y) i = 0 := by
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    have h := congrFun hroot (j.natAdd 4)
    simpa only [reducedResidual, Fin.append_right, Pi.zero_apply, Fin.succAbove_zero] using h
  have hF : ∀ i, vectorResidual p.1 p.2 (sliceSatellites y) i = 0 := by
    apply (reducedPolarResiduals_zero_iff_vectorRoot p.1 p.2
      (sliceRadii y, sliceAngles y) hε hμ hreg.2.1 0).mp
    exact ⟨hR, hT⟩
  have hx := normalized_of_vectorResidual_zero p.1 p.2 hreg.1 hμ (sliceSatellites y)
    (sliceSatellites_relativeCollisionFree p y hreg) hF
  simpa only [slicePhysicalConfiguration, relativeCenteredContinuous_apply] using hx

/-- Manuscript Lemma 3.1 for the actual fixed-first-angle seven rows,
at an actual residual root. No CC, Hessian, transverse-coordinate or
invertibility equivalence is left as an extra assumption. -/
theorem reducedJacobian_isInvertible_iff_shape (p : ContinuationParameter) (y : SliceCoordinates)
    (hreg : SliceRegular p y) (hε : 0 < p.1) (hμ : PositiveRatio p.2)
    (hroot : reducedResidual p y = 0) :
    (reducedJacobian p y).IsInvertible ↔
      ShapeHessianNondegenerate (masses p.1 p.2) 1 (slicePhysicalConfiguration p y) :=
  reducedJacobian_isInvertible_iff_shape_at_normalizedCC p y hreg hε hμ
    (normalizedCC_of_reducedResidual_zero p y hreg hε hμ hroot)

theorem reducedJacobian_joint_continuousAt (p : ContinuationParameter) (y : SliceCoordinates)
    (hreg : SliceRegular p y) :
    ContinuousAt (fun z : ContinuationParameter × SliceCoordinates => reducedJacobian z.1 z.2) (p, y) := by
  let f : (ContinuationParameter × SliceCoordinates) → SliceCoordinates → SliceCoordinates :=
    fun z v => reducedResidual z.1 v
  have hparam : ContDiff ℝ 1
      (fun z : (ContinuationParameter × SliceCoordinates) × SliceCoordinates => (z.1.1, z.2)) := by
    fun_prop
  have hf : ContDiffAt ℝ 1 (Function.uncurry f) ((p, y), y) := by
    convert! (reducedResidual_joint_contDiffAt 1 p y hreg).comp
      ((p, y), y) hparam.contDiffAt using 1
  have hg : ContDiffAt ℝ 0 (fun z : ContinuationParameter × SliceCoordinates => z.2) (p, y) :=
    contDiffAt_snd
  have h := hf.fderiv hg (by norm_num : (0 : ℕ∞ω) + 1 ≤ 1)
  exact h.continuousAt

theorem euclidean_clm_isInvertible_iff_det_ne_zero {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : A.IsInvertible ↔ A.det ≠ 0 := by
  constructor
  · rintro ⟨e, he⟩
    rw [← he]
    exact e.toLinearEquiv.isUnit_det'.ne_zero
  · intro h
    exact ⟨A.toContinuousLinearEquivOfDetNeZero h,
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero A h⟩

theorem isOpen_euclidean_clm_isInvertible {n : ℕ} :
    IsOpen {A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) | A.IsInvertible} := by
  have h : IsOpen {A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) | A.det ≠ 0} :=
    (isClosed_eq ContinuousLinearMap.continuous_det continuous_const).isOpen_compl
  convert! h using 1
  ext A
  exact euclidean_clm_isInvertible_iff_det_ne_zero A

theorem reducedJacobian_eventually_isInvertible (p : ContinuationParameter)
    (y : SliceCoordinates) (hreg : SliceRegular p y) (hJ : (reducedJacobian p y).IsInvertible) :
    ∀ᶠ z : ContinuationParameter × SliceCoordinates in 𝓝 (p, y),
      (reducedJacobian z.1 z.2).IsInvertible :=
  (reducedJacobian_joint_continuousAt p y hreg).tendsto.eventually
    (isOpen_euclidean_clm_isInvertible.mem_nhds hJ)

/-- Independent product IFT with genuine regularity and invertibility
preserved on the continued branch. Inverse persistence is derived from
continuity of the actual Jacobian and openness of nonzero determinant. -/
theorem reducedResidual_local_product_regular_invertible (p : ContinuationParameter)
    (y : SliceCoordinates) (hreg : SliceRegular p y)
    (hroot : reducedResidual p y = 0) (hJ : (reducedJacobian p y).IsInvertible) :
    ∃ ψ : ContinuationParameter → SliceCoordinates, ∃ η ζ : ℝ,
      0 < η ∧ 0 < ζ ∧ ψ p = y ∧ ContDiffAt ℝ ∞ ψ p ∧
      ∀ ε μ, dist ε p.1 < η → dist μ p.2 < η →
        SliceRegular (ε, μ) (ψ (ε, μ)) ∧ (reducedJacobian (ε, μ) (ψ (ε, μ))).IsInvertible ∧
        dist (ψ (ε, μ)) y < ζ ∧ reducedResidual (ε, μ) (ψ (ε, μ)) = 0 ∧
          (∀ z, dist z y < ζ → (reducedResidual (ε, μ) z = 0 ↔ ψ (ε, μ) = z)) := by
  obtain ⟨ψ, a, ζ, ha, hζ, hbase, hsmooth, hlocal⟩ :=
    reducedResidual_local_product p y hreg hroot hJ
  have hInvNear : ∀ᶠ q in 𝓝 p, (reducedJacobian q (ψ q)).IsInvertible := by
    have h := reducedJacobian_eventually_isInvertible p y hreg hJ
    have h' : ∀ᶠ z : ContinuationParameter × SliceCoordinates in 𝓝 (p, ψ p),
        (reducedJacobian z.1 z.2).IsInvertible := by simpa only [hbase] using h
    exact (continuousAt_id.prodMk hsmooth.continuousAt).tendsto.eventually h'
  have hRegNear : ∀ᶠ q in 𝓝 p, SliceRegular q (ψ q) := by
    have hynear : ∀ᶠ q in 𝓝 p, SliceRegular p (ψ q) := by
      have hbaseReg : SliceRegular p (ψ p) := by simpa only [hbase] using hreg
      have h := hsmooth.continuousAt.tendsto.eventually
        ((isOpen_sliceRegular p).mem_nhds hbaseReg)
      simpa only [hbase] using h
    have hεnear : ∀ᶠ q : ContinuationParameter in 𝓝 p, -1 < q.1 :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hreg.1
    filter_upwards [hynear, hεnear] with q hy hε
    exact ⟨hε, hy.2⟩
  obtain ⟨b, hb, hnear⟩ := Metric.eventually_nhds_iff.mp (hRegNear.and hInvNear)
  refine ⟨ψ, min a b, ζ, lt_min ha hb, hζ, hbase, hsmooth, ?_⟩
  intro ε μ hε hμ
  have hparam : dist (ε, μ) p < b := by
    rw [Prod.dist_eq]
    exact max_lt (lt_of_lt_of_le hε (min_le_right _ _))
      (lt_of_lt_of_le hμ (min_le_right _ _))
  obtain ⟨hregq, hJq⟩ := hnear hparam
  refine ⟨hregq, hJq, ?_⟩
  exact hlocal ε μ (lt_of_lt_of_le hε (min_le_left _ _))
    (lt_of_lt_of_le hμ (min_le_left _ _))

end DominantFiveBody
