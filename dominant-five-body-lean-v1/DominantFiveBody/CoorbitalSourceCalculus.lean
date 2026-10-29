import DominantFiveBody.CoorbitalCovering
import DominantFiveBody.CoorbitalIntegralRepresentation

/-! Source formula checks in Sections 1 and 2, including the first derivative
of the chord-distance potential. These are not assumed analytic interfaces. -/
noncomputable section
open scoped BigOperators
namespace DominantFiveBody
open Coorbital

theorem source_masses (ε : ℝ) (μ : MassRatio) :
    masses ε μ 0=1 ∧ (∀ i : Satellite,masses ε μ i.succ=ε*μ i) ∧
      (PositiveRatio μ ↔ (∀ i,0<μ i) ∧ ∑ i,μ i=1) := by
  exact ⟨rfl,fun _ => rfl,Iff.rfl⟩

theorem source_angle_domain (θ : Satellite → ℝ) :
    CoorbitalAngleDomain θ ↔ θ 0=0 ∧ 0<θ 1 ∧ θ 1<θ 2 ∧ θ 2<θ 3 ∧ θ 3<Real.pi := by
  constructor
  · rintro ⟨hz,hm,hp⟩
    exact ⟨hz,by simpa [hz] using hm 0 1 (by decide),hm 1 2 (by decide),hm 2 3 (by decide),hp⟩
  · rintro ⟨hz,h1,h2,h3,hp⟩
    refine ⟨hz,?_,hp⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> linarith

theorem source_scalar_derivatives {t : ℝ} (ht : 0<t) (hp : t<Real.pi) :
    deriv pairPotential t = -kernelF t ∧ deriv kernelF t = -kappa t ∧
      deriv (deriv pairPotential) t = kappa t ∧
      deriv kappa t=kappaPrime t ∧ kappaPrime t<0 :=
  ⟨deriv_pairPotential ht hp,deriv_kernelF ht hp,
    (pairPotential_second_hasDerivAt ht hp).deriv,(kappa_hasDerivAt ht hp).deriv,
    kappaPrime_neg ht hp⟩

theorem coorbitalPotential_hasFDerivAt (mass theta : Satellite → ℝ)
    (harc : OrderedSemicircle theta) :
    HasFDerivAt (coorbitalPotential mass) (angularPotentialDerivative mass theta) theta := by
  have heq : coorbitalPotential mass =ᶠ[nhds theta] angularPotential mass := by
    filter_upwards [(isOpen_orderedSemicircle 4).mem_nhds harc] with a ha
    exact coorbitalPotential_eq_angularPotential mass a ha
  exact (angularPotential_hasFDerivAt mass theta harc).congr_of_eventuallyEq heq

theorem coorbitalPotential_coordinate_derivative (mass theta : Satellite → ℝ)
    (harc : OrderedSemicircle theta) (k : Satellite) :
    fderiv ℝ (coorbitalPotential mass) theta (Pi.single k 1) =
      mass k*coorbitalResidual mass theta k := by
  classical
  rw [(coorbitalPotential_hasFDerivAt mass theta harc).fderiv]
  have ha (i j : Satellite) (hij : i<j) :
      coorbitalKernel (theta j-theta i)=kernelF (theta j-theta i) :=
    coorbitalKernel_eq_positive_formula _ (harc i j hij).1.le
  have hn (i j : Satellite) (hij : i<j) :
      coorbitalKernel (theta i-theta j) = -kernelF (theta j-theta i) := by
    rw [show theta i-theta j=-(theta j-theta i) by ring,coorbitalKernel_neg,ha i j hij]
  have h01 := ha 0 1 (by decide)
  have h02 := ha 0 2 (by decide)
  have h03 := ha 0 3 (by decide)
  have h12 := ha 1 2 (by decide)
  have h13 := ha 1 3 (by decide)
  have h23 := ha 2 3 (by decide)
  have h10 := hn 0 1 (by decide)
  have h20 := hn 0 2 (by decide)
  have h30 := hn 0 3 (by decide)
  have h21 := hn 1 2 (by decide)
  have h31 := hn 1 3 (by decide)
  have h32 := hn 2 3 (by decide)
  simp only [angularPotentialDerivative,sum_apply,angleDifference]
  rw [coorbitalResidual,Finset.sum_erase_eq_sub (Finset.mem_univ k)]
  fin_cases k <;> simp [Fin.sum_univ_four,h01,h02,h03,h12,h13,h23,
    h10,h20,h30,h21,h31,h32] <;> ring

theorem source_integral_comparisons :
    (∀ t : ℝ,0<t → t<h → kernelF t=(∫ s in t..h,kappa s) ∧
      (∫ s in t..h,kappa s)<(h-t)*kappa t) ∧
    (∀ t : ℝ,h<t → t<Real.pi → kernelF t=(∫ s in t..Real.pi,kappa s) ∧
      (∫ s in t..Real.pi,kappa s)<(Real.pi-t)*kappa t) :=
  ⟨fun _ => kernelF_integral_short,fun _ => kernelF_integral_long⟩

end DominantFiveBody
