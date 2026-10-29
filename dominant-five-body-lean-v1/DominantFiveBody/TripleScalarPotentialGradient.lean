import DominantFiveBody.TripleScalarPotential

/-! Actual Frechet derivative of the original scalar potential and the
literal mass-divided gradient equations in the ordered chamber. -/
noncomputable section
open scoped BigOperators
open Filter Set Topology
namespace DominantFiveBody

def tripleScalarPotentialDerivative (alpha z : TripleVector) : TripleVector →L[ℝ] ℝ :=
  ∑ i,(alpha i*tripleScalarResidual alpha z i) •
    (ContinuousLinearMap.proj i : TripleVector →L[ℝ] ℝ)

theorem tripleScalarPotentialDerivative_apply (alpha z v : TripleVector) :
    tripleScalarPotentialDerivative alpha z v=∑ i,alpha i*tripleScalarResidual alpha z i*v i := by
  simp [tripleScalarPotentialDerivative]

theorem tripleScalarPotential_hasFDerivAt (alpha z : TripleVector) (hz : TripleOrdered z) :
    HasFDerivAt (tripleScalarPotential alpha) (tripleScalarPotentialDerivative alpha z) z := by
  let p := fun i : TripleLabel => (ContinuousLinearMap.proj i : TripleVector →L[ℝ] ℝ)
  have hQ : HasFDerivAt (fun w : TripleVector => tripleD0/2*(∑ i,alpha i*w i^2))
      ((tripleD0/2) • (∑ i,(alpha i*(2*z i)) • p i)) z := by
    apply HasFDerivAt.const_mul
    apply HasFDerivAt.fun_sum
    intro i _
    simpa [p,smul_smul] using
      ((hasFDerivAt_apply (𝕜 := ℝ) i z).pow 2).const_mul (alpha i)
  have hpair (i j : TripleLabel) (hij : i<j) :
      HasFDerivAt (fun w : TripleVector => alpha i*alpha j/(w j-w i))
        ((alpha i*alpha j*(-((z j-z i)^2)⁻¹)) • (p j-p i)) z := by
    simpa only [div_eq_mul_inv,smul_smul,Function.comp_def,Pi.sub_apply] using
      ((hasDerivAt_inv (sub_pos.mpr (hz i j hij)).ne').comp_hasFDerivAt z
        ((hasFDerivAt_apply (𝕜 := ℝ) j z).sub (hasFDerivAt_apply (𝕜 := ℝ) i z))).const_mul
        (alpha i*alpha j)
  have hd := hQ.add (((hpair 0 1 (by decide)).add (hpair 0 2 (by decide))).add (hpair 1 2 (by decide)))
  have hnear : ∀ᶠ w in 𝓝 z,TripleOrdered w := tripleScalarChamber_isOpen.mem_nhds hz
  have heq : tripleScalarPotential alpha =ᶠ[𝓝 z]
      (fun w : TripleVector => tripleD0/2*(∑ i,alpha i*w i^2)+
        (alpha 0*alpha 1/(w 1-w 0)+alpha 0*alpha 2/(w 2-w 0)+alpha 1*alpha 2/(w 2-w 1))) :=
    hnear.mono (fun w hw => tripleScalarPotential_ordered_formula alpha w hw)
  convert! hd.congr_of_eventuallyEq heq using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [tripleScalarPotentialDerivative,p,add_apply,smul_apply,sub_apply,
    ContinuousLinearMap.proj_apply,sum_apply,smul_eq_mul]
  simp [Fin.sum_univ_three,tripleScalarResidual,Finset.sum_erase_eq_sub,tripleScalarForce]
  rw [abs_sub_comm (z 0) (z 1),abs_sub_comm (z 0) (z 2),abs_sub_comm (z 1) (z 2),
    abs_of_pos (sub_pos.mpr (hz 0 1 (by decide))),
    abs_of_pos (sub_pos.mpr (hz 0 2 (by decide))),
    abs_of_pos (sub_pos.mpr (hz 1 2 (by decide)))]
  field_simp [(sub_pos.mpr (hz 0 1 (by decide))).ne',
    (sub_pos.mpr (hz 0 2 (by decide))).ne',(sub_pos.mpr (hz 1 2 (by decide))).ne']
  ring

theorem tripleScalarPotential_fderiv_apply (alpha z v : TripleVector) (hz : TripleOrdered z) :
    fderiv ℝ (tripleScalarPotential alpha) z v=∑ i,alpha i*tripleScalarResidual alpha z i*v i := by
  rw [(tripleScalarPotential_hasFDerivAt alpha z hz).fderiv]
  exact tripleScalarPotentialDerivative_apply alpha z v

theorem tripleScalarPotential_divided_gradient (alpha z : TripleVector)
    (ha : ∀ i,0<alpha i) (hz : TripleOrdered z) (i : TripleLabel) :
    fderiv ℝ (tripleScalarPotential alpha) z (Pi.single i 1)/alpha i=tripleScalarResidual alpha z i := by
  rw [tripleScalarPotential_fderiv_apply alpha z _ hz]
  simp only [Pi.single_apply,Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_ite,mul_one,mul_zero]
  exact mul_div_cancel_left₀ _ (ha i).ne'

theorem tripleScalarPotential_critical_iff_root (alpha z : TripleVector)
    (ha : ∀ i,0<alpha i) (hz : TripleOrdered z) :
    fderiv ℝ (tripleScalarPotential alpha) z=0 ↔ ∀ i,tripleScalarResidual alpha z i=0 := by
  constructor
  · intro h i
    rw [←tripleScalarPotential_divided_gradient alpha z ha hz i,h,zero_apply,zero_div]
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    rw [tripleScalarPotential_fderiv_apply alpha z v hz]
    simp only [h,mul_zero,zero_mul,Finset.sum_const_zero,zero_apply]

end DominantFiveBody
