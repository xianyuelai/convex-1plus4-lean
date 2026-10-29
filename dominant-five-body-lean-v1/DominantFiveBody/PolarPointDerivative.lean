import DominantFiveBody.PairExterior

/-! # Explicit polar differential for the actual exterior target field -/

noncomputable section

namespace DominantFiveBody

local instance polarPlaneAddCommGroup : AddCommGroup Plane := (inferInstance : NormedAddCommGroup Plane).toAddCommGroup
local instance polarPlaneModule : Module ℝ Plane := (inferInstance : NormedSpace ℝ Plane).toModule
local instance polarPlaneTopology : TopologicalSpace Plane :=
  (inferInstance : PseudoMetricSpace Plane).toUniformSpace.toTopologicalSpace

def polarPointDerivative (p : ℝ×ℝ) : (ℝ×ℝ) →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (polarPoint 1 p.2)+
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (quarterTurn (polarPoint p.1 p.2))

theorem polarPointDerivative_apply (p v : ℝ×ℝ) :
    polarPointDerivative p v=v.1 • polarPoint 1 p.2+v.2 • quarterTurn (polarPoint p.1 p.2) := rfl

theorem polarPoint_hasFDerivAt (p : ℝ×ℝ) :
    HasFDerivAt (fun z : ℝ×ℝ => polarPoint z.1 z.2) (polarPointDerivative p) p := by
  let L : (ℝ×ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let M : (ℝ×ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hr : HasFDerivAt (fun z : ℝ×ℝ => z.1) L p := L.hasFDerivAt
  have ht : HasFDerivAt (fun z : ℝ×ℝ => z.2) M p := M.hasFDerivAt
  have hc := (Real.hasDerivAt_cos p.2).comp_hasFDerivAt p ht
  have hs := (Real.hasDerivAt_sin p.2).comp_hasFDerivAt p ht
  let d : (ℝ×ℝ) →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi fun k =>
    if k=0 then Real.cos p.2 • L+p.1 • (-Real.sin p.2 • M)
    else Real.sin p.2 • L+p.1 • (Real.cos p.2 • M)
  have hcoords : HasFDerivAt
      (fun z : ℝ×ℝ => ![z.1*Real.cos z.2,z.1*Real.sin z.2]) d p := by
    apply hasFDerivAt_pi.mpr
    intro k
    fin_cases k
    · convert! hr.mul hc using 1
      apply ContinuousLinearMap.ext
      intro v
      change Real.cos p.2*v.1+p.1*(-Real.sin p.2*v.2)=
        p.1*(-Real.sin p.2*v.2)+Real.cos p.2*v.1
      ring
    · convert! hr.mul hs using 1
      apply ContinuousLinearMap.ext
      intro v
      change Real.sin p.2*v.1+p.1*(Real.cos p.2*v.2)=
        p.1*(Real.cos p.2*v.2)+Real.sin p.2*v.1
      ring
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp p hcoords
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  ext k
  fin_cases k <;> simp [d,L,M,polarPointDerivative,polarPoint,quarterTurn,point] <;> ring

theorem polarPoint_hasDerivAt_angle (r theta : ℝ) :
    HasDerivAt (polarPoint r) (quarterTurn (polarPoint r theta)) theta := by
  have hp : HasDerivAt (fun v : ℝ => (r,v)) (0,1) theta :=
    (hasDerivAt_const theta r).prodMk (hasDerivAt_id theta)
  have h := (polarPoint_hasFDerivAt (r,theta)).comp_hasDerivAt theta hp
  convert! h using 1
  simp [polarPointDerivative_apply]

end DominantFiveBody
