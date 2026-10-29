import DominantFiveBody.Coordinates

/-! The single satellite permutation induced by an original hull order.
This only reindexes coordinates and masses; it is not a similarity. -/

namespace DominantFiveBody

theorem hullOrder_label_succ_ne_zero (σ : HullOrder) (i : Satellite) : σ.labels i.succ≠0 := by
  intro h
  have hi := σ.labels.injective (h.trans σ.primary_first.symm)
  exact Fin.succ_ne_zero i hi

theorem hullOrder_inv_succ_ne_zero (σ : HullOrder) (i : Satellite) : σ.labels.symm i.succ≠0 := by
  intro h
  have hi := congrArg σ.labels h
  rw [Equiv.apply_symm_apply,σ.primary_first] at hi
  exact Fin.succ_ne_zero i hi

def hullSatellitePermutation (σ : HullOrder) : Equiv.Perm Satellite where
  toFun i := (σ.labels i.succ).pred (hullOrder_label_succ_ne_zero σ i)
  invFun i := (σ.labels.symm i.succ).pred (hullOrder_inv_succ_ne_zero σ i)
  left_inv i := by
    apply Fin.succ_injective
    simp only [Fin.succ_pred,Equiv.symm_apply_apply]
  right_inv i := by
    apply Fin.succ_injective
    simp only [Fin.succ_pred,Equiv.apply_symm_apply]

theorem hullSatellitePermutation_succ (σ : HullOrder) (i : Satellite) :
    (hullSatellitePermutation σ i).succ=σ.labels i.succ :=
  Fin.succ_pred _ (hullOrder_label_succ_ne_zero σ i)

theorem hullOrder_label_succ (σ : HullOrder) (i : Satellite) :
    σ.labels i.succ=(hullSatellitePermutation σ i).succ :=
  (hullSatellitePermutation_succ σ i).symm

end DominantFiveBody
