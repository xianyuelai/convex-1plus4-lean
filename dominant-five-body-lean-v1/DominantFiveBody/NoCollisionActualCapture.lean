import DominantFiveBody.OrderedPhysicalSequence
import DominantFiveBody.PolarSliceCoordinates
import DominantFiveBody.PairActualCapture

/-! The no-collision chart captures actual root sequences, including
limits on the closed mass simplex. A surviving positive mass is selected
before the angular row is deleted. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 600000

theorem normalized_noCollision_actual_capture
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (thetaLimit : Satellite → ℝ) (htt : Tendsto theta atTop (𝓝 thetaLimit))
    (hsep : Function.Injective qLimit) :
    ∃ e : Equiv.Perm Satellite,0<muLimit (e 0) ∧
      Nonempty (NoCollisionCapturedBranches (fun n => mu n ∘ e) eps
        (fun n => polarSlice (r n ∘ e) (fun i => theta n (e i)-theta n (e 0)))) := by
  classical
  obtain ⟨hrt,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x
    heps hepst hm hx r theta hr hpolar horder muLimit hmt qLimit hqt thetaLimit htt
  have hmn (i : Satellite) : 0≤muLimit i :=
    ge_of_tendsto ((continuous_apply i).continuousAt.tendsto.comp hmt)
      (Eventually.of_forall (fun n => ((hm n).1 i).le))
  have hsum : ∑ i,muLimit i=1 := by
    have ht : Tendsto (fun n => ∑ i,mu n i) atTop (𝓝 (∑ i,muLimit i)) :=
      tendsto_finsetSum _ (fun i _ => (continuous_apply i).continuousAt.tendsto.comp hmt)
    have he : (fun n => ∑ i,mu n i)=(fun _ : ℕ => (1 : ℝ)) := funext (fun n => (hm n).2)
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hex : ∃ p,0<muLimit p := by
    by_contra! hn
    have hle : ∑ i,muLimit i≤0 := Finset.sum_nonpos (fun i _ => hn i)
    linarith
  obtain ⟨p,hp⟩ := hex
  let e : Equiv.Perm Satellite := Equiv.swap 0 p
  have he0 : e 0=p := Equiv.swap_apply_left 0 p
  let nu : ℕ → MassRatio := fun n => mu n ∘ e
  let theta' : ℕ → MassRatio := fun n i => theta n (e i)-theta n (e 0)
  let theta0 : MassRatio := fun i => thetaLimit (e i)-thetaLimit (e 0)
  let y : ℕ → SliceCoordinates := fun n => polarSlice (r n ∘ e) (theta' n)
  let y0 : SliceCoordinates := polarSlice (fun _ => 1) theta0
  have hz (n : ℕ) : theta' n 0=0 := sub_self _
  have hz0 : theta0 0=0 := sub_self _
  have hordered0 : OrderedSemicircle thetaLimit := by
    intro i j hij
    have hne : thetaLimit i≠thetaLimit j := by
      intro he
      apply hij.ne
      apply hsep
      rw [hunit i,hunit j,he]
    refine ⟨sub_pos.mpr (lt_of_le_of_ne (hmono hij.le) hne),?_⟩
    have hi := hmono (Fin.zero_le i)
    have hj := hmono (Fin.le_last j)
    change thetaLimit j≤thetaLimit 3 at hj
    linarith
  have hsep0 : SeparatedSemicircle theta0 := by
    intro i j hij
    have hh := separatedSemicircle_of_ordered thetaLimit hordered0 (e i) (e j) (e.injective.ne hij)
    refine ⟨?_,?_⟩
    · dsimp only [theta0]
      exact sub_left_inj.not.mpr hh.1
    · simpa only [theta0,sub_sub_sub_cancel_right] using hh.2
  have hreg : SliceRegular (0,muLimit ∘ e) y0 :=
    sliceRegular_at_coorbital_separated (muLimit ∘ e) y0
      (fun i => congrFun (polarSlice_radii _ _) i)
      (by simpa only [y0,polarSlice_angles _ _ hz0] using hsep0)
  have hmut : Tendsto nu atTop (𝓝 (muLimit ∘ e)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact (continuous_apply (e i)).continuousAt.tendsto.comp hmt
  have hrt' : Tendsto (fun n => r n ∘ e) atTop (𝓝 (fun _ => (1 : ℝ))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact (continuous_apply (e i)).continuousAt.tendsto.comp hrt
  have htt' : Tendsto theta' atTop (𝓝 theta0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact ((continuous_apply (e i)).continuousAt.tendsto.comp htt).sub
      ((continuous_apply (e 0)).continuousAt.tendsto.comp htt)
  have hyt : Tendsto y atTop (𝓝 y0) :=
    (polarSlice_contDiff 0).continuous.continuousAt.tendsto.comp (hrt'.prodMk_nhds htt')
  have hroots (n : ℕ) : reducedResidual (eps n,nu n) (y n)=0 := by
    have hp := normalized_polar_reindex_sub_constant (eps n) (mu n) (x n)
      (heps n) (hm n) (hx n) (r n) (theta n) (hr n) (hpolar n) e (theta n (e 0))
    have hall := polarResiduals_zero_of_normalized (eps n) (nu n)
      (centeredFromRelative (eps n) (nu n) (polarSatellites (r n ∘ e) (theta' n))) hp.2
      (positiveRatio_satellitePermutation _ (hm n) e) (heps n) (r n ∘ e) (theta' n)
      (fun i => hr n (e i)) (satellitesRelative_centeredFromRelative _ _ _)
    exact polarSlice_residual_zero _ _ _ _ (hz n) hall.1 hall.2
  refine ⟨e,by simpa only [he0] using hp,?_⟩
  exact noCollision_actual_sequence_capture_of_regular_limit (muLimit ∘ e) y0
    (fun i => hmn (e i)) ((Equiv.sum_comp e muLimit).trans hsum)
    (by simpa only [Function.comp_apply,he0] using hp) hreg
    (by simpa only [y0,polarSlice_angles _ _ hz0] using hsep0)
    nu eps y (fun n => positiveRatio_satellitePermutation _ (hm n) e) heps hmut hepst hyt hroots

end DominantFiveBody
