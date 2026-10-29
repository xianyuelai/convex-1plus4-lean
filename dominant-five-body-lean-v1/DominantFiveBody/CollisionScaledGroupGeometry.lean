import DominantFiveBody.CollisionScaledGroupBounds

/-! # Equal scaled limiting positions give uniform cross-group separation -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1500000

theorem finite_positive_limits_uniform_lower {ι : Type*} (S : Finset ι)
    (F : ℕ → ι → ℝ) (L : ι → ℝ) (hL : ∀ i∈S,0<L i)
    (hF : ∀ i∈S,Tendsto (fun n => F n i) atTop (nhds (L i))) :
    ∃ eta : ℝ,0<eta ∧ ∀ᶠ n in atTop,∀ i∈S,eta≤F n i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,Eventually.of_forall (by simp)⟩
  | @insert i S hi ih =>
    obtain ⟨eta,heta,hbound⟩ := ih (fun j hj => hL j (Finset.mem_insert_of_mem hj))
      (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    have hLi := hL i (Finset.mem_insert_self i S)
    refine ⟨min (L i/2) eta,lt_min (by positivity) heta,?_⟩
    filter_upwards [hbound,(hF i (Finset.mem_insert_self i S)).eventually
      (Ioi_mem_nhds (by linarith : L i/2<L i))] with n hn hiNear
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl|hj
    · exact (min_le_left _ _).trans hiNear.le
    · exact (min_le_right _ _).trans (hn j hj)

theorem equal_scaled_class_cross_separation
    (q : ℕ → SatelliteConfiguration) (d : ℕ → ℝ) (hd : ∀ n,0<d n)
    (E S : Finset Satellite) (hS : S⊆E) (ref : Satellite) (z : Satellite → Plane)
    (hzt : ∀ i∈E,Tendsto (fun n => (d n)⁻¹ • (q n i-q n ref)) atTop (nhds (z i)))
    (hclasses : ∀ i∈S,∀ j∈E\S,z i≠z j) :
    ∃ eta : ℝ,0<eta ∧ ∀ᶠ n in atTop,
      ∀ i∈S,∀ j∈E\S,eta*d n≤satelliteDistance (q n) j i := by
  classical
  let P := S×ˢ(E\S)
  let L : Satellite×Satellite → ℝ := fun ij => ‖z ij.2-z ij.1‖
  have hL : ∀ ij∈P,0<L ij := by
    intro ij hij
    have hp := Finset.mem_product.mp hij
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (hclasses ij.1 hp.1 ij.2 hp.2).symm)
  have hdist : ∀ ij∈P,Tendsto (fun n => satelliteDistance (q n) ij.2 ij.1/d n) atTop (nhds (L ij)) := by
    intro ij hij
    have hp := Finset.mem_product.mp hij
    have ht := (hzt ij.2 (Finset.mem_sdiff.mp hp.2).1).sub (hzt ij.1 (hS hp.1))
    have hv : Tendsto (fun n => (d n)⁻¹ • (q n ij.2-q n ij.1)) atTop (nhds (z ij.2-z ij.1)) := by
      convert! ht using 1
      funext n
      module
    convert! hv.norm using 1
    funext n
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd n)]
    simp only [satelliteDistance,div_eq_mul_inv,mul_comm]
  obtain ⟨eta,heta,hbound⟩ := finite_positive_limits_uniform_lower P
    (fun n ij => satelliteDistance (q n) ij.2 ij.1/d n) L hL hdist
  refine ⟨eta,heta,?_⟩
  filter_upwards [hbound] with n hn
  intro i hi j hj
  exact (le_div_iff₀ (hd n)).mp (hn (i,j) (Finset.mem_product.mpr ⟨hi,hj⟩))

theorem finite_exterior_scaled_difference_bound
    (q : ℕ → SatelliteConfiguration) (q0 : SatelliteConfiguration) (hq : Tendsto q atTop (nhds q0))
    (E : Finset Satellite) (_hE : E.Nonempty) (ref p : Satellite) (c : Plane)
    (href : q0 ref=c) (hcenter : ∀ i∈E,q0 i=c) (hsep : q0 p≠c)
    (d : ℕ → ℝ) (hd : ∀ n,0<d n)
    (hdiam : ∀ n,∀ i∈E,satelliteDistance (q n) ref i≤d n) (v : Plane) (hv : ‖v‖=1) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ n in atTop,∀ i∈E,
      |inner ℝ (newtonTargetField (q n p) (q n i)-newtonTargetField (q n p) (q n ref)) v|≤K*d n := by
  classical
  have hEach : ∀ i : {i // i∈E},∃ K : ℝ,0<K ∧ ∀ᶠ n in atTop,
      ‖newtonTargetField (q n p) (q n i.val)-newtonTargetField (q n p) (q n ref)‖≤K*d n := by
    intro i
    obtain ⟨K,hK,hb⟩ := separated_moving_source_newton_difference_bound q q0 hq ref i.val p c href
      (hcenter i.val i.property) hsep
    refine ⟨K,hK,?_⟩
    filter_upwards [hb] with n hn
    exact hn.trans (mul_le_mul_of_nonneg_left (hdiam n i.val i.property) hK.le)
  choose K hK hb using hEach
  let C : ℝ := (∑ i : {i // i∈E},K i)+1
  have hC : 0<C := by
    dsimp only [C]
    have hs : 0≤∑ i : {i // i∈E},K i := Finset.sum_nonneg (fun i _ => (hK i).le)
    linarith
  have hle (i : {i // i∈E}) : K i≤C := by
    have hs := Finset.single_le_sum (s := Finset.univ) (fun j _ => (hK j).le) (Finset.mem_univ i)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [(eventually_all).mpr hb] with n hn
  intro i hi
  calc
    |inner ℝ (newtonTargetField (q n p) (q n i)-newtonTargetField (q n p) (q n ref)) v|
        ≤‖newtonTargetField (q n p) (q n i)-newtonTargetField (q n p) (q n ref)‖*‖v‖ := abs_real_inner_le_norm _ _
    _≤K ⟨i,hi⟩*d n := by rw [hv,mul_one];exact hn ⟨i,hi⟩
    _≤C*d n := mul_le_mul_of_nonneg_right (hle ⟨i,hi⟩) (hd n).le

end DominantFiveBody
