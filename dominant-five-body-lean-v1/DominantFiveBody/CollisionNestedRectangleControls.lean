import DominantFiveBody.CollisionTripleNestedRectangle

/-! # Actual uniform sign and bounds in the nested polar rectangle -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1500000

def physicalPairExteriorAngularRadialDerivative (mu r theta : Satellite → ℝ)
    (a b : Satellite) (rho v : ℝ) : ℝ :=
  ∑ j∈pairExteriorLabels a b,mu j*physicalSourceAngularRadialDerivative (r j) (theta j) rho v

def physicalPairExteriorAngularAngularDerivative (mu r theta : Satellite → ℝ)
    (a b : Satellite) (rho v : ℝ) : ℝ :=
  ∑ j∈pairExteriorLabels a b,mu j*physicalSourceAngularAngularDerivative (r j) (theta j) rho v

theorem physicalPairExteriorAngularRadialDerivative_eq_selected (mu r theta : Satellite → ℝ)
    (a b c p : Satellite) (hab : a≠b) (hcp : c≠p)
    (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b) (rho v : ℝ) :
    physicalPairExteriorAngularRadialDerivative mu r theta a b rho v=
      mu c*physicalSourceAngularRadialDerivative (r c) (theta c) rho v+
      mu p*physicalSourceAngularRadialDerivative (r p) (theta p) rho v := by
  rw [physicalPairExteriorAngularRadialDerivative,pairExteriorLabels_eq_two a b c p hab hc hp hcp,
    Finset.sum_pair hcp]

theorem physicalPairExteriorAngularAngularDerivative_eq_selected (mu r theta : Satellite → ℝ)
    (a b c p : Satellite) (hab : a≠b) (hcp : c≠p)
    (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b) (rho v : ℝ) :
    physicalPairExteriorAngularAngularDerivative mu r theta a b rho v=
      mu c*physicalSourceAngularAngularDerivative (r c) (theta c) rho v+
      mu p*physicalSourceAngularAngularDerivative (r p) (theta p) rho v := by
  rw [physicalPairExteriorAngularAngularDerivative,pairExteriorLabels_eq_two a b c p hab hc hp hcp,
    Finset.sum_pair hcp]

theorem physicalPairExteriorAngularField_named_derivatives (mu r theta : Satellite → ℝ)
    (a b : Satellite) (rho v : ℝ) (hr : ∀ i,0<r i)
    (hsep : ∀ j∈pairExteriorLabels a b,polarPoint (r j) (theta j)≠polarPoint rho v) :
    HasDerivAt (fun s => physicalPairExteriorAngularField mu r theta a b s v)
      (physicalPairExteriorAngularRadialDerivative mu r theta a b rho v) rho ∧
    HasDerivAt (fun w => physicalPairExteriorAngularField mu r theta a b rho w)
      (physicalPairExteriorAngularAngularDerivative mu r theta a b rho v) v :=
  physical_pair_exterior_angular_derivatives mu r theta a b rho v hr hsep

theorem moving_rectangle_uniform_sign_bound
    (R V : ℕ → ℝ → ℝ → ℝ) (ra rb va vb : ℕ → ℝ) (A B : ℝ) (hA : 0<A) (hB : 0≤B)
    (hU : ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,∀ rho∈uIcc (ra n) (rb n),∀ v∈uIcc (va n) (vb n),
      |R n rho v+A|<eta ∧ |V n rho v-B|<eta) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,∀ rho∈uIcc (ra n) (rb n),∀ v∈uIcc (va n) (vb n),
      R n rho v≤ -C⁻¹ ∧ |R n rho v|+|V n rho v|≤C := by
  let C : ℝ := 2/A+(A+B+2)+1
  have hC : 0<C := by dsimp only [C]; positivity
  have hClower : 2/A≤C := by dsimp only [C]; linarith
  have hCinv : C⁻¹≤A/2 := by
    have hm := mul_le_mul_of_nonneg_left hClower (by linarith : 0≤A/2)
    have he : (A/2)*(2/A)=1 := by field_simp [ne_of_gt hA]
    rw [he] at hm
    simpa only [one_mul] using (mul_inv_le_iff₀ hC).mpr hm
  refine ⟨C,hC,?_⟩
  filter_upwards [hU 1 (by norm_num),hU (A/2) (by positivity)] with n hnOne hnSign
  intro rho hr v hv
  have h1 := hnOne rho hr v hv
  have hs := hnSign rho hr v hv
  have hR : R n rho v≤ -A/2 := by linarith [(le_abs_self (R n rho v+A)).trans hs.1.le]
  refine ⟨by linarith,?_⟩
  have hRabs : |R n rho v|≤|R n rho v+A|+A := by
    calc
      |R n rho v|=|(R n rho v+A)-A| := by congr 1; ring
      _≤|R n rho v+A|+|A| := abs_sub _ _
      _=|R n rho v+A|+A := by rw [abs_of_pos hA]
  have hVabs : |V n rho v|≤|V n rho v-B|+B := by
    calc
      |V n rho v|=|(V n rho v-B)+B| := by congr 1; ring
      _≤|V n rho v-B|+|B| := abs_add_le _ _
      _=|V n rho v-B|+B := by rw [abs_of_nonneg hB]
  have hCU : A+B+2≤C := by dsimp only [C]; linarith [div_pos (by norm_num : (0 : ℝ)<2) hA]
  linarith [h1.1,h1.2]

theorem moving_rectangle_uniform_change_center
    (V : ℕ → ℝ → ℝ → ℝ) (ra rb va vb center : ℕ → ℝ) (B : ℝ)
    (hU : ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,∀ rho∈uIcc (ra n) (rb n),∀ v∈uIcc (va n) (vb n),
      |V n rho v-B|<eta)
    (hcenter : Tendsto center atTop (nhds B)) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,∀ rho∈uIcc (ra n) (rb n),∀ v∈uIcc (va n) (vb n),
      |V n rho v-center n|<eta := by
  intro eta heta
  filter_upwards [hU (eta/2) (by positivity),
    hcenter.eventually (Metric.ball_mem_nhds B (by positivity : 0<eta/2))] with n hn hc
  intro rho hr v hv
  have h1 := hn rho hr v hv
  have h2 : |B-center n|<eta/2 := by simpa only [Real.dist_eq,abs_sub_comm] using hc
  have htriangle : |V n rho v-center n|≤|V n rho v-B|+|B-center n| := by
    convert! abs_add_le (V n rho v-B) (B-center n) using 1
    congr 1
    ring
  linarith

theorem normalized_complete_lower_triple_nested_rectangle_controls
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder standardHullOrder (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,OrderedSemicircle (theta n))
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htt : Tendsto theta atTop (𝓝 theta0))
    (clusterCenter : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 clusterCenter)
    (a b c : TripleLabel) (hab : a<b) (hca : c≠a) (hcb : c≠b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc/
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    (∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,
      ∀ rho∈uIcc (r n a.castSucc) (r n b.castSucc),∀ v∈uIcc (theta n a.castSucc) (theta n b.castSucc),
      physicalPairExteriorAngularRadialDerivative (mu n) (r n) (theta n) a.castSucc b.castSucc rho v≤ -C⁻¹ ∧
      |physicalPairExteriorAngularRadialDerivative (mu n) (r n) (theta n) a.castSucc b.castSucc rho v|+
        |physicalPairExteriorAngularAngularDerivative (mu n) (r n) (theta n) a.castSucc b.castSucc rho v|≤C) ∧
    (∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,
      ∀ rho∈uIcc (r n a.castSucc) (r n b.castSucc),∀ v∈uIcc (theta n a.castSucc) (theta n b.castSucc),
      |physicalPairExteriorAngularAngularDerivative (mu n) (r n) (theta n) a.castSucc b.castSucc rho v-
        ((9/4 : ℝ)+2*mu n c.castSucc/tripleLowDiameter (satellitesRelative (x n))^3)|<eta) := by
  have hcastNe {i j : TripleLabel} (hij : i≠j) : i.castSucc≠j.castSucc := by
    intro he
    apply hij
    apply Fin.ext
    exact congrArg (fun k : Satellite => k.val) he
  have hlowNe (i : TripleLabel) : i.castSucc≠(3 : Satellite) := by fin_cases i <;> decide
  have hc : c.castSucc∈pairExteriorLabels a.castSucc b.castSucc := by
    simp only [pairExteriorLabels,Finset.mem_erase,Finset.mem_univ,and_true]
    exact ⟨hcastNe hcb,hcastNe hca⟩
  have hp : (3 : Satellite)∈pairExteriorLabels a.castSucc b.castSucc := by
    simp only [pairExteriorLabels,Finset.mem_erase,Finset.mem_univ,and_true]
    exact ⟨(hlowNe b).symm,(hlowNe a).symm⟩
  have hU := normalized_complete_lower_triple_nested_rectangle_uniform_limits eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt clusterCenter htriple a b c hab hca hcb hpair
  let R := fun n rho v => physicalPairExteriorAngularRadialDerivative (mu n) (r n) (theta n) a.castSucc b.castSucc rho v
  let V := fun n rho v => physicalPairExteriorAngularAngularDerivative (mu n) (r n) (theta n) a.castSucc b.castSucc rho v
  have hU' : ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,
      ∀ rho∈uIcc (r n a.castSucc) (r n b.castSucc),∀ v∈uIcc (theta n a.castSucc) (theta n b.castSucc),
      |R n rho v+3*Real.sqrt 3/4|<eta ∧ |V n rho v-(27/4 : ℝ)|<eta := by
    simpa only [R,V,physicalPairExteriorAngularRadialDerivative_eq_selected _ _ _ _ _ _ _
      (hcastNe hab.ne) (hlowNe c) hc hp,
      physicalPairExteriorAngularAngularDerivative_eq_selected _ _ _ _ _ _ _
        (hcastNe hab.ne) (hlowNe c) hc hp] using hU
  have hA : 0<3*Real.sqrt 3/4 := by positivity
  refine ⟨moving_rectangle_uniform_sign_bound R V _ _ _ _ (3*Real.sqrt 3/4) (27/4) hA (by norm_num) hU',?_⟩
  have hV : ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,
      ∀ rho∈uIcc (r n a.castSucc) (r n b.castSucc),∀ v∈uIcc (theta n a.castSucc) (theta n b.castSucc),
      |V n rho v-(27/4 : ℝ)|<eta := by
    intro eta heta
    filter_upwards [hU' eta heta] with n hn
    exact fun rho hr v hv => (hn rho hr v hv).2
  have hmc := (normalized_complete_lower_triple_nested_precise_scales eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt clusterCenter htriple a b c hab hca hcb hpair).2.2.2.2.2.1
  have hcenter : Tendsto (fun n => (9/4 : ℝ)+2*mu n c.castSucc/
      tripleLowDiameter (satellitesRelative (x n))^3) atTop (nhds (27/4 : ℝ)) := by
    convert! (hmc.const_mul 2).const_add (9/4) using 1
    · funext n; ring
    · norm_num
  exact moving_rectangle_uniform_change_center V _ _ _ _ _ (27/4) hV hcenter

end DominantFiveBody
