import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The conditional global argument of §7

This file formalizes the quantifier/connectedness part of the proof of
`thm:main`.  The parameter type `P` is arbitrary: specializing it to the *open*
mass simplex retains `∃ δ > 0, ∀ μ, ∀ ε ∈ (0, δ), ...`, without a compactness
or positive-lower-bound assumption on the satellite mass ratios.

The finite-dimensional chart/collision/IFT facts are explicit hypotheses.
None of the declarations in this file is the unconditional five-body theorem.
-/

open Filter Set Topology

namespace DominantFiveBody

universe u v

/-- The uniform quantifier order in §7 / `thm:main`. -/
def UniformBelow {P : Type u} (good : P → ℝ → Prop) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ p ε, 0 < ε → ε < δ → good p ε

/-- A counterexample sequence to a uniform threshold, as used three times
in §7 / `thm:main`. The parameters `p n` may approach the mass boundary. -/
def BadSequence {P : Type u} (good : P → ℝ → Prop) : Prop :=
  ∃ p : ℕ → P, ∃ ε : ℕ → ℝ,
    (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧ ∀ n, ¬ good (p n) (ε n)

/-- §7 / `thm:main`: failure of uniformity supplies bad parameters tending
to zero. The proof chooses `0 < ε n < 1 / (n + 1)` and proves convergence. -/
theorem badSequence_of_not_uniformBelow {P : Type u} {good : P → ℝ → Prop}
    (h : ¬ UniformBelow good) : BadSequence good := by
  classical
  have hbad : ∀ δ : ℝ, 0 < δ → ∃ p ε, 0 < ε ∧ ε < δ ∧ ¬ good p ε := by
    intro δ hδ
    by_contra hnone
    push Not at hnone
    exact h ⟨δ, hδ, fun p ε hε hεδ => hnone p ε hε hεδ⟩
  have hsmall (n : ℕ) : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  choose p ε hε hbound hnot using fun n => hbad _ (hsmall n)
  refine ⟨p, ε, hε, ?_, hnot⟩
  exact tendsto_const_nhds.squeeze tendsto_one_div_add_atTop_nhds_zero_nat
    (fun n => (hε n).le) (fun n => (hbound n).le)

/-- §7 / `thm:main`: a uniform threshold excludes every bad sequence. -/
theorem not_badSequence_of_uniformBelow {P : Type u} {good : P → ℝ → Prop}
    (h : UniformBelow good) : ¬ BadSequence good := by
  rintro ⟨p, ε, hε, hlim, hbad⟩
  rcases h with ⟨δ, hδ, hgood⟩
  have hsmall : ∀ᶠ n in atTop, ε n < δ := hlim.eventually (gt_mem_nhds hδ)
  obtain ⟨n, hn⟩ := hsmall.exists
  exact hbad n (hgood (p n) (ε n) (hε n) hn)

/-- §7 / `thm:main`: sequence exclusion implies a single positive threshold
before the parameter and ε quantifiers. -/
theorem uniformBelow_of_no_badSequence {P : Type u} {good : P → ℝ → Prop}
    (h : ¬ BadSequence good) : UniformBelow good := by
  by_contra hn
  exact h (badSequence_of_not_uniformBelow hn)

/-- Exact equivalence used in all three threshold contradiction arguments
of §7 / `thm:main`. -/
theorem uniformBelow_iff_no_badSequence {P : Type u} (good : P → ℝ → Prop) :
    UniformBelow good ↔ ¬ BadSequence good :=
  ⟨not_badSequence_of_uniformBelow, uniformBelow_of_no_badSequence⟩

/-- The final finite minimum in §7 / `thm:main`, with all positivity and
restriction inequalities proved. -/
theorem uniformBelow_three {P : Type u} {A B C : P → ℝ → Prop}
    (hA : UniformBelow A) (hB : UniformBelow B) (hC : UniformBelow C) :
    UniformBelow (fun p ε => A p ε ∧ B p ε ∧ C p ε) := by
  rcases hA with ⟨δA, hδA, hA⟩
  rcases hB with ⟨δB, hδB, hB⟩
  rcases hC with ⟨δC, hδC, hC⟩
  refine ⟨min δA (min δB δC), lt_min hδA (lt_min hδB hδC), ?_⟩
  intro p ε hε hδ
  exact ⟨hA p ε hε (lt_of_lt_of_le hδ (min_le_left _ _)),
    hB p ε hε (lt_of_lt_of_le hδ ((min_le_right _ _).trans (min_le_left _ _))),
    hC p ε hε (lt_of_lt_of_le hδ ((min_le_right _ _).trans (min_le_right _ _)))⟩

/-- Local uniqueness supplied by a regular chart/IFT, in the precise form
used to make the branch equality set open in §7 / `thm:main`.
This is an explicit *condition*, not a definition of geometric uniqueness. -/
def LocalRootUniqueness {T : Type u} {Y : Type v}
    [TopologicalSpace T] [TopologicalSpace Y] (root : T → Y → Prop) : Prop :=
  ∀ t y, root t y → ∃ V ∈ 𝓝 y,
    ∀ᶠ s in 𝓝 t, ∀ a ∈ V, ∀ b ∈ V, root s a → root s b → a = b

/-- The open part of the open/closed branch comparison in §7 / `thm:main`.
Continuity puts both roots in the same chart neighborhood. -/
theorem isOpen_branch_eq_of_localUniqueness
    {T : Type u} {Y : Type v} [TopologicalSpace T] [TopologicalSpace Y]
    {root : T → Y → Prop} (hlocal : LocalRootUniqueness root)
    {f g : T → Y} (hf : Continuous f) (hg : Continuous g)
    (hfr : ∀ t, root t (f t)) (hgr : ∀ t, root t (g t)) :
    IsOpen {t | f t = g t} := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  obtain ⟨V, hV, huniq⟩ := hlocal t (f t) (hfr t)
  have hfV : ∀ᶠ s in 𝓝 t, f s ∈ V := hf.continuousAt.eventually hV
  have hgV : ∀ᶠ s in 𝓝 t, g s ∈ V := by
    rw [ht] at hV
    exact hg.continuousAt.eventually hV
  filter_upwards [huniq, hfV, hgV] with s hs hfs hgs
  exact hs _ hfs _ hgs (hfr s) (hgr s)

/-- §7 / `thm:main`: continuous branches in a Hausdorff target with local
root uniqueness agree throughout a preconnected parameter space once they
agree at one point. The equality set is proved both open and closed. -/
theorem branches_eq_of_localUniqueness
    {T : Type u} {Y : Type v} [TopologicalSpace T] [PreconnectedSpace T]
    [TopologicalSpace Y] [T2Space Y]
    {root : T → Y → Prop} (hlocal : LocalRootUniqueness root)
    {f g : T → Y} (hf : Continuous f) (hg : Continuous g)
    (hfr : ∀ t, root t (f t)) (hgr : ∀ t, root t (g t))
    (t₀ : T) (hzero : f t₀ = g t₀) : f = g := by
  have hc : IsClopen {t | f t = g t} :=
    ⟨isClosed_eq hf hg, isOpen_branch_eq_of_localUniqueness hlocal hf hg hfr hgr⟩
  have hall : {t | f t = g t} = univ := hc.eq_univ ⟨t₀, hzero⟩
  funext t
  have ht : t ∈ {t | f t = g t} := by rw [hall]; trivial
  exact ht

/-- The common half-open connection interval in Proposition 7.1
(`prop:connection`), equipped with its subspace topology. -/
abbrev ConnectionInterval (τ : ℝ) := ↥(Ico (0 : ℝ) τ)

/-- §7 / `thm:main`: the preceding open/closed argument applies to precisely
the paper's `[0, τ)` domain, including the zero endpoint. -/
theorem branches_eq_on_connectionInterval
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] {τ : ℝ} (hτ : 0 < τ)
    {root : ConnectionInterval τ → Y → Prop} (hlocal : LocalRootUniqueness root)
    {f g : ConnectionInterval τ → Y} (hf : Continuous f) (hg : Continuous g)
    (hfr : ∀ t, root t (f t)) (hgr : ∀ t, root t (g t))
    (hzero : f ⟨0, le_rfl, hτ⟩ = g ⟨0, le_rfl, hτ⟩) : f = g := by
  let : PreconnectedSpace (ConnectionInterval τ) :=
    Subtype.preconnectedSpace isPreconnected_Ico
  exact branches_eq_of_localUniqueness hlocal hf hg hfr hgr _ hzero

/-- Proposition 7.1 (`prop:connection`) together with the endpoint
identification by Theorem 2.2 (`thm:coorbital`), with the essential common
interval and fixed-mass endpoint explicit. Smoothness implies the
continuity recorded here; differentiability is not needed in §7 once the
local chart uniqueness hypothesis is supplied separately.

`root` and `nondegenerate` must later be instantiated with the actual
normalized central-configuration and constrained-Hessian predicates.
This structure has no instance supplied for the five-body problem. -/
structure CapturedBranches {P : Type u} {Y : Type v} [TopologicalSpace Y]
    (root nondegenerate : P → ℝ → Y → Prop) (endpoint : P → Y)
    (p : ℕ → P) (ε : ℕ → ℝ) (y : ℕ → Y) where
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  radius : ℝ
  radius_pos : 0 < radius
  parameters_lt_radius : ∀ n, ε (subseq n) < radius
  branch : ℕ → ℝ → Y
  continuous : ∀ n, ContinuousOn (branch n) (Ico 0 radius)
  hits : ∀ n, branch n (ε (subseq n)) = y (subseq n)
  roots : ∀ n s, 0 < s → s < radius → root (p (subseq n)) s (branch n s)
  nondegenerate_at : ∀ n s, 0 < s → s < radius →
    nondegenerate (p (subseq n)) s (branch n s)
  endpoints : ∀ n, branch n 0 = endpoint (p (subseq n))

/-- Explicit conditional form of Proposition 7.1 (`prop:connection`):
every *actual root sequence* has a captured subsequence. In particular,
one cannot apply this to a sequence of parameters with no roots. -/
def ConnectionProperty {P : Type u} {Y : Type v} [TopologicalSpace Y]
    (root nondegenerate : P → ℝ → Y → Prop) (endpoint : P → Y) : Prop :=
  ∀ (p : ℕ → P) (ε : ℕ → ℝ) (y : ℕ → Y),
    (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    (∀ n, root (p n) (ε n) (y n)) →
    Nonempty (CapturedBranches root nondegenerate endpoint p ε y)

/-- The local existence part of Proposition 3.3 (`prop:local`). Its radius
may depend on the fixed positive mass parameter, and is never reported as
a uniform radius. -/
def FixedParameterLocalExistence {P : Type u} {Y : Type v}
    (root : P → ℝ → Y → Prop) : Prop :=
  ∀ p, ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ ε, 0 < ε → ε < ℓ → ∃ y, root p ε y

/-- The root relation used only for comparing captured branches on
`[0, τ)`: at zero it records the unique coorbital endpoint; at positive
parameters it records an actual root and its geometric nondegeneracy.
This is not the definition of a central configuration or of a Hessian. -/
def ContinuationRoot {P : Type u} {Y : Type v}
    (root nondegenerate : P → ℝ → Y → Prop) (endpoint : P → Y)
    (p : P) (ε : ℝ) (y : Y) : Prop :=
  (ε = 0 ∧ y = endpoint p) ∨ (0 < ε ∧ root p ε y ∧ nondegenerate p ε y)

/-- The fixed-mass local uniqueness required in the open/closed proof of
§7 / `thm:main`. At zero it must come from Proposition 3.3 and Theorem 2.2;
at positive parameters it must come from Lemma 3.1 and the IFT.
It is an unimplemented conditional interface in this development. -/
def LocalContinuationUniqueness {P : Type u} {Y : Type v}
    [TopologicalSpace Y] (root nondegenerate : P → ℝ → Y → Prop)
    (endpoint : P → Y) : Prop :=
  ∀ p τ, 0 < τ → LocalRootUniqueness
    (fun s : ConnectionInterval τ => ContinuationRoot root nondegenerate endpoint p s)

namespace CapturedBranches

/-- Restricting a captured branch to a smaller common connection interval
preserves continuity; this is used for two successive captures in §7. -/
theorem continuous_restrict {P : Type u} {Y : Type v} [TopologicalSpace Y]
    {root nondegenerate : P → ℝ → Y → Prop} {endpoint : P → Y}
    {p : ℕ → P} {ε : ℕ → ℝ} {y : ℕ → Y}
    (c : CapturedBranches root nondegenerate endpoint p ε y)
    (n : ℕ) {τ : ℝ} (hτ : τ ≤ c.radius) :
    Continuous (fun s : ConnectionInterval τ => c.branch n s) := by
  exact (c.continuous n).comp_continuous continuous_subtype_val
    (fun s => ⟨s.property.1, lt_of_lt_of_le s.property.2 hτ⟩)

/-- Captured branches satisfy the zero/positive continuation relation
throughout their domain, retaining the current fixed mass parameter. -/
theorem continuationRoot {P : Type u} {Y : Type v} [TopologicalSpace Y]
    {root nondegenerate : P → ℝ → Y → Prop} {endpoint : P → Y}
    {p : ℕ → P} {ε : ℕ → ℝ} {y : ℕ → Y}
    (c : CapturedBranches root nondegenerate endpoint p ε y)
    (n : ℕ) {s : ℝ} (hs : 0 ≤ s) (hbound : s < c.radius) :
    ContinuationRoot root nondegenerate endpoint (p (c.subseq n)) s (c.branch n s) := by
  by_cases hzero : s = 0
  · subst s
    exact Or.inl ⟨rfl, c.endpoints n⟩
  · have hpos : 0 < s := lt_of_le_of_ne hs (Ne.symm hzero)
    exact Or.inr ⟨hpos, c.roots n s hpos hbound, c.nondegenerate_at n s hpos hbound⟩

end CapturedBranches

/-- §7 / `thm:main`, existence contradiction. Auxiliary roots are first
obtained below both the bad parameter and the fixed-parameter local
radius. The connection theorem is applied to those roots, never to the
empty fibers. A common captured interval then reaches the bad parameters. -/
theorem uniform_existence_of_connection
    {P : Type u} {Y : Type v} [TopologicalSpace Y]
    {root nondegenerate : P → ℝ → Y → Prop} {endpoint : P → Y}
    (hlocal : FixedParameterLocalExistence root)
    (hconnection : ConnectionProperty root nondegenerate endpoint) :
    UniformBelow (fun p ε => ∃ y, root p ε y) := by
  classical
  apply uniformBelow_of_no_badSequence
  rintro ⟨p, ε, hε, hlim, hbad⟩
  choose ℓ hℓ hlocalRoots using hlocal
  let s : ℕ → ℝ := fun n => min (ε n) (ℓ (p n)) / 2
  have hspos (n : ℕ) : 0 < s n := by
    dsimp [s]
    exact div_pos (lt_min (hε n) (hℓ (p n))) (by norm_num)
  have hsε (n : ℕ) : s n < ε n := by
    dsimp [s]
    have hm : min (ε n) (ℓ (p n)) ≤ ε n := min_le_left _ _
    linarith [hε n]
  have hsℓ (n : ℕ) : s n < ℓ (p n) := by
    dsimp [s]
    have hm : min (ε n) (ℓ (p n)) ≤ ℓ (p n) := min_le_right _ _
    linarith [hℓ (p n)]
  have hslim : Tendsto s atTop (𝓝 0) :=
    tendsto_const_nhds.squeeze hlim (fun n => (hspos n).le) (fun n => (hsε n).le)
  choose z hz using fun n => hlocalRoots (p n) (s n) (hspos n) (hsℓ n)
  obtain ⟨c⟩ := hconnection p s z hspos hslim hz
  have hsmall : ∀ᶠ n in atTop, ε (c.subseq n) < c.radius :=
    (hlim.comp c.subseq_strictMono.tendsto_atTop).eventually (gt_mem_nhds c.radius_pos)
  obtain ⟨n, hn⟩ := hsmall.exists
  exact hbad (c.subseq n) ⟨c.branch n (ε (c.subseq n)),
    c.roots n _ (hε (c.subseq n)) hn⟩

/-- §7 / `thm:main`, nondegeneracy contradiction. Every selected root is
equal to its captured branch value, where geometric nondegeneracy is an
explicit field of Proposition 7.1. -/
theorem uniform_nondegeneracy_of_connection
    {P : Type u} {Y : Type v} [TopologicalSpace Y]
    {root nondegenerate : P → ℝ → Y → Prop} {endpoint : P → Y}
    (hconnection : ConnectionProperty root nondegenerate endpoint) :
    UniformBelow (fun p ε => ∀ y, root p ε y → nondegenerate p ε y) := by
  classical
  apply uniformBelow_of_no_badSequence
  rintro ⟨p, ε, hε, hlim, hbad⟩
  have hwitness (n : ℕ) : ∃ y, root (p n) (ε n) y ∧ ¬ nondegenerate (p n) (ε n) y := by
    have hn := hbad n
    push Not at hn
    exact hn
  choose y hy hdeg using hwitness
  obtain ⟨c⟩ := hconnection p ε y hε hlim hy
  have hsmall : ∀ᶠ n in atTop, ε (c.subseq n) < c.radius :=
    (hlim.comp c.subseq_strictMono.tendsto_atTop).eventually (gt_mem_nhds c.radius_pos)
  obtain ⟨n, hn⟩ := hsmall.exists
  have hnd := c.nondegenerate_at n (ε (c.subseq n)) (hε (c.subseq n)) hn
  rw [c.hits n] at hnd
  exact hdeg (c.subseq n) hnd

/-- §7 / `thm:main`, uniqueness contradiction, using the two successive
subsequence captures and the common finite-minimum connection interval.
The endpoint uniqueness and IFT steps are explicit `hlocal` hypotheses. -/
theorem uniform_uniqueness_of_connection
    {P : Type u} {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    {root nondegenerate : P → ℝ → Y → Prop} {endpoint : P → Y}
    (hlocal : LocalContinuationUniqueness root nondegenerate endpoint)
    (hconnection : ConnectionProperty root nondegenerate endpoint) :
    UniformBelow (fun p ε => ∀ y z, root p ε y → root p ε z → y = z) := by
  classical
  apply uniformBelow_of_no_badSequence
  rintro ⟨p, ε, hε, hlim, hbad⟩
  have hwitness (n : ℕ) : ∃ y z, root (p n) (ε n) y ∧ root (p n) (ε n) z ∧ y ≠ z := by
    have hn := hbad n
    push Not at hn
    exact hn
  choose y z hy hz hne using hwitness
  obtain ⟨c₁⟩ := hconnection p ε y hε hlim hy
  obtain ⟨c₂⟩ := hconnection (p ∘ c₁.subseq) (ε ∘ c₁.subseq) (z ∘ c₁.subseq)
    (fun n => hε _) (hlim.comp c₁.subseq_strictMono.tendsto_atTop)
    (fun n => hz _)
  let τ : ℝ := min c₁.radius c₂.radius
  have hτ : 0 < τ := lt_min c₁.radius_pos c₂.radius_pos
  have hlim₂ : Tendsto (ε ∘ c₁.subseq ∘ c₂.subseq) atTop (𝓝 0) :=
    (hlim.comp c₁.subseq_strictMono.tendsto_atTop).comp c₂.subseq_strictMono.tendsto_atTop
  have hsmall : ∀ᶠ n in atTop, ε (c₁.subseq (c₂.subseq n)) < τ :=
    hlim₂.eventually (gt_mem_nhds hτ)
  obtain ⟨n, hn⟩ := hsmall.exists
  let f : ConnectionInterval τ → Y := fun s => c₁.branch (c₂.subseq n) s
  let g : ConnectionInterval τ → Y := fun s => c₂.branch n s
  have hf : Continuous f := c₁.continuous_restrict _ (min_le_left _ _)
  have hg : Continuous g := c₂.continuous_restrict _ (min_le_right _ _)
  have hfr (s : ConnectionInterval τ) :
      ContinuationRoot root nondegenerate endpoint (p (c₁.subseq (c₂.subseq n))) s (f s) :=
    c₁.continuationRoot _ s.property.1 (lt_of_lt_of_le s.property.2 (min_le_left _ _))
  have hgr (s : ConnectionInterval τ) :
      ContinuationRoot root nondegenerate endpoint (p (c₁.subseq (c₂.subseq n))) s (g s) :=
    c₂.continuationRoot _ s.property.1 (lt_of_lt_of_le s.property.2 (min_le_right _ _))
  have hzero : f ⟨0, le_rfl, hτ⟩ = g ⟨0, le_rfl, hτ⟩ := by
    exact (c₁.endpoints (c₂.subseq n)).trans (c₂.endpoints n).symm
  have hfg : f = g := branches_eq_on_connectionInterval hτ
    (hlocal _ τ hτ) hf hg hfr hgr hzero
  let sₙ : ConnectionInterval τ := ⟨ε (c₁.subseq (c₂.subseq n)),
    (hε _).le, hn⟩
  have heq : c₁.branch (c₂.subseq n) (ε (c₁.subseq (c₂.subseq n))) =
      c₂.branch n (ε (c₁.subseq (c₂.subseq n))) := congrFun hfg sₙ
  exact hne _ ((c₁.hits (c₂.subseq n)).symm.trans (heq.trans (c₂.hits n)))

/-- Conditional §7 / `thm:main` assembly, retaining the requested uniform
quantifier order and taking all three positive bounds at once.
The hypotheses are not yet instantiated by the five-body chart analysis. -/
theorem main_of_chart_facts
    {P : Type u} {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    {root nondegenerate : P → ℝ → Y → Prop} {endpoint : P → Y}
    (hexistence : FixedParameterLocalExistence root)
    (huniqueness : LocalContinuationUniqueness root nondegenerate endpoint)
    (hconnection : ConnectionProperty root nondegenerate endpoint) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ε, 0 < ε → ε < δ →
      (∃! y, root p ε y) ∧ (∀ y, root p ε y → nondegenerate p ε y) := by
  have h := uniformBelow_three (uniform_existence_of_connection hexistence hconnection)
    (uniform_uniqueness_of_connection huniqueness hconnection)
    (uniform_nondegeneracy_of_connection hconnection)
  rcases h with ⟨δ, hδ, hall⟩
  refine ⟨δ, hδ, ?_⟩
  intro p ε hε hεδ
  rcases hall p ε hε hεδ with ⟨⟨y, hy⟩, huniq, hnd⟩
  exact ⟨⟨y, hy, fun z hz => huniq z y hz hy⟩, hnd⟩

end DominantFiveBody
