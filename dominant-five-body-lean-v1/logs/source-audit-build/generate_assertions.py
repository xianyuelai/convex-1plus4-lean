"""Inventory the unchanged supplied source, without promoting partial proofs."""
from pathlib import Path
import hashlib, json, re

root = Path(__file__).resolve().parents[2]
source = root / 'source/dominant_five_body_ARMA_rewritten.tex'
tex = source.read_text(encoding='utf-8')
lines = tex.splitlines()
aux = (root / 'logs/source-audit-build/manuscript.aux').read_text(encoding='utf-8')
page_by_label = {m[1]: int(m[2]) for m in re.finditer(r'\\newlabel\{([^}]+)\}\{\{[^}]*\}\{(\d+)\}', aux)}

def location(start, end, labels=()):
    pages = sorted({page_by_label[k] for k in labels if k in page_by_label})
    return {'tex_path': 'source/dominant_five_body_ARMA_rewritten.tex',
            'tex_lines': [start + 1, end + 1], 'pdf_pages_from_aux_labels': pages}

assertions = []
occupied = set()

def add(id, start, end, exact, kind, labels=()):
    assertions.append({'id': id, 'source_location': location(start, end, labels),
        'paper_location': ', '.join(labels) if labels else f'TeX:{start+1}-{end+1}',
        'exact_claim': exact, 'claim_kind': kind, 'lean_declaration': None,
        'lean_statement': None, 'remaining_dependencies': [
            'A faithful current Lean declaration proving this complete source assertion has not yet been bound.'],
        'status': 'OPEN'})

start_body = next(i for i, s in enumerate(lines) if s == r'\begin{abstract}')
end_body = next(i for i, s in enumerate(lines) if s == r'\section*{Statements and Declarations}')

# Complete numbered assertions, retaining every hypothesis and conclusion.
for i in range(start_body, end_body):
    m = re.search(r'\\begin\{(theorem|proposition|lemma)\}', lines[i])
    if not m:
        continue
    kind = m[1]
    end = next(j for j in range(i, end_body) if rf'\end{{{kind}}}' in lines[j])
    block = '\n'.join(lines[i:end+1])
    labels = re.findall(r'\\label\{([^}]+)\}', block)
    add(labels[0] if labels else f'{kind}:{i+1}', i, end, block, 'numbered_assertion', labels)

# Every mathematical display, including all unnumbered asymptotics, limits,
# chart matrices, area factors, and capture assertions.
i = start_body
while i < end_body:
    s = lines[i]
    m = re.search(r'\\begin\{(equation|align|gather)\*?\}', s)
    if m or s.strip() == r'\[':
        if m:
            env = m[0].replace(r'\begin', r'\end')
            end = next(j for j in range(i, end_body) if env in lines[j])
        else:
            end = next(j for j in range(i+1, end_body) if lines[j].strip() == r'\]')
        block = '\n'.join(lines[i:end+1])
        labels = re.findall(r'\\label\{([^}]+)\}', block)
        if labels:
            for label in labels:
                add(label, i, end, block, 'displayed_assertion', labels)
        else:
            add(f'display:{i+1}', i, end, block, 'displayed_assertion')
        occupied.update(range(i, end+1))
        i = end+1
    else:
        i += 1

# Source prose carries substantive assertions outside numbered results: open
# semicircle equivalence, matrix positive definiteness, smooth signed-scale
# extension, current-weight averaging, four-type exhaustion, root capture,
# positive area quotients, common intervals, relabeling, and normalization.
i = start_body
while i < end_body:
    if i in occupied or not lines[i].strip():
        i += 1
        continue
    end = i
    while end+1 < end_body and end+1 not in occupied and lines[end+1].strip():
        end += 1
    selected = []
    for line in lines[i:end+1]:
        line = re.sub(r'\\(?:begin|end)\{(?:abstract|proof|theorem|proposition|lemma)\}(?:\[[^]]*\])?', '', line)
        line = re.sub(r'\\label\{[^}]+\}', '', line)
        if re.match(r'^\s*\\(?:section|subsection|paragraph)', line):
            continue
        if line.strip():
            selected.append(line)
    if selected:
        add(f'prose:{i+1}', i, end, '\n'.join(selected), 'prose_assertion')
    i = end+1

def bind(id, declaration, statement, dependencies=(), note=None):
    entry = next(e for e in assertions if e['id'] == id)
    entry['lean_declaration'] = declaration
    entry['lean_statement'] = statement
    entry['remaining_dependencies'] = list(dependencies)
    entry['status'] = 'VERIFIED' if not dependencies else 'CONDITIONAL'
    if note:
        entry['proof_route_note'] = note

numbered_dependencies = {
    'prop:closed': ['Pointwise kernel/deleted inverse and uniform closed-root inverse are now individually proved; the complete packaged type and source gauge correspondence await binding.'],
    'lem:hessian': ['Actual U/G second differential, rotation kernel, radial 3I splitting and complete fixed-first-angle physical shape/Jacobian bridge are proved. Generic smooth coordinate/row transformation preservation is proved. The source assertion allowing any other positive mass angular row to be omitted still requires its concrete invertible row-replacement derivative transport to be bound.'],
    'prop:local': ['Actual coorbital graph; complete compact-base IFT; actual ε=0 seven-by-seven derivative; geometric strict convexity and actual constrained Hessian nondegeneracy.'],
    'prop:pair-scale': ['Actual complete-pair adjacency and fixed-label limits; radial/tangential alternative; support exclusion of radial pair; ν→0 and all exact rates; exterior separation; two-pair exclusion; probe equation and positive scale limit.'],
    'prop:triple-scale': ['Endpoint block classification; exact exterior J derivatives; first/last angular estimates; current-weight rescaled group averages; radial o(d); angular width/d→1; ν/d³ upper and lower bounds without a mass-fraction floor.'],
    'prop:nested-scale': ['Actual shortest-pair adjacency; near/exterior derivative control; support exclusion of radial alternative; ξ/ν→0; current-weight macro average identity and ν/d³→D0; ξ/s³→3D0 and radial O(εs) independent of pair fractions.'],
    'prop:chart-interface': ['All four actual regularized chart constructions; positive denominator and exact row recovery; independent products; actual signed-area factorizations and positivity; physical shape Hessian correspondence; capture; fixed same positive mass endpoints and a common interval.'],
    'prop:connection': ['Actual complete collision classification and all four chart captures; source-normalized representative correspondence; same-mass branch endpoints; strict convexity and actual shape nondegeneracy on a common interval.']}
for entry in assertions:
    if entry['id'] in numbered_dependencies:
        entry['remaining_dependencies'] = numbered_dependencies[entry['id']]

lemma_cycle_type = '''∀ (n : ℕ) (_hn₂ : 2 ≤ n) (_hn₄ : n ≤ 4) (mass theta : Fin n → ℝ),
  (∀ i, 0 < mass i) → DominantFiveBody.OrderedSemicircle theta →
  (∀ i, DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
  (∀ i j, i < j → 0 < DominantFiveBody.Coorbital.positiveRemainder (theta j-theta i)) ∧
  (∀ u, DominantFiveBody.angularChordHessian mass theta u u =
      DominantFiveBody.Coorbital.coorbitalKappaForm mass theta u ∧
    DominantFiveBody.Coorbital.coorbitalRemainderForm mass theta u ≤
      DominantFiveBody.angularChordHessian mass theta u u) ∧
  (∀ u, (∀ v, DominantFiveBody.angularChordHessian mass theta u v = 0) ↔
    ∀ i j, u i = u j)'''
bind('lem:cycle', 'DominantFiveBody.angular_hessian_estimate', lemma_cycle_type,
     note='The scalar proof uses the mean value theorem and the finite cycle proof uses explicit algebraic decomposition. Original integral and general flow-decomposition derivations remain separate OPEN assertions.')
bind('eq:cycle-bound', 'DominantFiveBody.Coorbital.coorbital_cycle_bound', '''∀ (n : ℕ) (_hn₂ : 2 ≤ n) (_hn₄ : n ≤ 4)
  (mass theta u : Fin n → ℝ), (∀ i, 0 < mass i) →
  (∀ i j, i < j → 0 < theta j-theta i ∧ theta j-theta i < Real.pi) →
  (∀ i, DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
  DominantFiveBody.Coorbital.coorbitalRemainderForm mass theta u ≤
    DominantFiveBody.Coorbital.coorbitalKappaForm mass theta u''')

probe_type = '''∀ (p q x : ℝ), 0 ≤ p → 0 ≤ q → p+q = 1 → x ≠ 0 →
  x ≠ DominantFiveBody.Coorbital.h → DominantFiveBody.twoSourceSpan x < Real.pi →
  p * DominantFiveBody.coorbitalKernel x +
    q * DominantFiveBody.coorbitalKernel (x-DominantFiveBody.Coorbital.h) = 0 →
  0 < p * DominantFiveBody.Coorbital.kappa |x| +
    q * DominantFiveBody.Coorbital.kappa |x-DominantFiveBody.Coorbital.h|'''
bind('lem:probe', 'DominantFiveBody.twoSourceProbe', probe_type)
bind('display:181', 'DominantFiveBody.twoSourceProbe', probe_type)
bind('prop:closed', 'DominantFiveBody.coorbital_closed_mass_jacobian_complete', '''
  (∀ mass theta : DominantFiveBody.Satellite → ℝ,
    (∀ i, 0 ≤ mass i) → (∑ i, mass i) = 1 →
    DominantFiveBody.SeparatedSemicircle theta →
    (∀ i, DominantFiveBody.coorbitalResidual mass theta i = 0) →
    HasFDerivAt (fun angles i => DominantFiveBody.coorbitalResidual mass angles i)
      (DominantFiveBody.angularDifferential mass theta) theta ∧
    (∀ u, DominantFiveBody.angularDifferential mass theta u = 0 ↔ ∀ i j, u i = u j) ∧
    (∀ p q, 0 < mass p → IsUnit (DominantFiveBody.deletedAngularJacobian mass theta p q))) ∧
  (∀ (K : Set ((DominantFiveBody.Satellite → ℝ) × (DominantFiveBody.Satellite → ℝ)))
    (delta eta : ℝ) (p q : DominantFiveBody.Satellite), IsClosed K → 0 < delta → 0 < eta →
    (∀ z ∈ K, (∀ i, 0 ≤ z.1 i) ∧ (∑ i, z.1 i) = 1 ∧ z.2 0 = 0 ∧
      (∀ i : Fin 3, delta ≤ z.2 i.succ - z.2 i.castSucc) ∧
      z.2 3 - z.2 0 ≤ Real.pi - eta ∧ (1 / 4 : ℝ) ≤ z.1 p ∧
      (∀ i, DominantFiveBody.coorbitalResidual z.1 z.2 i = 0)) →
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ‖(DominantFiveBody.deletedAngularJacobian z.1 z.2 p q)⁻¹‖ ≤ C)''',
    note='All original labels are allowed pointwise. The uniform closed-set clause uses the manuscript translation gauge theta 0=0; the actual finite permutation and original-label transport are proved.')
bind('eq:distance', 'DominantFiveBody.polar_distance_sq', '''∀ (r s a b : ℝ),
  ‖DominantFiveBody.polarPoint s b-DominantFiveBody.polarPoint r a‖^2 =
    (s-r)^2+4*r*s*Real.sin ((b-a)/2)^2''')
bind('eq:full-cut', 'DominantFiveBody.full_angular_cut', '''∀ (ε : ℝ)
  (μ r theta : DominantFiveBody.Satellite → ℝ),
  (∀ i, DominantFiveBody.angularResidual ε μ r theta i = 0) →
  ∀ (S : Finset DominantFiveBody.Satellite),
  (∑ i ∈ S, ∑ j ∈ Sᶜ, DominantFiveBody.fullAngularPair ε μ r theta i j) = 0''',
  note='The named pair expands to the actual μ_i μ_j ρ_i ρ_j sin(angle difference) times the physical distance inverse cube minus c_epsilon. Every subset is allowed, including the original initial-segment cuts.')
bind('eq:action', 'DominantFiveBody.relativeAction_eq_augmentedPotential_div', '''∀
  (eps : ℝ) (mu : DominantFiveBody.MassRatio), (∑ i, mu i) = 1 → eps ≠ 0 → 1+eps ≠ 0 →
  ∀ (q : DominantFiveBody.SatelliteConfiguration), DominantFiveBody.relativeAction eps mu q =
  DominantFiveBody.augmentedPotential (DominantFiveBody.masses eps mu) 1
    (DominantFiveBody.centeredFromRelative eps mu q) / eps''')

def subclaim(id, line, exact, declaration, statement, dependencies=()):
    add(id, line-1, line-1, exact, 'source_subclaim')
    bind(id, declaration, statement, dependencies)

subclaim('prop:uniform.diameter', 324,
    'For every ε>0, every positive ratio μ of sum one, and every actual centered multiplier-one configuration x, diam(x)≤4(1+ε)^(1/3).',
    'DominantFiveBody.dominant_normalized_diameter_le', '''∀ (ε : ℝ) (μ : DominantFiveBody.MassRatio),
  0 < ε → DominantFiveBody.PositiveRatio μ → ∀ (x : DominantFiveBody.Configuration),
  DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses ε μ) x →
  Metric.diam (Set.range x) ≤ 4 * Real.rpow (1 + ε) (1 / 3)''')
subclaim('prop:uniform.current_cluster_force_cancellation', 339,
    'For every subset of labels, the mass-weighted internal Newtonian forces cancel using the current masses.',
    'DominantFiveBody.cluster_internal_force_zero', '''∀ (m : DominantFiveBody.MassVector)
  (x : DominantFiveBody.Configuration) (S : Finset DominantFiveBody.Label),
  (∑ i ∈ S, ∑ j ∈ S, DominantFiveBody.pairForce m x i j) = 0''')
subclaim('prop:uniform.exact_cluster_virial', 342,
    'For every nonempty current-mass cluster of an actual normalized solution, U_C=I_C+Σ m_i(x_i-b)·(A(x_i)-Acenter). Acenter can be the exterior acceleration at b.',
    'DominantFiveBody.normalized_cluster_virial', '''∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m → ∀ (x : DominantFiveBody.Configuration),
  DominantFiveBody.NormalizedCentralConfiguration m x → ∀ (S : Finset DominantFiveBody.Label),
  S.Nonempty → ∀ (Acenter : DominantFiveBody.Plane),
  DominantFiveBody.clusterPotential m x S = DominantFiveBody.clusterInertia m x S +
  ∑ i ∈ S, m i * inner ℝ (x i-DominantFiveBody.clusterCenter m x S)
    (DominantFiveBody.exteriorAcceleration m x S i-Acenter)''')
subclaim('prop:uniform.lower_radius', 324,
    'For every E>0 there exists b(E)>0 before all positive ratios and all actual normalized configurations with 0<ε≤E, such that every primary-relative satellite radius is at least b(E).',
    'DominantFiveBody.dominant_primary_relative_radius_lower', '''∀ (E : ℝ), 0 < E →
  ∃ b : ℝ, 0 < b ∧ ∀ (ε : ℝ) (μ : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
  0 < ε → ε ≤ E → DominantFiveBody.PositiveRatio μ →
  DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses ε μ) x →
  ∀ i : DominantFiveBody.Satellite, b ≤ ‖DominantFiveBody.satellitesRelative x i‖''')
subclaim('prop:uniform.uniform_radius_to_one', 324,
    'Uniformly over every positive satellite mass ratio and every actual normalized configuration, all four primary-relative radii tend to one as ε tends to zero. For each η>0 one common δ>0 precedes all positive ratios and configurations.',
    'DominantFiveBody.dominant_primary_relative_radii_uniform', '''∀ (η : ℝ), 0 < η →
  ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ) (μ : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
  0 < ε → ε < δ → DominantFiveBody.PositiveRatio μ →
  DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses ε μ) x →
  ∀ i : DominantFiveBody.Satellite, |‖DominantFiveBody.satellitesRelative x i‖-1| < η''')
subclaim('eq:action.inertia_reduction', 244,
    'The actual centered inertia in primary-relative coordinates is I=ε Σ μ_i‖q_i‖²−ε²/(1+ε)‖X‖²; the sum-one and nonzero denominator hypotheses are explicit.',
    'DominantFiveBody.inertia_centeredFromRelative', '''∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio),
  (∑ i, mu i) = 1 → 1+eps ≠ 0 → ∀ (q : DominantFiveBody.SatelliteConfiguration),
  DominantFiveBody.inertia (DominantFiveBody.masses eps mu)
    (DominantFiveBody.centeredFromRelative eps mu q) =
  eps * (∑ i, mu i * ‖q i‖^2) - eps^2/(1+eps) * ‖DominantFiveBody.relativeAverage mu q‖^2''')
subclaim('kernel.collision_blowup', 112,
    't f(t) tends to +∞ as t tends to zero from above.',
    'DominantFiveBody.kernelF_angle_mul_tendsto_atTop', '''Filter.Tendsto
  (fun t : ℝ => t * DominantFiveBody.Coorbital.kernelF t)
  (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop''')
bind('display:164', 'DominantFiveBody.coorbitalVirial_zero', '''∀
  (mass theta : DominantFiveBody.Satellite → ℝ), DominantFiveBody.OrderedSemicircle theta →
  (∀ i, DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
  DominantFiveBody.coorbitalVirial mass theta = 0''')
subclaim('thm:coorbital.mass_floor_collision_exclusion', 167,
    'On a compact interior mass set with a fixed common positive mass floor α, every actual coorbital root has all pair angles bounded below by a common d>0. The mass floor is used only in this original interior properness argument.',
    'DominantFiveBody.coorbital_roots_uniform_pair_separation', '''∀ (alpha : ℝ), 0 < alpha →
  ∃ d : ℝ, 0 < d ∧ ∀ mass theta : DominantFiveBody.Satellite → ℝ,
  DominantFiveBody.PositiveRatio mass → (∀ i, alpha ≤ mass i) →
  DominantFiveBody.OrderedSemicircle theta →
  (∀ i, DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
  ∀ i j, i < j → d ≤ theta j-theta i''')
subclaim('eq:action.mass_metric_positive', 246,
    'The actual primary-relative mass matrix C=diag(μ)−ε/(1+ε) μμᵀ is positive definite for ε>−1, all μ_i>0 and sum μ=1.',
    'DominantFiveBody.relativeMassMatrix_posDef', '''∀ (eps : ℝ)
  (mu : DominantFiveBody.Satellite → ℝ), -1 < eps → (∀ i, 0 < mu i) →
  (∑ i, mu i) = 1 → (DominantFiveBody.relativeMassMatrix eps mu).PosDef''')
subclaim('eq:action.actual_critical_equivalence', 248,
    'At a genuinely collision-free primary-relative configuration, the actual Fréchet derivative of Φ vanishes if and only if all physical mass-divided vector residuals vanish; ε>−1, positive ratios of sum one.',
    'DominantFiveBody.relativeAction_critical_iff_vectorRoot', '''∀ (eps : ℝ)
  (mu : DominantFiveBody.MassRatio), -1 < eps → DominantFiveBody.PositiveRatio mu →
  ∀ (q : DominantFiveBody.SatelliteConfiguration), DominantFiveBody.RelativeCollisionFree q →
  (fderiv ℝ (DominantFiveBody.relativeAction eps mu) q = 0 ↔
    (∀ i, DominantFiveBody.vectorResidual eps mu q i = 0))''')
subclaim('prop:uniform.actual_ordered_polar_bridge', 350,
    'Every actual normalized strictly convex five-point configuration in its specified original directed hull order has a common rotation angle, positive polar radii and theta_0=0 with strictly increasing angles of span below pi; after synchronously transporting masses and positions, all four actual divided angular residuals vanish in this gauge.',
    'DominantFiveBody.normalized_strictConvex_ordered_angular_rep', '''∀ (eps : ℝ)
  (mu : DominantFiveBody.MassRatio) (sigma : DominantFiveBody.HullOrder)
  (x : DominantFiveBody.Configuration), 0 < eps → DominantFiveBody.PositiveRatio mu →
  DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
  DominantFiveBody.StrictConvexInOrder sigma x →
  ∃ (r theta : DominantFiveBody.Satellite → ℝ) (phi : ℝ),
    (∀ i, 0 < r i) ∧ theta 0 = 0 ∧
    (∀ i j, i < j → 0 < theta j-theta i ∧ theta j-theta i < Real.pi) ∧
    (∀ i, x (sigma.labels i.succ)-x 0 = DominantFiveBody.polarPoint (r i) (theta i+phi)) ∧
    (∀ i, DominantFiveBody.angularResidual eps
      (mu ∘ DominantFiveBody.hullSatellitePermutation sigma) r theta i = 0)''')
subclaim('prop:uniform.selected_limit_span_zero_exclusion', 360,
    'Along every actual positive-ratio angular-root sequence in the ordered polar gauge, if all four radii converge to one and all angles have selected finite limits, the limiting angular span is strictly positive. No lower bound or positive limiting satellite mass is required.',
    'DominantFiveBody.ordered_full_angular_limit_span_pos', '''∀ (eps : ℕ → ℝ),
  (∀ n, 0 < eps n) → ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ),
  (∀ n i, 0 < mu n i) → (∀ n i, 0 < r n i) →
  (∀ n i, DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = 0) →
  (∀ n, ∀ i j, i < j → 0 < theta n j-theta n i ∧ theta n j-theta n i < Real.pi) →
  ∀ (rLimit thetaLimit : DominantFiveBody.Satellite → ℝ), (∀ i, rLimit i = 1) →
  Filter.Tendsto r Filter.atTop (nhds rLimit) →
  Filter.Tendsto theta Filter.atTop (nhds thetaLimit) → 0 < thetaLimit 3-thetaLimit 0''')
subclaim('prop:uniform.selected_cut_gap_limit', 353,
    'For any selected convergent actual angular-root sequence with epsilon tending to zero and all limiting radii equal to one, an ordered nonempty angular cut cannot have every limiting cross-cut angle gap bounded below by g greater than pi/3. This is a selected-limit cut estimate, not yet the whole uniform span or full consecutive-gap assertion.',
    'DominantFiveBody.full_angular_cut_limit_gap_le', '''∀ (eps : ℕ → ℝ),
  (∀ n, 0 < eps n) → Filter.Tendsto eps Filter.atTop (nhds 0) →
  ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ),
  (∀ n i, 0 < mu n i) → (∀ n i, 0 < r n i) →
  (∀ n i, DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = 0) →
  ∀ (rLimit thetaLimit : DominantFiveBody.Satellite → ℝ), (∀ i, rLimit i = 1) →
  Filter.Tendsto r Filter.atTop (nhds rLimit) →
  Filter.Tendsto theta Filter.atTop (nhds thetaLimit) →
  ∀ (S : Finset DominantFiveBody.Satellite), S.Nonempty → Sᶜ.Nonempty →
  (∀ n, ∀ i ∈ S, ∀ j ∈ Sᶜ, 0 < theta n j-theta n i ∧ theta n j-theta n i < Real.pi) →
  ∀ (g : ℝ), (∀ i ∈ S, ∀ j ∈ Sᶜ, g ≤ thetaLimit j-thetaLimit i) → g ≤ Real.pi/3''')
subclaim('prop:uniform.selected_consecutive_gap_limit', 353,
    'Every consecutive gap has selected limiting value at most pi/3 along any convergent actual positive-ratio angular-root sequence with epsilon tending to zero and all radii tending to one. The initial-segment cuts and their limiting order inequalities are proved, rather than supplied as a cross-gap condition.',
    'DominantFiveBody.ordered_full_angular_limit_consecutive_gap_le', '''∀ (eps : ℕ → ℝ),
  (∀ n, 0 < eps n) → Filter.Tendsto eps Filter.atTop (nhds 0) →
  ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ),
  (∀ n i, 0 < mu n i) → (∀ n i, 0 < r n i) →
  (∀ n i, DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = 0) →
  (∀ n, ∀ i j, i < j → 0 < theta n j-theta n i ∧ theta n j-theta n i < Real.pi) →
  ∀ (rLimit thetaLimit : DominantFiveBody.Satellite → ℝ), (∀ i, rLimit i = 1) →
  Filter.Tendsto r Filter.atTop (nhds rLimit) →
  Filter.Tendsto theta Filter.atTop (nhds thetaLimit) →
  ∀ k : Fin 3, thetaLimit k.succ-thetaLimit k.castSucc ≤ Real.pi/3''')
subclaim('prop:uniform.selected_limit_span_pi_exclusion', 354,
    'Every selected convergent actual positive-ratio angular-root sequence with epsilon tending to zero, current mass sum one and all limiting radii equal to one has limiting span strictly below pi. The proof preserves all four unweighted rows and allows zero limiting satellite masses.',
    'DominantFiveBody.ordered_full_angular_limit_span_lt_pi', '''∀ (eps : ℕ → ℝ),
  (∀ n, 0 < eps n) → Filter.Tendsto eps Filter.atTop (nhds 0) →
  ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ),
  (∀ n i, 0 < mu n i) → (∀ n, ∑ i, mu n i = 1) → (∀ n i, 0 < r n i) →
  (∀ n i, DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = 0) →
  (∀ n, ∀ i j, i < j → 0 < theta n j-theta n i ∧ theta n j-theta n i < Real.pi) →
  ∀ (muLimit rLimit thetaLimit : DominantFiveBody.Satellite → ℝ), (∀ i, rLimit i = 1) →
  Filter.Tendsto mu Filter.atTop (nhds muLimit) →
  Filter.Tendsto r Filter.atTop (nhds rLimit) →
  Filter.Tendsto theta Filter.atTop (nhds thetaLimit) → thetaLimit 3-thetaLimit 0 < Real.pi''')
subclaim('thm:coorbital.equal_mass_chamber_seed', 172,
    'For the actual normalized equal mass ratio 1/4, the anchored ordered open-semicircle angular domain has exactly one root of all four actual coorbital equations. This is the minimal seed needed for the covering argument; it does not assert the full AF three-class classification outside this chamber.',
    'DominantFiveBody.equalMass_coorbital_existsUnique', '''∃! theta : DominantFiveBody.Satellite → ℝ,
  DominantFiveBody.CoorbitalAngleDomain theta ∧
    ∀ i, DominantFiveBody.coorbitalResidual DominantFiveBody.equalMassRatio theta i = 0''')
subclaim('thm:coorbital.actual_projection_proper', 169,
    'The mass projection from the true coorbital zero-set subtype to the positive mass-simplex subtype is a proper map. Its compact preimages and boundary exclusions are proved for the actual equations.',
    'DominantFiveBody.coorbitalMassProjection_isProperMap', '''IsProperMap
  DominantFiveBody.coorbitalMassProjection''')

bind('thm:coorbital', 'DominantFiveBody.coorbital_global_complete', '''
  (∀ m : DominantFiveBody.MassRatio, DominantFiveBody.PositiveRatio m →
    ∃! theta : DominantFiveBody.Satellite → ℝ, DominantFiveBody.CoorbitalAngleDomain theta ∧
      ∀ i, DominantFiveBody.coorbitalResidual m theta i = 0) ∧
  ContDiffOn ℝ ∞ DominantFiveBody.coorbitalRootAngles {m | DominantFiveBody.PositiveRatio m} ∧
  (∀ m : DominantFiveBody.MassRatio, DominantFiveBody.PositiveRatio m →
    ∀ u : DominantFiveBody.Satellite → ℝ, u 0 = 0 → u ≠ 0 →
    0 < DominantFiveBody.coorbitalPhysicalHessian m (DominantFiveBody.coorbitalRootAngles m) u u) ∧
  IsProperMap DominantFiveBody.coorbitalMassProjection ∧
  IsCoveringMapOn DominantFiveBody.coorbitalMassProjection Set.univ''',
  note='The package includes actual D²V positivity on the anchored slice, global positive-simplex existence and uniqueness, smoothness, actual proper projection and covering. The minimal equal-mass chamber seed is proved independently in Lean; the full AF whole-circle classification is not asserted.')

def complete_package_type(path, name, local_names):
    text = (root/path).read_text(encoding='utf-8')
    marker = f'theorem {name} :'
    start = text.index(marker) + len(marker)
    end = text.index(':= by', start)
    statement = text[start:end].strip()
    for ident in local_names:
        statement = re.sub(r'(?<![\w.])'+re.escape(ident)+r'\b', 'DominantFiveBody.'+ident, statement)
    for ident in ['Tendsto', 'atTop']:
        statement = re.sub(r'(?<![\w.])'+re.escape(ident)+r'\b', 'Filter.'+ident, statement)
    return statement

uniform_type = complete_package_type('DominantFiveBody/CollisionScales.lean',
    'dominant_uniform_geometry_complete', [
      'MassRatio', 'PositiveRatio', 'Configuration', 'NormalizedCentralConfiguration',
      'masses', 'Satellite', 'satellitesRelative', 'HullOrder', 'StrictConvexInOrder',
      'polarPoint', 'angularResidual', 'hullSatellitePermutation'])
bind('prop:uniform', 'DominantFiveBody.dominant_uniform_geometry_complete', uniform_type,
  note='All clauses concern actual physical multiplier-one configurations. Uniform constants precede every positive ratio; the span gauge is obtained from strict convexity of all five points in the original directed order, and the true sequence limsup permits the order and masses to vary at every index. No positive limiting satellite mass fraction is assumed.')

span_type = complete_package_type('DominantFiveBody/CollisionScales.lean',
    'dominant_strictConvex_uniform_polar_span', [
      'MassRatio', 'PositiveRatio', 'Configuration', 'NormalizedCentralConfiguration',
      'masses', 'Satellite', 'HullOrder', 'StrictConvexInOrder', 'polarPoint',
      'angularResidual', 'hullSatellitePermutation'])
bind('eq:span', 'DominantFiveBody.dominant_strictConvex_uniform_polar_span', span_type,
  note='The original standard-order statement is proved for every original directed order with synchronized mass reindexing; reflections or label permutations are not added to the similarity equivalence.')

subclaim('prop:uniform.actual_sequence_gap_limsup', 331,
    'Each consecutive angular gap has genuine limsup at most pi/3 for any actual normalized positive-ratio solution sequence epsilon_n→0 in its ordered positive polar gauge. The current masses and original directed hull order can vary with n, with no positive mass floor.',
    'DominantFiveBody.dominant_ordered_polar_gap_limsup', '''∀ (eps : ℕ → ℝ)
  (mu : ℕ → DominantFiveBody.MassRatio) (sigma : ℕ → DominantFiveBody.HullOrder)
  (x : ℕ → DominantFiveBody.Configuration)
  (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (phi : ℕ → ℝ),
  (∀ n, 0 < eps n) → Filter.Tendsto eps Filter.atTop (nhds 0) →
  (∀ n, DominantFiveBody.PositiveRatio (mu n)) →
  (∀ n, DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
  (∀ n, ∀ i, 0 < r n i) → (∀ n, theta n 0 = 0) →
  (∀ n, ∀ i j, i < j → 0 < theta n j-theta n i ∧ theta n j-theta n i < Real.pi) →
  (∀ n, ∀ i, x n ((sigma n).labels i.succ)-x n 0 =
    DominantFiveBody.polarPoint (r n i) (theta n i+phi n)) →
  ∀ k : Fin 3, Filter.limsup (fun n => theta n k.succ-theta n k.castSucc) Filter.atTop ≤ Real.pi/3''')

bind('eq:chi', 'DominantFiveBody.singleScaleChi_complete', '''∀ t b : ℝ,
  DominantFiveBody.singleScaleChi t b = t*b^2/2*Real.sinc (t*b/2)^2 ∧
    1-Real.cos (t*b) = t*DominantFiveBody.singleScaleChi t b''',
  note='The exact identity is kernel proved for all real signed t and b, including t=0. This does not promote the complete pair/triple chart to VERIFIED.')

bind('lem:product', 'DominantFiveBody.CompactImplicit.compact_product', '''∀
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] {n : ℕ}
  (F : P → DominantFiveBody.CompactImplicit.Unknown n → DominantFiveBody.CompactImplicit.Unknown n)
  (D K : Set (P × DominantFiveBody.CompactImplicit.Unknown n)),
  IsOpen D → ContDiffOn ℝ ∞ (Function.uncurry F) D → IsCompact K →
  (∀ a ∈ K, a ∈ D ∧ F a.1 a.2 = 0 ∧
    (DominantFiveBody.CompactImplicit.jacobian F a.1 a.2).IsInvertible) →
  ∀ tau : ℝ, 0 < tau → ∃ eta r C : ℝ, 0 < eta ∧ 0 < r ∧ 0 < C ∧ r ≤ tau ∧ eta ≤ r ∧
    ∀ a ∈ K, ∃ psi : P → DominantFiveBody.CompactImplicit.Unknown n,
      psi a.1 = a.2 ∧ ContDiffOn ℝ ∞ psi (Metric.ball a.1 eta) ∧
      ∀ q, dist q a.1 < eta → dist (psi q) a.2 < r/2 ∧ (q,psi q) ∈ D ∧
        (DominantFiveBody.CompactImplicit.jacobian F q (psi q)).IsInvertible ∧
        ‖(DominantFiveBody.CompactImplicit.jacobian F q (psi q)).inverse‖ ≤ C ∧ F q (psi q) = 0 ∧
        (∀ z, dist z a.2 < r → (F q z = 0 ↔ psi q = z))''',
  note='The compact graph is supplied directly, avoiding any unproved compactness input. The proof gives common parameter and root radii, smooth gluing, actual invertibility and bounded actual inverse, on a genuine independent parameter ball; a finite-dimensional parameter product contains an independent rectangle inside this ball.')

subclaim('lem:hessian.actual_fixed_slice_bridge', 277,
  'At a root of the actual positive-mass seven divided polar rows in the fixed-first-angle slice, the true residual Jacobian is invertible exactly when the original physical six-dimensional shape Hessian is nondegenerate. All criticality, mass-metric, coordinate and transverse-slice conversions have actual proofs.',
  'DominantFiveBody.reducedJacobian_isInvertible_iff_shape', '''∀
  (p : DominantFiveBody.ContinuationParameter) (y : DominantFiveBody.SliceCoordinates),
  DominantFiveBody.SliceRegular p y → 0 < p.1 → DominantFiveBody.PositiveRatio p.2 →
  DominantFiveBody.reducedResidual p y = 0 →
  ((DominantFiveBody.reducedJacobian p y).IsInvertible ↔
    DominantFiveBody.ShapeHessianNondegenerate (DominantFiveBody.masses p.1 p.2) 1
      (DominantFiveBody.slicePhysicalConfiguration p y))''')

def parameterized_decl_type(path, name, local_names):
    code = (root/path).read_text(encoding='utf-8')
    marker = 'theorem '+name
    start = code.index(marker)+len(marker)
    end = code.index(':=', start)
    header = code[start:end].strip()
    depth = 0
    colon = None
    for k, char in enumerate(header):
        if char in '({[':
            depth += 1
        elif char in ')}]':
            depth -= 1
        elif char == ':' and depth == 0:
            colon = k
            break
    if colon is None:
        raise ValueError(name+' has no result colon')
    statement = '∀ '+header[:colon].strip()+',\n'+header[colon+1:].strip()
    # Proof arguments are named in the source proof, but may be unused in its
    # independently reproduced type.  Preserve the dependent Pi type while
    # marking only these local binder names as intentionally unused.
    proof_binders = re.findall(r'[({]\s*(h[A-Za-z0-9_]+)\s*:', header[:colon])
    for binder in proof_binders:
        statement = re.sub(r'\b'+re.escape(binder)+r'\b', '_'+binder, statement)
    for ident in local_names:
        statement = re.sub(r'(?<![\w.])'+re.escape(ident)+r'\b', 'DominantFiveBody.'+ident, statement)
    for ident in ['Tendsto', 'atTop']:
        statement = re.sub(r'(?<![\w.])'+re.escape(ident)+r'\b', 'Filter.'+ident, statement)
    return statement

pair_names = ['MassRatio', 'SatelliteConfiguration', 'Satellite', 'Plane', 'Configuration',
  'NormalizedCentralConfiguration', 'masses', 'satellitesRelative', 'primaryRadialField',
  'pairExteriorField', 'satelliteDistance', 'primaryRadialScalar', 'polarSatellites', 'polarPoint',
  'PositiveRatio', 'CompleteLimitingSatellitePair', 'physicalPairDirection',
  'physicalPairExteriorAngularField', 'physicalSourceAngularRadialDerivative',
  'Label', 'StrictConvexInOrder', 'Coorbital', 'coorbitalKernel', 'pairExteriorLabels']
def pair_type(name):
    return parameterized_decl_type('DominantFiveBody/CollisionPairScales.lean', name, pair_names)

bind('eq:pair-vdiff', 'DominantFiveBody.normalized_pair_vector_difference',
  pair_type('normalized_pair_vector_difference'),
  note='This is the actual normalized physical pair difference. The pair mass is the current mu_a+mu_b; all relative distances are actual collision-free distances. No chart capture or individual-fraction division is used.')
bind('eq:midpoint', 'DominantFiveBody.normalized_pair_midpoint_identity',
  pair_type('normalized_pair_midpoint_identity'),
  note='The projection is exactly onto the current midpoint ray. The radial coefficient is retained without division by Delta-rho, so equal radii and arbitrary current pair shares are covered.')
bind('eq:pair-qdiff', 'DominantFiveBody.normalized_complete_pair_tangential_difference_positive',
  pair_type('normalized_complete_pair_tangential_difference_positive'),
  note='The complete equality and eventual positive sign are proved for every actual selected complete pair in the original ordered positive polar representation. Current masses may approach zero. This does not close the later support exclusion or the full scale theorem.')
subclaim('prop:pair-scale.actual_direction_alternative', 405,
  'A selected unit pair-direction limit of actual normalized roots is tangential with lambda→0 or radial with lambda→3 and v=plus or minus c. The lambda limit is derived, not assumed. The positive tangential orientation and radial exclusion remain separate obligations.',
  'DominantFiveBody.normalized_complete_pair_direction_alternative',
  pair_type('normalized_complete_pair_direction_alternative'))
subclaim('prop:pair-scale.current_exterior_error_bound', 386,
  'For any selected complete pair of actual positions, the exterior Newton field difference is bounded by C times the CURRENT exterior mass sigma times the pair distance. The source-by-source proof needs no convergence or floor for the current masses.',
  'DominantFiveBody.complete_pair_exterior_error_bound',
  pair_type('complete_pair_exterior_error_bound'))
subclaim('prop:pair-scale.radial_bound_on_tangential_branch', 423,
  'On an actual selected complete-pair tangential branch lambda→0 with angular gap→0, the original radial estimate |Delta-rho|≤C epsilon sigma d is proved from the exact midpoint identity and the current-mass exterior error bound. This statement does not assert that all complete pairs are tangential.',
  'DominantFiveBody.normalized_complete_pair_radial_bound_of_tangential',
  pair_type('normalized_complete_pair_radial_bound_of_tangential'))

bind('prop:pair-scale', 'DominantFiveBody.normalized_complete_pair_scale_complete',
  pair_type('normalized_complete_pair_scale_complete'),
  note='The entire selected fixed-label physical sequence assertion is proved: actual adjacent pair, current pair mass tending to zero, angular-distance ratio one, original radial C epsilon sigma d bound, two exterior limits distinct with original oriented gap h, the translated probe formula including p=0 or p=1, the true positive cube coefficient and its limit, and exclusion of any other complete pair. The true source/target exterior field is jointly differentiated at moving endpoints. No limiting pair direction, probe positivity, ratio floor, individual-fraction limit, chart capture or artificial analytic estimate is assumed.')
bind('eq:pair-scale', 'DominantFiveBody.normalized_complete_pair_scale_complete',
  pair_type('normalized_complete_pair_scale_complete'),
  note='The displayed rates are consequences of the complete actual Proposition 4.2 theorem; its type also preserves the positive probe coefficient and the physical root hypotheses.')
bind('prose:376', 'DominantFiveBody.normalized_complete_pair_scale_complete',
  pair_type('normalized_complete_pair_scale_complete'),
  note='The two actual exterior limits and their positively ordered separation h are proved. The gauge subtracts the first exterior angle and preserves orientation.')
bind('display:377', 'DominantFiveBody.normalized_complete_pair_scale_complete',
  pair_type('normalized_complete_pair_scale_complete'),
  note='The translated genuine signed-kernel probe equation and its actual positive derivative appear explicitly in the complete type, with p in the full closed unit interval.')
subclaim('prop:pair-scale.actual_first_stage', 418,
  'Every actual selected complete pair is positively tangential and adjacent; delta/d tends to one, Delta-rho/d tends to zero, nu/d^3 is at most C sigma eventually, nu tends to zero, and the original radial bound holds. A direction limit is not assumed.',
  'DominantFiveBody.normalized_complete_pair_tangential_mass_scale',
  pair_type('normalized_complete_pair_tangential_mass_scale'))
subclaim('prop:pair-scale.actual_positive_cube_limit', 425,
  'The true physical complete pair satisfies nu/d^3 tending to the strictly positive genuine exterior probe derivative. Both exterior limiting weights may be endpoints, and no convergence of the individual pair fraction is imposed.',
  'DominantFiveBody.normalized_complete_pair_mass_cube_limit',
  pair_type('normalized_complete_pair_mass_cube_limit'))
subclaim('prop:pair-scale.actual_two_pair_exclusion', 381,
  'Two actual distinct complete pair classes cannot coexist. Each current total pair mass would tend to zero, contradicting the unchanged satellite mass sum one.',
  'DominantFiveBody.normalized_complete_pairs_cannot_coexist',
  pair_type('normalized_complete_pairs_cannot_coexist'))

pair_actual_names = pair_names + ['pairPhysicalScale', 'pairExteriorFraction',
  'pairPhysicalFraction', 'pairVariablesFromPolar', 'pairBoundaryScale',
  'pairProbeDerivative', 'pairUnitPoint', 'PairCapturedBranches']
def pair_actual_type(name):
    return parameterized_decl_type('DominantFiveBody/PairActualCapture.lean', name, pair_actual_names)
subclaim('subsec:pair-chart.actual_inverse_limits', 589,
  'The actual complete pair enters the true inverse coordinates after the explicit satellite permutation and current exterior-angle gauge: t tends to zero, p tends to its limiting closed-interval value, and all seven chart variables tend to the genuine unit boundary root. No alpha fraction convergence is imposed.',
  'DominantFiveBody.normalized_complete_pair_actual_chart_limits',
  pair_actual_type('normalized_complete_pair_actual_chart_limits'))
subclaim('subsec:pair-chart.actual_common_interval_capture', 589,
  'The original complete-pair physical sequence is captured on one common epsilon interval. Chart roots, all inverse scale limits and regularity are derived from the actual normalized equations. The explicit relabeling and current angular gauge give genuine physical branches, strict convexity, original six-dimensional shape nondegeneracy and same-current-mass collision-free coorbital zero endpoints. The current pair fraction need not converge.',
  'DominantFiveBody.normalized_complete_pair_actual_capture',
  pair_actual_type('normalized_complete_pair_actual_capture'))

nested_names = pair_names + ['RelativeCollisionFree', 'vectorResidual', 'newtonTargetField',
  'physicalSourceAngularAngularDerivative', 'nestedPairCurrentKernel', 'nestedPairCurrentExterior',
  'tripleLargestDistance', 'pairSecantExteriorField', 'dividedNewtonTargetField']
def nested_type(name):
    return parameterized_decl_type('DominantFiveBody/CollisionNestedScales.lean', name, nested_names)
def nested_geometry_type(name):
    return parameterized_decl_type('DominantFiveBody/CollisionNestedGeometry.lean', name, nested_names)
bind('eq:nested-field', 'DominantFiveBody.physical_pair_exterior_angular_derivatives',
  nested_type('physical_pair_exterior_angular_derivatives'),
  note='Both actual target partial derivatives are proved for the original physical H field, before taking any near-source limit. Source radii, angles and current masses are fixed only within the target differentiation; all source parameters remain joint variables in the smoothness proofs. No claim that the subsequent uniform nested-rectangle inequalities are already closed is made.')
bind('eq:nested-macro-average', 'DominantFiveBody.normalized_nested_macro_average',
  nested_type('normalized_nested_macro_average'),
  note='The exact normalized physical angular equations are averaged with the current positive pair weights. Internal pair interactions cancel before division by the proved positive current total pair mass. The kernel K is the actual variational fullAngularMatrix and exterior sigma is proved equal to one minus the current triple mass; no individual mass-share convergence is assumed.')
subclaim('prop:nested-scale.actual_macro_cube_bridge', 502,
  'The actual normalized macro equations and explicit first-order triple geometry force nu/d^3 to the real exterior kernel derivative. The bridge does not assume chart roots, current pair-share convergence, prior nu convergence, or prior nu/d^3 convergence.',
  'DominantFiveBody.normalized_nested_macro_mass_cube_limit_of_first_order_geometry',
  nested_type('normalized_nested_macro_mass_cube_limit_of_first_order_geometry'))
subclaim('prop:nested-scale.actual_current_weight_group_radial', 483,
  'From actual physical vector rows, the current positive masses, the genuine triple diameter, a pair-distance/diameter ratio tending to zero and the initial triple cubic upper bound, the two cross-group scaled radial projections tend to zero on the original sequence. Compactness removes a selected-direction premise and no pair mass fraction convergence is used.',
  'DominantFiveBody.physical_nested_group_radial_projections_tendsto',
  nested_geometry_type('physical_nested_group_radial_projections_tendsto'))

main = next(e for e in assertions if e['id'] == 'thm:main')
main['target_specification'] = 'DominantFiveBody.MainUniformStatement'
main['target_specification_expanded'] = '''∃ δ : ℝ, 0 < δ ∧
  ∀ μ : DominantFiveBody.MassRatio, DominantFiveBody.PositiveRatio μ →
  ∀ ε : ℝ, 0 < ε → ε < δ → ∀ σ : DominantFiveBody.HullOrder,
  ∃ x : DominantFiveBody.Configuration,
    DominantFiveBody.StrictConvexCentralConfiguration (DominantFiveBody.masses ε μ) σ x ∧
    (∀ y : DominantFiveBody.Configuration,
      DominantFiveBody.StrictConvexCentralConfiguration (DominantFiveBody.masses ε μ) σ y →
      DominantFiveBody.OrientedSimilar x y) ∧
    (∀ y : DominantFiveBody.Configuration,
      DominantFiveBody.StrictConvexCentralConfiguration (DominantFiveBody.masses ε μ) σ y →
      DominantFiveBody.NondegenerateCentralConfiguration (DominantFiveBody.masses ε μ) y)'''
main['remaining_dependencies'] = [
    'Lemma lem:hessian: the actual fixed-first-slice bridge is proved; complete arbitrary positive omitted-row transport remains to be bound.',
    'Proposition prop:local: actual local positive-mass branches.',
    'Propositions prop:triple-scale/prop:nested-scale and complete collision classification remain open; full Proposition 4.1 uniform physical geometry and Proposition 4.2 actual complete-pair scales are proved.',
    'Section 5: all four actual regularized charts, independent parameter products, row recovery and sequence capture.',
    'Section 6: exact signed-area factorizations and positivity on independent products.',
    'Propositions prop:chart-interface and prop:connection: fixed same-mass endpoints and common-interval actual branches.',
    'Physical local continuation uniqueness, relabeling, multiplier normalization, and similarity-representative correspondence.']

assertions.sort(key=lambda e: (e['source_location']['tex_lines'][0], e['id']))
ledger = {'schema_version': 1, 'source_scope': {
    'tex_path': 'source/dominant_five_body_ARMA_rewritten.tex',
    'pdf_path': 'source/dominant_five_body_ARMA_rewritten.pdf',
    'pdf_page_count': 19, 'scope': 'Entire supplied 19-page manuscript, including the abstract, all numbered results, all displayed mathematical formulas and all substantive mathematical prose through the proof of Theorem 1.1.',
    'tex_sha256': hashlib.sha256(source.read_bytes()).hexdigest().upper(),
    'pdf_sha256': hashlib.sha256((root/'source/dominant_five_body_ARMA_rewritten.pdf').read_bytes()).hexdigest().upper(),
    'source_body_tex_lines': [start_body+1, end_body],
    'excluded_nonmathematical_material': ['title and author metadata', 'funding and declarations', 'bibliography entries'],
    'display_inventory_method': 'Every equation/align/gather environment and every unnumbered display in the source body; each label in a shared display is indexed separately.',
    'prose_inventory_method': 'Every nonempty prose paragraph outside display blocks; theorem statements are additionally indexed in full.',
    'page_mapping_note': 'Auxiliary label page locations are included where available; all source line intervals are exact. Unlabelled prose/display page attribution is not invented.'},
    'complete_source_inventory': True,
    'verification_note': 'VERIFIED means an exact declaration type was separately checked. No whole-paper success is claimed; an OPEN source assertion blocks verify_paper. Partial subclaims do not close their containing proposition.',
    'lean_statement_context': ['open scoped BigOperators ContDiff Matrix.Norms.Operator'],
    'assertions': assertions}
(root/'docs/FULL_ASSERTIONS.json').write_text(json.dumps(ledger, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')

md = ['# 全文断言清单：原稿全部 19 页', '',
    '原文所有编号结论、编号及无编号公式、实质性数学文字段落均按源码逐项登记。范围不止主定理或已实现模块。原件与源码版本绑定见 SOURCE_AUDIT.md；这里保留原文的量词和推导断言，不用弱化后的 Lean 类型冒充完整命题。', '',
    '`VERIFIED` 必须有真实声明及完整可验收类型；`CONDITIONAL` 公开实质待证输入；`OPEN` 的 `lean_statement` 为 null，表示完整忠实证明尚未实现。一个子结论 VERIFIED 不关闭包含它的完整命题。原文被等价证法替代的中间推导也单独 OPEN。', '',
    f'机器清单见 FULL_ASSERTIONS.json。共 {len(assertions)} 项；整个 19 页正文均纳入。任何一项非 VERIFIED 都不能获得全文验收成功。', '']
for e in assertions:
    loc = e['source_location']
    a, b = loc['tex_lines']
    pages = loc['pdf_pages_from_aux_labels']
    md += [f"## {e['id']} — {e['status']}", '',
        f'来源：TeX 行 {a}–{b}' + (f'；aux 标签页 {pages}' if pages else '') + '。', '',
        '原文完整断言：', '', '```tex', e['exact_claim'], '```', '',
        'Lean 声明：'+ (f"`{e['lean_declaration']}`" if e['lean_declaration'] else '`null`')+'。', '']
    if e['lean_statement']:
        md += ['完整 Lean 类型：', '', '```lean', e['lean_statement'], '```', '']
    else:
        md += ['完整 Lean 类型：`null`。', '']
    md += ['剩余依赖：'+ ('；'.join(e['remaining_dependencies']) if e['remaining_dependencies'] else '无（对应声明仍需绑定本次构建、公理审计及内核回放 receipt）')+'。', '']
    if e.get('target_specification_expanded'):
        md += ['主目标规格展开（这是目标 Prop，尚无无条件证明）：', '', '```lean',
               e['target_specification_expanded'], '```', '']
    if e.get('proof_route_note'):
        md += ['证法说明：'+e['proof_route_note'], '']
(root/'docs/FULL_ASSERTIONS.md').write_text('\n'.join(md), encoding='utf-8')

partial = ['import DominantFiveBody.CoorbitalCovering', 'import DominantFiveBody.Probe', 'import DominantFiveBody.BoundaryJacobian', 'import DominantFiveBody.RelativeMassMetric', 'import DominantFiveBody.CollisionPairScales', 'import DominantFiveBody.PairActualCapture', 'import DominantFiveBody.CollisionNestedScales', 'import DominantFiveBody.CollisionNestedGeometry', 'import DominantFiveBody.SingleScaleKernel', 'import DominantFiveBody.CompactImplicit',
           'open scoped BigOperators ContDiff Matrix.Norms.Operator', '']
for e in assertions:
    if e['lean_statement']:
        partial += [f"-- {e['id']}", f"example : {e['lean_statement']} := @{e['lean_declaration']}",
                    f"#print axioms {e['lean_declaration']}", '']
(root/'logs/source-audit-build/AssertionCoveragePartial.lean').write_text('\n'.join(partial), encoding='utf-8')
print(json.dumps({'assertions': len(assertions), 'numbered': sum(e['claim_kind']=='numbered_assertion' for e in assertions),
                  'displayed': sum(e['claim_kind']=='displayed_assertion' for e in assertions),
                  'status_counts': {s: sum(e['status']==s for e in assertions) for s in ('OPEN','CONDITIONAL','VERIFIED')}}, indent=2))
