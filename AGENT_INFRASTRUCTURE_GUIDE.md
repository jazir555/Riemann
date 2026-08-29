# Root Riemann-Hypothesis Formalization — Agent Infrastructure Guide

This document orients **agents working in this repo** on the custom Lean root
(`C:\Users\mmeadow\Documents\Lean\mathlib4`). Read it **before** doing any work. It tells you
what already exists (so you never reimplement), exact file/line locations, how to find things
reliably, the build discipline, and the one outstanding goal.

The single outstanding NON-RH-equivalent goal is closing the last real `sorry` in
`KadiriZeroFree.lean:630` (`kadiriLamzouriZetaZeroFreeEdge`). Everything else described here is
infrastructure that already exists and is meant to be **called**, not redone.

---

## 1. Golden rules (the things past agents got wrong)

1. **INFRASTRUCTURE EXISTS. Grep BEFORE you write.** Past agents repeatedly concluded "this
   lemma doesn't exist" and planned to write 300–600 lines from scratch — when the lemma
   already existed a few files away. Reimplementing subtle complex analysis here is almost
   always the wrong move.
2. **Grep correctly or you will "miss" existing lemmas.** Use `rg` from Bash (not just the grep
   tool) and be explicit: `rg -n "theorem hadamard_factorization" ZeroFreeRegionHadamard.lean`.
   If a name in a brief is a doc-prose guess rather than an exact Lean identifier, search the
   **stem** (`rg -n "hadamard_factorization" <FILE>`), then read the declaration. A name in
   this guide is the exact Lean identifier unless marked "≈".
3. **`private` vs `public` matters.** A `private` lemma is NOT accessible from another file. If
   you need it, use the sibling **public** theorem (e.g. `xi_bound_re_gt_one` is private → use
   the public `xi_norm_bound_whole_plane`).
4. **Read the actual file before editing.** Re-`read` before any `edit`; if `oldString`
   mismatches, re-read and reconcile. Never edit blind.
5. **Build discipline (concurrency).** Only ONE `lake`/`lean` process at a time — the
   `.lake/build` dir is NOT concurrency-safe. Self-serialize via the mutex
   `.lake_build_lock` (see §3).

---

## 2. How to find things (reliable recipe)

1. **Find the file** by stem keyword:
   `rg -l "hadamard_factorization|zeroFreeEdge|riemannZeta_ne_zero" --glob "*.lean" --no-ignore`
2. **Find the declaration** with exact word boundary + line numbers:
   `rg -n "theorem hadamard_factorization_genus_one" ZeroFreeRegionHadamard.lean`
3. **Check the namespace** (`rg -n "^namespace " FILE`). Quote the full name for another agent,
   e.g. `ZeroFreeRegionHadamard.hadamard_factorization_genus_one` or (inside a namespace)
   `Kadiri.re_three_four_one_one_over_sub_nonneg`.
4. **Check `private`** (`rg -n "private theorem" <FILE>`).
5. **Confirm module registration** in `lakefile.lean` (`rg -n "RootScratch" lakefile.lean`,
   lines 196–209) before relying on a build.

---

## 3. Build discipline

- `lake build <Module>` is the only supported command. A successful EXIT 0 writes the `.olean`
  to `.lake\build\lib\lean\`. A bare `lake env lean` sometimes crashes (EXIT=-1); prefer
  `lake build`.
- **One process at a time.** Acquire the filesystem mutex before any `lake`/`lean`:
  - Lock file: `C:\Users\mmeadow\Documents\Lean\mathlib4\.lake_build_lock`.
  - Acquire: `New-Item -Path <lock> -ErrorAction Stop` (atomic).
  - If it exists OR a `lake.exe` process is running, wait ~10s and retry. A lock older than
    25 min is stale — delete it.
  - Release: `Remove-Item <lock>` in a `finally` block.
- Heavy imports → set Bash `timeout` up to **900000 ms**.

---

## 4. The "3-4-1" zero-free infrastructure (core of the proof)

This is the combinatorial/analytic engine that turns a bound on `-ζ'/ζ` (the log-derivative)
into a zero-free *edge* `σ - Re ρ ≥ 4/(A₀/(σ-1)+A₁·log(|t|+2)+A₂)`. The name "3-4-1" comes
from the weights `3,4,1` in the three-point inequality.

- **`ZeroFreeRegionInfra.lean`** (namespace `ZeroFreeRegion`): the raw analytic ingredients.
  - `three_four_one_re_LSeries_vonMangoldt` (312), `three_four_one_neg_logDeriv_riemannZeta`
    (335): the `3·f(σ)+4·f(σ+it)+f(σ+2it) ≥ 0` sum over von Mangoldt.
  - `re_three_four_one_one_over_sub_borderline` (615) and `re_three_four_one_one_over_sub_nonneg`
    (632/640): the key scalar inequality `3/(σ-ρ.re) + 4/(...) + 1/(...) ≥ 4/d` with the
    `1/a`-shift nonnegativity (`re_inv_nonneg_of_re_nonneg` 556, `re_inv_le_inv_of_re_pos` 565).
  - `re_neg_logDeriv_riemannZeta_le` (522), `re_neg_logDeriv_riemannZeta_ofReal_le` (533):
    the `-ζ'/ζ` real-part bounds.
  - real-axis estimates: `norm_riemannZeta_ofReal` (201), `one_div_sub_one_le_riemannZeta_ofReal`
    (212), `re_term_vonMangoldt_comb_nonneg` (267).
- **`ZeroFreeRegionProof.lean`**: two namespaces.
  - `namespace ZeroFreeRegion` (87): **re-exports most `ZeroFreeRegionInfra` theorems** (same
    names) so they are reachable as `ZeroFreeRegion.*` and via `open ZeroFreeRegion`.
  - `namespace Kadiri` (846): the Kadiri-flavored edge conclusion — `kadiriConstant_pos` (760),
    `zeroFreeEdge_lt_one`/`_le_one`/`_gt_nine_tenths` (779–785), `zeroFree_gap` (808),
    `DerivativeBound` (873, a holomorphic MVT wrapper) with `norm_image_sub_le` (879),
    `riemannZeta_ne_zero_of_zeroFreeEdge` (930). NOTE: the `ZeroFreeRegion`-namespace copy of
    `three_four_one_*` / `re_three_four_*` is what `HadamardBridge` and `KadiriZeroFree` call
    (after `open ZeroFreeRegion`).
  - `zeroFreeEdge_from_factorization` (660) (in `ZeroFreeRegion` ns) is the general bridge
    `Σ(1/(s-ρ)+1/ρ) bounded ⇒ zero-free edge`.
- **`ZeroFreeRegion.lean`** (101 lines, no namespace): top-level aggregation — `trig_inequality`
  (10), `riemannZeta_ne_zero_near_edges` (35), `riemannZeta_ne_zero_outside_middle_gap` (93).
- **`HadamardBridge.lean`** (118 lines): the crucial junction from a Hadamard tsum
  decomposition to the Kadiri edge. `zeroFreeEdge_from_tsum` (15) takes a decomposition
  `LSeries ↗Λ s = analytic s - Σ'(1/(s-a n)+1/a n)` and, using
  `three_four_one_re_LSeries_vonMangoldt` + `re_three_four_one_one_over_sub_nonneg`, produces
  `σ-ρ₀.re ≥ 4/(A₀/(σ-1)+A₁·log(|t|+2)+A₂)`. **This is the template to follow** when wiring
  `KadiriAnalyticInputAtZero` into `kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero`.

---

## 5. Borel-Carathéodory infrastructure

- **`BorelCaratheodory.lean`** (root, 15 lines): a **redundant compatibility shim**. It just
  re-imports Mathlib and documents that the real lemmas live in upstream Mathlib:
  - `Complex.borelCaratheodory_zero` (`Mathlib/Analysis/Complex/BorelCaratheodory.lean:86`):
    `f` analytic on `ball 0 R`, `f 0 = 0`, `Re(f z) ≤ M` ⇒ `‖f z‖ ≤ 2·M·‖z‖/(R-‖z‖)`.
  - `Complex.borelCaratheodory` (109): general version without `f 0 = 0`.
  - `Complex.norm_eqOn_closedBall_of_isMaxOn` (`Mathlib/Analysis/Complex/AbsMax.lean`): maximum
    modulus principle.
  - Don't recreate these; call them. Used in the `hadamard_exponent_affine` step to bound `g`.

---

## 6. Jensen infrastructure

Two layers — both already in Mathlib, both imported:

- **`Mathlib/Analysis/Complex/JensenFormula.lean`** (analytic Jensen's formula):
  - `MeromorphicOn.circleAverage_log_norm` (308), `AnalyticOnNhd.circleAverage_log_norm` (376),
    `AnalyticOnNhd.sum_divisor_le` (390). These relate `log|f|` on a circle to a zero count via
    Jensen's formula.
- **`Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Basic.lean`** (zero-counting via
  Jensen): `logCounting_*` family (e.g. `logCounting_nonneg` 221, `logCounting_le` 239);
  `logCounting_divisor_eq_circleAverage_sub_const` (580) links the counting function to the
  circle average.
- **`Mathlib/Analysis/Complex/ValueDistribution/FirstMainTheorem.lean`,
  `CharacteristicFunction.lean`, `Cartan.lean`**: the full value-distribution / characteristic
  function layer built on the above.
- **`zeta-23-lean/Zeta23/WeilEF/Landau.lean`** (namespace `Zeta23.WeilEF`): Jensen applied to
  `ζ` — zero counts and the partial-fraction expansion of `f'/f` on disks
  (`Zeta23.WeilEF.Landau.*`). **This is the standard tool for the canonical-product lower bound**
  `|P| ≥ exp(-O(R·log R))` via Jensen + a zero-count bound. Builds (part of Zeta23 submodule).
- Root experimental copies: `JensenScratch.lean` (namespace `JensenScratch`, 393 lines) and
  `JensenTranslation.lean` (namespace `JensenRH`, 430 lines, 5 RH-equivalent sorries) — these
  explore the Polya/Jensen hyperbolic-region formulation of RH. **Read-only orientation; not
  part of the non-RH goal.**

---

## 7. Mertens / PNT estimates (and lower bounds)

- **`MertensEstimate.lean`** (148 lines, no namespace): elementary prime estimates used to bound
  `-ζ'/ζ` on `Re > 1`. `primeCounting_le` (18), `πBound` (24), `sum_primes_div_le` (37),
  `sum_primes_recip` (51), `prime_exponential_sum_bound` (74), `mertens_first_vonMangoldt` (105),
  `sum_vonMangoldt_div_le`/`_ge` (111/118), `sum_primes_log_div_le` (127),
  `sum_primes_recip_le_log` (147).
- **`ApproxZetaLowerBound.lean`** (127 lines): the middle-gap zero-freeness via Stirling/functional
  equation. `T₀` (44), `zetaTail_summable` (54), `riemannZeta_abs_lower_bound_of_re_gt_one` (61),
  `riemannZeta_functional_equation` (105), `riemannZeta_abs_lower_bound` (116),
  `riemannZeta_ne_zero_of_middle_gap` (122), `riemannZeta_ne_zero_critical_strip_middle_gap` (133).
- **`zeta-23-lean/Zeta23/FromPNTPlus/Mertens.lean`** (namespace `Mertens`): a verified Zeta23
  Mertens estimate if you need a stronger, already-built bound.

---

## 8. Hadamard product infrastructure

- **`ZeroFreeRegionHadamard.lean`** (namespace `ZeroFreeRegionHadamard`, ~4700 lines): the
  completed-zeta / Hadamard-product core. Everything Hadamard-related lives here. Key items:
  - Primary factors: `logDeriv_primaryFactor_one` (167), `logDeriv_primaryFactor_one_scaled`
    (193), `differentiableAt_primaryFactor_one_scaled` (222), `sum_log_primaryFactor_deriv` (274),
    `primaryFactor_log_bound` (337), `multipliable_primaryFactor_of_summable` (397),
    `norm_primaryFactor_one_sub_one` (505).
  - Order: `orderOfEntire_le` (250), `orderSet_completedRiemannZeta₀` (2313),
    `completedZeta_order_le_one` (2388).
  - xi on right half-plane: `private theorem xi_bound_re_gt_one` (1522) — **private**; use the
    public `xi_norm_bound_whole_plane` (4535) instead.
  - Digamma: `norm_digamma_term_le` (1063), `digamma_le_log` (1236, crude),
    `logDeriv_GammaSeq_eq` (2520), `summable_digamma_tsum` (2564). NOTE: there is **no** theorem
    named exactly `logDeriv_Gammaℝ`; compose
    `Re(logDeriv Γℝ)(s) = -(log π)/2 + (1/2)·Re ψ(s/2)` from `logDeriv_GammaSeq_eq` + Zeta23.
  - Canonical product: `multipliableLocallyUniformlyOn_primaryFactor` (3097),
    `differentiable_canonicalProductNat` (3180), `canonicalProductNat_ne_zero` (3284),
    `canonicalProductNat_eq_zero_of_mem` (3292), `logDeriv_canonicalProductNat` (3314),
    `logDeriv_canonicalProductNat_genus_one` (3462),
    `multipliableLocallyUniformlyOn_primaryFactorSkip` (3486),
    `differentiable_canonicalProductNatSkip` (3585).
  - **`hadamard_factorization_genus_one` (3823)**: `xi = exp g · canonicalProductNat 1 a` with
    `Differentiable ℂ g`. THE entry point for the affine-exponent proof.
  - xi: `xi_differentiable` (4045), `xi_zero_iff_riemannZeta_zero` (4061),
    `xi_zero_imp_riemannZeta_zero` (4371), `xi_zero_imp_zero_lt_re` (4443),
    `xi_norm_bound_whole_plane` (4535, the public whole-plane bound), `xiZeros_bounded_finite`
    (4635), `xi_zero_enumeration` (4642).

---

## 9. Kadiri infrastructure

- **`KadiriZeroFree.lean`** (the CURRENT TARGET file). Key items:
  - `kadiri_numerical_bridge` (19), `xi_zero_iff_isNontrivialZero` (32),
    `Ncount_self` (53)/`Ncount_window_le` (63) (Zeta23 `Ncount` wrappers),
    `xiZeros_infinite` (99) — `xi` has infinitely many zeros (genuine proof, here).
  - `xi_enum_ncard_bound` (128): zero-count `≤ D·r^{7/4}` (used at 410 for `Summable (1/‖aₙ‖²)`).
  - `axiom xiZeros_simple` (242): `∀ z, meromorphicOrderAt xi z ≤ 1` — a declared **simplicity
    axiom** (open conjecture, NOT a `sorry`).
  - `zeta_ne_zero_of_pow_edge` (254).
  - `KadiriAnalyticInput` (280): **vacuous/false** — proven `not_kadiriAnalyticInput` (333).
    Do NOT make it an `axiom`; it is an old dead path.
  - `kadiriLamzouriZetaZeroFreeEdge_of_analyticInput` (380): dead `KadiriAnalyticInput` path.
  - **`KadiriAnalyticInputAtZero` (513)**: the real property to feed; already includes
    `riemannZeta s = 0`, `0 < s.re`, `σ ≤ 9/8`, safety constants.
  - **`kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero` (536–601)**: ALREADY proved — the
    `(A₀,A₁,A₂)=(3,4,0)` numeric bridge → `riemannZeta_ne_zero_of_zeroFreeEdge`. You only need
    to pass it a term of type `KadiriAnalyticInputAtZero`.
  - **`kadiriLamzouriZetaZeroFreeEdge` (627–630)**: contains the `(sorry :
    KadiriAnalyticInputAtZero)`. **Replace that `sorry` with a proof term.** This is THE
    remaining non-RH-equivalent goal.
  - `xiFE` (647): `xi (1 - s) = xi s` (functional equation; gives the ρ↦1-ρ involution).
- **`KadiriDigammaBound.lean`** (namespace `KadiriDigamma`, 287 lines, builds clean): the
  **sharp digamma bound** used in place of `Re ψ ≤ log|z|`. `re_digamma_le` (253):
  `0<z.re → z.re≤1 → z.im≠0 → (Complex.digamma z).re ≤ Real.log (|z.im|+2)+1`;
  `re_digamma_le_of_real` (268), `re_digamma_eq_tsum` (114), `summable_re_digamma_terms` (133),
  `tsum_re_digamma_terms_le` (169). The `+1` constant fits `A₂=0`.
- **`KadiriOrderInfra.lean`** (47 lines): `orderSet_xi_of` (18), `orderSet_xi` (51): the genuine
  `(7/4) ∈ orderSet xi` proof. Referenced by `OrderXiScratch.lean`.
- **`KadiriZerosInfra2.lean`** (5 lines): sanity re-export (`example : Differentiable ℂ xi := xi_differentiable`).
- **`KadiriHScratch.lean`** (42 lines): scratch — `kadiriLamzouriZetaZeroFreeEdge'` (34),
  `xiZeros_infinite_holds` (42), `zeta_ne_zero_of_pow_edge'` (47).

---

## 10. Jensen / Polya / xi-zero orientation scratch files

These are exploratory and RH-equivalent; **read for orientation only**:
- **`JensenScratch.lean`** (namespace `JensenScratch`, 393 lines): Pólya/Hyperbolic-region
  approach — `RiemannHypothesisProp` (16), `xiMathlib` (17), `Hyperbolic` (68),
  `jensenPoly_*` (122–399), `gauss_lucas_hyperbolic` (254), `hPolya` (405), `hSchur` (436),
  `rh_bridge` (100).
- **`JensenTranslation.lean`** (namespace `JensenRH`, 430 lines, **5 RH-equivalent sorries** at
  103/109/449/462/471): the translation of the Pólya machinery — `Hyperbolic` (96),
  `rh_iff_all_jensen_hyperbolic` (101), `real_affine_hyperbolic` (114),
  `real_quadratic_hyperbolic_of_discriminant` (136), `jensen_degree_one/..._hyperbolic` (217/240),
  `all_shifts_from_zero` (447), `rh_iff_jensen_zero` (460), `tail_nonvanishing_iff_jensen` (467).
- **`XiStub.lean`** (14 lines): minimal stub reproducing the definitional facts
  `JensenScratch` P1/P2/hPolya depend on (lets that proof typecheck in isolation).
- **`XiZerosInfiniteScratch.lean`** (34 lines): `xiZero_eq_nontrivialZero` — the elementary
  equivalence `xi z = 0 ↔ ζ z = 0 ∧ 0<Re z<1` from `ZeroFreeRegionHadamard`. Notes the heavy
  Zeta23 route was abandoned as too expensive.
- **`OrderXiScratch.lean`** (9 lines): thin re-export of `orderSet_xi` (now proved in
  `KadiriOrderInfra.lean`).
- **`TailLaguerreScratch.lean`** (93 lines): mollifier/tail experiment — `shiftedS` (27),
  `dirichletMollifier` (28), `geomTailDecay` (50), `rectNormBound` (97).
- **`FirstQuadrantScratch.lean`** (312 lines): first-quadrant thin-region approach — `XiFE` (33),
  `ThinRegion` (49), `NoRightHalfZeros` (63), `crit_line_iff_no_right_half` (98),
  `rh_iff_thin_region` (117), `nonvanishing_central_from_first_quadrant` (259),
  `rh_first_quadrant_proof_to_off_real` (318). Heavily overlaps `rh_residual_gap`.
- **`riemann_hypothesis_newsection.lean`** (namespace `MollifiedAttack`,`TailBound`, 80 lines):
  `Lambda0_fourier_rep` (41), `completedRiemannZeta₀_eq_polar` (61),
  `hardDifferenceNonzero_iff_RH` (67), `rh_from_mollified_rouche` (90).

---

## 11. The `rh_*` engine cluster (green, 0 sorries)

All build cleanly; do not touch unless asked.
- **`rh_residual_gap.lean`** (233 lines): first-quadrant thin-region engine (parallel to
  `FirstQuadrantScratch`) — `XiZeroEquivInStrip` (55), `XiFE` (59), `ThinRegion` (77),
  `zeta_zeroFree_pow` (180), `zeta_thin_region_is_exact_gap` (227), `rh_iff_thin_region_zeta`
  (247), `strip_criterion_of_riemannHypothesis` (268).
- **`rh_certificate.lean`** (6 lines): module stub.
- **`rh_certificate_infra.lean`** (namespace `BoundaryProofEngine`, `CellProofEngine`,
  `Rect2D`, `TailProofEngine`, 461 lines): the sharp-½ Taylor fencing bounds.
  `norm_sub_taylor_le_half_mul_sq` (340), `hasDerivAt_ofReal_toComplex`, `hasDerivAt_vertLine`,
  `hasDerivAt_comp_vertLine` (fencing/differential-inequality bounds).
- **`rh_analytic_infra.lean`** / **`rh_infra.lean`** / **`rh_term_fps.lean`** / **`rh_term_deriv.lean`**
  (namespaces `ZetaAsymptotics`): analytic-derivative / power-series infrastructure for the
  molar/mollifier tail terms (`hasDerivAt_rpow_exp`, `analyticalOnNhd_rpow_*`, `termFPS_coeff`,
  `exp_hasSum_div_factorial`, `hasFPowerSeriesAt_term_succ`).
- **`rh_zeta_cert_data.lean`** (412 lines): numerical certificate data tables.

---

## 12. Engine files (RH-equivalent, flagged)

- **`riemann hypothesis.lean`** and **`riemann_hypothesis.lean`**: cleaned of prose `sorry` but
  still carry **`axiom RiemannHypothesisProp_apply` (line 34)** which asserts RH directly.
  Treat as an open/flagging item, NOT closable here.
- **`riemann_hypothesis_newsection.lean`**: see §10.

---

## 13. Zeta23

- **`Zeta23.lean`** (root, 18 lines): the import root of the Zeta23 library (junction/copy at
  `zeta-23-lean/Zeta23`). Pulls `Zeta23.Unconditional`, `Zeta23.ThmD/Final`, `Zeta23.ThmE/Final`,
  `Zeta23.ThmDE/Final`, `Zeta23.FinalMult`, `Zeta23.XiPrime.Final`, `Zeta23.PairCeiling.*`, etc.
- Zeta23 uses Mathlib `Complex.riemannZeta`. Buildable modules of interest: `Zeta23.WeilEF.Landau`
  (§6), `Zeta23.FromPNTPlus.Mertens` (§7). `Zeta23.Final`, `Zeta23.XiPrime.ZeroCount`,
  `Zeta23.ZeroSide` have no `.olean` and are not needed.
- Imported into the root via `Glob.submodules `Zeta23`` (lakefile:201,208).

---

## 14. Other registered root files

For completeness (all in `lean_lib RootScratch`, lakefile 196–209):
`ktest.lean`, `ScratchCheck.lean`, `JTest.lean`, `TestScratch.lean`, `TestZeta0.lean`,
`TestAnalytic.lean`, `docs.lean`, `Archive.lean`, `Counterexamples.lean`, `probe.lean`,
`probe2.lean`, `probe_X.lean`, `Zeta23Probe.lean`, `rh_probe6/7/8/9/10/11/12.lean`. These are
experiments/probes — search before writing your own, but don't rely on them as infrastructure.

- **`SorryFix.lean`** (namespace `SorryFix`, 104 lines): a **re-export shim** that re-proves
  `orderSet_completedRiemannZeta₀` (107) so it is reachable via `SorryFix.*`; also
  `cosKernel_sub_le` (61), `evenKernel_sub_le` (97). Useful if the `ZeroFreeRegionHadamard`
  name is shadowed.

---

## 15. Registering a new file (only if you create one)

Edit `lakefile.lean`, the `lean_lib RootScratch` block (196–209): add the module name to
`roots` and a matching `Glob.one `Name`` to `globs`. Then rebuild.

---

## 16. The current open target (what to actually prove)

**Goal:** a term of type `KadiriAnalyticInputAtZero`, then replace the `sorry` at
`KadiriZeroFree.lean:630`.

Three short NEW proofs, each an **assembly of existing lemmas** (names verified above):

- **(A) `hadamard_exponent_affine` (`deriv g ≡ B`)**: from `hadamard_factorization_genus_one`
  (`f := xi`, `a` from `xi_zero_enumeration xiZeros_simple xiZeros_infinite`), bound
  `Re g ≤ O(R·log R)` via `xi_norm_bound_whole_plane` (right half-plane) + `xiFE` (left) +
  polynomial strip bound, plus the Jensen-based product lower bound (`Zeta23.WeilEF.Landau`);
  apply `borelCaratheodory`, then Cauchy (`Complex.norm_deriv_le_div_of_mapsTo_ball`,
  `Mathlib/Analysis/Complex/Schwarz.lean:257`) to kill `g''` ⇒ `g` degree ≤ 1.
- **(B) `hadamard_constant_re : B.re = -Σ' Re(1/ρ)`**: from `xiFE` (ρ↦1-ρ bijection) +
  `logDeriv_completedZeta` (KadiriZeroFree:414); the two absolutely-convergent sums recombine.
- **(C) `KadiriAnalyticInputAtZero` term**: instantiate `logDeriv_completedZeta`,
  `re_three_four_one_one_over_sub_nonneg` (drop non-`s` zeros since `F(n) ≥ 0`),
  `KadiriDigamma.re_digamma_le` for `logDeriv Γℝ`, assemble to `≤ 3/(σ-1)+4·log(|t|+2)`.

**Trap to avoid:** if a lemma "doesn't exist," re-grep the file for the stem (§2). `xi_bound_re_gt_one`
is the only notable `private` recycle — use `xi_norm_bound_whole_plane`.

Finish with: `lake build KadiriZeroFree` EXIT 0, then
`#print axioms kadiriLamzouriZetaZeroFreeEdge` shows **no `sorryAx`**.

---

## 17. Known open items (flagged, NOT closable here)

- `JensenTranslation.lean` lines 103/109/449/462/471 — RH-equivalent sorries (excluded by scope).
- Engine files' `axiom RiemannHypothesisProp_apply` — asserts RH directly (flagged).
- `xiZeros_simple` — open simplicity conjecture (a declared axiom, not a `sorry`).

---

## Appendix A — Precise interfaces (exact types; verified)

Quote the **fully-namespaced** name to another agent, e.g.
`ZeroFreeRegionHadamard.hadamard_factorization_genus_one` or `KadiriDigamma.re_digamma_le`.
Where a theorem lives inside `namespace ZeroFreeRegion` (ZeroFreeRegionProof.lean:87) the bare
name is reachable after `open ZeroFreeRegion`; inside `namespace Kadiri` (ZeroFreeRegionProof.lean:846)
use `Kadiri.*`.

### A.1 Hadamard / completed zeta (`ZeroFreeRegionHadamard.lean`)
- `hadamard_factorization_genus_one {f a} (hf : Differentiable ℂ f) (hane : ∀n, a n ≠ 0)`
  `(hzero : ∀z, f z = 0 ↔ ∃n, z = a n) (hord : ∀z, meromorphicOrderAt f z ≤ 1)`
  `(hinj : Function.Injective a) (hs2 : Summable fun n => (‖a n‖²)⁻¹)`
  `(htend : Tendsto (fun n => ‖a n‖) atTop atTop) :`
  `∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = exp (g z) * canonicalProductNat 1 a z`.
- `xi_zero_enumeration (hord : ∀z, meromorphicOrderAt xi z ≤ 1) (hSinf : Set {xi = 0}.Infinite) :`
  `∃ a, (∀n, a n ≠ 0) ∧ Injective a ∧ Tendsto ‖a n‖ atTop atTop ∧ (∀z, xi z = 0 ↔ ∃n, z = a n)`.
  (Call: `xi_zero_enumeration xiZeros_simple xiZeros_infinite`.)
- `xi_differentiable : Differentiable ℂ xi`.
- `xi_norm_bound_whole_plane` — **public** whole-plane bound for `ξ` (use instead of `private xi_bound_re_gt_one`).
- `logDeriv_completedZeta {a} (hane) (hinj) (hs2) (htend) (hzero) (hord : ∀z, meromorphicOrderAt xi z ≤ 1) :`
  `∃ g, Differentiable ℂ g ∧ ∀ s, 1 < s.re →`
  `-deriv riemannZeta s / riemannZeta s = (-deriv g s + 1/s + 1/(s-1) + logDeriv (fun x => x.Gammaℝ) s)`
  ` - ∑' n, (1/(s - a n) + 1/a n)`. (Call with `xiZeros_simple` as the `hord` argument; needs `a`
  from `xi_zero_enumeration`, `hs2` from `xi_enum_ncard_bound`.)
- `orderSet_completedRiemannZeta₀ : (3/2 : ℝ) ∈ orderSet (completedRiemannZeta₀)` (re-exported in `SorryFix`).
- `canonicalProductNat`, `canonicalProductNat_ne_zero` (3284), `differentiable_canonicalProductNat` (3180),
  `logDeriv_canonicalProductNat` (3314), `logDeriv_canonicalProductNat_genus_one` (3462).

### A.2 3-4-1 inequality (`ZeroFreeRegionInfra.lean`, namespace `ZeroFreeRegion`)
- `re_three_four_one_one_over_sub_nonneg {σ t} (ρ : ℂ) (hd : 0 < σ - ρ.re) :`
  `0 ≤ 3·((1/(σ-ρ)).re) + 4·((1/(σ+t·I-ρ)).re) + ((1/(σ+2t·I-ρ)).re)`.
- `re_three_four_one_one_over_sub_borderline (d g : ℝ) (hd : 0 < d) :`
  `4/d ≤ 3·((d - g·I)⁻¹).re + 4·((d)⁻¹).re + ((d+g·I)⁻¹).re`.
- `re_inv_nonneg_of_re_nonneg {z} (h : 0 ≤ z.re) : 0 ≤ z⁻¹.re` (used for the `+1/a n` shift terms).
- `three_four_one_neg_logDeriv_riemannZeta` / `three_four_one_re_LSeries_vonMangoldt` (335/312):
  the `3·f(σ)+4·f(σ+it)+f(σ+2it) ≥ 0` identity for `−ζ'/ζ` (a LOWER bound; you need an UPPER bound,
  so use it only to check signs, and use the per-zero lemmas above to DROP nonneg terms).
- `zeroFreeEdge_from_factorization` (652): takes `(σ t) (hσ : 1<σ) (Z : Finset ℂ) (ρ₀) (ρ₀∈Z)
  (ρ₀.im=t) (0<ρ₀.re) (ρ₀.re<1) (∀ρ∈Z,0<ρ.re) (∀ρ∈Z,ρ.re<1) (analytic) (h_decomp : ∀s',1<s'.re,
  LSeries ↗Λ s' = analytic s' - ∑ ρ'∈Z, (1/(s'-ρ')+1/ρ')) (A₀ A₁ A₂) (0≤A₀)(0≤A₁)
  (h_analytic : 3·analytic(σ).re+4·analytic(σ+t·I).re+analytic(σ+2t·I).re ≤ A₀/(σ-1)+A₁·log(|t|+2)+A₂)
  (hRHS_pos) : σ - ρ₀.re ≥ 4/(A₀/(σ-1)+A₁·log(|t|+2)+A₂)`.

### A.3 Final zero-free edge (`ZeroFreeRegionProof.lean` / `ZeroFreeRegion`)
- `riemannZeta_ne_zero_of_zeroFreeEdge` (930): `(s) (ht : |s.im|≥1) (hσ : s.re ≥ zeroFreeEdge s.im)`
  `(σ) (hσgt : 1<σ) (Z) (s∈Z) (∀ρ∈Z,0<ρ.re) (∀ρ∈Z,ρ.re<1) (analytic) (h_decomp) (A₀ A₁ A₂)
  (0≤A₀)(0≤A₁) (h_analytic) (hRHS_pos)
  (h_c : kadiriConstant/log(|s.im|+10) < 4/(A₀/(σ-1)+A₁·log(|s.im|+2)+A₂) - (σ-1)) : riemannZeta s ≠ 0`.
- `kadiriConstant` (def, `ZeroFreeRegionProof.lean:760`, `kadiriConstant_pos`): a numeric constant;
  `kadiri_numerical_bridge` (KadiriZeroFree:19) proves `kadiriConstant = 1/57.54` — this is what makes
  the `(3,4,0)` bridge `1/57.54 < 1/56` close.
- `zeroFreeEdge` (def, `ZeroFreeRegionProof.lean`): the curve `s.re ≥ zeroFreeEdge s.im` (≈ `1 - 1/(…)`);
  `zeroFreeEdge_gt_nine_tenths` is used to get `0 < s.re` for a supposed zero.

### A.4 Borel-Carathéodory / Cauchy (`Mathlib`)
- `Complex.borelCaratheodory (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))` (BorelCaratheodory.lean:109):
  `Re(f z) ≤ M` on `ball 0 R` ⇒ bounds `‖f z‖` on a smaller ball. General (no `f 0 = 0`) version.
- `Complex.norm_deriv_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))` (Schwarz.lean:257):
  if `f : ball c R₁ → ball 0 C` then `‖deriv f c‖ ≤ C/R₁`. Use to kill `g''` from the Borel-Carathéodory
  growth bound.
- `Complex.norm_eqOn_closedBall_of_isMaxOn` (AbsMax.lean): maximum modulus.

### A.5 Digamma (`KadiriDigammaBound.lean`, namespace `KadiriDigamma`)
- `re_digamma_le {z} (hx0 : 0<z.re) (hx1 : z.re≤1) (hy : z.im≠0) :`
  `(Complex.digamma z).re ≤ Real.log (|z.im|+2)+1`.
- `re_digamma_le_of_real {x} (hx0 : 0<x) (hx1 : x≤1) : (digamma x).re ≤ log(|x|+2)+1`.
- Supports: `re_digamma_eq_tsum` (114), `summable_re_digamma_terms` (133), `tsum_re_digamma_terms_le` (169).
- Use this for `Re(logDeriv Γℝ)(s) = -(log π)/2 + (1/2)·Re ψ(s/2)`; the `+1` constant is admissible with `A₂=0`.

### A.6 Jensen (`Mathlib` + Zeta23)
- `MeromorphicOn.circleAverage_log_norm` (JensenFormula.lean:308),
  `AnalyticOnNhd.circleAverage_log_norm` (376), `AnalyticOnNhd.sum_divisor_le` (390).
- `logCounting_*` family (ValueDistribution/LogCounting/Basic.lean); `logCounting_divisor_eq_circleAverage_sub_const` (580).
- `Zeta23.WeilEF.Landau.*` — Jensen applied to `ζ` for zero counts / partial fractions (`f'/f` on disks).

---

## Appendix B — Data-flow / dependency map

```
xi (completed zeta)                [ZeroFreeRegionHadamard.xi_differentiable, xi_zero_*, xiFE]
   │
   ├─ xi_zero_enumeration (xiZeros_simple, xiZeros_infinite) ──► a : ℕ → ℂ  (zero enumeration)
   │       └─ xi_enum_ncard_bound ──► Summable (1/‖a n‖²)  (hs2)
   │
   ├─ hadamard_factorization_genus_one (f:=xi) ──► ∃ g, xi = exp g · canonicalProductNat 1 a
   │       │
   │       └─ logDeriv_completedZeta ──► -ζ'/ζ = (-g' + 1/s + 1/(s-1) + logDeriv Γℝ) - Σ'(1/(s-a n)+1/a n)
   │                                      (this is THE equation to feed KadiriAnalyticInputAtZero)
   │
   └─ xiFE : xi(1-s) = xi s  ──► ρ↦1-ρ involution  ──► hadamard_constant_re (B.re = -Σ' Re(1/ρ))

3-4-1 engine [ZeroFreeRegionInfra / ZeroFreeRegion]
   re_three_four_one_one_over_sub_nonneg (per-zero ≥ 0)  +  re_inv_nonneg_of_re_nonneg (1/a n shift)
       └─ used by HadamardBridge.zeroFreeEdge_from_tsum AND by KadiriZeroFree assembly

KadiriZeroFree.lean
   KadiriAnalyticInputAtZero (513)  ──[needs: hadamard_exponent_affine + hadamard_constant_re
   │                                       + KadiriDigamma.re_digamma_le]──► proof term
   kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero (536, SORRY-FREE, (3,4,0) bridge)
       └─ riemannZeta_ne_zero_of_zeroFreeEdge (A₀=3,A₁=4,A₂=0)  [ZeroFreeRegionProof:930]
           └─ zeroFreeEdge_from_factorization (652)  [the generic 3-4-1 edge]
   kadiriLamzouriZetaZeroFreeEdge (627)  ── (sorry : KadiriAnalyticInputAtZero)  ← OPEN TARGET
```

Build chain: every file `import`s either `Mathlib` or another custom file; the root `lean_lib
RootScratch` (lakefile.lean:196–209) lists the build roots. Zeta23 is pulled via
`Glob.submodules `Zeta23``.

---

## Appendix C — Reading order (read these doc-comments FIRST)

In order, before attempting the target:
1. `KadiriZeroFree.lean:482–520` — the authoritative explanation of `KadiriAnalyticInputAtZero`,
   why the old `KadiriAnalyticInput` is false (`not_kadiriAnalyticInput`), and the two missing
   classical ingredients (sharp digamma + affine exponent). **This comment is the spec.**
2. `KadiriZeroFree.lean:603–625` — why the leaf is still open and the explicit instruction NOT to
   `axiom`-ify `KadiriAnalyticInput`.
3. `KadiriZeroFree.lean:380–481` — the *dead* `kadiriLamzouriZetaZeroFreeEdge_of_analyticInput`
   (uses refutable `KadiriAnalyticInput`); study the call shape of `riemannZeta_ne_zero_of_zeroFreeEdge`
   so you replicate it correctly in the `AtZero` version.
4. `ZeroFreeRegionHadamard.lean:4320–4358` — `logDeriv_completedZeta` (the decomposition equation).
5. `ZeroFreeRegionInfra.lean:615–642` — the per-zero 3-4-1 inequalities and their exact shapes.
6. `HadamardBridge.lean:1–122` — `zeroFreeEdge_from_tsum`: the canonical worked example that turns
   a `Σ(1/(s-a n)+1/a n)` decomposition into the `(A₀,A₁,A₂)` edge.

---

## Appendix D — Worked skeleton for the Kadiri term

**Obligation** (the `∀`-body of `KadiriAnalyticInputAtZero`, line 513), given
`s σ analytic` with `1<σ`, `σ≤9/8`, `1≤|s.im|`, `0<s.re`, `s.re<1`, `riemannZeta s = 0`, and
`hdecomp : ∀ s', 1<s'.re, LSeries ↗Λ s' = analytic s' - ∑ ρ∈{s}, (1/(s'-ρ)+1/ρ)`, prove
`C(analytic) := 3·analytic(σ).re + 4·analytic(σ+t·I).re + analytic(σ+2t·I).re
 ≤ 3/(σ-1) + 4·log(|t|+2) + 0`.

**Step 1 — decompose.** Build `a` from `xi_zero_enumeration xiZeros_simple xiZeros_infinite`, get
`hs2` from `xi_enum_ncard_bound`, then `logDeriv_completedZeta ... xiZeros_simple` yields `g`,
`hgd`, `heq`. Because `LSeries ↗Λ s' = -deriv riemannZeta s' / riemannZeta s'` for `1<s'.re`, equate
with `hdecomp` and cancel the single `{s}` term to obtain
`analytic s' = (-g'(s') + 1/s' + 1/(s'-1) + logDeriv Γℝ s') - ∑'_{a n ≠ s} (1/(s'-a n) + 1/a n)`.

**Step 2 — 3-4-1 upper bound.** Define `C(f)` as the 3-4-1 combination. For each `a n ≠ s` with
`0 < Re(a n) < 1 < σ`, `re_three_four_one_one_over_sub_nonneg σ t (a n) _` gives the `1/(s'-a n)`
part `≥ 0`, and `re_inv_nonneg_of_re_nonneg` gives the `1/a n` shift `≥ 0`; so the whole subtracted
sum has `C(·) ≥ 0`. Likewise `C(1/s' + 1/(s'-1)) ≥ 0` (apply the per-zero lemma at ρ=0 and ρ=1).
Hence `C(analytic) ≤ C(-g') + C(logDeriv Γℝ)`.

**Step 3 — digamma part.** `C(logDeriv Γℝ) = 3·(-(log π)/2 + (1/2)Re ψ(σ/2)) + ...`; bound each
`Re ψ` by `KadiriDigamma.re_digamma_le` (sharp, `+1`). This yields `≤ 4·log(|t|+2) + O(1)` with
ample room (the `O(1)` is absorbed because `A₂ = 0` and `kadiri_numerical_bridge` makes the bridge
admissible — see the file's own numerical proof at `kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero:574–589`).

**Step 4 — affine exponent part.** With `hadamard_exponent_affine` (`g' ≡ B`) and `hadamard_constant_re`
(`B.re = -Σ' Re(1/ρ)`), pin `C(-g')` to the constant. The exact sign bookkeeping that combines
`C(-g')` with the dropped sums and the digamma term to reach the `3/(σ-1)+4·log(|t|+2)` bound is the
subtle core — do NOT guess it; follow the file's doc-comment (lines 482–520) and re-check every
`Re`/`-B` sign against `logDeriv_completedZeta` (note its `-deriv g s` term). If a sign comes out
positive/divergent, you have mis-cancelled the `{s}` pole in Step 1.

**Step 5 — conclude.** Supply the resulting proof term as the argument to
`kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero` at line 630 (replace the `sorry`).

---

## Appendix E — Pitfalls / FAQ

- **"I can't find lemma X."** Re-grep the specific file for the stem (§2). Names in briefs are sometimes
  doc-prose, not exact identifiers. Verified existing ones: `hadamard_factorization_genus_one`,
  `xi_zero_enumeration`, `logDeriv_completedZeta`, `canonicalProductNat_ne_zero`,
  `orderSet_completedRiemannZeta₀`, `completedZeta_order_le_one`, `xi_differentiable`,
  `xi_zero_iff_riemannZeta_zero`, `xi_norm_bound_whole_plane` — all in `ZeroFreeRegionHadamard.lean`.
- **`xi_bound_re_gt_one` is `private`** (line 1522) — unused outside its file. Use the public
  `xi_norm_bound_whole_plane` (4535).
- **No theorem named `logDeriv_Gammaℝ`** — compose `Re(logDeriv Γℝ)(s) = -(log π)/2 + (1/2)·Re ψ(s/2)`
  from `logDeriv_GammaSeq_eq` (ZeroFreeRegionHadamard:2520) + the Zeta23 Γ-shift, or use
  `KadiriDigamma.re_digamma_le` directly.
- **Don't `axiom`-ify `KadiriAnalyticInput`** — it is `false` (`not_kadiriAnalyticInput`, line 333).
- **Don't reinvent `re_three_four_one_one_over_sub_*`** — it exists in `ZeroFreeRegion` (Infra:632/615).
- **Don't reinvent Borel-Carathéodory or Schwarz** — both are in upstream Mathlib (§A.4).
- **Namespace confusion:** `re_three_four_one_one_over_sub_nonneg` exists both in `ZeroFreeRegion`
  (Infra + Proof) and is called by `HadamardBridge`/`KadiriZeroFree` after `open ZeroFreeRegion`.
- **Concurrency:** never run two `lake`/`lean` processes; always take `.lake_build_lock` (§3).

---

## Appendix F — Key global definitions (the vocabulary you must know)

| Name | Kind / where | Meaning |
|------|--------------|---------|
| `xi` | `noncomputable def` (`ZeroFreeRegionHadamard.lean:4042`) | completed Riemann xi: `s*(s-1)*completedRiemannZeta₀ s + 1`. NOT the same as Zeta23's `xi` (`s*(s-1)/2*… + 1/2`) — **do not mix the two**. |
| `completedRiemannZeta₀` | `def` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:64`) | `completedHurwitzZetaEven₀ 0 s` (the completed ζ, no `s(s-1)` factor here). |
| `Gammaℝ` | `def` (`Mathlib/Analysis/SpecialFunctions/Γ/Deligne.lean:43`) | `π^(-s/2) * Γ(s/2)`. So `logDeriv Γℝ(s) = -(log π)/2 + (1/2)·logDeriv Γ(s/2)`. |
| `LSeries ↗Λ` | notation (`open scoped LSeries.notation`) | the von-Mangoldt L-series; on `Re>1`, `LSeries ↗Λ s = -deriv riemannZeta s / riemannZeta s`. This is the object the 3-4-1 engine bounds. |
| `zeroFreeEdge` | `noncomputable def` (`ZeroFreeRegionProof.lean:776`) | zero-free curve `s.re ≥ zeroFreeEdge s.im`; `zeroFreeEdge_gt_nine_tenths` gives `0 < s.re` for a supposed zero. |
| `kadiriConstant` | `noncomputable def` (`ZeroFreeRegionProof.lean:758`) | `1/57.54`; `kadiri_numerical_bridge` (KadiriZeroFree:19) proves this value, making the `(3,4,0)` bridge `1/57.54 < 1/56` close. |
| `meromorphicOrderAt` | `def` (`Mathlib/Analysis/Meromorphic/Order.lean:50`) | order of a meromorphic fn at a point (`WithTop ℤ`). |
| `orderSet` | `def` (`ZeroFreeRegionHadamard.lean:239`) | the set of growth orders of an entire function. |
| `canonicalProductNat` | `def` (`ZeroFreeRegionHadamard.lean`) | Weierstrass canonical product of genus `p`. |

**Notation you will see:** `↗Λ` is the von-Mangoldt arithmetic function; `Σ' n, …` is a
dependent sum (`Summable`); `Finset.sum_singleton` collapses `∑ ρ∈{s}, …` to a single term
`1/(s'-s)+1/s`. The `3-4-1` combination is written inline as
`3·f(σ).re + 4·f(σ+t·I).re + f(σ+2t·I).re`.

---

## Appendix G — Per-file import & `open` map (so you know what is in scope)

| File | imports (key) | `open` / namespaces in scope |
|------|---------------|------------------------------|
| `ZeroFreeRegionHadamard.lean` | `Mathlib`, `LogBounds`, `Log.Summable` | `Complex Finset Real HurwitzZeta`; `Topology Filter Metric`; namespace `ZeroFreeRegionHadamard` |
| `ZeroFreeRegionInfra.lean` | `ZetaAsymp`, `LSeries.Dirichlet`, `BorelCaratheodory`, `Hadamard`, `PSeries`, `SumIntegralComparisons`, `ImproperIntegrals` | `Complex Real Topology Asymptotics`; `BigOperators`; `MeasureTheory Set`; `ArithmeticFunction hiding log`; namespace `ZeroFreeRegion` (79) |
| `ZeroFreeRegionProof.lean` | same as Infra + `Mathlib` | `Complex Real Topology Asymptotics`; `ZeroFreeRegion` (87) and `Kadiri` (846); `BigOperators` |
| `HadamardBridge.lean` | `Mathlib`, `ZeroFreeRegionProof` | `Complex Real ZeroFreeRegion`; `BigOperators LSeries.notation`; `ArithmeticFunction hiding log` |
| `KadiriZeroFree.lean` | `ZeroFreeRegionProof`, `ZeroFreeRegionHadamard`, `Zeta23.RvM.Statement`, `Zeta23.GammaFacts.Complete`, `Zeta23.Assembly`, `Zeta23.FromPNTPlus.ZetaBounds` | `Complex Real Topology`; `ZeroFreeRegionHadamard`; `ArithmeticFunction hiding log`; `LSeries.notation`; `Axiom xiZeros_simple` lives here (242) |
| `KadiriDigammaBound.lean` | `Mathlib`, `ZeroFreeRegionHadamard` | `Finset ZeroFreeRegionHadamard`; `BigOperators`; namespace `KadiriDigamma` |
| `MertensEstimate.lean` | `Mathlib`, `Zeta23.FromPNTPlus.Mertens` | `Complex Real Topology Filter MeasureTheory`; `BigOperators Nat.Prime`; `Chebyshev` |
| `ApproxZetaLowerBound.lean` | `Mathlib` only | `Complex Real Topology Filter`; `BigOperators` |
| `JensenTranslation.lean` | `Mathlib`, `riemann_hypothesis` | `Complex`; `Filter`; `BigOperators`; namespace `JensenRH` (RH-equivalent) |
| `BorelCaratheodory.lean` | `Mathlib.Analysis.Complex.BorelCaratheodory`, `AbsMax` | (shim; lemmas are `Complex.borelCaratheodory` etc.) |
| `SorryFix.lean` | `Mathlib`, `ZeroFreeRegionHadamard` | `Complex Finset Real HurwitzZeta`; `Topology`; namespace `SorryFix` |
| `rh_certificate_infra.lean` | `Mathlib` | `Complex Real Set Topology`; namespaces `BoundaryProofEngine`,`CellProofEngine`,`Rect2D`,`TailProofEngine` |

**Rule:** before calling a lemma from another file, check it is `open`ed or namespace-qualified, and
that the file is imported (directly or transitively). If a name is "not found," it is almost always
because the consuming file did not `open` the right namespace (e.g. you must write
`ZeroFreeRegion.re_three_four_one_one_over_sub_nonneg` or `open ZeroFreeRegion` first).

---

## Appendix H — Doc-prose → Lean-name lexicon (avoid reimplementing)

When a brief or comment says… | …the actual Lean name to use is |
|--------------------------------|------------------------------------------|
| "Hadamard factorization of ξ" | `ZeroFreeRegionHadamard.hadamard_factorization_genus_one` (3823) |
| "enumerate the zeros of ξ" | `xi_zero_enumeration xiZeros_simple xiZeros_infinite` (4642) |
| "log-derivative decomposition of −ζ'/ζ" | `logDeriv_completedZeta` (4320) — gives the exact equation in App. A.1 |
| "3-4-1 per-zero inequality" | `ZeroFreeRegion.re_three_four_one_one_over_sub_nonneg` (Infra:632) / `_borderline` (615) |
| "zero-free edge from factorization" | `zeroFreeEdge_from_factorization` (Proof:652) or `riemannZeta_ne_zero_of_zeroFreeEdge` (930) |
| "tsum bridge to the Kadiri edge" | `HadamardBridge.zeroFreeEdge_from_tsum` (15) — the template to copy |
| "sharp digamma bound `Re ψ(z) ≤ log|z|`" | `KadiriDigamma.re_digamma_le` (253) — NOT `Re ψ ≤ log|z|`, NOT crude `digamma_le_log` |
| "affine Hadamard exponent `deriv g ≡ B`" | **NOT yet in repo** — you must prove `hadamard_exponent_affine` (new). Don't search for it; build it from `hadamard_factorization_genus_one` + `borelCaratheodory` + `norm_deriv_le_div_of_mapsTo_ball`. |
| "Hadamard constant `Re B = -Σ'Re(1/ρ)`" | **NOT yet in repo** — prove `hadamard_constant_re` (new) from `xiFE` + `logDeriv_completedZeta`. |
| "canonical-product lower bound `|P|≥exp(-O(R·log R))`" | Jensen: `MeromorphicOn.circleAverage_log_norm` (308) + `Zeta23.WeilEF.Landau.*`; combine with a zero-count (`xi_enum_ncard_bound` or RvM). |
| "Borel-Carathéodory growth bound" | `Complex.borelCaratheodory` / `_zero` (Mathlib BorelCaratheodory.lean:86/109) |
| "Cauchy derivative estimate to kill higher derivatives" | `Complex.norm_deriv_le_div_of_mapsTo_ball` (Schwarz.lean:257) |
| "maximum modulus" | `Complex.norm_eqOn_closedBall_of_isMaxOn` (AbsMax.lean) |
| "xi has infinitely many zeros" | `xiZeros_infinite` (KadiriZeroFree:99, genuine proof) |
| "(7/4) is an order of ξ" | `orderSet_xi` (KadiriOrderInfra:51) |
| "whole-plane bound on ξ" | `xi_norm_bound_whole_plane` (4535) — use instead of `private xi_bound_re_gt_one` |
| "Mertens / PNT estimate" | `MertensEstimate.*` or `Zeta23.FromPNTPlus.Mertens` (namespace `Mertens`) |
| "middle-gap zero-freeness" | `ApproxZetaLowerBound.riemannZeta_ne_zero_of_middle_gap` (122) |

**If a name in this lexicon is marked "NOT yet in repo," that is expected — those are the few new
lemmas you must write (they are short assemblies, not from-scratch research).**

---

## Appendix I — Copy-paste build & verify commands

Run from the repo root `C:\Users\mmeadow\Documents\Lean\mathlib4`. The **lock must wrap every
`lake build`** so two agents/processes never touch `.lake/build` at once.

```powershell
# 1. Acquire the mutex (atomic). If it exists OR lake.exe is running, wait and retry.
$lock = "C:\Users\mmeadow\Documents\Lean\mathlib4\.lake_build_lock"
$got = $false
for ($i=0; $i -lt 30; $i++) {
  if (Test-Path $lock) { Start-Sleep -Seconds 10; continue }
  if (Get-Process -Name lake -ErrorAction SilentlyContinue) { Start-Sleep -Seconds 10; continue }
  try { New-Item -Path $lock -ItemType File -ErrorAction Stop | Out-Null; $got = $true; break }
  catch { Start-Sleep -Seconds 10 }
}
if (-not $got) { Write-Error "could not acquire lock"; exit 1 }

# 2. Build (single module). Heavy imports → allow the full 900000 ms.
try {
  lake build KadiriZeroFree
  # 3. Verify no sorry axiom leaked into the target:
  lake env lean --run "import KadiriZeroFree
#print axioms kadiriLamzouriZetaZeroFreeEdge" 2>&1 | Select-String "sorryAx"
}
finally {
  Remove-Item $lock -ErrorAction SilentlyContinue
}
```

- **Never** run `lake build` without the lock. If a previous agent crashed, the lock may be stale
  (>25 min): `Remove-Item $lock` then re-acquire.
- If `lake env lean` crashes with EXIT=-1 (intermittent), prefer `lake build <Module>` (EXIT 0 is
  what you need; it writes the `.olean`).
- To quickly check for real `sorry`s in a file (ignoring doc prose): `rg -n "\(sorry" <FILE>` or
  `rg -n "sorry :" KadiriZeroFree.lean`.

---

## Appendix J — Exact theorem headers to WRITE (the new lemmas)

These do not exist yet. Copy these headers as your starting point (adjust as Lean's elaborator
requires). They are short assemblies of existing lemmas, not research.

```lean
-- In ZeroFreeRegionHadamard.lean (or a new file registered in lakefile.lean):
-- (L1) The Hadamard exponent of ξ is affine: deriv g is a constant B.
theorem hadamard_exponent_affine
    (a : ℕ → ℂ) (hane : ∀ n, a n ≠ 0) (hinj : Function.Injective a)
    (hs2 : Summable fun n => (‖a n‖ ^ 2)⁻¹) (htend : Tendsto (fun n => ‖a n‖) atTop atTop)
    (hzero : ∀ z, xi z = 0 ↔ ∃ n, z = a n) (hord : ∀ z, meromorphicOrderAt xi z ≤ 1) :
    ∃ (g : ℂ → ℂ) (B : ℂ),
      Differentiable ℂ g ∧
      (∀ z, xi z = Complex.exp (g z) * canonicalProductNat 1 a z) ∧
      deriv g = fun _ => B :=
  by
    rcases hadamard_factorization_genus_one (f := xi) xi_differentiable hane hzero hord hinj hs2 htend
      with ⟨g, hgd, hdecomp⟩
    -- bound Re g ≤ O(R log R) via xi_norm_bound_whole_plane (right), xiFE (left),
    --   polynomial strip bound, and the Jensen canonical-product lower bound;
    -- apply Complex.borelCaratheodory, then Complex.norm_deriv_le_div_of_mapsTo_ball
    -- to show g'' ≡ 0 ⇒ g is affine ⇒ deriv g ≡ B.
    sorry   -- ← replace with the short assembly

-- (L2) The real part of that constant: B.re = -Σ' Re(1/ρ).
theorem hadamard_constant_re
    (a : ℕ → ℂ) (hane : ∀ n, a n ≠ 0) (hinj : Function.Injective a)
    (hs2 : Summable fun n => (‖a n‖ ^ 2)⁻¹) (htend : Tendsto (fun n => ‖a n‖) atTop atTop)
    (hzero : ∀ z, xi z = 0 ↔ ∃ n, z = a n) (hord : ∀ z, meromorphicOrderAt xi z ≤ 1)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hdecomp : ∀ z, xi z = Complex.exp (g z) * canonicalProductNat 1 a z)
    (B : ℂ) (hB : deriv g = fun _ => B) :
    B.re = -∑' n, (1 / a n).re :=   -- equivalently -∑' over zeros ρ, Re(1/ρ)
  by
    -- use xiFE (xi(1-s)=xi s) ⇒ ρ↦1-ρ bijection, and logDeriv_completedZeta to equate the
    -- two absolutely-convergent sums at w and 1-w.
    sorry   -- ← replace with the short assembly
```

Then in `KadiriZeroFree.lean`, build the `KadiriAnalyticInputAtZero` term (App. D) and replace the
`sorry` at line 630:
```lean
theorem kadiriLamzouriZetaZeroFreeEdge (s : ℂ) (ht : |s.im| ≥ 1)
    (hre : s.re ≥ zeroFreeEdge s.im) : riemannZeta s ≠ 0 :=
  kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero
    kadiriAnalyticInputAtZero_proof s ht hre
```
where `kadiriAnalyticInputAtZero_proof : KadiriAnalyticInputAtZero` is your assembly.

---

## Appendix K — Zeta23 module index (what you may call)

Zeta23 is a 316-file library (junction at `zeta-23-lean/Zeta23`), imported into the root via
`Glob.submodules `Zeta23`` (lakefile.lean:201,208). It uses Mathlib `Complex.riemannZeta`. Only a
few modules are needed here; the rest is context.

| Module (namespace) | What it gives | Build status |
|--------------------|---------------|--------------|
| `Zeta23.RvM.Statement` (`RvM`) | `riemannVonMangoldt : RiemannVonMangoldt zetaZeroConfig` (zero-count `N(T)=O(T log T)`) | builds |
| `Zeta23.GammaFacts.Complete` (`GammaFacts`) | `gammaFacts : GammaFacts` (via Stirling) | builds |
| `Zeta23.FromPNTPlus.ZetaBounds` (`ZetaBounds`) | residue/analytic facts for ζ; `analyticAt_riemannZeta`, `deriv_f_minus_A_inv_sub_clean`, `deriv_inv_sub` | builds |
| `Zeta23.FromPNTPlus.Mertens` (`Mertens`) | verified Mertens estimate (used by `MertensEstimate.lean`) | builds |
| `Zeta23.WeilEF.Landau` (`Zeta23.WeilEF`) | **Jensen applied to ζ**: `logDeriv_partial_fraction_unit` (299), `logDeriv_partial_fraction_disk` (348), `zeta_logDeriv_partial_fraction` (512), `logDeriv_zero_prod` (77), `logDeriv_split` (88), `norm_logDeriv_Cf_le` (129) — the canonical-product / `f'/f` tooling | builds |
| `Zeta23.Assembly` | top-level assembly glue | builds |
| `Zeta23.Final`, `Zeta23.XiPrime.ZeroCount`, `Zeta23.ZeroSide` | headline results | no `.olean` — not needed |

**When to reach for Zeta23:** only for the canonical-product lower bound / zero-count in (L1) — i.e.
`Zeta23.WeilEF.Landau.*` plus `RvM.Statement`. Everything else in the target is root infrastructure.

---

## Appendix L — The numerical bridge `kadiriConstant` (why `(3,4,0)` works)

`kadiriConstant := 1/57.54` (`ZeroFreeRegionProof.lean:758`); `kadiri_numerical_bridge`
(KadiriZeroFree:19) proves that value. The edge theorem `riemannZeta_ne_zero_of_zeroFreeEdge`
(App. A.3) requires
`kadiriConstant/log(|t|+10) < 4/RHS - (σ-1)` where `RHS = A₀/(σ-1) + A₁·log(|t|+2) + A₂`.

For the chosen `σ = 1 + (1/8)/log(|t|+10)` and `(A₀,A₁,A₂) = (3,4,0)`:
- `3/(σ-1) = 24·log(|t|+10)`, and `4·log(|t|+2) ≤ 4·log(|t|+10)`, so
  `RHS ≤ 28·log(|t|+10)` ⇒ `4/RHS ≥ 4/(28·log(|t|+10)) = 1/(7·log(|t|+10))`.
- The admissibility condition becomes `1/(57.54·log(|t|+10)) + 1/(8·log(|t|+10)) < 1/(7·log(|t|+10))`.
- The file proves this reduces to `1/57.54 < 1/56` (since `1/7 - 1/8 = 1/56`), which is true
  (see `kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero:574–589`, already sorry-free).

**Consequence for you:** you do NOT need to re-tune constants. Your only job is to produce a term of
`KadiriAnalyticInputAtZero` whose conclusion is `≤ 3/(σ-1) + 4·log(|t|+2) + 0`; the rest of the
bridge is already proven. The `+1` in `KadiriDigamma.re_digamma_le` and the `A₂=0` choice are
exactly what makes the bridge close, so do NOT switch to a bound with a larger additive constant.

---

## Appendix M — Expanded gotcha catalog (verified)

| Symptom | Cause | Fix |
|---------|-------|-----|
| `unknown identifier xi_bound_re_gt_one` in another file | it is `private` (Hadamard:1522) | use `xi_norm_bound_whole_plane` (4535) |
| `unknown identifier logDeriv_Gammaℝ` | no such name exists | compose from `logDeriv_GammaSeq_eq` (2520) or use `KadiriDigamma.re_digamma_le` |
| `unknown identifier re_three_four_one_one_over_sub_nonneg` | not `open`ed | write `ZeroFreeRegion.re_three_four_one_one_over_sub_nonneg` or `open ZeroFreeRegion` |
| `unknown identifier three_four_one_neg_logDeriv_riemannZeta` | exists only in `ZeroFreeRegion` ns (Infra/Proof) | qualify or `open ZeroFreeRegion` |
| "I grepped `*.lean` and found nothing" | wrong path / grep tool quirk | use `rg -n "STEM" <FILE>` from Bash with `--no-ignore` (§2) |
| `kadiriLamzouriZetaZeroFreeEdge` still has a `sorry` after edit | you edited the wrong theorem | the `sorry` is at line **630** inside `kadiriLamzouriZetaZeroFreeEdge`, fed to `..._of_analyticInputAtZero` |
| `axiom RiemannHypothesisProp_apply` in engine files | not a `sorry`; asserts RH | flagged open item, do NOT "close" it |
| `KadiriAnalyticInput` looks usable | it is **false** (`not_kadiriAnalyticInput`) | use `KadiriAnalyticInputAtZero` (513) instead |
| `xi` type mismatch between files | root `xi` ≠ Zeta23 `xi` (factor 1/2) | only use root `xi` (`ZeroFreeRegionHadamard.xi`) in this target |
| build writes no `.olean` | used `lake env lean` (intermittent EXIT=-1) | use `lake build <Module>` (EXIT 0) |
| two builds corrupt `.lake/build` | ran `lake` in parallel | always take `.lake_build_lock` (App. I) |
