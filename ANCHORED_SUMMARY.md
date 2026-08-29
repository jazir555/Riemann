# Anchored Summary — RH Sorries Closure Campaign

## Objective
Close all root `sorry`s by recursive decomposition, delegating subgoals to parallel
agents and leveraging the `zeta-23-lean` (Zeta23) library wherever its theorems
transfer directly to the root's Mathlib `riemannZeta` objects.

## Environment Constraints
- Single `lake` build at a time: parallel agents serialize via a filesystem mutex
  (`.lake_build_lock`) plus a `lake.exe` check to prevent cache corruption.
- Zeta23 `Final`, `XiPrime.ZeroCount`, `ZeroSide` have NO oleons in this checkout
  (not needed for the closed sorries).
- `zeta-23-lean` Mathlib `riemannZeta` sharing confirmed → Zeta23 theorems apply
  directly to root objects (transfer by name, math axioms standard only).

## Architecture
- Zeta23 import now works from root; it uses Mathlib `riemannZeta` / `vonMangoldt`,
  so its `FromPNTPlus.*`, `ZetaReflect`, and `Statement` results transfer.
- Pattern: agent builds a file green under the serialized lock wrapper; verified
  files are checked into the working tree (see git status).

## Work State

### Completed (this turn — verified green)
- **Zeta23 cluster** (agent `ses_fb45ad130ffeVZ2coK4tpNyOU4`, DONE):
  - `MertensEstimate.lean` (0 sorries): `mertens_first_vonMangoldt`,
    `sum_vonMangoldt_div_le/_ge`, `sum_primes_log_div_le`, `sum_primes_recip_le_log`
    from `Zeta23.FromPNTPlus.Mertens`.
  - `rh_residual_gap.lean` (0 sorries): `zeta_zeroFree_pow`, `zeta_strip_zero_reflect`,
    `zeta_crit_line_iff_no_right_half`, `ThinRegionZeta`, `BoundedCoverZeta`,
    `zeta_thin_region_is_exact_gap`, `rh_iff_thin_region_zeta`,
    `rh_iff_thin_region_zeta_of_boundedCover` (no ZFR hypothesis),
    `strip_criterion_of_riemannHypothesis`.
  - `KadiriZeroFree.lean` (1 sorry): `kadiriLamzouriZetaZeroFreeEdge` delegates to
    sorry-free conditional `kadiriLamzouriZetaZeroFreeEdge_of_analyticInput`
    (`xiZeros_infinite` + `xi_enum_ncard_bound` from Zeta23). Only leaf
    `KadiriAnalyticInput` (line 411) remains `sorry`.
  - `KadiriHScratch.lean` (0 sorries): `kadiriLamzouriZetaZeroFreeEdge'` delegates to
    the conditional theorem.
- `ApproxZetaLowerBound.lean` DONE (green, 0 sorries) — fixed rpow/nat-cast math.
- `JensenTranslation.lean` DONE (green) — helpers `msum_nonneg`/`msum_pos`/
  `deriv_prod_identity`/`sum_im_inv`/`derivative_hyperbolic` proven; remaining
  `sorry`s are RH-equivalence leaves (see Blocked-open).
- `rh_*` cluster GREEN: `rh_certificate`, `rh_analytic_infra`, `rh_infra`,
  `rh_term_fps`, `rh_term_deriv`, `rh_zeta_cert_data`.

### Active
- Agent `ses_fb3ebf110ffeSr2nflh66CSa72` → fixing `rh_certificate_infra.lean`
  (pre-existing committed proof errors: `frl` typo ~111, `Complex.smul_re`/
  `add_re` lemmas, plus errors at 63/94/97/280/289/290/299). Running.

### Blocked-open (honest — cannot close without major new work)
- `KadiriZeroFree.lean:411` `KadiriAnalyticInput` — Kadiri's sharp 3-4-1 estimate
  (constants 3 and 2; `zeroFreeEdge = 1 − (1/57.54)/log(|t|+10)`). Zeta23 has NO
  such explicit region (`ZetaZeroFree` is thinner: `1 − A/(log|t|)^9`, unspecified
  A), so it cannot imply this in either direction. Needs explicit digamma/Hadamard
  3-4-1 estimate — a genuine hard analytic lemma, CLOSEABLE with effort.
- axiom `xiZeros_simple` (in KadiriZeroFree) — simplicity of ζ's zeros; this is the
  (unproven) simplicity conjecture. Cannot be closed.
- `JensenTranslation` RH-equivalence sorries — equivalent to RH (GORZ); cannot be
  closed without proving RH. `all_shifts_from_zero` additionally needs
  `0 < natDegree (jensenPoly d n)` (nonvanishing of ξ Taylor coefficients),
  unavailable.

### Next-Move
1. Close `KadiriAnalyticInput` with an explicit 3-4-1 estimate.
2. Verify `rh_certificate_infra.lean` once `ses_fb3ebf110ffeSr2nflh66CSa72` returns.
3. Final sweep: re-confirm 0-sorry files still build; document remaining open sorries.
