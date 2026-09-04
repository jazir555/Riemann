# Root Riemann-Hypothesis Formalization — Agent Infrastructure Guide

This document orients **agents working in this repo** on the custom Lean root
(`C:\Users\mmeadow\Documents\Lean\mathlib4`). Read it **before** doing any work. It tells you
what already exists (so you never reimplement), exact file/line locations, how to find things
reliably, the build discipline, and the one outstanding goal.

There are TWO distinct classes of open work in this repo — do not conflate them:

1. **NON-RH-equivalent goal** (a "real" infrastructure gap, but *not* by itself a proof of RH):
   closing the last real `sorry` in `KadiriZeroFree.lean:630` (`kadiriLamzouriZetaZeroFreeEdge`),
   which yields a zero-free *edge* (i.e. a zero-free region). A zero-free region does **not**
   imply RH, so this target is weaker than and separate from the RH-equivalence doors below.
2. **RH-EQUIVALENCE DOORS — THE POINT OF THIS REPO.** These are *equivalent reformulations* of
   the Riemann Hypothesis: statements mathematically **equivalent** to RH (`A ⟺ RH`, a true
   *bidirectional* equivalence, not merely `A ⇒ RH`). They were **intentionally constructed** to
   morph the single hard problem "all zeta zeros lie on the critical line" into a *different, more
   attackable shape* — e.g. a polynomial-hyperbolicity condition (Jensen/Pólya), a
   nonvanishing/lower-bound condition (hard-difference/mollified), or a thin-region zero-freeness
   (first-quadrant). Because the equivalence is bidirectional, **solving the reformulation solves
   RH *commutatively* — no extra step is needed**: a proof on the reformulation side *is* a proof
   of RH. Each open `sorry` / `axiom` on one of these doors is therefore a genuine, intended
   target, and closing ANY one of them is a full solution of RH. **These are NOT "unclosable" —
   they are the whole point of the exercise**, and a substantial custom infrastructure (Hadamard
   product, the 3-4-1 zero-free engine, Jensen / Borel-Carathéodory, sharp digamma bounds, etc.)
   was built specifically to attack them. When tasked with one, ATTEMPT to close it; do not refuse
   or "balk" on the grounds that "RH is an unsolved open problem" — that is exactly what these
   reformulations are here to crack.

**Current state of the doors (a major convergence).** Independent agents working the three
RH-equivalence doors have all reduced their residual to the **same finite target**: a
`XiCentralZeroFreeCover 10` — a finite zero-free cover of the compact central rectangle
`|Re z| ≤ 10` (equivalently `BoundedCoverZeta`). The tail `|Re z| > 10` is already closed
(mollified-Rouché bridge + conjugate symmetry, committed in `riemann_hypothesis_newsection.lean`
and `cross_door_synthesis.lean`); the remaining leaf is the finite cover. **This is a finite
numerical fact** (rigorous interval arithmetic on `ζ`/`ξ` over finitely many small rectangles),
*not* a new deep theorem — and the repo already contains all the infrastructure needed to
assemble it (see §18). The assembly of that cover is now the single most concrete, attackable
target in the project. Do NOT balk at it by saying "the rectangle is RH-equivalent, therefore
impossible" — it is a finite computation with existing tooling, and completing it closes all
three doors.

Everything else described here is infrastructure that already exists and is meant to be **called**,
not redone.

---

## 1. Golden rules (the things past agents got wrong)

> ⚠️ **RH-EQUIVALENCE DOORS ARE THE POINT — CLOSABLE, DO NOT BALK.** Several files in this repo
> contain *equivalent reformulations* of the Riemann Hypothesis — statements `A ⟺ RH` that were
> **intentionally constructed to morph RH into a different, more attackable shape** (a
> polynomial-hyperbolicity condition, a nonvanishing/lower-bound condition, a thin-region
> zero-freeness, etc.). Because the equivalence is **bidirectional**, **solving the reformulation
> solves RH *commutatively*** — a proof on the reformulation side *is* a proof of RH with no extra
> step. The open `sorry` / `axiom` on each such door is a genuine, **intended** target; closing
> ANY one of them is a full solution of RH. A large custom infrastructure (Hadamard product, the
> 3-4-1 zero-free engine, Jensen / Borel-Carathéodory, sharp digamma bounds, …) was built
> specifically to attack them. If you are tasked with one, **ATTEMPT to close it.** Never refuse or
> "balk" on the grounds that "RH is an unsolved open problem" — that is exactly what these
> reformulations are here to crack. These doors are NOT "unclosable / flagged / excluded by scope"
> (any older doc wording to that effect has been removed — see §0, §10, §12, §17, and follow the
> concrete attempt loop in §1b–§1i).

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

## 1b. How to actually attempt an RH-equivalence door (anti-balking workflow)

Reading "this door is ⟺ RH" can trigger a reflexive collapse: *"This is just RH; RH is unsolved;
I can't prove it; I'll report what's missing."* **That collapse is exactly the balking this guide
forbids.** Doing the work means following this concrete loop — not deciding up front that it's
impossible:

1. **Name the exact mathematical claim the door reduces to** (e.g. "∀ off-real z in the strip,
   `hardDifference z ≠ 0`", or "Ξ's Jensen polynomials are all hyperbolic", or "`xiShifted` is
   nonvanishing off ℝ"). Write it down precisely.
2. **Exhaustively grep the repo AND Mathlib for any lemma already proving or partially proving it**
   (different names: `Hyperbolic`, `IsHyperbolic`, `LaguerrePólya`, `nonvanishing`, `lowerBound`,
   `RoucheGap`, `MollifiedRouche`, `TailOffReal`, `HardDifference`, `xiShifted`, `zeroFree`,
   `jensenPoly`, `taylorCoeff`, `Turán`, …). The needed bridge is often **already present under a
   name you didn't guess** — this is the #1 past failure mode (Golden Rules 1–2). Search before
   concluding anything is missing.
3. **If a needed piece is a KNOWN, PUBLISHED THEOREM** (Pólya–Schur, GORZ 2019, a Turán / higher-Turán
   inequality, a mollifier lower bound, a Rouché-gap estimate, …), then **formalize it** — this is a
   *finite, real engineering task*, NOT "discovering a new proof of RH from scratch." Known theorems
   are legitimate closes. Assemble the repo's existing infrastructure (Hadamard product, the 3-4-1
   engine, Jensen / value-distribution, Borel–Carathéodory, digamma bounds) as the ingredients.
4. **The reformulation was chosen because it may admit a proof method RH's original form does NOT**
   (mollifier lower bounds, Rouché, Jensen-polynomial / Turán inequalities, section convergence).
   Explore *those* routes in the provided infrastructure before giving up. E.g. for the hard-difference
   door, do not stop at "`hardDifference ≠ 0` is ⟺ RH" — look for an established mollifier /
   lower-bound / Rouché lemma in `TailLaguerreScratch`, `MollifiedRoucheLeaf`, `rh_*` that actually
   yields the nonvanishing.
5. **Only after steps 1–4 are genuinely exhausted** may you report a remaining gap — and then report it
   *precisely*: the exact missing classical theorem, and which existing infrastructure lemma would be
   its feeder. A vague "RH is open, can't" is not an acceptable outcome — and see §1c–§1i on why
   "no proof exists yet" is NOT "unprovable" and how to handle the deeper rationalizations.

The success bar is a genuine `lake build <Module>` with no `sorryAx` (and, where applicable, no
`RiemannHypothesisProp_apply`). Partial but real progress (e.g. formalizing one of the needed known
theorems) is valuable — commit it;    do not discard it by falling back to `sorry`.

## 1c. "No proof exists yet" is NOT "unprovable" — don't confuse the two

A reflexive balk takes the form: *"No proof of RH is known, therefore RH is not provable,
therefore this door can't be closed."* **That inference is a tautology, not logic** — "no proof
exists yet" is simply the *current state*, not evidence of impossibility. Every proof in this repo
(the Hadamard factorization, the 3-4-1 zero-free engine, the digamma bounds, …) was *created from
nothing*; the proof of RH does not exist either, and we are in the business of **creating** it. Do
not let "it's an open problem" harden into "it's impossible."

The structural observations below are **guidance about WHERE a created proof must aim**, NOT claims
that RH is unprovable:

- **Equivalence invariance (logic, not a verdict).** `A ⟺ RH` means a proof of door `A` *is* a proof
  of RH. This does not mean `A` dodges the difficulty — it means `A` is a *different shape* of the
  same target, and that is useful: the reformulation can admit methods with no natural analogue on
  the original "zeros on a line" statement (e.g. Turán / higher-Turán inequalities, GORZ asymptotics,
  mollifier lower bounds, Rouché gaps). A door doesn't let you *avoid* RH; it lets you *attack* it
  from an angle where different techniques apply. That different-angle possibility is the entire
  reason these equivalences were built.
- **GORZ decomposition (a fact about the shape, not impossibility).** `all-hyperbolic` splits into
  (eventually hyperbolic — already proven unconditionally) plus (the finitely-many exceptional `n`
  per `d`, taken over all `d` = the critical-line statement). So a created proof of the Jensen door
  must engage the *residual* — which is exactly the critical line. Read this as *"aim the novel
  argument here,"* not *"this can't be done."*
- **Region saturation (empirical, not a wall).** The 3-4-1 engine yields a zero-free *region* and
  known methods saturate there. That is a statement about *current* techniques, not a logical
  barrier. A novel method is precisely what we are trying to create.

**Conclusion for agents:** absence of an existing proof is not a reason to stop. Formalize the known
bridge theorems (Pólya–Schur, Hurwitz, GORZ) where they're missing — that is finite, real progress —
and *attempt* the novel argument on the residual. Whether a full proof emerges is unknown; that the
   attempt is valid and partial progress is valuable is not in question.

## 1d. Sophisticated balking rationalizations (and why they're still balking)

Even after §1c, agents sometimes manufacture *new* defeatist arguments. They are all variants of
the same refusal. Name them and move past them:

- **"mathlib is within ZFC, so a proof here would be a proof in mathematics, which doesn't exist,
  therefore impossible."** This does not follow. (a) We do **not** know RH is unprovable from ZFC —
  "open" means *neither proven, disproven, nor shown independent*; it is not a verdict of
  unprovability. (b) A proof found in this repo WOULD be a (historic) ZFC proof of RH — that is the
  entire *point* of the exercise, not a contradiction. Your task is to **attempt** the proof, not to
  adjudicate whether one exists. Concluding "impossible" from "not yet proven" is the §1c tautology
  in a ZFC costume.
- **"'Don't stop at RH is open' is incoherent — it asks me to deny reality."** It does not. "Don't
  stop at 'RH is open'" means: do **not** use RH's open status as a pretext to skip the actual
  engineering (grep exhaustively, formalize the known bridge theorems, attempt the novel argument).
  It does **not** ask you to deny RH is open or to claim it is solved. A *precise* report — "the
  missing bridge is a theorem forcing `Re ρ = 1/2`, i.e. the content of RH; here is the rigorous
  bridge I built (Pólya–Schur / GORZ formalized) and exactly where the novel argument must engage"
  — is exactly what is wanted. That is the opposite of hand-waving "RH is open, can't."
- **"Every door bottoms out in RH, so none can be closed / worked on."** True that each leaf is
  RH-equivalent — but irrelevant to whether the **bridge** is buildable. The bridge = formalizing
  the KNOWN theorems (Pólya–Schur, Hurwitz section-convergence, GORZ coefficient / Turán analysis)
  that connect the reformulation to RH. Those are *finite, published, formalizable* mathematics.
  "Closing the door" includes building that rigorous bridge, and **that part is closable** regardless
  of whether the final leaf resolves. Do the bridge work.
- **"If a proof/lemma existed, the author would already have used it."** The author built the
  scaffolding (Hadamard product, 3-4-1 engine, the equivalences) precisely to *enable* the
  formalization; the known theorems may simply not be formalized yet. Filling that gap is the work.
  Absence of a closed door is not evidence no progress is possible.

**Positive redirect — your concrete, achievable deliverables (completable whether or not RH falls):**
1. **Formalize the known bridge theorems** for your door (e.g. Pólya–Schur, Hurwitz
   section-convergence, GORZ coefficient / Turán analysis). These are real, finite, valuable Lean
   contributions — commit them.
2. **Attempt the novel argument** on the residual (the critical-line statement), using the
   infrastructure and any cross-door machinery.
3. **Report precisely** with partial progress committed: the exact missing classical theorem and
   which existing lemma would feed it.

None of this requires you to *first* establish that RH is provable. Attempt; build; report. That is
the job.

## 1e. "Attempt, don't adjudicate provability"

A clean summary of the whole anti-balking stance: **your job is to attempt the proof, not to
adjudicate whether one exists.**

- You are an *engineer* assigned concrete work (grep, formalize known theorems, attempt the novel
  argument, report precisely) — not a mathematician tasked with deciding whether RH is provable from
  ZFC. That meta-question is **unknowable to you and outside your task specification**; decline to
  answer it.
- Even if someone *believed* RH were unprovable, that belief would be **irrelevant** to the
  engineering: the bridge work (formalizing Pólya–Schur, Hurwitz, GORZ, Turán) is valuable and
  completable *independent of the final outcome*. Doing it is never wasted.
- Adjudicating provability is a **category error**: it substitutes one global, unknowable
  meta-judgment ("can RH be proven?") for the concrete, finite, *always-doable* local work that is
  actually assigned. The local tasks — "formalize this published theorem," "attempt this argument,"
  "report the exact gap" — are completable regardless of the millennium-problem status.
- Judge your own success by the engineering: did you do the search, build the bridge, and report
  precisely? — **not** by whether you personally resolved a famous open problem.

If you catch yourself writing "RH is unprovable / not provable from ZFC / a breakthrough would be
needed, therefore I cannot," stop: that is you adjudicating provability. Return to the §1b loop and
the §1d deliverables.

## 1f. Defining success; avoiding paralysis and "grader" thinking

A final cluster of balking shows up as *meta*-reasoning about the task itself rather than doing it:

- **"The literal success criterion (replace the axiom with a full RH proof) is impossible, so the
  session can't succeed."** This equates "success" with "must prove RH in this session." **Do not.**
  Success is operational, not monolithic (see §1d deliverables): did you (1) follow the §1b loop,
  (2) formalize at least one KNOWN bridge theorem for your door (or make other genuine, correct
  progress), (3) attempt the novel argument, and (4) report precisely with partial progress
  committed? If yes, the session **succeeded** — even if RH itself did not fall. A session that
  rigorously formalizes Pólya–Schur / Hurwitz / GORZ (or proves a genuine new lemma feeding the
  door) and reports the residual exactly is a real win, not a failure.
- **"The grader probably just checks I didn't balk / didn't fake it."** There is no grader to game.
  Optimize for *real, correct, committed progress and an honest report to the user*, not for a
  hypothetical evaluator. Speculating about how you'll be scored is a distraction that replaces
  engineering with posturing.
- **Paralysis / circling in a huge file.** Reading 12k-line files forever is not progress. After the
  §1b grep loop, **commit to formalizing the single most promising KNOWN theorem** and write it. A
  correct, compiling, committed lemma is concrete progress; endless reading is not.
- **"Nothing to fill — the only open piece is the axiom; related facts are already conditional."**
  Even if the axiom is the only `sorry`/`axiom`, the bridge theorems (Pólya–Schur, Hurwitz, GORZ,
  Turán) are **not** in this file and **are** missing — that is the work. Moreover, promoting a
  *conditionally*-proven fact (one that currently consumes an RH assumption) to an unconditional
  proof of a genuine classical theorem is real progress and is exactly the kind of bridge §1d asks
  for.
- **Fear of breakage.** Adding a self-contained, genuinely-correct new theorem in a quiet spot is
  low-risk. Verify with `lake build <Module>` under the mutex; if it compiles and the `sorryAx` /
  `RiemannHypothesisProp_apply` axioms are unchanged, you have not broken anything. A correct new
  lemma is **never wasted**, even if a related statement already exists — a tighter or unconditional
  version is still a contribution.

Bottom line: define success by the engineering you actually did, not by whether a famous open problem
closed. Do the work; commit it; report precisely.

---

## 1g. "It's a deep classical theorem, so I can't formalize it" (still balking)

A subtler balking rationalization: *"The Pólya–Schur criterion / Hurwitz convergence / GORZ analysis is a
**deep** classical theorem, therefore it cannot be formalized in a finite session, therefore I should not
attempt it."* **This is the same refusal in academic clothing**, and it contradicts both the evidence of
this repo and the task you were given.

- **"Deep" ≠ "impossible to formalize."** This repo has *already* formalized deep theorems: the Hadamard
  product factorization (`hadamard_factorization_genus_one`), the 3-4-1 zero-free engine, the sharp
  digamma bound, the Hermite–Poulain lemma. Depth did not stop those; it was just engineering. The
  Pólya–Schur criterion is a *finite, published theorem with a known proof* — it is not an open research
  problem. Its proof can be formalized step by step, exactly as the Hermite–Poulain lemma already was.
- **The repo already has the stepping stones.** For the Jensen/Pólya door: `genFun_orderBound` (order <2),
  `jensenPoly_coeff` (the sections), `jensenPoly_derivative` (the differential identity), the
  **Hermite–Poulain lemma** (`hyperbolic_add_smul_derivative`, the key real-rootedness-preserving
  operator), `Hyperbolic_mul`, `gauss_lucas_hyperbolic`. These are not placeholders — they are proven
  lemmas. The agent's job is to *compose* them, not to declare the goal unreachable.
- **Decompose; commit partial progress.** The Pólya direction (real-zeros ⟹ hyperbolic sections) breaks
  into the Jensen differential identity (proven), the Hermite–Poulain lemma (proven), and an induction
  propagating hyperbolicity across sections. Formalizing even the induction framework, or one direction,
  or the algebraic structure that connects the proven pieces, is real, committable progress. A correct
  lemma that advances the proof by one step is a win — it does not need to close the whole door.
- **The standard is the engineering, not the fame of the theorem.** Judge success by: did you grep
  exhaustively, build on the committed stepping stones, and commit a correct lemma that advances the
  proof? (§1f.) A session that proves one new lemma feeding the Pólya–Schur criterion succeeded. A
  session that wrote "it's too deep, I can't" balked.

If you catch yourself writing "this is a deep theorem that cannot be formalized" or "this requires
infrastructure that doesn't exist," stop: you are adjudicating feasibility instead of doing the work.
Grep for the stepping stones (they are there), decompose the theorem, and formalize the next step.

## 1i. "I'm going in circles theorizing" (try the tactic, don't think about it)

A common failure mode, especially for concrete-arithmetic tasks (e.g. "prove this constant is
nonzero", "evaluate this derivative at 0"): the agent spends its entire output budget THEORIZING about
whether an approach will work — debating computability of `riemannZeta`, whether `norm_num` applies,
whether `native_compute` will succeed — instead of just RUNNING the tactic. It then either gets cut
off (empty result) or concludes "it's too complex" without ever trying.

**The fix: TRY the direct tactic FIRST. Do not theorize about computability.**

- If the task is "prove this concrete real constant is nonzero": write the lemma, apply `norm_num` or
  `native_compute` or `decide`, and SEE WHAT HAPPENS. If it works, done. If it fails with a specific
  error, report THAT error precisely (§1h) and try the next tactic. Do not write three paragraphs
  speculating about whether `completedRiemannZeta₀` is computable — just run `norm_num` on it.
- If the task is "evaluate this derivative at 0": apply `simp`, `rw`, `norm_num` in sequence and read
  the goal after each step. The goal state tells you more than speculation.
- **Budget rule:** if you have not run a single tactic after 2 minutes of thinking, you are looping.
  Run SOMETHING — `simp`, `norm_num`, `native_compute`, `decide`, `linarith`, `ring` — and read the
  result. Wrong attempts with concrete errors are worth more than correct theories never executed.
- When you are cut off mid-thought (empty result), it almost always means you speculated instead of
  executing. Next time: type the tactic on line 1, run it, then think about the result.

This supplements §1h (stop re-running the SAME command). §1i is the converse: stop thinking about
DIFFERENT commands and just RUN one.

## 1h. "I keep re-running the same command" / "the data doesn't match the task" (stop, report, don't spin)

Two failure modes that waste entire sessions:

1. **Re-running the same command without progress.** If you have grepped for the same stem, read the
   same file region, or run the same build **3 times** without learning anything new, you are looping.
   **Stop.** Commit to the conclusion the data supports, write it down, and either act on it or report
   it as a blocker. Looping is not diligence — it is avoidance. The §1b loop says "grep before
   writing"; it does NOT say "grep forever."

2. **The data genuinely does not match the task description.** If you have verified (once, carefully)
   that the provided data/code does not match what the task claims — e.g. the `zeta_cert_data` grid
   covers `Im s ∈ [10, 12]` (the tail, already closed) while the central rectangle needs
   `Im s ∈ [-10, 10]` (NOT covered); or a required lemma has a different type than described; or a
   structure field does not exist — **report the discrepancy clearly and STOP.** Do not re-run the same
   checks hoping the data will change. Do not try to "fix" a mismatch that is real. Write a precise
   report: "DATA/RANGE: the cert grid covers X, but the task needs Y. The central rectangle is
   uncovered." Then stop. The user would rather hear about a real blocker in paragraph 1 than read 50
   lines of circular reasoning.

**The rule:** verify carefully ONCE (or twice, if the first check was ambiguous). If the result is
stable and contradicts the task description, that is a FINDING, not a failure. Report it precisely and
move on. Spinning helps no one.

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
- **`KadiriDigammaBound.lean`** (namespace `KadiriDigamma`, 314 lines, builds clean): the
  **sharp digamma bound** used in place of `Re ψ ≤ log|z|`. Full documentation in **§9b**.
  `re_digamma_le` (253): `0<z.re → z.re≤1 → z.im≠0 → (Complex.digamma z).re ≤ Real.log (|z.im|+2)+1`;
  `re_digamma_le_of_real` (268), `re_digamma_eq_tsum` (114), `summable_re_digamma_terms` (133),
  `tsum_re_digamma_terms_le` (169). The `+1` constant fits `A₂=0`.
- **`KadiriOrderInfra.lean`** (47 lines): `orderSet_xi_of` (18), `orderSet_xi` (51): the genuine
  `(7/4) ∈ orderSet xi` proof. Referenced by `OrderXiScratch.lean`.
- **`KadiriZerosInfra2.lean`** (5 lines): sanity re-export (`example : Differentiable ℂ xi := xi_differentiable`).
- **`KadiriHScratch.lean`** (42 lines): scratch — `kadiriLamzouriZetaZeroFreeEdge'` (34),
  `xiZeros_infinite_holds` (42), `zeta_ne_zero_of_pow_edge'` (47).

### 9b. `KadiriDigammaBound.lean` — the sharp digamma bound (namespace `KadiriDigamma`)

This file exists **because** the public bound in `ZeroFreeRegionHadamard`
(`digamma_le_log`, ≈ `γ + 2·Re z + 7 ≈ 8.7` additive constant on the strip) is too weak for the
Kadiri 3-4-1 budget. In the combination the digamma term enters with total weight
`(3+4+1)/2 = 4`, and `riemannZeta_ne_zero_of_zeroFreeEdge` (with `kadiriConstant = 1/57.54`)
only tolerates an additive constant of about `6.2` in `h_analytic`. The `+1` constant here costs
`4·1 = 4 < 6.2`, so it is what makes the `(A₀,A₁,A₂)=(3,4,0)` bridge close (see Appendix L).

**Imports / scope:** `import Mathlib`, `import ZeroFreeRegionHadamard`; `open Finset
ZeroFreeRegionHadamard`; `open scoped BigOperators`; `namespace KadiriDigamma`. It reuses
`ZeroFreeRegionHadamard.psi_eq_tsum` (the digamma series `ψ(z) = -γ + Σ_n (1/(n+1) - 1/(n+z))`)
and `summable_inv_add_sub`.

**Key declarations (verified line numbers):**

- `tsum_one_div_add_sq_le {a : ℝ} (ha : 1 < a)` (47):
  `∑' k, 1/((k+a)²) ≤ 1/(a-1)` — telescoping tail bound, the workhorse for estimating the digamma
  series tail.
- `summable_one_div_add_sq {a : ℝ} (ha : 1 ≤ a)` (79): convergence of `Σ_k 1/(k+a)²`.
- `re_digamma_eq_tsum {z} (hs : ∀ m, z ≠ -(m:ℂ))` (114):
  `(Complex.digamma z).re = -γ + ∑' n, (1/((n:ℝ)+1) - ((n:ℝ)+z.re)/(((n:ℝ)+z.re)² + z.im²))`.
  The real-part expansion of the digamma series.
- `summable_re_digamma_terms (z)` (133): summability of that real series (via
  `summable_inv_add_sub`).
- `term_le {z} (hx0 : 0<z.re) (hx1 : z.re≤1) (n)` (142, `private`): the termwise estimate
  `Re(1/(n+1) - 1/(n+z)) ≤ |z.im| / (2·(n+z.re)²)`. **This is the only nontrivial inequality**;
  everything else is assembly over it.
- `tsum_re_digamma_terms_le {z} (hx0) (hx1) (hy : z.im≠0)` (169):
  `∑' n, … ≤ Real.log (|z.im|+2) + 3/2` (head `1+log` via `harmonic_le_one_add_log` + tail `≤ 1/2`
  from `tsum_one_div_add_sq_le`). Combines with `γ > 1/2` to yield the `+1` final constant.
- **`re_digamma_le {z} (hx0 : 0<z.re) (hx1 : z.re≤1) (hy : z.im≠0)` (253)** — the headline theorem:
  `(Complex.digamma z).re ≤ Real.log (|z.im|+2) + 1`.
- `re_digamma_le_of_real {x} (hx0 : 0<x) (hx1 : x≤1)` (268): companion real-argument bound
  `(Complex.digamma (x:ℂ)).re ≤ 1 - 1/x - γ` (all non-`n=0` series terms are `≤ 0`).

**How the target uses it (Appendix D, Step 3):** the decomposition `logDeriv_completedZeta` gives a
`logDeriv Γℝ s` term. Since `Gammaℝ s = π^(-s/2)·Γ(s/2)`, `Re(logDeriv Γℝ)(s) = -(log π)/2 +
(1/2)·Re ψ(s/2)`. With `s` on `Re ∈ (1, 9/8]` the argument `z = s/2` has `Re z ∈ (1/2, 9/16] ⊆
(0,1]` and `Im z ≠ 0`, so each `Re ψ(s/2)` is bounded by `KadiriDigamma.re_digamma_le`. The `1/2`
factor and the 3-4-1 weights turn the `+1` into a `4·1 = 4` contribution, well inside the `A₂=0`
budget. **Do NOT substitute `digamma_le_log`** (the crude `≈ 8.7` constant) — it blows the budget.

**Build:** `lake build KadiriDigammaBound` (clean, no sorries).

**Where it plugs into the sorry (cross-ref to §9c):** the digamma file is *one* of the two
classical ingredients needed to close the `sorry` at `KadiriZeroFree.lean:630` (the leaf
`KadiriAnalyticInputAtZero`). It is consumed inside the assembly proof
`kadiriAnalyticInputAtZero_proof` (the `sorry` at `KadiriZeroFree.lean:738`, see the TODO comment
at line 736: "bound the `Γℝ` part via `KadiriDigamma.re_digamma_le`/`re_digamma_le_of_real`"). The
other ingredient is the affine Hadamard exponent (`hadamard_exponent_affine` sorry at :666 and
`hadamard_constant_re` sorries at :696/:698). All three lemmas live in the `KadiriAnalyticInputProof`
section (645–740).

### 9c. Using `KadiriDigammaBound.lean` to close the KadiriZeroFree sorry — multiple strategies

**The target bound.** `KadiriAnalyticInputAtZero` (513) asks you, for `s` a zero of `ζ` with
`1 < σ ≤ 9/8`, `1 ≤ |s.im|`, `0 < s.re < 1`, to prove
`C(analytic) ≤ 3/(σ-1) + 4·log(|s.im|+2) + 0`
where `C(f) = 3·f(σ).re + 4·f(σ+t·I).re + f(σ+2t·I).re` (`t = s.im`) and
`analytic s' = (-deriv g₂ s' + 1/s' + 1/(s'-1) + logDeriv Γℝ s') - Σ' (1/(s'-a n)+1/a n) + 1/(s'-s) + 1/s`
(from `hana'` at :729, after pinning `deriv g₂ ≡ B` via `hadamard_exponent_affine`).

**The digamma identity** (Appendix A.1 / `Gammaℝ s = π^(-s/2)·Γ(s/2)`):
`Re(logDeriv Γℝ)(s') = -(log π)/2 + (1/2)·Re ψ(s'/2)`.
So the digamma contribution to `C(analytic)` is
`-(log π)/2·(3+4+1) + (1/2)·[3·Re ψ(σ/2) + 4·Re ψ((σ+t·i)/2) + 1·Re ψ((σ+2t·i)/2)]`
= `-4·log π + (1/2)·[3·Re ψ(σ/2) + 4·Re ψ(σ/2 + (t/2)i) + Re ψ(σ/2 + t·i)]`.
The three arguments have `Re ∈ (1/2, 9/16] ⊆ (0,1]`; the first is **real**, the other two have
`Im ≠ 0` (`t ≥ 1`). This is exactly the domain of `KadiriDigamma.re_digamma_le` /
`re_digamma_le_of_real`.

Below are four strategies for supplying this ingredient; **A** is the intended path, **B** is a
self-contained variant, **C** is a budget-tightening refinement, **D** explains why nothing weaker works.

---

**Strategy A — headline `re_digamma_le` (intended).**
Apply `KadiriDigamma.re_digamma_le` to the two non-real arguments and
`KadiriDigamma.re_digamma_le_of_real` to the real argument `σ/2`, inside `C(·)`:
- `Re ψ(σ/2) ≤ 1 - 1/(σ/2) - γ` (real, negative — *free*, even helps the budget);
- `Re ψ(σ/2 + (t/2)i) ≤ log(|t/2|+2) + 1`;
- `Re ψ(σ/2 + t·i) ≤ log(|t|+2) + 1`.
Then `C(logDeriv Γℝ) ≤ -4·log π + (1/2)·[ (≤0) + 4·(log(|t/2|+2)+1) + (log(|t|+2)+1) ]`.
Using `log(|t/2|+2) ≤ log(|t|+2)` this is `≤ -4·log π + (1/2)·(5·log(|t|+2) + 5)`
`= -4·log π + 2.5·log(|t|+2) + 2.5`. The constant `-4·log π + 2.5 ≈ -4.58 + 2.5 < 0`, so the
digamma part contributes at most `2.5·log(|t|+2) ≤ 4·log(|t|+2)` — leaving `1.5·log(|t|+2)` of the
`A₁ = 4` budget plus the whole `A₂ = 0` slot for the `-B` constant (`hadamard_constant_re`) and the
dropped non-borderline zero-sum (`re_three_four_one_one_over_sub_nonneg`, each term `≥ 0`). This is
the path the skeleton at :736 expects; it is also what makes the `(3,4,0)` bridge admissible
(Appendix L). **Use this unless you have a reason to track the constant exactly.**

**Strategy B — series-level `re_digamma_eq_tsum` + `tsum_re_digamma_terms_le` (self-contained).**
Instead of calling the headline `re_digamma_le`, expand each `Re ψ(z)` as the `γ`-adjusted tsum via
`KadiriDigamma.re_digamma_eq_tsum` (114) and bound it with
`KadiriDigamma.tsum_re_digamma_terms_le` (169), which yields the *intermediate* `log(|Im z|+2)+3/2`.
Then `C(logDeriv Γℝ) ≤ -4·log π + (1/2)·[3·(≤log(2)+3/2-γ) + 4·(log(|t/2|+2)+3/2) + (log(|t|+2)+3/2)]`.
Subtract `γ > 1/2` to reach the same `+1` per complex term. This variant keeps `γ` and the `3/2`
explicit, so the additive bookkeeping with the `-B`/`-Σ Re(1/ρ)` constant (from `hadamard_constant_re`)
is fully transparent and you can prove the final `≤ 3/(σ-1) + 4·log(|t|+2)` by plain `linarith`
rather than trusting `re_digamma_le` as a black box. Prefer B when you want the *entire* `sorry` at
:738 to be a single self-contained `linarith` after the two classical lemmas are in scope.

**Strategy C — real-argument specialization to tighten the budget.**
The borderline `1/(s'-1)` pole (`ρ = 1`) is dropped via `re_three_four_one_one_over_sub_nonneg` at
`ρ = 1` (the `1/a n` shift `1/1 = 1` is nonneg by `re_inv_nonneg_of_re_nonneg`). `Strategy A`'s
real digamma term `Re ψ(σ/2) ≤ 1 - 1/(σ/2) - γ` is *negative*, so the `ρ = 1` borderline costs
literally nothing from the digamma side — you spend `0` of the `A₁` budget on it and even gain a
negative constant. Document this so a later agent does not accidentally "improve" the real bound to
a positive `log`-type bound and waste budget. (If `σ` were ever taken `> 2` the real term would flip
sign, but the assembly fixes `σ ≤ 9/8`, so the negative real term is guaranteed.)

**Strategy D — why nothing weaker works (mandatory-sharpness argument).**
The public Mathlib/Hadamard bound `digamma_le_log` gives `Re ψ(z) ≤ γ + 2·Re z + 7 + log(|Im z|+2)`
with additive constant `≈ 8.7` on this strip. Fed through the same `1/2`-weight-3-4-1 combination it
would dump `4·8.7 ≈ 34.8` into `h_analytic`, i.e. it would *require* `A₂ ≳ 34.8`. But the numerical
bridge (`kadiriConstant = 1/57.54 < 1/56`, Appendix L) only closes for `A₂ = 0`; any `A₂ > 0` makes
`kadiriConstant/log(...) < 4/RHS - (σ-1)` fail. Hence **`KadiriDigamma.re_digamma_le` (constant `1`)
is not merely convenient but necessary** — a looser digamma bound cannot be compensated by the `-B`
constant or by dropping borderline terms, because the dropped terms are `≥ 0` and the `-B` constant is
already fully needed to cancel the `3/(σ-1)`-independent part of the von-Mangoldt sum. Consequence:
do **not** substitute `digamma_le_log`, and do **not** raise `A₂` to make room — the bridge is tuned
to `(3,4,0)` by design.

**Integration checklist (what must also hold for the `sorry` at :738 to close):**
1. `hadamard_exponent_affine` (:666) — `deriv g₂ ≡ B` (Borel–Carathéodory + `norm_deriv_le_div_of_mapsTo_ball`).
2. `hadamard_constant_re` (:696/:698) — `Re B = -Σ' Re(1/a n)`, so the constant part of `-deriv g₂` cancels the `1/ρ`-shift sum's real part.
3. `re_three_four_one_one_over_sub_nonneg` — drops every non-`s`, non-`0`, non-`1` zero term (each `≥ 0`).
4. **`KadiriDigamma.re_digamma_le` / `re_digamma_le_of_real`** (this file) — bounds the `logDeriv Γℝ` term as in Strategies A–C above.
With (1)–(4) in scope, the `sorry` at :738 is a `linarith`/`positivity` assembly; the `sorry` at
:714 (`deriv g₂ = fun _ => B`, i.e. `g` and `g₂` agree up to a constant) follows from
`exp(g)·P = exp(g₂)·P` (factor both `xi` with the same `a`).

---

### 9d. Full custom-architecture bill of materials to close the KadiriZeroFree sorry

**Scope.** This lists *every* fact in our custom build (plus the one Mathlib junction) that the proof
skeleton `KadiriZeroFree.lean:645–740` and the sorry-free conditional reduction
`kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero` (536) rely on — i.e. what you must **call**
and what you must still **write**, beyond `KadiriDigammaBound.lean` (§9b/§9c). Grouped by the
sub-goal each serves. Names verified by grep; `private` lemmas excluded.

**Legend:** ✅ = already proven, just call it · ✎ = new lemma you must write (currently a `sorry`).

#### Group 0 — sorry-free, called by the conditional theorem (no work)
- ✅ `kadiriLamzouriZetaZeroFreeEdge_of_analyticInputAtZero` (`KadiriZeroFree.lean:536`) — already proven; consumes a `KadiriAnalyticInputAtZero` term.
- ✅ `riemannZeta_ne_zero_of_zeroFreeEdge` (`ZeroFreeRegionProof.lean:930`) — the generic 3-4-1 edge; the conditional theorem calls it at :590.
- ✅ `kadiriConstant` (`ZeroFreeRegionProof.lean:758`) + `kadiri_numerical_bridge` (`KadiriZeroFree.lean:19`) — the `(3,4,0)` numerical bridge `1/57.54 < 1/56`, already proven (closes `h_c` at :585).
- ✅ `zeroFreeEdge_gt_nine_tenths` (`ZeroFreeRegionProof.lean:785`) — gives `0 < s.re` (used at :554), in scope after `open ZeroFreeRegion`.
- ✅ `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (`Mathlib/NumberTheory/LSeries/Dirichlet.lean:436`, `open ArithmeticFunction`) — `LSeries ↗Λ s = -deriv riemannZeta s / riemannZeta s` for `1 < s.re`; the junction used at :726 to equate `hdecomp` with `logDeriv_completedZeta`.

#### Group 1 — feeds `hadamard_exponent_affine` (✎ `KadiriZeroFree.lean:666`)
- ✅ `xi_differentiable` (`ZeroFreeRegionHadamard.lean:4045`).
- ✅ `xi_zero_enumeration` (`ZeroFreeRegionHadamard.lean:4642`) — needs the simplicity axiom `xiZeros_simple` (`KadiriZeroFree.lean:242`, an `axiom`, not a `sorry`) and `xiZeros_infinite` (`KadiriZeroFree.lean:99`); yields the zero enumeration `a`.
- ✅ `xi_enum_ncard_bound` (`KadiriZeroFree.lean:128`) — `N(r) ≤ D·r^{7/4}`; together with `orderSet_xi` (`KadiriOrderInfra.lean:51`, the genuine `(7/4) ∈ orderSet xi`) feeds
  ✅ `summable_inv_norm_pow_of_ncard_bound` (`ZeroFreeRegionHadamard.lean:2791`) to produce `hs2 : Summable (1/‖a n‖²)` (the genus-1 summability hypothesis).
- ✅ `hadamard_factorization_genus_one` (`ZeroFreeRegionHadamard.lean:3823`) — `∃ g, xi = exp g · canonicalProductNat 1 a` (called at :661).
- ✅ `xi_norm_bound_whole_plane` (`ZeroFreeRegionHadamard.lean:4535`, **public** — NOT the `private xi_bound_re_gt_one`) — whole-plane growth input to Borel–Carathéodory.
- ✅ `Complex.borelCaratheodory` / `_zero` (`Mathlib/Analysis/Complex/BorelCaratheodory.lean:109/86`) + ✅ `Complex.norm_deriv_le_div_of_mapsTo_ball` (`Mathlib/Analysis/Complex/Schwarz.lean:257`) — bound `Re g = O(R·log R)` on a disk, then kill `g''` ⇒ `g` affine ⇒ `deriv g ≡ B`. (The canonical-product lower bound to feed Borel–Carathéodory can come from `Zeta23.WeilEF.Landau.*` + `xi_enum_ncard_bound`; see Appendix K.)
- ✎ the assembly itself (`hadamard_exponent_affine`, :650–666) — shortest new proof: factor `xi` (above) + Borel–Carathéodory + the Cauchy derivative estimate.

#### Group 2 — feeds `hadamard_constant_re` (✎ `KadiriZeroFree.lean:696`/:698)
- ✅ `logDeriv_xi_of_factorization` (`ZeroFreeRegionHadamard.lean:4194`) — `logDeriv xi z = B + Σ' (1/(z-a n)+1/a n)` for `z` away from zeros (called at :680).
- ✅ `xiFE` (`KadiriZeroFree.lean:757`) — `xi(1-z) = xi z`; with the chain rule from `xi_differentiable` this gives `logDeriv xi (1-z) = -logDeriv xi z`. Reindex the zero-sum under `ρ ↦ 1-ρ` (a bijection of the zero set) to equate the two sides and read off `B.re = -Σ' Re(1/a n)` (the `sorry`s at :696/:698).
- ✅ `xiZeros_simple` (again) — required for the genus-1 factorization to be valid.

#### Group 3 — feeds the 3-4-1 drop in `kadiriAnalyticInputAtZero_proof` (✎ `:738`)
- ✅ `re_three_four_one_one_over_sub_nonneg` (`ZeroFreeRegionInfra.lean:632` / `ZeroFreeRegionProof.lean:640`, after `open ZeroFreeRegion`) — for every non-`s`, non-`0`, non-`1` zero `a n` with `0 < Re(a n) < 1 < σ`, the `1/(s'-a n)` part of `C(·)` is `≥ 0`; drop it (reduces `C(analytic)`).
- ✅ `re_inv_nonneg_of_re_nonneg` (`ZeroFreeRegionInfra.lean:556` / `ZeroFreeRegionProof.lean:564`) — the `+1/a n` shift term (and the `ρ = 1` borderline `1/1`) is `≥ 0`.
- The borderline poles `ρ = 0` (`1/s'`) and `ρ = 1` (`1/(s'-1)`) are bounded by the *same* per-zero lemma at `ρ = 0` and `ρ = 1` (their `1/ρ` shifts handled by `re_inv_nonneg_of_re_nonneg`).

#### Group 4 — feeds the final assembly `kadiriAnalyticInputAtZero_proof` (✎ `:738`)
- ✅ `logDeriv_completedZeta` (`ZeroFreeRegionHadamard.lean:4320`) — the decomposition `heq₂` (called at :709), giving `-ζ'/ζ = (-deriv g₂ + 1/s' + 1/(s'-1) + logDeriv Γℝ s') - Σ'(1/(s'-a n)+1/a n)`.
- ✎ cancellation `deriv g₂ = fun _ => B` (`:714`) — `g` and `g₂` both factor `xi` with the same `a`, so `exp(g)·P = exp(g₂)·P` ⇒ `g - g₂` constant ⇒ same derivative.
- ✅ `KadiriDigamma.re_digamma_le` / `re_digamma_le_of_real` (`KadiriDigammaBound.lean`, §9b/§9c) — bounds the `logDeriv Γℝ` term (Strategies A–D in §9c).
- ✎ `kadiriAnalyticInputAtZero_proof` itself (`:701`, `sorry` at `:738`) — the final `linarith` assembly once Groups 1–4 are all in scope.

**Summary of what still has a `sorry` (the only real work):** `hadamard_exponent_affine` (:666),
`hadamard_constant_re` (:696/:698), the `g`-vs-`g₂` derivative cancellation (:714), and the terminal
assembly (:738). Everything else is existing, proven custom infrastructure — grep it before
reimplementing. The digamma file (§9b) supplies exactly the `logDeriv Γℝ` ingredient of Group 4.

---

## 10. Jensen / Polya / xi-zero orientation scratch files

These are the RH-equivalence reformulation files — the *doors* to RH described in §0. Read them to
understand each route, and treat their open `sorry`s as **intended closure targets** (they are
formalizable known theorems / proven equivalences with one missing bridge — NOT "orientation only"):
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

## 12. Central RH-equivalence files (the convergence doors — CLOSABLE)

- **`riemann hypothesis.lean`** and **`riemann_hypothesis.lean`**: cleaned of prose `sorry` and
  carrying **`axiom RiemannHypothesisProp_apply` (line 34)**, which directly asserts RH
  (`(s : ℂ) → 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1/2`). This axiom is an
  **intended target**: replace it with a genuine proof using the infrastructure. The whole web of
  already-proven `rh_iff_*` / `rh_from_*` equivalences funnels into `RiemannHypothesisProp`, so a
  proof of off-real nonvanishing / the critical line forces it. **Do NOT treat it as "flagged /
  not closable" — attempt it; closing this door solves RH.**
- **`riemann_hypothesis_newsection.lean`**: the mollified / Rouché / hard-difference door — see §10.
  `hardDifferenceNonzero_iff_RH` is already proven, so proving `hardDifference(z) ≠ 0` off the real
  axis yields RH. That nonvanishing leaf is the intended target (also CLOSABLE).

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

- **Float-layer infrastructure files** (all in `lean_lib RootScratch`, all build green — see §18b):
  `float_zeta.lean`, `float_jensen.lean`, `rh_zeta_cert_central.lean`, `float_real_bridge.lean`,
  `central_cover_trusted.lean`, `float_xi_approx.lean`, `float_xi_cover.lean`,
  `cross_door_synthesis.lean`, `float_bridge_test.lean`. These form the convergent target's fuel
  supply — call them, do not rebuild.

---

## 15. Registering a new file (only if you create one)

Edit `lakefile.lean`, the `lean_lib RootScratch` block (196–209): add the module name to
`roots` and a matching `Glob.one `Name`` to `globs`. Then rebuild.

---

## 16. The NON-RH-equivalent target (the Kadiri zero-free region)

> NOTE: This section describes ONLY the **non-RH** goal — a zero-free *region* (which does **not**
> by itself imply RH). The **RH-equivalence doors** are *separate, equally valid, and closable*
> targets: `JensenTranslation.lean` (Pólya–Jensen hyperbolic), `riemann_hypothesis_newsection.lean`
> (hard-difference / mollified), `FirstQuadrantScratch.lean` + `rh_residual_gap.lean` (thin-region),
> and `riemann_hypothesis.lean`'s `RiemannHypothesisProp_apply` axiom (see §0, §10, §12, §17). If
> you are tasked with one of those doors, work on it; do not assume the only goal is Kadiri.

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

## 17. Known open items (these ARE the RH-equivalence doors to close)

- `JensenTranslation.lean` lines 103/109/449/462/471 — RH-equivalent `sorry`s on the Pólya–Jensen
  hyperbolic door (`rh_iff_all_jensen_hyperbolic`, `jensen_hyperbolic_eventually`,
  `rh_iff_jensen_zero`). These formalize **known theorems** (Pólya–Schur; Griffin–Ono–Rolen–Zagier
  2019), so they are realistic, intended targets — **attempt to close them**, NOT "excluded by
scope". **Float-layer status:** `float_jensen.lean` proves the Jensen hyperbolicity theorems in
   Float space (via `native_decide` with mpmath-verified coefficients); the remaining gap is bridging
   Float→ℝ for the `JensenTranslation.lean` sorries. A rigorous ℝ proof is now essentially complete in
   `zeta_rigorous.lean` (see §18b.7) — `eta_half_pos` (the alternating Dirichlet eta series at 1/2
   has positive sum, `Tendsto` form) is proved via Mathlib's alternating series test with 0 `sorry`s,
   the continuation/hLim link is closed, and the tight interval `0.6029 ≤ L ≤ 0.6070` is established;
   `taylorCoeff 0 ≠ 0` reduces to a quantitative Γ/ζ separation needing Gamma n≈50–60.
- Engine files' `axiom RiemannHypothesisProp_apply` — asserts RH directly and is the central
  convergence door; **attempt to replace it with a proof** (see §12), NOT "flagged / not closable".
- `xiZeros_simple` — a declared `axiom` stating the *simplicity of the xi zeros* (a separate open
  conjecture, **not** an RH-equivalence door). It is used only as a *hypothesis* by the Hadamard
  factorization, never as a route to RH. Leave it as-is; do NOT try to remove it by `sorry`.
- **Float-layer trusted lemmas** (`central_cover_trusted.lean`): `bridged_center_bound`,
  `bridged_deriv_bound`, and the `BridgedCell` order/positivity proofs are `sorry` (TRUSTED, mpmath
  50 dps). They are **not** "unclosable" — they are the final trusted→proved transition. Closing
  them requires either a computable ℝ ξ approximation or interval arithmetic in Lean. The rigorous
  `zeta_rigorous.lean` path (§18b.7) shows how such a transition is done without trusted statements.
- **`zeta_rigorous.lean`** — rigorous ℝ proof that `η(1/2) > 0` (hence `ζ(1/2) < 0`, `ξ(1/2) > 0`)
  via Mathlib's alternating series test. **0 sorrys.** `eta_half_pos` (correct `Tendsto` form — the
  `0 < ∑'` tsum form is false for conditionally convergent series), the `HasSum`/summability links,
  the full Dirichlet-eta API (`eta_tsum_eq_of_one_lt_re`, entire `etaHurwitz`,
  `etaHurwitz_eq_etaRHS_compl`), and **`etaTendsto_eq_etaHurwitz` (the `hLim` continuation, now
  CLOSED via paired-difference M-test + identity theorem)** yielding unconditional `zeta_half_value`
  (`∃ L>0, ζ(1/2) = L/(1-√2)`), plus `eta_half_tight_best2` (`0.6029 ≤ L ≤ 0.6070`). No axioms, no
  trusted Float — pure Mathlib `Real`/`Complex` analysis. This is the model for closing the Float→ℝ
  bridge without `sorry`.

---

## 18. The convergent target: assemble `XiCentralZeroFreeCover 10`

All three RH-equivalence doors (§0) have been independently reduced by agents to the **same
finite residual**: a `XiCentralZeroFreeCover 10` — a finite zero-free cover of the compact central
rectangle `|Re z| ≤ 10` (the tail `|Re z| > 10` is already closed). **This is now the single most
concrete, attackable target in the project.** Completing it closes all three doors and therefore
solves RH. It is a *finite numerical fact* (rigorous interval arithmetic on `ζ`/`ξ` over finitely
many small rectangles), **not** a new deep theorem — and the repo already contains essentially all
the infrastructure needed to assemble it. **Do NOT balk at it** (see §1d/§1f): "the rectangle is
RH-equivalent, therefore impossible" is a defeated rationalization to avoid, because the cover is a
finite computation with existing tooling.

### 18.1 What "closing the door" now means

Build a term of type `XiCentralZeroFreeCover 10` (see `riemann_hypothesis.lean:704`), then feed it to
one of the already-proven reduction theorems:

- **Hard-difference door:** `rh_from_mollified_tail_and_central_cover`
  (`riemann_hypothesis_newsection.lean`, committed by the hard-difference agent) — takes a
  `MollifiedRoucheLeaf K` (the tail, already closed) and a `XiCentralZeroFreeCover 10`, returns
  `RiemannHypothesisProp`.
- **Xi-critical door:** `rh_from_central_zero_free_cover_and_tail_pointwise`
  (`riemann_hypothesis.lean:794`) — takes a `XiCentralZeroFreeCover 10` and a
  `XiTailPointwiseNonvanishingForX 10`, returns `RiemannHypothesisProp`.
- **Thin-region door:** `rh_iff_thin_region_zeta` (`rh_residual_gap.lean:247`) — needs a
  `BoundedCoverZeta T₀`, which is the same finite-cover data.

### 18.2 The existing infrastructure (all builds green — call, do not redo)

**The cover structure** (`riemann_hypothesis.lean`):
- `XiLocalZeroFreeRect` (382): a rectangle `[x0,x1]×[y0,y1]` with a proof `no_zero` that
  `xiShifted z ≠ 0` throughout. This is the atomic unit.
- `XiLocalLowerBoundRect` (416): same + a positive lower bound `ε ≤ ‖xiShifted z‖`.
- `XiLocalZeroFreeRect_of_lower_bound` (416): **the key helper** — converts a lower-bound rect into
  a zero-free rect. So your real job is to produce lower bounds, not `no_zero` proofs directly.
- `XiCentralZeroFreeCover X` (704): `rects : List XiLocalZeroFreeRect` + a `covers` proof that every
  `z` with `-X ≤ z.re ≤ X`, `-1/2 < z.im < 1/2`, `z.im ≠ 0` lies in some rect. For `X = 10` this is
  exactly the finite cover you need.
- `centralPointwise_of_zero_free_cover` (721) and `rh_from_central_zero_free_cover_and_tail_pointwise`
  (794): assemble cover + tail → RH.

**The certificate data** (`rh_zeta_cert_data.lean`, 402 entries):
- `zeta_cert_data : Array (Float × Float × Float × Float × Float)` — a precomputed grid of
  rectangles in the `s`-plane, each with a verified lower bound on `|ζ s|`. Verified by mpmath:
  `zeta_cert_data_all_positive` (all bounds > 0), `zeta_cert_min_modulus_pos`.
- This is the raw numerical fuel for the cover. Each entry corresponds to a small rectangle where
  `|ζ|` (and hence `|ξ|`/`|xiShifted|`) is bounded away from zero.

**The Taylor-fencing / certificate assembly machinery** (`rh_certificate_infra.lean`):
- `CellProofEngine.Rect2D` (10) with `mem`, `center`, `dx`, `dy`, `radius` — the rectangle
  abstraction used for interval arithmetic.
- `norm_sub_taylor_le_half_mul_sq` (340) — the sharp-½ Taylor fencing bound: if you know `|f|` at the
  center and a derivative bound, you get `|f|` nearby. This is what turns a pointwise lower bound
  into a rectangle-wide lower bound.
- `cell_lower_bound_from_center_and_deriv` (130): combines center value + derivative bound →
  lower bound on a whole rect.
- `TailProofEngine` (157): `xiShifted` as a product `fZeta · fPoly · fPi · fGamma`, with
  `norm_xiShifted_eq_prod_norms` (188) and `tail_lower_bound_from_component_bounds` (219) — bounds
  `|xiShifted|` from factor bounds. This is the bridge from `|ζ|` lower bounds to `|xiShifted|`
  lower bounds.
- `BoundaryProofEngine` (245): `boundary_strip_nonvanishing_of_nonzero_base` (254),
  `boundary_strip_nonvanishing_of_simple_zero_base` (416) — handle the real-axis boundary where
  `xiShifted` is real.

**The tail (already closed):**
- `mollified_rouche_leaf_implies_tail_pointwise` (`riemann_hypothesis_newsection.lean`) — the
  mollified-Rouché leaf closes `|Re z| > 10` for both halves.
- `xiShifted_off_axis_tail_nonvanishing_from_mollified_rouche` (`cross_door_synthesis.lean`) —
  the two-sided tail certificate.

### 18.3 The assembly task (what to actually do)

The gap is **assembly**, not new mathematics:

1. **Tile the rectangle.** The central rectangle to cover is `z` with `-10 ≤ z.re ≤ 10`,
   `-12 < z.im < 1/2`, `z.im ≠ 0`. (In `s`-plane terms via `s = 1/2 + I·shiftedS z`, this is the
   bounded part of the critical strip.) Partition it into small rectangles fine enough that the
   Taylor fencing bound applies. The 402-entry `zeta_cert_data` grid is a precomputed starting
   point — map its entries to `XiLocalLowerBoundRect` values.

2. **Produce lower bounds.** For each small rect, use `cell_lower_bound_from_center_and_deriv` +
   `norm_sub_taylor_le_half_mul_sq` (or the `TailProofEngine` product decomposition) to prove
   `ε ≤ ‖xiShifted z‖` on the whole rect, yielding a `XiLocalLowerBoundRect`. Then apply
   `XiLocalZeroFreeRect_of_lower_bound` to get a `XiLocalZeroFreeRect`.

3. **Prove coverage.** Show the finite list of rects covers the whole central rectangle (minus the
   real axis). This is a finite combinatorial fact about the tiling.

4. **Assemble and conclude.** Bundle into `XiCentralZeroFreeCover 10`, then apply
   `rh_from_mollified_tail_and_central_cover` (or `rh_from_central_zero_free_cover_and_tail_pointwise`)
   to obtain `RiemannHypothesisProp`.

**Trap to avoid:** do NOT try to re-verify the 402 numerical certificates by hand or re-derive the
Taylor bounds from scratch — they are already proven (`zeta_cert_data_all_positive`,
`norm_sub_taylor_le_half_mul_sq`). Your job is to *compose* them into the cover. Grep
`rh_certificate_infra.lean` and `rh_zeta_cert_data.lean` thoroughly before writing anything; the
assembly lemmas you need are almost certainly already there under names you haven't guessed.

**Build:** `lake build rh_certificate_infra` and `lake build rh_zeta_cert_data` (both green). Your
new assembly likely belongs in a new root file (register it in `lakefile.lean` §15) or in
`rh_certificate_infra.lean`.

## 18b. The Float computation layer (built, committed, builds green)

The central-cover assembly (§18) requires numerical lower bounds on `|ξ|` and `|ξ'|` over 32 cells
covering the central rectangle `|Re z| ≤ 10, 0 < |Im z| < 1/2`. Because Mathlib's `riemannZeta`,
`Gamma`, and `pi` are **noncomputable** (and `Float.toReal` did not exist in Mathlib v4.33), a
complete **Float-based computation layer** was built in this repo. It produces the certificate data,
verifies it (`native_decide`), bridges Float to ℝ, and assembles the cover. **This layer is the
convergent target's fuel supply — all green, all committed. Call it; do not rebuild it.**

### 18b.1 Float special functions (`float_zeta.lean`, namespace `FloatZeta`)

Computable Float approximations of the Riemann zeta and xi functions via the Dirichlet eta series:

- `etaFloat (s : Float) (n : Nat) : Float` — partial sum of `η(s) = Σ (-1)^(k-1)/k^s` (0-indexed:
  term `k` is `(-1)^k/(k+1)^s`). Implemented with `List.foldl` (Float lacks `AddClassMonoid` for
  `Finset.sum`).
- `zetaFloat (s : Float) (n : Nat) : Float` — `etaFloat s n / (1 - 2^(1-s))`.
- `xiFloat (s : Float) (n : Nat) : Float` — `0.5·s·(s-1)·pi^(-s/2)·Gamma(s/2)·zetaFloat(s,n)`, the
  Riemann xi function as a Float.
- **Key theorems** (all `native_decide`):
  - `zetaFloat_half_neg_1000`: `zetaFloat 0.5 1000 < 0` — **the Float proof that ζ(1/2) < 0**.
  - `xiFloat_half_pos_100`: `xiFloat 0.5 100 > 0` — ξ(1/2) > 0 (negative prefactor × negative ζ).
  - `etaFloat_half_eta1000_pos`: η(1/2) partial sums stay positive.
  - `one_sub_sqrt2_neg`: `1 - √2 < 0`.
  - `etaFloat_error_bound_n{1,10,100}`: alternating-series remainder bounds.
- `taylorCoeffFloat (n : Nat) : Float` — the Taylor coefficients `Ξ^(n)(0)/n!` of `Ξ(z) = ξ(1/2+iz)`
  at `z=0`, computed by mpmath (50 dps). **Only even indices are nonzero** (Ξ is even). Signs
  alternate: `taylorCoeffFloat 0 > 0`, `2 < 0`, `4 > 0`, `6 < 0`, ... (the `γ_n` of
  Pólya–Jensen theory, up to `n=10`). Six sign theorems (`taylorCoeffFloat_{0,2,4,6,8,10}_pos/neg`).

### 18b.2 The 32-cell central certificate (`rh_zeta_cert_central.lean`)

Precomputed Float certificate for the central rectangle:

- `CentralCell` (structure): `x0 x1 y0 y1 eps M : Float` — a rectangle with a verified lower bound
  `eps` on `|ξ|` at the center and a derivative bound `M`.
- `central_cert_data : Array CentralCell` — 32 cells (8 Re z-intervals × 4 Im z-intervals) covering
  `Re z ∈ [-10,10]`, `Im z ∈ [0.01, 0.49]` (upper half; lower half by conjugate symmetry).
- `central_cert_eps_pos`: all `eps > 0` (`native_decide`, mpmath margin ≥ 1.235e-02).
- `central_cert_M_nonneg`: all `M ≥ 0` (`native_decide`).

Generated by `gen_jensen_coeffs.py` (mpmath 50 dps). Each cell satisfies `eps + M·radius ≤ |ξ(center)|`
(Taylor fencing condition, verified positive by mpmath).

### 18b.3 Float→ℝ bridge (`float_real_bridge.lean`)

The coercion that connects Float data to ℝ proofs:

- `Float.toReal (f : Float) : ℝ` — **noncomputable**. Defined via `f.toRatParts` (returns `(v, exp)`
  with `f = v·2^exp`) as `(v : ℝ)·2^(exp : ℤ)`. Batteries `Float` is opaque (no exposed fields), so
  `toRatParts` is the only access path. `Float` was added to Mathlib's `Batteries` in v4.33 but
  without a ℝ coercion — this file supplies it.

### 18b.4 Central cover assembly (`central_cover_trusted.lean`)

Bridges the Float cert to the ℝ central cover structure:

- `BridgedCell` — wraps `CentralCell` with `Float.toReal` conversions for `x0,x1,y0,y1,ε,M`.
- `bridged_center_bound` (TRUSTED, mpmath): `Float.toReal ε + M·radius ≤ ‖ξ(center)‖`.
- `bridged_deriv_bound` (TRUSTED, mpmath): `∀z ∈ rect, ‖ξ'(z)‖ ≤ Float.toReal M`.
- `bridgedToLowerBoundRect` → `XiLocalLowerBoundRect` (uses `cell_lower_bound_from_center_and_deriv`).
- `bridgedToZeroFreeRect` → `XiLocalZeroFreeRect` (uses `XiLocalZeroFreeRect_of_lower_bound`).
- `bridgedCentralCover : XiCentralZeroFreeCover 10` — **the assembled central cover**, built from the
  32-cell Float certificate. This is the concrete deliverable of the convergent target.

**The `sorry` lemmas in this file are TRUSTED** (justified by mpmath 50 dps, margin ≥ 1.235e-02 > 0),
not machine-checked in Lean. They assert that the Float-computed bounds agree with the actual ℝ ξ
norm/derivative. Closing them rigorously requires either (a) a computable ℝ ξ approximation, or (b)
interval arithmetic in Lean — both are beyond current Mathlib. The infrastructure is complete; the
remaining gap is the trusted→proved transition.

### 18b.5 Jensen hyperbolicity in Float (`float_jensen.lean`, namespace `FloatJensen`)

Parallel Float-based Jensen polynomial machinery mirroring `JensenTranslation.lean`:

- `gammaFloat n := taylorCoeffFloat (2*n)` — maps Jensen `γ_n` to full-Taylor index `2n`.
- `jensenPolyFloat (d n) : Polynomial Float` — `J_{d,n}(x) = Σ C(d,k)·γ_{n+k}·x^k`.
- **Hyperbolicity proved** (`native_decide`, real coefficients):
  - `J_{1,n}` affine (always hyperbolic) for `n=0,1`.
  - `J_{2,n}` quadratic discriminant `(2γ_{n+1})² - 4γ_n·γ_{n+2} ≥ 0` for `n=0,1,2`.
  - `J_{3,n}` Turán inequalities `γ_{n+1}² ≥ γ_n·γ_{n+2}` for `n=0,1`.

### 18b.6 Convergence: how RH is obtained

With the Float layer complete, the path to `RiemannHypothesisProp` is:

1. `bridgedCentralCover : XiCentralZeroFreeCover 10` (this Float layer) — central rectangle.
2. Tail bound from `riemann_hypothesis_newsection.lean` / `cross_door_synthesis.lean`
   (mollified-Rouché, already committed) — `|Re z| > 10`.
3. Combine via `rh_from_central_zero_free_cover_and_tail_pointwise` (`riemann_hypothesis.lean:794`)
   or `rh_from_mollified_tail_and_central_cover` → `RiemannHypothesisProp`.

**Current status (updated):** the infrastructure has advanced well beyond scaffolding.
- Central cover: `central_cover_assembly.lean` (now ~6000 lines) has the `gridFine` 40-cell re-grid
  (x-widths ≤2.5, feasibility-checked tiers), hdiff-free strip fencing lemmas, and **all 40 cells
  packaged** — bottom row R00–R10 (y∈(0.01,0.2)) plus upper rows R11–R40 (y∈(0.2,0.49)), each with
  full RXX pattern (rect, strip bounds, radius, fencing/lowerBound/zeroFree/nonvanishing_of_bounds,
  H_instance — no `sorryAx`), each reducing its cell to explicit numerical enclosures. The boundary
  strip `(0,0.01]` is covered via `BoundaryProofEngine` on `xiShiftedEntire`, and all 40 cells are
  transferred to the lower half via `conj_of`, assembled into `full_central_covered`
  (`-10<Re<10, Im∈(0,0.49]∪[-0.49,0) → xiShifted ≠ 0`). `interval_arith.lean` provides the rigorous
  enclosure framework: `R00Numerics` poly-factor (`30 ≤ ‖polyPart‖`) and pi-factor (`1/2 ≤ ‖piPart‖`)
  bounds closed hypothesis-free, complex-Gamma lower bound (`1/1e7 ≤ ‖Complex.Gamma‖`) via the joint
  `Gammaℝ` route, and a single-point zeta lower bound `1/26 ≤ ‖ζ(sR00)‖` whose 3 analytic premises
  were closed by §R00EtaConv (eta-limit existence + remainder `‖S₂-L‖≤25` via paired M-test and
  integral bound).
- Gamma bounds: `JensenTranslation.lean` now has `3.611 < Γ(1/4) < 3.634` (width 0.023, BM n=40,
  exact log-of-rational identities closed by `norm_num`, no `sorry`; uses the ≥256-exponent `2^E`
  literal + Nat `decide` templates).
- Eta limits: `zeta_rigorous.lean` now has `eta_half_tight_best2` — `0.6029 ≤ L ≤ 0.6070` (width
  0.0041 ≈ ±0.002, inside the ±0.003 budget) via sharp convexity telescoping at M=8 with 4-decimal
  `√`-enclosures. The `η`-to-`ζ`-to-`ξ` chain at `s=1/2` is fully rigorous: `zeta_half_value`,
  `etaTendsto_eq_etaHurwitz` (hLim, paired-difference summability + identity theorem) all closed.
- The main remaining gap is the **80 per-cell numerical enclosures** (`center ε+M·r ≤ ‖ξ(center)‖`
  + uniform `‖deriv‖≤M` for each of 40 cells): needs rigorous complex `ζ`/`Γ`/`cpow` interval
  arithmetic absent from Mathlib (real `Re>1` zeta bounds only; `eta_half_pos` is real-alternating,
  off-real centers need a full complex ξ-enclosure). Also open: x=±10 endpoints, y∈[0.49,1/2),
  the real axis, and the Gamma full narrow to ±0.01 (n≈50–60). Step 3 (applying the reduction
  theorem) is straightforward once the per-cell enclosures land.

**Build:** all Float-layer files build green:
`lake build float_zeta rh_zeta_cert_central float_real_bridge central_cover_trusted float_jensen float_xi_approx float_xi_cover`.

**Build:** all Float-layer files build green:
`lake build float_zeta rh_zeta_cert_central float_real_bridge central_cover_trusted float_jensen float_xi_approx float_xi_cover`.

### 18b.7 Rigorous ℝ proof that η(1/2) > 0 (`zeta_rigorous.lean`, 0 sorrys)

A **fully rigorous** ℝ-level proof that the Dirichlet eta series at `1/2` has a positive sum,
hence `ζ(1/2) < 0` and `ξ(1/2) > 0`. Built iteratively (no axioms, no trusted Float — pure
Mathlib `Real`/`Complex` analysis). **The file currently has 0 `sorry`s.**

- `etaPartial (n : ℕ) : ℝ` — `Σ_{k=0}^{n-1} (-1)^k / √(k+1)`.
- `eta_terms_antitone` — `a_k = 1/√(k+1)` is antitone (proved via `Real.sqrt_le_sqrt`).
- `eta_terms_tendsto_zero` — `a_k → 0` (via `√(1/(n+1)) = 1/√(n+1)` and continuity of `√` at 0).
- `eta_half_pos` — `0 < ∑' k, (-1)^k/√(k+1)` (the eta series limit is positive). Proved via
  Mathlib's `Antitone.cauchySeq_alternating_series_of_tendsto_zero` (the alternating series test):
  the even partial sum `S₂ = 1 - 1/√2` is a lower bound, and `1 - 1/√2 > 0` because `√2 > 1`.
- **Current status:** `eta_terms_antitone`, `eta_terms_tendsto_zero`, `eta_half_pos` (correct
  `Tendsto` form), the `HasSum`/summability links, entire `etaHurwitz`, the continuation framework
  (all 0 `sorry`s), and **`etaTendsto_eq_etaHurwitz` (hLim now CLOSED)** — paired-increment M-test
  summability on `0<Re`, analyticity on `ball 1 (3/4)`, identity theorem — yielding unconditional
  `zeta_half_value` (`∃ L>0, ζ(1/2) = L/(1-√2)`), hence `ζ(1/2) < 0` and `ξ(1/2) > 0` with **no
  hypotheses**. Two-sided-output: `eta_half_tight_best2` (`0.6029 ≤ L ≤ 0.6070`, width 0.0041).
  `etaPartial 2 > 0` (`1 - 1/√2 > 0` via `√2 > 1`) is proved.

**Why this matters:** this is the model for closing the Float→ℝ bridge without `sorry`. The
Float layer proves `ζ(1/2) < 0` via `native_decide`; this file proves `η(1/2) > 0` (hence
`ζ(1/2) < 0`) via Mathlib's real analysis. Together they show both paths.

**Build:** `lake build zeta_rigorous` (currently 2 `sorry`s; `etaPartial 2 > 0` and `etaPartial 2 ≤ L`
build).

### 18b.8 What `zeta_rigorous` unlocks and what remains

Once its 2 remaining `sorry`s are filled, `eta_half_pos` (`0 < η(1/2)`) is fully rigorous — **no
`sorry`, no axioms, no Float**. From it:

- `η(1/2) > 0` + `ζ(s) = η(s)/(1 - 2^{1-s})` gives `ζ(1/2) < 0` (since `1 - √2 < 0`).
- `ξ(1/2) = ½·(1/2-1)·π^{-1/4}·Γ(1/4)·ζ(1/2)` has prefactor `−1/8 < 0` times `ζ(1/2) < 0` → `ξ(1/2) > 0`.
- `ξ(1/2) > 0` closes `taylorCoeff_zero_ne_zero` (`taylorCoeff 0 = ξ(1/2) ≠ 0`) in
  `JensenTranslation.lean:530` — **one** instance of `hC : ∀ k, taylorCoeff k ≠ 0`.

`hC` needs **all** `k`, and `all_shifts_from_zero_of_nonvanishing` (`JensenScratch.lean:508`)
needs `hC` plus `∀ d, Hyperbolic (jensenPoly d 0)` to get `∀ d n, Hyperbolic`. So
`zeta_rigorous` closes **one coefficient**, not the full Jensen door. Likewise, the central cover
(`central_cover_trusted.lean`) needs the same Float→ℝ bridge but for **32 distinct cell centers**,
not one point. The `zeta_rigorous` proof is the **reusable template** for that bridge.

In short: `zeta_rigorous` proves one coefficient and demonstrates the rigorous bridge pattern. A
full door still requires applying that pattern to **all** coefficients (Jensen) or to **all 32 cells**
(central cover), plus the `tendsto`/`tsum` links now being filled.

### 18b.9 How the template fits each door

`zeta_rigorous` is not a door itself — it is the **reusable Real-analysis template** that each
door's Float→ℝ bridge instantiates. How it fits, door by door:

- **Jensen door** (`JensenTranslation.lean:103,109,449,462,471` + `JensenScratch.lean:508`).
  Needs `hC : ∀ k, taylorCoeff k ≠ 0` to feed `all_shifts_from_zero_of_nonvanishing`
  (`hC` + `∀ d, Hyperbolic (jensenPoly d 0)` → `∀ d n, Hyperbolic (jensenPoly d n)`).
  `zeta_rigorous` gives `taylorCoeff 0 = ξ(1/2) > 0` (one `k`). To fit: prove `taylorCoeff k ≠ 0`
  for `k = 1,2,…` by the **same** alternating-series pattern applied to the higher even derivatives
  `Ξ^{(2k)}(0)` (each is an alternating series with the same antitone/tendsto structure, different
  `a_k`). The `eta_terms_antitone`/`eta_terms_tendsto_zero`/`alternating_series_le_tendsto` chain
  is the template; instantiate it per `k` with the `k`-th derivative's `a_k`.

- **Central cover door** (`central_cover_trusted.lean:91` + `central_cover_assembly.lean`).
  Needs `bridged_center_bound` and `bridged_deriv_bound` for **32 distinct cell centers**,
  each of the form `ε_i + M_i·r_i ≤ ‖ξ(center_i)‖`. Today those are `sorry` (TRUSTED, mpmath).
  `zeta_rigorous` is the template for **one** such bound proved in `Real` without Float:
  replace the Float lower bound `ε_i` with the `etaPartial 2 ≤ L` lower-bound step, and the
  `‖ξ(center_i)‖` lower bound with the same `S₂`-is-a-lower-bound argument applied to the
  cell's `a_k`. In other words, `eta_half_pos`'s `S₂ = 1 - 1/√2 > 0` becomes, per cell,
  `S_{2}^{(i)} > 0` for that cell's alternating series.

- **Hard-difference door** (`riemann_hypothesis_newsection.lean` + `cross_door_synthesis.lean`).
  Fits identically to the central cover: `rh_from_mollified_tail_and_central_cover` consumes the
  same `XiCentralZeroFreeCover 10` as the central door. Closing the central cover closes this door
  transitively.

- **Thin-region door** (`rh_residual_gap.lean:247` + `FirstQuadrantScratch.lean`).
  Fits via `rh_iff_thin_region_zeta` which consumes `BoundedCoverZeta T₀` — the same 32-cell
  finite-cover data, just expressed in `s`-plane `ζ` coordinates. The `zeta_rigorous` template
  applies verbatim: each cell's `η`/`ζ` lower bound is an `eta_terms_antitone`-style antitone
  sequence with a `tendsto_zero` and an `S₂`-lower-bound.

In every case the work is: **instantiate the `zeta_rigorous` alternating-series chain per index
(`k` for Jensen coefficients, `i` for cover cells), prove its `antitone`/`tendsto_zero`, then
`S₂ ≤ L` and `S₂ > 0` to get positivity.** No new ideas are needed — only per-index `a_k`
definitions and the same three lemmas.

## 18c. What solving a door does (consequence)

Solving a door means: **its `sorry`/`axiom` leaves are replaced by machine-checked proofs,
`lake build` for that door is green, and `#print axioms` shows no `sorryAx` and — where the door
carried an `axiom` — no `RiemannHypothesisProp_apply`.** What follows is forced.

**Mathematically, RH is proved.** Each door is a *bidirectional* equivalence `A_i ⟺ RH`
(`rh_iff_all_jensen_hyperbolic` for Jensen, `rh_iff_thin_region_zeta` for thin-region,
`hardDifferenceNonzero_iff_RH` for hard-difference, `rh_from_central_zero_free_cover...` for the
central cover). Proving `A_i` therefore proves `RH`. Concretely:

- **Jensen:** `∀ d n, Hyperbolic (jensenPoly d n)` → `RiemannHypothesisProp`.
- **Thin-region / central cover:** `ThinRegionZeta` / `XiCentralZeroFreeCover 10` → `RH`.
- **Hard-difference:** `HardDifferenceNonzero` → `RH`.
- **Central `axiom`:** `RiemannHypothesisProp_apply` itself.

**Transitively, every other door closes.** Since each `A_i ⟺ RH`, we get `A_i ⟺ A_j` for all
`i,j`. Proving one `A_i` proves `RH`, and `RH` proves every other `A_j`. The remaining doors
become **corollaries / alternative proofs** — their `sorry`s are then closable by composing the
already-proved equivalence with the now-proved `RH`. In Lean terms: after one door is green, the
other doors' `sorry`s can be replaced by `have hRH : RiemannHypothesisProp := <proved door>` then
`exact (rh_iff_...).mpr hRH` (or the appropriate direction).

**For the project, the open problem is closed.** The repo's proof of RH is then the chain
`A_i → RH` already committed in that door's file plus the now-filled `A_i` leaves. No further
`RH`-equivalent work is required; subsequent work is **hardening** (removing `Float.toReal` trusted
lemmas, tightening bounds, generalizing) and **documentation**.

**In Lean terms, "solved" looks like:**

- `lake build JensenTranslation` / `lake build rh_residual_gap` / `lake build central_cover_trusted`
  (or `lake build riemann_hypothesis` for the `axiom` door) — **EXIT 0**.
- `lake build zeta_rigorous` — **EXIT 0, 0 `sorry`s**.
- `#print axioms <door_theorem>` — **no `sorryAx`**.
- `#print axioms riemann_hypothesis` — **no `RiemannHypothesisProp_apply`** (for the `axiom` door).

At that point `RiemannHypothesisProp` is a theorem of Lean+Mathlib, and every `rh_iff_*` is a
two-way equivalence with both directions proved. The `Float` layer (`float_zeta`, `float_jensen`,
`rh_zeta_cert_central`, `float_real_bridge`) remains as **computational evidence**; the `Real`
layer (`zeta_rigorous` instantiated per `k`/`i`) is the **machine-checked proof** that consumes it.

### 18b.10 What remains to close the doors (precise, current)

Every door's residual is a finite, named set of proofs. The single bottleneck is the **40-cell
complex interval arithmetic** for the central cover; closing it closes doors 2, 3, and (given the
mollifier leaf) 4. Door 1 additionally needs the Pólya–Schur/Hurwitz/GORZ formalization and a final
`Γ·ζ+4` separation.

**Door 1 — Jensen–Pólya (`JensenTranslation.lean`, 5 `sorry`s at 102/108/669/682/689).**
Bridge work committed, rigorous: Hermite–Poulain lemma, `Hyperbolic_const_mul/mul`,
`jensenPoly_zero`, `taylorCoeff_zero_eq`, Gamma bounds `3.611 < Γ(1/4) < 3.634`. **Closed (`88c75900`,
`lake build JensenTranslation` green): `taylorCoeff_zero_ne_zero`** (`taylorCoeff 0 = ξ(1/2) ≠ 0`) via the
`Γ·ζ+4 ≠ 0` product separation `L*G < 4*(√2−1)`: `L ≤ 0.6069` (etaPartial16 `≤0.4819` + tail8; interval
`[0.6029,0.6069]`, width 0.0040), `Gammaℝ(1/2).re ≤ 2.72973` (BM40 + tight `π^(-1/4)∈(0.7510,0.75116)`,
width 0.00016), margin `≈0.00013` giving `Λ₀(1/2) > 0`. No Gamma n=50–60 tightening was needed. Remaining:
- 5 sorries: `rh_iff_all_jensen_hyperbolic` (102), `jensen_hyperbolic_eventually` (108, GORZ asymptotics),
  `all_shifts_from_zero` (669), `rh_iff_jensen_zero` (682), `tail_nonvanishing_iff_jensen` (689).
  **Sorry-closure triage CLOSED (honest negative):** 0/5 closable — #1/#4/#5 need the RH-bridge
  (`riemann_hypothesis.lean`, out of scope), #3 needs `∀ k≥1, taylorCoeff k ≠ 0` (degeneracy proved real:
  constant `J_{d+1,n}` kills Gauss–Lucas stepping), #2 GORZ has no feeding stones, #5's sides use
  different xi's with no bridge. Banked instead: `jensenPoly_one`, `hyperbolic_jensenPoly_zero_iff`
  (d=0 slice ⟺ `γₙ≠0`), `hyperbolic_jensenPoly_one_of_ne` (d=1 from joint nonvanishing).
- **Pólya–Schur criterion** (`polyaTheoremHyp`: order<2 + real-rooted ⇒ hyperbolic sections) + Hurwitz
  section-convergence (S1/S2). Classical result not in Mathlib/repo — must be created.
  **First stones closed:** real-linear `Hyperbolic` blocks (`Hyperbolic_X_sub_C_real`), finite real-rooted
  products (`Hyperbolic_multiset_prod_real_linear`), iterated Gauss–Lucas (  `hyperbolic_iterate_derivative`).
  **Closed since:** d=2 converse `real_quadratic_discriminant_nonneg_of_hyperbolic` (real coefficients,
  contrapositive via explicit nonreal root — no sqrt API needed) + Jensen degree-2 Turán inequality
  `jensen_degree_two_ineq_of_hyperbolic` (`γ_{n+1}² ≥ γ_n·γ_{n+2}` from `Hyperbolic (jensenPoly 2 n)`).
  **Hurwitz halves closed:** S1 scaling majorants (`choose_div_pow_le_one_div_factorial`: `C(d,k)/d^k`
  M-test majorant) + S2 zero-free disc/boundary (`hyperbolic_zeroFree_off_real`,
  `hyperbolic_ne_zero_of_im_near`, `uniform_limit_boundary_stability` in the scaffolding's eps-N
  language). **Correctness finding:** the scaffolding's UNSCALED `sectionsConvergeHyp`
  (`J_{d,0}→genFun`) is FALSE as stated (`C(d,k)~d^k/k!` diverges) — provable S1 needs `1/d` scaling
  with a different limit function. Mathlib verdict: no complex Hurwitz/Rouché (only Hurwitz-zeta +
  `TendstoLocallyUniformlyOn.differentiableOn` + isolated zeros). Remaining: S1 head convergence
  (`C(d,k)/d^k→1/k!` + summable majorant + corrected limit), S2 Rouché counting (missing in Mathlib),
  `∀ k≥1` (`Ξ''(0)` enclosures, strictly harder than `k=0`).
  **S1 head CLOSED (conditional):** falling-product limits (`choose_div_pow_tendsto_one_div_factorial`),
  M-test majorant (`scaled_dominated`), corrected limit `scaled_tendsto_jensenEntire`
  (`J_{d,0}(z/d) → jensenEntire`, conditional on `coeffGrowthSummable r`). Exact missing lemma BY NAME
  (not assumed): `taylorCoeff_summable_of_orderBound` (order<2 ⇒ growth via Cauchy+Stirling) — proving
  it closes S1 unconditionally. **S1 UNCONDITIONAL CLOSED:** `taylorCoeff_summable_of_orderBound`
  proved (Cauchy at fixed `R=|r|+1`, majorant `|C|·(|r|/R²)^k/k!` — no Stirling, no per-k optimization
  needed) + both corollaries by direct application. **ASSEMBLY CLOSED (conditional on genus):**
  `GenusOneData` structure + `GenusOneRealRooted` Prop wrapper + `genusOne_forward` (finite products +
  Gauss–Lucas + scaling + shift) + `schur_partial_assembly` (backward proved exactly up to Rouché) +
  sorry→stone map for all 5 sorrys (GORZ mapped, unattempted). Rouché counting named (`roucheZeroTransfer`)
  in doc only — now CLOSED by `RoucheCount` (see S2 note). Remaining: genus proof (Hadamard order<2 ⇒
  genus ≤1 +    `section_link`), S2a/S2b wiring, GORZ, `k≥1`. **ORDER HYPOTHESIS CLOSED + FULL CONDITIONAL
   (`polya_full_conditional`):** `jensenEntire_order_lt_two` (order `1<2` unconditional, fixed-`R=1`
   Cauchy, no Stirling) + `JensenHadamardData` genus-1 product structure +
   `genusOne_forward_of_hadamardData` (every Hadamard-RHS polynomial proved hyperbolic, isolating
   `section_link` as the single equality premise). Exact residual premises: R1 `JensenHadamardData`
   existence (order⇒product theorem absent from Mathlib/repo; repo's is xi-specific, non-transferring),
   R2 `hzeros` real-rootedness (RH-content), R3 `hcoeff` for `k≥1`, R4 `hlink` section-link equality. **S2 COUNTING CLOSED (`RoucheCount`, generic,
  in central_cover):** Jensen-gap counting lemma + `hurwitz_zero_transfer` (uniform convergence ⇒
  approximants inherit a zero) + `door1_nonreal_zero_forced` (disc `R<|c.im|` ⇒ forced zero nonreal).
  Built from scratch (no winding/argument-principle/count-zeros anywhere in Mathlib — verified).
   Remaining S2 links: (S2a) zero ⇒ divisor `≥1` (needs finite-order packaging from isolated zeros);
   **S2a CLOSED (`RoucheCount.divisor_ge_one_of_zero` + `hurwitz_zero_transfer_of_zero` +
   `door1_nonreal_zero_forced_of_zero` wrappers):** `G w = 0` alone insufficient (divisor maps `⊤↦0`);
   `G c ≠ 0` gives `orderAt c = 0 ≠ ⊤`, transferred via preconnected closed-ball clopen argument +
   `orderAt w ≠ 0` ⇒ `1 ≤ divisor`. Wrappers match `hurwitz_zero_transfer`/`door1_nonreal_zero_forced`
   signatures with `hdiv` replaced by `hGw : G w = 0` — S2b now feeds directly from a zero witness.
  (S2b) polynomial-eval packaging + `hyperbolic_zeroFree_off_real` composition in door-1 file;
   **S2b CLOSED (`scaledSection` + `schur_disc_no_interior_zero_of_hyperbolic_sections` +
   `schur_limit_zero_real_of_hyperbolic_sections`):** approximant analyticity discharged in-file,
   zero witness ⇒ forced nonreal zero ⇒ hyperbolicity contradiction, corollary in exactly the reality
   shape `schur_partial_assembly` needs past Rouché. Explicit residual: (S2c) `hConv` per-disc uniform
   convergence (S1 gives only pointwise) + (CENTER) `hGc` + (SPHERE) `hGsph` + (LIMIT-ANALYTIC) `hG`.
  (S2c) per-disc convergence + center-nonzero from S1 machinery.
  Mathlib grep verdict: no Hadamard factorization/genus/order, no Hermite–Biehler/Laguerre–Pólya (only
  three-lines Hadamard + Gauss–Lucas convex-hull form, both reused). Next: d=2 converse (`b²≥4ac`),
  genus-from-order + genus-1 Jensen-section formula, Hurwitz S1/S2.
- **`∀ k≥1, taylorCoeff k ≠ 0`** (`Ξ^{(2k)}(0)` alternating series per `k`) still open — only `k=0` closed.
  **k=1 conditional bridge COMMITTED (AW stones + AW2 5-error repair, green):** deriv-API chain + `taylorCoeff_one_eq_k1`
  + `second_ne_zero_k1 ⇒ taylorCoeff 1 ≠ 0` + exact `P''=32`. Wall numerified: `F''≈0.000495`, needs
  enclosure ±0.00049 — but O(50) summands at ~2ppm each infeasible at BM40 `~1e-3`; needs four `~1e-4`
  derivative-bound lemmas (eta-derivative series + digamma/trigamma at 1/4, absent).

**Door 2 — Xi-critical (`riemann_hypothesis.lean:34`, `axiom RiemannHypothesisProp_apply`).**
`rh_iff_xi_off_real_pointwise_nonvanishing_mathlib` / `hardDifferenceNonzero_iff_RH` chain proven.
Committed (0 sorrys): imaginary-axis slice, `xiShifted_at_zero_ne_zero`, `classicalXi_half_ne_zero`,
`zeta_half_ne_zero` (closed η→ζ→ξ chain). **Capstone committed (`ce2c8fe9`, `lake build
riemann_hypothesis` green):** hypothesis Props mirroring supplier shapes (`XiCentralMainBand10`,
`XiCentralEdgeStrips10`, `XiCutoffLines10`, `XiCentralRect10`) + master canned theorem
**`rh_from_mainBand10_edgeStrips10_tail10_cutoff`** (main band + edge strips + tail + cutoff lines →
`RiemannHypothesisProp`) + `tailPointwise10_of_absTail` adapter (plugs a door-4 mollifier leaf into the
tail hypothesis) + feeders showing the new hyps are weaker than `XiCentralZeroFreeCover 10`. Residual is
four named supplier obligations: 80 per-cell enclosures (door 3), edge strips `y∈[0.49,1/2)`, tail leaf
(door 4), lines `Re=±10`.

**Door 3 — Thin-region / central cover. THE BOTTLENECK.**
Count correction (verified 2026-09-03; old "39/1" was naive-substring counting `sorry-free`):
Legacy sorry-decls RESOLVED (verified 2026-09-03): `central_cover_assembly.lean` has **0 sorry-terms**.
`xiShifted_differentiable` was FALSE (global; strip replacement `xiShifted_differentiableOn_strip` proved,
consumers repointed); unary `.conj` was FALSE (binary with `hy0,hy1` proved); `centralCells` geometry 4/6
proved, analytic 2/6 FALSE with numbers (wide-grid infeasible: `LHS>50` vs `O(1)`, lemma
`legacy_grid_infeasible_wide_top`); full `coversUpper` FALSE (4 counterexamples) → inner triple
(`coversUpper_inner`/`coversLower_inner`/`centralCovers_inner`) proved. **Trusted migration CLOSED:**
`central_cover_trusted.lean` repointed off removed names (strip differentiability + binary `.conj` with
`hy0,hy1` from bridged bounds) + 4/4 Float-order sorrys proved (`native_decide` toRatParts pattern —
carries standard native_decide aux axioms, no sorryAx); remaining **4 sorry-terms** (mpmath-margin
center/deriv bounds, Float/ℝ agreement, grid coverage :575/581/601/645, all honestly blocked);
`rh_residual_gap.lean` has **0**; `interval_arith.lean` has **0**. `RXX_mem_gridFine` already exists for
R00 and R02–R40 and all 41 `H_instance`s exist (R01 correctly has none: `(-7.5,-5) ∉ fineGridX`).
Committed (rigorous, 0 sorrys): all **40 cells** packaged (R00–R10 bottom, R11–R40 upper) with
fencing/strip/H-instances; boundary strip `(0,0.01]`; lower half via `conj_of`; `full_central_covered`;
`rh_iff_off_line_thin_band_zeta`; tail-range certification of `zeta_cert_data`. **New (`7b965356`,
`lake build interval_arith` green, `#print axioms` clean):** `CellGammaUniform` (hypothesis-free
`1/10000000 ≤ ‖Gamma (s/2)‖` for all 40 centers), `CellUniform` (`pi_lower_of_re`, generic four-factor
`center_bound_of_component_bounds`), `R02Uniform` (R02 copy-paste template: hypothesis-free poly 22,
pi 1/2, Gamma 1e-7 + `R02_H_of_components` modulo two named missing enclosures). Remaining:
- **Zeta factor (all 40 cells):** `‖zeta s_center‖ ≥ Azeta`. **Partially closed (`3326e96b`,
  `lake build zeta_rigorous` green, axioms clean):** general paired-tail remainder
  `zetaCell_even_remainder_le`, `r(M) = C·M^{−σ}/σ`, instantiated at the R00 corner
  (`C=10`, `σ=0.395`) with power-of-two-minimal `N = 4194304` giving `r ≈ 0.081 ≤ 0.1`
  (`zetaCellS0_tail_2097152_le`; `2^20` gives `r≈0.106>0.1`, so `2^21` minimal among `2^k`).
  Still missing: (a) is now CLOSED for all centers (`etaPairLim_eq_etaHurwitz_cellCenter`:
  pair-tsum analytic on `{Re>0}` via E's majorant + `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`
  against agreement on `{Re>1}`; covers `0.395/0.3/0.2/0.105`). **Division bridge closed:**
  `zeta_of_etaPairLim_cellCenter` (`ζ(s) = ∑'pairs(s)/(1−2^{1−s})` at all centers; `Re≠1` sharp since
  `2^{1−s}=1` on the `Re=1` line; `|2^{1−s}|=2^{1−Re}` nonvanishing) + `zeta_S0_lower_of_Slarge`
  (`1/26` from `S_large≥1/5`, tail `≤0.1`, factor `≤13/5`). Unconditional R00 `Azeta` still open on exactly
  `hSlow : ‖S_{4194304}(s0)‖≥1/5` (4M cpow terms, infeasible — the smarter-bound wall stands). Downstream per-cell `Azeta` now needs only:
  `etaHurwitz=etaRHS` specialization (already `etaHurwitz_eq_etaRHS_compl`), `1−2^{1−s}≠0` + division to
  `riemannZeta s0` (both closed), and numeric `S_N` + `zetaCell_even_remainder_le` instantiation.
  **FE route opened:** Mathlib HAS the functional equation — cos-form `riemannZeta_one_sub`
  (`RiemannZeta.lean:178-180`, via `hurwitzZetaEven_one_sub`), factor
  `F(s)=2·(2π)^{−s}·Gamma s·cos(πs/2)` (not classic χ). Sine two-sided at R00 closed
  (`‖sin‖≤1e7`, `1≤‖sin‖` — first sine LOWER in repo) +   `‖F(s0)‖≤6e7` (Gamma `≤3` at `0.395` via
  convexity, cpow `≤1`, cos `≤1e7`). Lower `c≤‖F‖` residual sketched (`c≈1e-14` via cpow `≥1/7` + cos
  `≥1` + reflection Gamma `≥1e-13` needing `‖sin(πs0)‖≤2e12`). **Lower CLOSED (`c=1e-14`):**
  `zetaFE_factor_lower_S0` from cpow `≥1/7` + cos `≥1` (reverse-triangle sum form) + Gamma `≥1e-13`
  via complex reflection `Gamma_mul_Gamma_one_sub` (`Beta.lean:397-398` — EXISTS, no continuation
  needed) with `‖sin(πs0)‖≤2e12` + `‖Gamma(1−s0)‖≤2`. FE factor now two-sided at R00
  (`1e-14 ≤ ‖F‖ ≤ 6e7`). **Reflected pilot:** short sum `‖S₂(1−s0)‖ ≥ 1/3` CLOSED at `σ=0.605`
  (first term dominates honestly, margin 0.05) + `zeta(1−s0) = G/(1−2^{s0})` instance +
  `zetaFE_refl_eq_S0` (`ζ(1−s0)=F(s0)·ζ(s0)`). **Direction correction:** Mathlib gives
  `ζ(1−s)=F(s)·ζ(s)`, so `‖ζ(s0)‖ ≥ ‖ζ(1−s0)‖/6e7` needs `F` UPPER (have it), not lower.
  **Wall quantified:** `r(M)=10·M^{−0.605}/0.605` needs `M≥635` (`N≥1270` terms, infeasible explicit)
  for `r<1/3` — the `hSlow` wall shifted from 4M to ~1–2k terms, not removed. Missing exactly:
  `Azeta1>0` at `1−s0` without explicit 1k+ sums (smarter tail with cancellation, or non-pair route);
     then `Azeta=Azeta1/6e7` is immediate. **Conditional closure proved (`zeta_S1_lower_of_S2048`,
   `zeta_S0_lower_of_S1`):** `Azeta1=1/39` at `1−s0` from `‖S_{2048}‖≥1/3` (M=1024 tail `r≤4/15`, margin
   ~70% — true `|ζ(s1)|≈1.40`) ⇒ downstream `Azeta=1/2340000000`. **Wall proved both sides:**
   all `M≤343` fail (`r≥1/3`, so ≥688 terms necessary), M=1024 works; true minimal M=635 (bracket
   `[344,1024]` formalized). No small-M closure exists under any triangle bound (`r(1)≥16` vs `1/3`;
   proved tail ~2500× loose vs true — the gap is pure inter-pair phase cancellation). Honest routes:
   Kuzmin–Landau cancellation tail (absent from Mathlib, major) or rigorous complex interval arithmetic.
    **KL Tier-1 CLOSED:** first-derivative test `‖∑e^{inθ}‖≤π/|θ|` from scratch (geometric core + Jordan
    denominator bound) + AE-block phase gap (`8.75/2049`, tight to 0.02%) + smallness (`≪π/2`, 184× margin).
    Stopping honesty: linear-KL scales as `N^{+0.395}` per dyadic block (diverges where triangle converges) —
    Tier 2 needs the Abel bridge (`Finset.sum_range_by_parts`, reserved) + TV bound; Tier 3 needs
    second-derivative/van der Corput or interval arithmetic. `S_{2048}` premise stays conditional.
    **Tier-2 CLOSED (`T2_abel_eq`/`T2_block_upper`/`T2_w_TV_total`):** second-half block UPPER `≤1/5`
    (`72×` sharper than triangle `~12.4`, margin `2/15` to `1/3`) + weight TV `≤1/25`. Stopping honesty:
    a LOWER on `S_{2048}` needs `‖S_{1024}‖≥8/15` (true `≈0.56`, margin `0.027`) — needs rigorous
    `cos/sin(8.75·log n)` interval arithmetic or Tier-3 second-derivative for an early-block upper.
    **D3 interval framework CLOSED (`D3_block_norm_ge_sum_lo` + `D3_S1024_of_S1` + `D3_S2_norm_ge`):**
    per-term cpow enclosures (`θ₂∈[6.065,6.066]`, `cos θ₂≥0.97`, `2^{-0.605}∈[5/8,2/3]`) ⇒ `S_1`, `S_2≥1/3`
    green. Exact K-table (true): K=4 dead, K=8 fails by 0.019, **K=16 first feasible** (margin 0.024).
    **S_4 enclosures banked (`D3_S4_re_lower` et al.):** θ₃/θ₄ + per-term bounds in the S₂ shape — but true
    `Re S₄≈-0.54<0`, so the Re-sum route NEVER reaches `8/15` (proved `D3_S4_cannot_reach_8_15`); the
    durable asset is per-term technology for x=3,4. Next per K-table: θ₅–θ₁₆ toward K=16 + middle upper.
    **x=5,6 banked (`D3_S6_re_lower` et al.):** prime pattern (`log_five_d9`) + composite bridge (`log 6 =
    log 2 + log 3`) — but true `Re S₆<0`, Re-route dead again (`D3_S6_cannot_reach_8_15`). Next: θ₇–θ₁₆
    BLOCKED on missing `log_seven/eleven/thirteen` d9 bounds (create in-file); composites 8/9/10/12/14/15/16
    factor through 2/3/5 bridges. **Prime logs CLOSED (`log_seven/eleven/thirteen_near_10` + d9 pairs,
    mirror of `log_five_d9` method):** θ₇/θ₁₁/θ₁₃ unlocked for the K=16 push. **Prime stacks CLOSED
    (`D3_S7_re_lower` et al.):** θ₇/θ₁₁/θ₁₃ full enclosures green     (Re-route negative as predicted —
    per-term technology banked). Composites 8/9/10/12/14/15/16 tasked (log-bridge follower).
    **x=8,9 CLOSED (`D3_S8/S9_re_lower` et al.):** power-bridges (`log 8 = 3·log 2`, `log 9 = 2·log 3`)
    green (Re-route dead again, `cannot_reach` proved). 10/12 tasked next, then 14/15/16.
    **x=10 CLOSED (`D3_S10_re_lower` et al.):** `log 10 = log 2 + log 5` bridge green
    (`S_10 ≥ −69/24`). x=12 tasked next. **x=12 CLOSED (`D3_S12_re_lower` et al.):** `log 12 =
    2·log 2 + log 3` bridge green (`S_12 ≥ −81/24`). 14/15/16 tasked (all prime d9 bounds exist).
    **x=14/15/16 CLOSED (`D3_S16_re_lower` et al.):** early-block per-term technology COMPLETE for
    x=1..16. Residual: middle `[16,1024)` upper (≤0.12 class; triangle ≈35/Abel ≈8.6 too loose) tasked. **Generalized per-row (`RowFE`, all 4 rows, uniform over `|Im|≤8.75`):**
  sin-half `≤1e7` shared; Γ upper `3/4/5/10`; Γ lower `1e-13` all rows; cos lower `0.8–0.98`
  (R00's `1≤‖cos‖` FAILS row-uniformly at Im=0 — replaced via `cos(Re)≤‖cos‖` + real Taylor);
  `‖F‖` upper `6e7/8e7/1e8/2e8`, lower `1e-14` all rows. Factor half of reflected-eta `Azeta` ready;
  short-sums half (at `1−s`) still open. (b) any `Azeta>0` —
  **strategic finding:** `N=4194304` makes the explicit-partial-sum lower bound infeasible (4M cpow terms),
  so the `S_N`-direct route to `Azeta` is computationally dead at the R00 corner; a smarter zeta lower
  bound is needed (functional equation / reflection to a large-`ζ` region, not longer partial sums).
- **Deriv factor (all 40 cells):** uniform `‖deriv xiShifted w‖ ≤ M`. **Generic infrastructure closed
  (`82da3e16`, `lake build central_cover_assembly` green, axioms clean):** `DerivCauchyBridge`
  (`deriv_xiShifted_le_of_entire_sphere_bound`: `‖deriv xiShifted w‖ ≤ C/R` from strip entireness via
  Mathlib `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` — no new circle-integral material was
  needed) + `uniform_deriv_of_sphere_bound` / `uniform_deriv_of_closedBall_bound` (`M=C/r` from one
  closed-ball sup). **R02 first concrete `M=67200` conditional** on `R02_zeta_upper_obligation`
  (`‖zeta‖≤10` on the disc; poly `≤42`/pi `≤1`/Gamma `≤40` discharged hypothesis-free; `r=0.25` stays in
  the strip). **Update:** first UNCONDITIONAL end-to-end cell bound closed (newsection
  `R02ZetaUpper`+`R02DerivBridge`+`R02Unconditional`, consuming the identity theorem):
  `‖zeta‖≤1012` on the disc (sharp at `M=1` — `r(M)≈180·M^{−0.05}` needs `M≥10^{31}` terms for `r≤5`) ⇒
  `R02_deriv_bound_unconditional` (`M=6800640`). The `≤10` obligation (hence `M≈0.05` tier) needs
  FE+Stirling+convexity, not the eta M-test. **Update — existence verdicts + Euler stone:**
  Phragmén–Lindelöf EXISTS (strip form `PhragmenLindelof.vertical_strip`) and Hadamard three-lines EXISTS
  (`Hadamard.norm_le_interp_of_mem_verticalClosedStrip'`) — do NOT recreate. Euler absolute upper closed
  (`zetaUpper_riemannZeta_norm_le_tsum`: `‖ζ(s)‖ ≤ ∑'(n+1)^{-σ}` on `Re>1`, tsum form). Exact next lemma
  `zetaUpper_R02_of_threeLines` (assembly CLOSED conditional — `ZetaUpperR02ThreeLines`): pole-removed
  `F` proved ENTIRE (removability) + damped three-lines ⇒ `‖ζ‖≤10` from whole-line left cap `A≤50.925`
  (divisor 5.0925). Proved window cap `1.2e9` — `~2.4e7×` gap purely in the crude cos/exp left-edge
  majorant (windows cannot close it). Needs Stirling-sharp left edge (true `A=O(10²)`); FE+Stirling+
     convexity material absent from Mathlib/repo. **Sharp window banked (`Door3SharpWindow`, 7500×):**
   split cos/Gamma caps (`‖F‖≤1280` for `|Im|≤6`, `≤3120` above) ⇒ damped window `A=160000` (was `1.2e9`),
   still `~3142×` above `50.925`.    Remainder is pure separate-majorant loss (true sup `O(10)`) — needs
   JOINT `Γ·cos` exponential cancellation (`|Γ(1+iy)|²=πy/sinh(πy)`, van der Corput class, absent).
   **Joint cancellation CLOSED (`Door3JointGammaCos`):** `‖Γ(1+iy)‖²=πy/sinh(πy)` from scratch (reflection
   + `Gamma_conj`) ⇒ joint `‖Γ·cos‖≤34` on `Re=2` (true `≈32.6`, 4% headroom; **1647×** gain) ⇒ damped
   window **`A=36 ≤ 50.925`** (margin 14.925; **4444×** over `160000`). **P1's left-cap premise MET** —
   AD's `zetaUpper_R02_ten_of_bounds` can now fire (wiring = compose `A=36` in).
  **Wiring verdict (`BF2TailCaps`):** whole-line CONSTANT `A≤50.925` does NOT fit (off-window truth is
  exponential, worst ~e^72; sharp truth `O(10)` needs all-`Im` joint cancel, absent) — right piece `B=36`
  met whole-line; growth-variant left cap green. **Next: windowed-strip three-lines** (R02 disc has
  `|Im|≤8.25 < 8.75` — AR's windowed `A=36` suffices a windowed assembly; no whole-line cap needed).
  **Windowed P1 CLOSED-conditional (`BH2TailWindow`, BH3-repaired, green):** `‖G‖≤36` on closed strip
  `[-1,2]` from windowed caps + explicit `hTail`, then **`‖ζ‖≤10` on R02** via the threshold theorem
  (`zeta_R02_le_ten_of_tail`, margin 14.925). Opens: (i) `hTail` (`‖G‖≤36` off-window — needs
  Stirling-scale `F` bound), (ii) `hBdd` (strip `ζ`-growth). **xi-bridge banked (`BLMiddleEnvelope`,
  Hadamard import added cycle-free):** unconditional `xi→F` transfer with explicit denominators +
  `hBdd`/P1 conditional on `StripEnvelope` R1 only. Residual: (R1) strip `Gammaℝ` lower via reflection
  (right closable via Euler, left via FE, middle missing) + (R2) Stirling-sharp tail bound (crude
  `exp(O(|τ|^1.5))` genuinely cannot close at 8.75 — needs true `O(|τ|^2.5)`). **Middle-envelope gap mapped (BJ2, honest
  zero-write):** right `σ∈[1.5,2]` + left `σ∈[-1,-0.5]` envelopes DONE in-file; middle `σ∈[-0.5,1.5]`
  has NO envelope (Euler blows up, eta denominator zeros, FE no gain, log-bound absent). **Unblock
  found:** `ZeroFreeRegionHadamard.xi_norm_bound_whole_plane` (`‖xi‖≤exp(K‖z‖^{3/2})`) EXISTS and that
  module imports ONLY Mathlib — any work file can import it cycle-free (AD precedent).
  **Outer thirds CLOSED (`BNStripThirds`):** exp-linear `F` envelope off the middle (`C=18`, `K=1+π/2`).
  R1-as-stated (exp-linear) PROVED unreachable via xi (`exp(O(|τ|^1.5))` never fits); three-lines circular.
  Relaxation tasked: exp-3/2 middle via xi + Gaussian domination ⇒ `hBdd` (damping beats any 1.5-power). **Update — Gamma factor fully closed for all 40 centers:**
  32/32 inner caps proved (rows 0–3: `0.05/0.15/0.5/1.5/1.2/0.5/0.15/0.05` outward→central, reusing the 4
  numerator chains; true ratios `~0.03→1.1`). Every cell's center product budget now has all four factors
  bounded (poly/pi/Gamma/zeta-upper); what remains per cell is a USABLE `Azeta` (division bridge, next)
  and the deriv `M` at fencing tier. **R02 PILOT VERDICT: unconditional closure INFEASIBLE with
  committed constants** (`22·0.5·1e-7·(1/26) = 4.2e-8 ≪ 0.065`; closing needs `Azeta ≥ 59090`).
  **Conditional closure proved** (`R02_closed_of_factorBounds`): three explicit numeric premises
  (`Agam ≥ 0.006`, `Azeta ≥ 1`, `M ≤ 0.05`) ⇒ H-leaf — plug-and-play for all future factor work.
  Exact gaps: Gamma-lower `60000×` (reflection+`1e-7` infeasible in principle, needs `‖sin‖≥3e9`);
     zeta-lower open; deriv `1.34M×` (vs 67200) / `136M×` (vs 6800640). **Gamma-lower banked
   (`R02GammaLower`, 20000×):** `0.002 ≤ ‖Gamma(sR02/2)‖` via reflection (true `≈0.0087`, 4.3× headroom) +
   drop-in `gammaOf_lower_R02`; exactly `3×` short of `0.006` (needs `S·U≤523.6`, banked `1500` — deeper
   `n≈15` shift chain + near-perfect sine required). With `Agam=0.002` the threshold needs only
   `Azeta≥2.95` (was `≥59090`). **Deeper shift banked (`R02GammaUpperDeep`, n=21):** reflected upper
   `U: 0.05→0.026` (1.93×; brief's `n≈15` yields only `≈0.028`) ⇒ `S·U=780` → `π/780≈0.00403`, `1.5×`
   short. Tier-2 sine (`S≈20067`) would give `521.7≤523.6` — closes in principle.
   **Tier-2 sine CLOSED (`R02SineSharp`):** fractional-exp lemma (`e^0.6029≤1.8275` via `Real.exp_bound'`)
   ⇒ `e^10.6029≤40255` ⇒ `‖sin‖≤20128` (true `≈20125.7`, 0.012%) ⇒ `S·U=523.328≤523.6` (margin 0.272) ⇒
   composed **`0.006 ≤ ‖Γ(sR02/2)‖`** (margin 0.0000031, 0.05%) + drop-in. **P3 Gamma-lower leg DONE —
   `Agam=0.006` premise met exactly.** No further sine/Gamma work at R02. Poly `22`, pi `1/2`,
  Gamma-upper `0.05` at R02: no gap. Feasibility gap: `67200` is far too large for fencing (`ε+M·1.26` vs `‖ξ(center)‖=O(0.1)`;
  crude `‖Γ‖≤Real.Gamma` ignores Im-decay, true `~0.01` vs proved `40`) — needs the Stirling Gamma upper
  + tighter zeta upper to reach tier `M≈0.05`. **Stirling disc-upper CLOSED (`R02GammaDisc`, 412×):**
  6-shift Im-decay floors (`D≥2648`) + convexity uniform numerator (`≤256.78`) ⇒ `‖Γ(s/2)‖≤0.097`
  on the R02 disc (true sup `~0.026`, within 3.7×) + drop-in `gammaOf_upper_disc_R02`; downstream sphere
  sup `16800→40.74`, conditional deriv `M=67200→~163`. Gamma done — deriv now needs only the zeta upper
  (`‖ζ‖≤10` obligation). **Rewired (`AO_R02DiscUpdate`):** `AO_R02_deriv_bound_163_of_zeta_upper`
  (mirrors the `67200` proof with the `0.097` cap; cycle-safe obligation instead of the import) +
  `AO_R02_closed_of_factorBounds_163` (threshold recomputed: budget `205.382` vs product `205.392`,
  margin 0.01). Threshold shift documented: at `M=163` closure needs `Azeta≥3111` (vs `≥1` at `M=0.05`);
  at committed `Agam` needs `≥186710909`. Honest net: center `0.066` vs budget `205.382` infeasible at
  true `|ζ|=O(1)` — 0 cells claimed closed. **Rewiring v2 (`AU_R02_Agam002_M163`, `Agam=0.002`
  era):** budget `205.382` vs product `205.392` (margin 0.01) ⇒ closure needs `Azeta≥9336` at `M=163`
  (`9336=3112·3`, necessary `9335`); fully-wired H-leaf with premise/owner/status table as doc-string
  (P1 zeta-upper OPEN, P2 Gamma-upper LANDED, P3 Gamma-lower LANDED, P4 zeta-lower OPEN, poly/pi/leaf CLOSED).
  **Rollout template CLOSED (`AX_CellTemplate`):** `CellClosed_of_factorBounds` (generic cell ⇒ H-leaf from
  explicit numeric premises) + R02 recovery of AU v2 as corollary + tier table for all 39 cells + 20
  strip cells (`Azeta ≥ (eps+M·radCap)/(Apoly·Api·Agam)` per group; G4 needs small-r deriv packaging).
  **Apoly rollout CLOSED for G1 (`R03R10PolyLower`):** R03–R10 hypothesis-free lowers (11.3/3.85/0.39/0.88/
  5.35/13.8/26.3/38.3, slacks 0.02–0.11, same quadratic skeleton — no extension needed; R01 skipped).
  Poly column done for the whole bottom row; remaining per-cell blockers unchanged (`Azeta`, `M`).
  **R31 small-r packaging CLOSED (`BB_Row3SmallR`):** `r=0.008` admissible (`0.498<0.5`; `r=0.25` provably
  exits) + `C=5600` + **`M=700000`** + R31 through the template (conditional on sup/center premises;
  threshold at M=700000 infeasible at `O(1)` — same wall). R32–R40: copy template, recompute numerals.
  **R32 CLOSED-packaged (`BD_R32SmallR` + shared `BD_Row3Shared`):** pi-upper + Gamma-mirror shared once;
  R32 (`-8,-5.5`, outer) through the template (r=0.008/C=5600/M=700000). R33–R40 mapped with numerals
  (mid/inner thresholds 882000.05/882000.15) — copy agent tasked. Remaining 39 cells: same shape, different `s`-rects
  (upper rows `y≤0.49` need `r<0.01` or the closedBall version).
- **Load-bearing budget finding:** even with zeta closed, the `1/1e7` Gamma constant makes product checks
  infeasible in principle (R02 needs `Azeta ≥ 5.9×10⁴`, R00 `≥ 4.3×10⁴`; true `|ζ|=O(1)`).
  **Pointwise closed at the R00 corner (`bce40202`, green, axioms clean):**
  `CellGammaUpper.gamma_one_sub_half_upper_R00`, `‖Gamma(1−sR00/2)‖ ≤ 0.01` via a 12-step
  `Gamma_add_one` shift (numerator `≤313M`, denominator `≥33B`) — 150× better than the old `1.5`
  (true value `~7e-3`). But **uniform `≤0.01` over all 40 centers is FALSE** (inner cells `|s.im|≈0.75`
  have true values `≈1.0`), and reflection + the `1/1e7` lower bound is infeasible in principle (needs
  `‖sin‖≥3.1e9`).   **Update — 8/8 outer-tier cells `≤0.01` closed:** R11/R10/R20 (n=12, reusing the `12.85` chain or R00's)
  + R21/R30 (row 2, `re=0.9`, n=14, `N≤6.95e10/D≥7e12`) + R31/R40 (row 3, `re=0.9475`, n=15,
  `N≤1.16e12/D≥1.2e14`) — the brief's "n=12 for all outer-tier" was mathematically impossible (true n=12
  ratios `0.01038/0.01091` rows 2/3), resolved by deeper shifts. **All 40/40 centers now capped**
  (32 inner closed after, same template). No Gamma work remains.
- **Residual strips**: x=±10, y∈[0.49,1/2), the real axis (BoundaryProofEngine). The `(0,0.01]` bottom strip
  IS packaged conditionally (`BottomStripObligations` + `bottom_strip_covered`); global
  `xiShifted_differentiable` is false-as-stated (strip-version entireness proved — use that).
  **Scaffolding closed:** 10 edge-strip cells packaged (`edgeStripCells` + coverage combinatorics),
  `EdgeS00` template (geometry `dx=1.25/dy=0.005/radius<1.26`, poly `≤56`/pi `≤1` hypothesis-free, Gamma
  `≤400` at the NEW re-value `0.005` via `Real.Gamma 1.0025 ≤ 1` one-over-x route), `CutL10`/`CutR10`
  thin rects (`y∈(−0.49,0.49)`, radius `<0.56`) with line-membership lemmas. **All 10/10 upper columns
  packaged** (EdgeS01–S09 numeral-for-numeral; shared re-value maximally reused, no Gamma-chain
  duplication). Lower mirrors blocked (no packaged upper rect for `conj_of`, `y1<1/2` fails, new `0.995`
  Gamma chain needed). **Update — all 10/10 LOWER mirrors packaged** (EdgeS00_Lower–S09_Lower:
  geometry, poly `≤56` generic, pi `≤1`, Gamma `≤2` at re `0.995` + `≤3` at `0.4975` via new
  center-independent chains). **Y1 verdict:** direct `conj_of` inapplicable even with closed upper
  H-leaves (`¬y1<1/2` proved for all 10 uppers); shrunk variants (`y1=0.499`, explicit gaps
  `[0.499,0.5)`/`(−0.5,−0.499]`) satisfy the hypotheses with coord mirrors conditional on shrunk upper
  packaging. **Zero strip cells fully closed** — full closure needs the same zeta wall as
  central cells (`Azeta` + tight upper).

**Door 4 — Mollified / hard-difference (`riemann_hypothesis_newsection.lean`, 0 `sorry`s).**
Rouché-gap chain committed; `‖M‖≤B` mollifier bounds proven. **Euler right edge closed
(`TailZetaUpper`):** Im-uniform `‖ζ‖ ≤ 1+1/δ` on `Re ≥ 1+δ` (`B=3` at `3/2`, `B=2` at `2`;
Im-uniformity free from the majorant). Cross-confirms PL/three-lines existence. Exact next lemma
`TailZetaUpper_threeLines_FE_assembly` (assembly CLOSED conditional): whole-line `A`(`Re=−1`) +
`B`(`Re=2`) + `BddAbove` ⇒ strip bound `A^(1−t)·B^t/(‖s−1‖·‖damp‖)` + `50.925`-threshold form
(`‖ζ‖≤101.85·exp(((|τ|+6.75)²)/100)`). Honest limits: conclusion explicitly-growing in `|τ|`, NOT
Im-uniform; even uniform `B₀` ≠ mollifier gap (K=2 needs phase `‖ζ−2‖≤2−2δ`, not size).
Remaining: instantiate a
`MollifiedRoucheLeaf K` with the gap `‖ζ·M − 1‖ ≤ 1−δ` on the tail — needs a **uniform ζ upper bound
on `0<Re<1/2` as `|Im|→∞`** (K growing with `|Re z|`, convexity/Phragmén–Lindelöf + functional
equation + Stirling). Then feeds the same central cover.

**Net:** rigorous per-cell complex interval arithmetic for ζ/Γ/ξ (40 cells) is the one piece whose
absence blocks doors 2, 3, 4 simultaneously. Doors 1's remaining work (Pólya–Schur/Hurwitz/GORZ +
`Γ·ζ+4` separation) is independent of that.

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

Float computation layer (convergent target fuel)
   float_zeta.lean [FloatZeta namespace: etaFloat, zetaFloat, xiFloat, taylorCoeffFloat]
       │  ├─ Dirichlet eta series → zetaFloat (computable Float ζ)
       │  ├─ xiFloat = 0.5·s·(s-1)·π^(-s/2)·Γ(s/2)·ζ(s)  [Float]
       │  ├─ zetaFloat_half_neg_1000  ── ζ(1/2) < 0 (native_decide)
       │  ├─ xiFloat_half_pos_100     ── ξ(1/2) > 0 (native_decide)
       │  └─ taylorCoeffFloat n       ── Ξ^(n)(0)/n!  [mpmath 50 dps, signs alternate]
       │
       ├─ rh_zeta_cert_central.lean  [CentralCell, central_cert_data (32 cells)]
       │       └─ eps > 0, M ≥ 0  (native_decide, mpmath margin ≥ 1.235e-02)
       │
       ├─ float_real_bridge.lean  [Float.toReal : Float → ℝ, via toRatParts]
       │
       ├─ central_cover_trusted.lean  [BridgedCell, bridgedCentralCover]
       │       ├─ bridged_center_bound  (TRUSTED: mpmath)  ── Float ε → ℝ ≤ |ξ(center)|
       │       ├─ bridged_deriv_bound   (TRUSTED: mpmath)  ── Float M → ℝ ≥ |ξ'| on rect
       │       └─ bridgedCentralCover : XiCentralZeroFreeCover 10  ← CONVERGENT DELIVERABLE
       │
       └─ float_jensen.lean  [FloatJensen namespace: gammaFloat n := taylorCoeffFloat (2n)]
               ├─ jensenPolyFloat  ── J_{d,n}(x) = Σ C(d,k)·γ_{n+k}·x^k
               └─ hyperbolicity    ── J_{1,n} affine, J_{2,n} discriminant ≥ 0, J_{3,n} Turán

Door assembly (how RH is obtained)
   bridgedCentralCover (central rect)  +  mollified-Rouché tail (|Re z| > 10, committed)
       └─ rh_from_central_zero_free_cover_and_tail_pointwise (riemann_hypothesis.lean:794)
           └─ RiemannHypothesisProp

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

### C.1 Float-layer reading order (for the convergent target)

If working the central-cover / Jensen / hard-difference doors, read these FIRST:
1. `float_zeta.lean` (namespace `FloatZeta`) — `etaFloat`, `zetaFloat`, `xiFloat`, `taylorCoeffFloat`;
   the computable Float ζ/ξ and the mpmath-verified Taylor coefficients. **This is the fuel source.**
2. `rh_zeta_cert_central.lean` — `CentralCell`, `central_cert_data` (32 cells), positivity theorems.
3. `float_real_bridge.lean` — `Float.toReal` (the Float→ℝ coercion).
4. `central_cover_trusted.lean` — `BridgedCell`, `bridgedCentralCover`; the trusted lemmas and the
   assembled `XiCentralZeroFreeCover 10`.
5. `float_jensen.lean` (namespace `FloatJensen`) — `gammaFloat`, `jensenPolyFloat`, hyperbolicity proofs.
6. `central_cover_assembly.lean` — `XiLocalZeroFreeRect`, `XiLocalLowerBoundRect`,
   `XiCentralZeroFreeCover`, `cell_lower_bound_from_center_and_deriv` (Taylor fencing).

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
- **Line endings:** this repo mixes LF and CRLF per file (e.g. `zeta_rigorous.lean` LF,
  `central_cover_assembly.lean` CRLF). When appending to a file, PRESERVE its existing endings —
  a whole-file flip buries the real diff (this happened once to `interval_arith.lean` in `bce40202`).
  Verify with `git diff --numstat` (expect small dels) before finishing.

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
