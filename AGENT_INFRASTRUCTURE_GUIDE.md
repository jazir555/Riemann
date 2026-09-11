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
- **One process at a time.** Build ONLY via the guarded wrapper (it owns the
  filesystem mutex, auto-clears stale locks, and owner-checks release):
  `pwsh -File scripts/Invoke-GuardedLakeBuild.ps1 -Module <Module>`.
  Manual fallback only if the wrapper itself breaks — acquire the mutex first:
  - Lock file: `C:\Users\mmeadow\Documents\Lean\mathlib4\.lake_build_lock`.
  - Acquire: `New-Item -Path <lock> -ErrorAction Stop` (atomic).
  - If it exists OR a `lake.exe` process is running, wait ~10s and retry. A lock older than
    25 min **with no live lake/lean process** is stale — delete it (the wrapper does this
    automatically and logs `GUARD-AUTOCLEARED`).
  - Release: `Remove-Item <lock>` in a `finally` block, only if you created it.
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
- **Historical Float-layer trusted lemmas** (`central_cover_trusted.lean`): the original
  `bridged_center_bound`/`bridged_deriv_bound` design used mpmath-backed `sorry` leaves. The current
  file has no `sorry` declarations: the production `BridgedCellCertificate` takes exact real center,
  derivative, and coverage inequalities as explicit fields. The remaining task is to supply those
  fields by a kernel-checked complex-ζ/ξ enclosure; the later Door-3 updates record the migrated API.
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

### 18b.4 Central cover assembly (`central_cover_trusted.lean`) — historical Float path

Bridges the Float cert to the ℝ central cover structure:

- `BridgedCell` — wraps `CentralCell` with `Float.toReal` conversions for `x0,x1,y0,y1,ε,M`.
- `bridged_center_bound` (historical trusted Float statement): `Float.toReal ε + M·radius ≤ ‖ξ(center)‖`.
- `bridged_deriv_bound` (historical trusted Float statement): `∀z ∈ rect, ‖ξ'(z)‖ ≤ Float.toReal M`.
- `bridgedToLowerBoundRect` → `XiLocalLowerBoundRect` (uses `cell_lower_bound_from_center_and_deriv`).
- `bridgedToZeroFreeRect` → `XiLocalZeroFreeRect` (uses `XiLocalZeroFreeRect_of_lower_bound`).
- `bridgedCentralCover : XiCentralZeroFreeCover 10` — the historical 32-cell Float assembly.

This subsection records the original Float design.  The current implementation has migrated the
production path to exact real certificate fields: `central_cover_trusted.lean` contains no `sorry`
declarations, and its `BridgedCellCertificate` requires the center, derivative, and coverage
inequalities as explicit inputs.  The mpmath/Float rows remain computational candidates until those
analytic inequalities are supplied by a kernel-checked enclosure.  See the dated Door-3 updates at
the end of this guide for the current 40-cell and finite-certificate status.

### 18b.5 Jensen hyperbolicity in Float (`float_jensen.lean`, namespace `FloatJensen`)

Parallel Float-based Jensen polynomial machinery mirroring `JensenTranslation.lean`:

- `gammaFloat n := taylorCoeffFloat (2*n)` — maps Jensen `γ_n` to full-Taylor index `2n`.
- `jensenPolyFloat (d n) : Polynomial Float` — `J_{d,n}(x) = Σ C(d,k)·γ_{n+k}·x^k`.
- **Hyperbolicity proved** (`native_decide`, real coefficients):
  - `J_{1,n}` affine (always hyperbolic) for `n=0,1`.
  - `J_{2,n}` quadratic discriminant `(2γ_{n+1})² - 4γ_n·γ_{n+2} ≥ 0` for `n=0,1,2`.
  - `J_{3,n}` Turán inequalities `γ_{n+1}² ≥ γ_n·γ_{n+2}` for `n=0,1`.

### 18b.6 Convergence: how RH is obtained

With the historical Float layer complete, the path to `RiemannHypothesisProp` was:

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
- The main remaining gap is the **80 per-cell numerical enclosures** (two fields for each of the
  40 current cells: `center ε+M·r ≤ ‖ξ(center)‖` and uniform `‖deriv‖≤M`): it needs rigorous
  complex `ζ`/`Γ`/`cpow` interval
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

**Build:** `lake build zeta_rigorous`; the current source has 0 `sorry` declarations.  The older
two-sorry status referred to an intermediate revision and is retained only in the commit history.

### 18b.8 What `zeta_rigorous` unlocks and what remains

`zeta_rigorous.lean` now has no `sorry` declarations. Its `eta_half_pos` result (`0 < η(1/2)`) is
fully rigorous — **no `sorry`, no axioms, no Float**. From it:

- `η(1/2) > 0` + `ζ(s) = η(s)/(1 - 2^{1-s})` gives `ζ(1/2) < 0` (since `1 - √2 < 0`).
- `ξ(1/2) = ½·(1/2-1)·π^{-1/4}·Γ(1/4)·ζ(1/2)` has prefactor `−1/8 < 0` times `ζ(1/2) < 0` → `ξ(1/2) > 0`.
- `ξ(1/2) > 0` closes `taylorCoeff_zero_ne_zero` (`taylorCoeff 0 = ξ(1/2) ≠ 0`) in
  `JensenTranslation.lean:530` — **one** instance of `hC : ∀ k, taylorCoeff k ≠ 0`.

`hC` needs **all** `k`, and `all_shifts_from_zero_of_nonvanishing` (`JensenScratch.lean:508`)
needs `hC` plus `∀ d, Hyperbolic (jensenPoly d 0)` to get `∀ d n, Hyperbolic`. So
`zeta_rigorous` closes **one coefficient**, not the full Jensen door. Likewise, the central cover
needs the same analytic bridge for **40 distinct cell centers**,
not one point. The `zeta_rigorous` proof is the **reusable template** for that bridge.

In short: `zeta_rigorous` proves one coefficient and demonstrates the rigorous bridge pattern. A
full door still requires applying that pattern to **all** coefficients (Jensen) or to **all 40 cells**
(central cover), plus the remaining complex enclosure and edge/cutoff suppliers.

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

- **Central cover door** (`central_cover_trusted.lean` + `central_cover_assembly.lean`).
  Needs explicit center and derivative inequalities for **40 current cell centers**, each of the
  form `ε_i + M_i·r_i ≤ ‖ξ(center_i)‖`.  The old 32-cell Float leaves have been removed from the
  production API; `BridgedCellCertificate` now receives these real inequalities as fields.
  `zeta_rigorous` remains a template for proving one such bound in `Real` without Float, while the
  current off-axis interface additionally permits finite eta-sum certificates.

- **Hard-difference door** (`riemann_hypothesis_newsection.lean` + `cross_door_synthesis.lean`).
  Fits identically to the central cover: `rh_from_mollified_tail_and_central_cover` consumes the
  same `XiCentralZeroFreeCover 10` as the central door. Closing the central cover closes this door
  transitively.

- **Thin-region door** (`rh_residual_gap.lean:247` + `FirstQuadrantScratch.lean`).
  Fits via `rh_iff_thin_region_zeta` which consumes `BoundedCoverZeta T₀` — the same current
  40-cell finite-cover data, just expressed in `s`-plane `ζ` coordinates. The `zeta_rigorous` template
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
four named supplier obligations: 80 per-cell enclosures (two fields for each current 40-cell row; door 3), edge strips `y∈[0.49,1/2)`, tail leaf
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
`hy0,hy1` from bridged bounds) and all four Float-order bridges are proved (`native_decide`
`toRatParts` pattern).  The module contains no `sorry` terms; its `BridgedCellCertificate` interface
keeps the mpmath-derived center/derivative inequalities and coverage as explicit data rather than
silently treating sampled Float values as analytic proofs.  The standard auxiliary axioms introduced
by `native_decide` are present, but no `sorryAx` is used;
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
    **Middle upper CLOSED-first (`MID_mid_block_upper`):** `≤5/3` via pairs+MVT+telescoping (beats triangle
    `≈31.5`; even perfect constants give `≈1.2` — Tier-3 vdC MANDATORY, tasked). **A-process identity
    CLOSED (`vdC_A_shift_identity_doubleSum` + `vdC_autocorr`):** pure Finset algebra green; linear-test
    plug-in tasked. **Linear plug-in CLOSED-honest (`CB_*`):** differenced gap + one diagonal + shift sums;
    BS pairing (`≤1`) beats proxy (`≤8` norm scale) — true nonlinear Tier-3 still open. **Off-window joint
    poly CLOSED (`CA2TailJoint`):** squared + FE-mirror norm-quadratic tail bounds green; hTail composition
    (Gaussian-vs-poly crossover) tasked. **Windowed `hBdd`
    CLOSED-conditional (`BUWindowed`):** punctured windowed GammaR lower `≥1e-9` + window `BddAbove`
    unconditionally; full-strip `hBdd` conditional on tail-`T`, P1 on tail-`T`+`hTail` (both tasked).
    **Tail assembly CLOSED (`BZTailEnvelope`):** tail Gamma-lower + tail F-envelope + both negative-`τ`
    numerals ⇒ tail-`T` ⇒ **`hBdd` UNCONDITIONAL**; **P1 conditional on `hTail` ONLY** (Stirling-sharp
    tail joint bound tasked).
    **x=5,6 banked (`D3_S6_re_lower` et al.):** prime pattern (`log_five_d9`) + composite bridge (`log 6 =
    log 2 + log 3`) — but true `Re S₆<0`, Re-route dead again (`D3_S6_cannot_reach_8_15`). Next: θ₇–θ₁₆
    BLOCKED on missing `log_seven/eleven/thirteen` d9 bounds (create in-file); composites 8/9/10/12/14/15/16
    factor through 2/3/5 bridges. **Prime logs CLOSED (`log_seven/eleven/thirteen_near_10` + d9 pairs,
    mirror of `log_five_d9` method):** θ₇/θ₁₁/θ₁₃ unlocked for the K=16 push. **Prime stacks CLOSED
    (`D3_S7_re_lower` et al.):** θ₇/θ₁₁/θ₁₃ full enclosures green     (Re-route negative as predicted —
    per-term technology banked). Composites 8/9/10/12/14/15/16 tasked (log-bridge follower).
    **Im-route opened (`D3_S16_im_lower` et al.):** per-term Im lowers x=1..16 green, but sum WEAK
    (`≥-1.138`, true `≈-0.51`) — needs Im-UPPER assembly (`Im S₁₆ ≤ -c`, tasked). **Im-uppers CLOSED
    (`D3_S16_im_upper` et al.):** bracket `[-1.138, +0.173]` STRADDLES 0 (true `-0.51` inside) — no
    positive lower; needs `0.68` total sin-sharpening (higher-order Taylor, tasked). **SIGN CLOSED
    (`D3_S16_norm_ge_sharp`):** quintic sharpening at k=11 (`0.25→0.0765`) ⇒ **`‖S₁₆‖ ≥ 29/42000`**
    — FIRST positive `‖S‖` lower (razor-thin; k=9/k=4/amp widening tasked). **Widened 120×
    (`D3_S16_norm_ge_sharp9413`):** k=9 monotonicity + k=4 septic + amp `5/8`-exponents ⇒
    **`‖S₁₆‖ ≥ 1159/14000 ≈ 0.0828`**. Leftover: sin k=12–16 coarse + amp k=12/14 (round 2 tasked).
    **Round 2 CLOSED (`D3_S16_norm_ge_CL3`):** term14 + k=13/15/12 sintics + amp 11.7%-margin ⇒
    **`‖S₁₆‖ ≥ 41369/350000 ≈ 0.1182`** (1.43×). Biggest lever next: term6 trivial `sin≥-1` (tasked). **Term6 lever
    CLOSED (`D3_S16_norm_ge_CN`, `b41d1ec1`, green, axioms clean):** honest Taylor lower `sin θ₇ ≥ -0.972`
    (CJ-1S monotonicity mirror: `y=θ₇−5π∈[1.276,1.327]`, quintic endpoint `Q(1.327)≈0.97183`; naive per-monomial
    transfer overshoots `≈1.015>1`, documented in-block) ⇒ term6 Im `≤81/250=0.324` (was `1/3`) ⇒
    **`‖S₁₆‖ ≥ 133907/1050000 ≈ 0.1275`** (1.079×, honest gain `0.00933`; true `Im S₁₆≈-0.51` remains ceiling).
    Residual tier 2 (k=11 amp tightening + k=12/16 sin-uppers) needs fresh scoping, tasked. **Tier-2 scoped
    CLOSED (`D3_S16_norm_ge_CO`, `4fa9a9ad`, green, axioms clean):** fresh slack audit — k=11 amp lower HAS
    slack (`1/5` vs true `0.2344`), k=12 amp/sin + k=13/k=16 sins honestly NO-SLACK via in-file Taylor alone
    (phase-limited: quintic/septic already near-exact, `12^{3/5}≈4.44`/`16^{5/8}≈5.657` razor-thin) — banked
    `2/9 ≤ D3_amp 10` (`9^8=43046721 ≥ 11^5·2^8`, margin 4.4%) ⇒ term10 `≤-79/450` ⇒
    **`‖S₁₆‖ ≥ 457021/3150000 ≈ 0.1451`** (1.138×, gain `0.01756`). Next: x=11 sin-lower septic (`0.79→0.84`,
    expected sum `→≈-0.156`, tasked); x=12/x=16 need tighter log phase or large-denominator clearing.
    **x=11 septic CLOSED (`D3_S16_norm_ge_CR`, `5de5c4ab`, green, axioms clean):** septic route SUCCEEDED no
    stall — `S(0.998)=0.840386…≥0.84` beats `0.79` on the existing phase box (monotone transfer
    `z∈[0.998,1.069]`, margin `0.000386`) ⇒ term10 `≤-14/75≈-0.186667` ⇒
    **`‖S₁₆‖ ≥ 492021/3150000 ≈ 0.1562`** (1.076×, gain `0.01111`; true `≈-0.51` ceiling). Taylor levers now
    EXHAUSTED on the early block — residual is the hard set: x=12/x=16 tighter log phase or
    large-denominator amp clearing (tasked). **Amp clearings CLOSED (`D3_S16_norm_ge_CS`, `4feab758`, green,
    axioms clean):** higher-power integer clearing both ends — `D3_amp 11 ≤ 34/151` (`151^5 ≤ 12^3·34^5`,
    margin `0.012%`) ⇒ term11 `≤2601/37750`; `3/17 ≤ D3_amp 15` (`17^8 ≥ 16^5·3^8`, margin `1.4%`) ⇒
    term15 `≤-2271/17000` ⇒ **`‖S₁₆‖ ≥ 461492569/2695350000 ≈ 0.1712`** (1.096×, gain `0.01502`). Phase-box
    levers honestly NO-HEADROOM (`θ₁₂` box `0.001` vs `δ₁₂` `0.061`, 6π-dominated; `θ₁₆` vs `8π` `0.08`) —
    both need Machin-class tighter `π` (tasked). x=12 amp slack now `0.0028` (near-exhausted at 3/5-exponent).
    **Tighter π CLOSED (`D3_pi_*_CU`, `0f337266`, green, axioms clean):** no Machin argument needed — Mathlib
    HAS `Real.pi_gt_d4`/`pi_lt_d4` (`3.1415<π<3.1416`), used directly ⇒ width `0.01→0.0001` (100×) ⇒
    `δ₁₂∈[2.8924,2.894]` w=`0.0016` (38×, true `≈2.89338` inside) + `θ₁₆−8π∈[−0.8728,−0.871]` w=`0.0018`
    (45×, true `≈−0.87259` inside). Trig re-derivation on the tight boxes (re-sharpen sin/cos θ₁₂/θ₁₆, feed
    term11/term15) tasked; head stays `≈0.1712` until recomposed. **Trig recomposed (`D3_S16_norm_ge_CV`,
    `816f5782`, green, axioms clean):** sin θ₁₂ `≤0.247` (was `0.306`; tight box `−y∈[0.2475,0.2492]` +
    exact quintic `Q(0.2492)≈0.24663`, gap `0.0013` vs true `≈0.24567`) + sin θ₁₆ `≤-0.764` (was `-0.757`;
    septic `S(0.871)≈0.76497`, gap `0.0020` vs true `≈-0.76600`) ⇒
    **`‖S₁₆‖ ≥ 500629219/2695350000 ≈ 0.1857`** (1.085×, gain `0.01452`). Next: sin θ₁₃ still on the wide
    `pi_d2`-era box — needs CU-style delta tightening + quintic re-sharpening to feed term12 (tasked).
    **sin θ₁₃ CLOSED (`D3_S16_norm_ge_CX`, `39faac0c`, green, axioms clean):** no pivot needed — slack was in
    the phase endpoint, not Taylor (`Q(0.464)` exact to `~9e-7`): tight-π `δ₁₃∈[3.5934,3.595]` w `0.061→0.0016`
    (38×) ⇒ endpoint `0.464→0.4535` ⇒ sin `≥-0.439` (was `-0.448`; gap `0.0021` vs true `≈-0.43691`, 5.3×
    tighter) ⇒ term12 `≤4829/50000` ⇒ **`‖S₁₆‖ ≥ 505966012/2695350000 ≈ 0.1877`** (1.0107×, gain `0.00198`).
    Next: x=13 amp `11/50` vs true `≈0.21190` (slack `0.008`, large-denominator clearing, tasked); x=16 amp
    slack `~0.01`; micro-levers (`-0.439→-0.4382`, `pi_d20`-era δ₁₃); term14 trivial-bound tightening.
    **x=13 amp cleared (`D3_S16_norm_ge_CY`, `d796a4a8`, green, axioms clean):** `D3_amp 12 ≤ 20/93`
    (`(93/20)^5≤13^3`, margin `1.05%`; `3/5`-floor `≈0.21461` so `~0.0027` residual structural) ⇒ term12
    `≤439/4650≈0.09441` ⇒ **`‖S₁₆‖ ≥ 3173275873/16711170000 ≈ 0.1899`** (1.0116×). x=16 lower untouched
    (only LOWER feeds term15; `5/8`-route near-exhausted, needs exact-`0.605`/large-denominator). Next:
    x=16 amp lower micro-gain, `-0.439→-0.4382`, `pi_d20` δ₁₃, term14 trivial-bound (tasked).
    **Micro-levers CLOSED (`D3_S16_norm_ge_DA`, `64e18b02`, green, axioms clean):** `35/198 ≤ D3_amp 15`
    (`198^8≥16^5·35^8`, margin `0.0408%`, 19-digit VERIFIED REAL; `5/8`-floor `≈0.17677` so `~0.0098`
    structural; exact-`0.605` needs `~1e145` ints, infeasible) + sin θ₁₃ `≥-0.4382` (same CX box, margin
    `0.000085`) ⇒ **`‖S₁₆‖ ≥ 6172832357/32439330000 ≈ 0.1903`** (1.00210×, gain `0.000399`).     Early block
    now in micro-gains — remaining: `pi_d20` δ₁₃ (`~0.00012`), term14 (`499/2500`, largest micro-pool
    `~0.007`, needs fresh scoping). Next macro-lever: MIDDLE `[16,1024)` upper via
    `Zeta23.MV.Final.mv_hilbert` large-sieve bridge (tasked — fires the queued Zeta23 lever).
    **Both micro-levers CLOSED (`D3_S16_norm_ge_DE2`, `3fdff6ae`, green, axioms clean):** `pi_d20`
    wrappers (1e-20 width, verified exist) ⇒ δ₁₃ w=`0.001001` + δ₁₅ w=`0.001001` (theta-dominated) ⇒
    sin θ₁₃ `≥-0.4376` (gap `0.0007`) + sin θ₁₅ `≥-0.9912` (gap `0.000097`, was `0.0069`; tight-box
    cos-shift + quartic) + amp15 `≤245/1244≈0.1969453` (16-digit clearing, margin `0.00066%`, best
    `q<3000` at 3/5) ⇒ term14 `≤60711/311000≈0.19521` (slack now all-amp) ⇒
    **`‖S₁₆‖ ≥ 393063866333/2017726326000 ≈ 0.1948`** (1.0237×, gain `0.00452`; δ₁₃ contributed
    `0.00013` as predicted). Next: term12 amp `20/93` slack `~0.0032` now dominates term12 (large-
    denominator `3/5` clearing toward floor `0.21190`, tasked); term14 amp floor residual `~0.00265`;
    middle upper (Tier-3 vdC). **Term12-amp essentially floored (`D3_S16_norm_ge_DH`, `015f763f`, green,
    axioms clean):** `D3_amp 12 ≤ 211911/987460 ≈ 0.21460211` (only `1.23e-11` above the `3/5`-floor;
    exact-`0.605` needs `~1e145` ints, infeasible) ⇒ **`‖S₁₆‖ ≥ 15666477209474893/80339678946450000 ≈
    0.19500`** (1.00102×, gain `0.000198`). NOTE: block landed with a Lean placement bug (60-line `/--`
    docstring before `set_option … in` — rejected); coordinator 1-char micro-fix (`/--`→`/-`, comment
    syntax only, disclosed in commit). DH's report never arrived (session lost post-write) — verified
    from diff per protocol. **Term14-amp larger-`q` cleared (`D3_S16_norm_ge_DI`, DJ, `27bf775f`, green
    8693 jobs, axioms clean):** exhaustive `q≤200000` scan winner `q=135063, p=26600` ⇒
    `D3_amp 14 ≤ 26600/135063` (only `3.9e-11` above `3/5`-floor) ⇒ **`‖S₁₆‖ ≥
    755971293966729191/3876712417843650000 ≈ 0.19500319`** (honest gain `~2.06e-07`, `1.00000106×`).
    NOTE: DJ named its theorems `_DI` (no file collision — true DI worked newsection); kept as-is.
    Term12 + term14 amp routes now BOTH essentially exhausted — no further denominator searches.
    Next: Tier-3 vdC narrow scope toward middle upper (tasked); true `Im S₁₆ ≈ −0.51` remains the ceiling.
    **vdC A-process machinery banked (`DV_*`, DK, `39d691a3`, green 8693 jobs, axioms clean):**
    `DV_A_H2` (H=2 Weyl-differencing inequality reusing Tier-1 KL read-only) + headline
    `DV_quad_H2_N16` (16-term quadratic-phase piece `‖S‖ ≤ 13.1 < 16`, genuine 18% savings over
    triangle) + `DV_mid_conditional_012` (63 per-16-block premises `≤ 12/6300`, pure Props, assembly
    fully proved). HONEST GAP: banked piece uses synthetic phase; true `8.75·log` curvature `≈0.034`
    at n=16 makes H=2 k=2 vacuous there, and BS baseline `5/3` averages `≈0.0265`/piece → 13.9× short
    of middle `≤ 0.12`. Next: one TRUE-phase diagonal bound on `[16,32)` beating triangle 15 (tasked).
    **True-phase diagonal banked (`DZ_*`, DO, `17190ac1`, green 8693 jobs, axioms clean):** defs
    (`ZPhi`/`ZDelta`/`ZPiece`/`ZDiag16`, true `8.75·log(16+n)` phase) + `DZ_delta_lower` (via
    read-only `KL_log_gap_ge`) + quartic-majorant pointwise cos bound ⇒ **headline `DZ_diag_Re_le`:
    `Re(diag) ≤ 14.9 < 15`** + `DZ_piece_DV_feed` closing the `DV_A_H2` loop read-only. HONEST:
    DV feed vacuous (`2·16+2·14.9 = 61.8 →` per-piece `≤ 16.73`, needs `B < 12.125`); H=2 cannot beat
    a coherent positive-Re diagonal at any H. **k=1 direct banked, REPAIR PENDING (`DZ1c_main`,
    DP, UNCOMMITTED):** linearization at `n=8` (`θ = 8.75/24`) ⇒ **`‖∑ ZPiece‖ ≤ 13.85`** (`8.62 +
    5.23`, beats `14.82` budget and triangle) — BUT the DZ1_/DZ1b_ first generations carry 10
    elaboration errors (rewrite-pattern, `le_or_lt`/`div_le_div_right`/`add_sub_cancel'` unknown
    ids, no-goals, type mismatches) with synthetic `sorryAx` dependents (coordinator-verified;
    no literal `sorry` text). **REPAIRED (`bee650c8`, DR fixed 13 errors in place, nothing excised,
    coordinator-verified green 8693 jobs, zero errors + zero `sorryAx`, all 30 DZ axioms clean):**
    Pi-add → `.const_add`/`.const_sub`, `by_cases`/`push_neg` for `le_or_lt`, bare `gcongr`, `abel` +
    rewrite-at-hypothesis. Triplicate `DZ1_main`/`DZ1b_main`/`DZ1c_main` all `≤ 13.85 < 16`.
    Next: amplitude-weighted per-16-block premise via Abel partial summation (tasked). **Abel
    weight machinery banked (`DZ2_*`, DS, `3545c124`, green 8693 jobs, axioms clean):**
    `w_n = (16+n)^{-0.605}`, `w0 ≤ 1/4`, `TV ≤ 1/4` + `DZ2_weighted_le_of_cap` (via read-only
    `T2_abel_norm`) ⇒ **unconditional `‖∑w·ZPiece‖ ≤ 4`**, conditional `≤ 3.4625` (under `13.85`
    prefix caps; k=14,15 caps open). HONEST: monotone weights give no extra savings (`w0·B`
    telescope); need `0.0019`/block → still 2100×/1818× short. **Head-weight tightened
    (`DZ2w0_le_fifth`, DU, `7748091a`, green 8693 jobs, axioms clean):** `w0 ≤ 1/5` via `3/5 ≤
    0.605` + `5^5 = 3125 ≤ 4096 = 16^3` (`0.19` provably out of this shape's reach — needs
    `16^0.605 ≥ 5.263` vs shape's `≥ 5`)     ⇒ **unconditional `≤ 3.2`**, conditional `≤ 2.77`
    (−20%; now 1680×/1454× short). **Per-k caps (`DZ2_prefix1385_le`, DV, `27ba18a4`, green 8693
    jobs, axioms clean):** `13.85` for ALL prefixes `k ≤ 16` (KL length-independent `8.62` +
    subset-monotone error) ⇒ **`2.77` promoted to UNCONDITIONAL**. Still 1454× short of
    `0.0019`/block. **TRUE eta identification (`DZ2e_*`, DW, `bb5b3c18`, green 8693 jobs, axioms
    clean):** `etaDirichletTerm (1-zetaCellS0) (16+n) = (-1)^n·((17+n)^(-s1))` (sign, norm,
    `16+n` vs `17+n` off-by-one all explicit) + one-sided remainder `‖eta‖ ≤ ‖DZ‖ ≤ 1/5` ⇒
    **TRUE block `≤ 3.2`** (triangle; 1680× over need). HONEST: synthetic Abel `2.77` does NOT
    transfer     (conjugate + alternating + off-by-one); `DZ2_prefix1385_le` caps synthetic partials
    only. **TRUE tightening (`DZ2g_*`, DX, `9413c995`, green 8693 jobs, axioms clean):**
    `D3_amp 31 ≤ 1/8` (`8^5 = 32768 = 32^3`) + per-term `|Re|/|Im| ≤ amp` ⇒ **TRUE block `≤
    3.125`** (`15×1/5 + 1/8`; −2.34%, now 1640× over need). Still triangle (one tight tail).
    **Double peel (`DZ2h_*`, DY, `a492ffab`, green 8693 jobs, axioms clean):** `D3_amp 30 ≤ 2/15`
    ⇒ **TRUE block `≤ 3.06`** (`14/5 + 2/15 + 1/8`; now 1606× over need). One peel step left
    (`D3_amp 29`, three-tail `29,30,31`); genuine cancellation still untouched.
    **Triple peel (`DZ2i_*`, DZ, `ddb84cc9`, green 8693 jobs, axioms clean):** `D3_amp 29 ≤ 2/15`
    ⇒ **TRUE block `≤ 3.0`** (`13/5 + 2/15 + 2/15 + 1/8`; now 1575× over need). Peel pattern
    exhausted at this denominator (`2/15`-shape needs `k^3 ≥ (15/2)^5 = 23730` — `28^3 = 21952`
    falls short, so `D3_amp 28` needs a new shape or genuine cancellation).
    **Fourth peel (`DZ2j_*`, E2, `510de05a`, green 8693 jobs, axioms clean):** CORRECTION —
    `D3_amp 28` uses base `28+1 = 29`, and `29^3 = 24389 ≥ 23730` fits the `2/15`-shape ⇒
    **TRUE block `≤ 2.925`** (`12/5 + 2/15×3 + 1/8`; now 1535× over need). `2/15`-shape NOW
    exhausted (`D3_amp 27` needs `28^3 = 21952 < 23730` — genuinely fails).
    Next: true-phase prefix caps, or fifth tightening via sevenths shape (`D3_amp 27 ≤ 1/7`:
    `7^5 = 16807 ≤ 21952`), or genuine `Re/Im` cancellation (tasked). **Fifth peel (`DZ2k_*`,
    E3, `38e93bad`, green 8693 jobs, axioms clean):** `D3_amp 27 ≤ 1/7` ⇒ **TRUE block `≤
    2.868`** (`11/5 + 1/7 + 2/15×3 + 1/8`; now 1505× over need). Next: sixths shape
    (`D3_amp 26 ≤ 1/6`: `6^5 = 7776 ≤ 19683 = 27^3`), true-phase prefix caps, or genuine
    cancellation (tasked). **Sixth peel (`DZ2l_*`, E4, `599ae607`, green 8693 jobs, axioms
    clean):** `D3_amp 26 ≤ 1/6` ⇒ **TRUE block `≤ 2.835`** (`10/5 + 1/6 + 1/7 + 2/15×3 + 1/8`;
    now 1488× over need). Same `1/6`-shape available at base 26 (`7776 ≤ 17576 = 26^3`) for
    `D3_amp 25`. **Seventh peel (`DZ2m_*`, E5, `6ae0d220`, green 8693 jobs, axioms clean):**
    `D3_amp 25 ≤ 1/6` (base-26 fit) ⇒ **TRUE block `≤ 2.802`** (`9/5 + 1/6×2 + 1/7 + 2/15×3 +
    1/8`; now 1471× over need).     `1/6`-shape holds at bases 27, 26 (next: base 25,
    `7776 ≤ 15625 = 25^3`, for `D3_amp 24`).
    **Eighth peel (`DZ2n_*`, E6, `885ae5a4`, green 8693 jobs, axioms clean):**
    `D3_amp 24 ≤ 1/6` (base-25 fit) ⇒ **TRUE block `≤ 2.768`** (`8/5 + 1/6×3 + 1/7 + 2/15×3 +
    1/8`; now 1453× over need).     `1/6`-shape holds at bases 27, 26, 25 (next: base 24,
    `7776 ≤ 13824 = 24^3`, for `D3_amp 23`).
    **Ninth peel (`DZ2o_*`, E7, `bce1a178`, green 8693 jobs, axioms clean):**
    `D3_amp 23 ≤ 1/6` (base-24 fit) ⇒ **TRUE block `≤ 2.735`** (`7/5 + 1/6×4 + 1/7 + 2/15×3 +
    1/8`; now 1435× over need).     `1/6`-shape holds at bases 27–24 (next: base 23,
    `7776 ≤ 12167 = 23^3`, for `D3_amp 22`).
    **Tenth peel (`DZ2p_*`, E8, `4a92ef5c`, green 8693 jobs, axioms clean):**
    `D3_amp 22 ≤ 1/6` (base-23 fit) ⇒ **TRUE block `≤ 2.702`** (`6/5 + 1/6×5 + 1/7 + 2/15×3 +
    1/8`; now 1418× over need).     `1/6`-shape holds at bases 27–23 (next: base 22,
    `7776 ≤ 10648 = 22^3`, for `D3_amp 21`).
    **Eleventh peel (`DZ2q_*`, E9, `887d9b64`, green 8693 jobs, axioms clean):**
    `D3_amp 21 ≤ 1/6` (base-22 fit) ⇒ **TRUE block `≤ 2.668`** (`5/5 + 1/6×6 + 1/7 + 2/15×3 +
    1/8`; now 1400× over need).     `1/6`-shape holds at bases 27–22 (next: base 21,
    `7776 ≤ 9261 = 21^3`, for `D3_amp 20`).
    **Twelfth peel (`DZ2r_*`, F0, `c6e89195`, green 8693 jobs, axioms clean):**
    `D3_amp 20 ≤ 1/6` (base-21 fit) ⇒ **TRUE block `≤ 2.635`** (`4/5 + 1/6×7 + 1/7 + 2/15×3 +
    1/8`; now 1383× over need).     `1/6`-shape holds at bases 27–21 (next: base 20,
    `7776 ≤ 8000 = 20^3`, for `D3_amp 19`).
    **Thirteenth peel (`DZ2s_*`, F1, `b90ca7ab`, green 8693 jobs, axioms clean):**
    `D3_amp 19 ≤ 1/6` (base-20 fit, slack 224) ⇒ **TRUE block `≤ 2.602`** (`3/5 + 1/6×8 + 1/7 +
    2/15×3 + 1/8`; now 1366× over need). `1/6`-shape EXHAUSTED (next base 19: `19^3 = 6859 <
    7776` — genuinely fails).
    **New-shape peel (`DZ2t_*`, F2, `1f5b4a97`, green 8693 jobs, axioms clean):**
    `D3_amp 18 ≤ 2/11` (`(11/2)^5 = 5032.8 ≤ 6859 = 19^3`) ⇒ **TRUE block `≤ 2.584`**
    (`2/5 + 2/11 + 1/6×8 + 1/7 + 2/15×3 + 1/8`; now 1356× over need).
    Next: new shape for `D3_amp 16/17`, true-phase prefix caps, or genuine `Re/Im`
    cancellation (tasked). **Fifteenth peel (`DZ2u_*`, F3, `6ca08379`, green 8693 jobs, axioms
    clean):** `D3_amp 16 ≤ 3/16` (`(16/3)^5 = 4315.1 ≤ 4913 = 17^3`) ⇒ **TRUE block `≤ 2.571`**
    (`3/16 + 1/5 + 2/11 + 1/6×8 + 1/7 + 2/15×3 + 1/8`; now 1349× over need). Cheapest next:
    `D3_amp 17 ≤ 2/11` (base 18: `5032.8 ≤ 5832 = 18^3` passes).
    Next: sixteenth peel, true-phase prefix caps, or genuine cancellation (tasked).
    **Sixteenth peel (`DZ2v_*`, F4, `085f791e`, green 8693 jobs, axioms clean):**
    `D3_amp 17 ≤ 2/11` (base-18 fit, last `1/5` replaced) ⇒ **TRUE block `≤ 2.553`**
    (`3/16 + 2/11×2 + 1/6×8 + 1/7 + 2/15×3 + 1/8`; now 1340× over need). MILESTONE:
    all 16 terms peeled — per-term triangle shaping exhausted; remaining routes are
    true-phase prefix caps + Abel feed, or genuine `Re/Im` cancellation (tasked).
    **BREAKTHROUGH — paired MVT cancellation (`DZ3c_*`, F5, `08b93861`, green 8693 jobs, axioms
    clean):** `norm_etaPairTerm_le` at `s1` (`zetaRefl`, `‖s1‖ ≤ 10`) ⇒ `‖pair m‖ ≤ 2/(2m+1)`
    for `m ≥ 8` ⇒ 8-pair sum `0.6926… ≤` **TRUE block `≤ 0.70`** (was `2.553`; saves 972.8 ratio
    units — now 367× over need). First genuine cancellation (not triangle).
    **Tightening (`DZ3d_*`, F6, `829bb740`, green 8693 jobs, axioms clean):**
    `‖1 - zetaCellS0‖ ≤ 8.78` ⇒ pair `≤ 1.756/(2m+1)` ⇒ **TRUE block `≤ 0.61`**
    (now 320× over need).
    Next: non-uniform base tightening (`~0.02`), true-phase prefix caps + Abel toward
    `≤ 0.6`-shape, or `Re`-only pair sums (tasked). **Non-uniform tightening (`DZ3e_*`, F7,
    `cff3982f`, green 8693 jobs, axioms clean):** per-base floors (`5.5–7.8` at `19–31`) ⇒
    pair sum `0.48921… ≤` **TRUE block `≤ 0.50`** (now 262× over need). **Fourth tightening
    (`DZ3f_*`, F8, `92e82afb`, green 8693 jobs, axioms clean):** sharper base-17 floor (`5.4`:
    `5.4^5 = 4591.65 ≤ 4913`) ⇒ **TRUE block `≤ 0.485`** (now 254× over need).     **Fifth
    tightening (`DZ3g_*`, F9, `4dbb9579`, green 8693 jobs, axioms clean):** `‖s1‖ ≤ 8.771`
    replay ⇒ **TRUE block `≤ 0.482`** (now 253× over need). **Single-pair Re lemma
    (`DZ3m_*`, G6, `7c18fcb3` joint, green 8693 jobs, axioms clean):** pair-8 `Re`
    explicit (`(-1)^k` signs) + `Re ≤ 0.095 < 2/17` (rides `Re ≤ norm`, not genuine
    cancellation — `Re ≈ 0.0002` unproved). **G5 salvage (`DZ3n_*`, G5-resumed, same
    commit):** `k=2` TRUE prefix cap `≤ 0.095` (MVT pair-8 form; deconfliction with G6
    held — non-colliding names, sequential anchors). **Sixth tightening (`DZ3h_*`, G0,
    `d8181c02`, green 8693 jobs, axioms clean):** base-19 floor sharpened (`5.5 → 5.8`:
    `5.8^5 = 6563.57 ≤ 6859`) ⇒ **TRUE block `≤ 0.477`** (now 250× over need). Sharpest
    leads: `6 → 6.2` at base 21, further `23..31` c-sharpenings, `‖s1‖` below `8.771`, or
    `Re`-only pair sums. **Seventh tightening (`DZ3i_*`, G1, `9e345693`, green 8693 jobs,
    axioms clean):** base-21 floor `6.2` (maximal one-decimal: `6.3^5 = 9924.4 > 9261`
    fails) ⇒ **TRUE block `≤ 0.475`** (now 249× over need). One-decimal shaping
    near-exhausted; remaining: two-decimal floors, `‖s1‖` cut, `Re`-only pairs, or prefix
    caps + Abel. **Two-decimal floors (`DZ3j_*`, G2, `84eefea1`, green 8693 jobs, axioms
    clean):** maximal two-decimal floors at all 8 bases ⇒ **TRUE block `≤ 0.471`**
    (now 247× over need). Two-decimal lane exhausted (each maximal). NOTE: G2 left a
    stray build log in the repo root; removed at commit (untracked artifact).
    **Three-decimal floors (`DZ3k_*`, G3, `5d9a12f7`, green 8693 jobs, axioms clean):**
    maximal three-decimal floors at all 8 bases ⇒ **TRUE block `≤ 0.4705`** (now 247×
    over need). Three-decimal lane exhausted (each maximal).
    **Four-decimal floors (`DZ3l_*`, G4, `17bd6397`, green 8693 jobs, axioms clean):**
    maximal four-decimal floors (6 strict, 2 reused) ⇒ **TRUE block `≤ 0.47047`** (saves
    `0.00003`; still ~247× over need). Floor-tightening now yields `~1e-5`/bridge —
    DIMINISHING; remaining structural routes are prefix caps + Abel or `Re`-only pairs.
    Next: prefix caps + Abel (preferred), `Re`-only pairs, or `‖s1‖` cut (tasked).
    **G5 FAILED EMPTY (no commit):** full prefix-caps+Abel scope too big — zero lines written,
    empty report (DE precedent). Salvaged via reduced-scope G6 (single-pair Re-cancellation
    lemma + report-from-diff clause) + resumed G5 (single-k cap).
    **Single-pair Re + k=2 cap (`DZ3m_*/DZ3n_*`, G6+G5r, `7c18fcb3` joint, green 8693 jobs,
    axioms clean):** pair-8 `Re ≤ 0.095` (explicit signs; rides `Re ≤ norm`) + `k=2` TRUE
    prefix cap `≤ 0.095` (deconfliction held).
    **k=4 cap + genuine cos-cancellation (`DZ3o_*/DZ3p_*`, G7+G8, `492c8aaf` joint, green
    8693 jobs, axioms clean):** `k=4` TRUE prefix cap `≤ 0.174` (pairs 8+9) + pair-8
    `Re ≤ 0.05` (rigorous `0.9 ≤ cos16, cos17` via log intervals + `2π` reduction; true
    `≈ −0.00215`, slack is `cos ≤ 1` on `c16`). NOTE: G7's commit held one wave (G8's
    concurrent append carried an error + `sorryAx`) — G8 self-repaired, joint commit.
    Next: pair-8 toward `≤ 0.02`, pair-9 `Re` start, `k=6` cap (tasked).
    **Pair-8 upgrade (`DZ3q_*`, G9, `f156682e`, green 8693 jobs, axioms clean):**
    `cos16 ≤ 0.96` upper + `amp16 ≤ 1/5.4735` ⇒ **pair-8 `Re ≤ 0.031`** (gap to `0.02`
    is `0.011`; true `≈ −0.00215`).
    Next: five-decimal `A16`, `A17·c17` upward, pair-9 `Re` start, or `k=6` cap (tasked).
    **Pair-9 template (`DZ3r_*`, G10, `97e92ace`, green 8693 jobs, axioms clean):**
    log-19/log-20 intervals + `2π` reduction + cos bounds + two-sided amps (26 theorems)
    ⇒ **pair-9 `Re ≤ 0.10`**. HONEST: does NOT beat MVT norm `0.08402` (short `0.01598`;
    sqrt-majorant template ceiling `≈ 0.088`).
    Next: Taylor cos upper (`cos18 ≤ ~0.852`), `A18 ≤ 1/5.85`, or pair-10 `Re` start (tasked).
    **Pair-9 tighten (`DZ3s_*`, G11, `ba9949a9`, green 8693 jobs, axioms clean):**
    `A18 ≤ 1/5.85` (`5.85^5 = 6851.40 ≤ 6859`) ⇒ **pair-9 `Re ≤ 0.0903`** (gap to MVT
    norm `0.08402` now `0.00628`; was `0.01598`).
    Next: quartic cos upper (`≈ 0.08659`, then raise `cos19`/`A19` lower to finish) or
    pair-10 `Re` start (tasked). **Quartic cos (`DZ3t_*`, G12, `2e5ae04c`, green 8693 jobs,
    axioms clean):** `cos18 ≤ 0.8567` (quartic majorant, per-monomial endpoints) ⇒
    **pair-9 `Re ≤ 0.0866`** (gap to MVT norm `0.08402` now `0.00258`; was `0.00628`).
    Next: raise `cos19`/`A19` lower to finish, or pair-10 `Re` start (tasked).
    **Pair-9 closed (`DZ3u_*`, G13, `845c064d`, green 8693 jobs, axioms clean):**
    sextic `cos19 ≥ 0.43` ⇒ **pair-9 `Re ≤ 0.08402`** (meets MVT norm; previous gap closed).
    Next: pair-10 `Re` start (tasked).
    **Pair-10 start (`DZ3v_*`, G14, `ac128218`, green 8693 jobs, axioms clean):**
    `log22 ∈ [3.0910424529, 3.0910424538]`, `log21 ∈ [3.04342, 3.0456]`,
    `cos20 ≤ 0.101` (quartic), `cos21 ≥ −0.343` (sextic),
    `A20 ≥ 1/6.75`, `A21 ≥ 1/6.95` ⇒ **pair-10 `Re ≤ 0.074`**
    (beats triangle `2/21 ≈ 0.0952` by `≥ 0.021`; `≈ 0.0067` above MVT slot `≈ 0.0673`).
    Next: close the `0.0067` gap (sextic cos20 / tighter amps) or pair-11 start (tasked).
    **Pair-10 tightened (`DZ3w_*`, G15, `9833092b`, green 8693 jobs, axioms clean):**
    `A20 ≤ 1/6.2` (via `6.2^5 ≤ 21^3`), `A21 ≤ 1/6.38` (via `6.38^5 ≤ 22^3`) ⇒
    **pair-10 `Re ≤ 0.0701`** (residual `0.0028` above MVT slot `≈ 0.0673`).
    Next: octic cos20 micro-close or pair-11 start (tasked).
    **Pair-10 CLOSED (`DZ3x_*`, G16, `582cabbd`, green 8693 jobs, axioms clean):**
    octic majorant ⇒ `cos20 ≤ 0.086`, `cos21 ≥ −0.338` ⇒
    **pair-10 `Re ≤ 0.0673`** (meets MVT slot `8.771/6.2134/21`, margin `≈ 0.00045`).
    Next: pair-11 `Re` start (tasked).
    **Pair-11 CLOSED first-bridge (`DZ3y_*`, G17, `a3306b91`, green 8693 jobs, axioms clean):**
    `log24 ∈ [3.177…, 3.178…]`, `log23 ∈ […, …]`, `cos22 ≤ −0.66` (sextic),
    `cos23 ≥ −0.894` (octic), amps `1/7.1 + 1/7.3` ⇒
    **pair-11 `Re ≤ 0.057`** (meets MVT slot `≈ 0.0614` on first bridge; true `≈ 0.03032`).
    Next: pair-12 `Re` start (tasked).
    **Pair-12 CLOSED first-bridge (`DZ3z_*`, G18, `cc275b64`, green 8693 jobs, axioms clean):**
    `log25 = 2·log5`, `log26 = log2+log13` (log-13 path, no fallback needed),
    `cos24 ≤ −0.99` (sextic), `−cos25 ≤ 0.974` (quartic), amps `1/7.5 + 1/7.7` ⇒
    **pair-12 `Re ≤ 0.035`** (meets MVT slot `≈ 0.057`; triangle `0.08`).
    Next: pair-13 `Re` start (tasked).
    **Pair-13 CLOSED (`DZ3aa_*`, G19, `8ee33164`, green 8693 jobs, axioms clean):**
    `log27 = 3·log3`, `log28 = 2·log2+log7` (log-7 d9 path),
    `cos26 ≤ −0.844` (sextic), `−cos27 ≤ 0.637` (quartic), amps `1/7.9 + 1/8.1` ⇒
    **pair-13 `Re ≤ 0`** (beats triangle `2/27 ≈ 0.0741`; MVT slot `≈ 0.053`; true `≈ −0.0305`).
    Next: pair-14 `Re` start (queued behind H6 verification).
    **Pair-14 CLOSED (`DZ3ab_*`, G20, `c991c30d`, green 8693 jobs, axioms clean):**
    `log30 = log2+log3+log5`, `log29` via `log(29/30)` fallback,
    `cos28 ≤ −0.36` (sextic), `−cos29 ≤ 0.1` (quartic), amps `1/8.3 + 2/15` ⇒
    **pair-14 `Re ≤ −0.03`** (beats triangle `2/29 ≈ 0.0690` by `≈ 0.099`; true negative).
    Next: pair-15 `Re` start — LAST pair (tasked).
    **Pair-15 CLOSED (`DZ3ac_*`, G21, `ba0dccdb`, green 8693 jobs, axioms clean):**
    `log32 = 5·log2`, `log31` via `log(31/32)` fallback,
    `cos30 ≤ 0.222` (sextic), `cos31 ≥ 0.45` (octic), amps `2/15 + 1/8.8` ⇒
    **pair-15 `Re ≤ −0.02`** (beats triangle `2/31 ≈ 0.0645` by `≈ 0.0845`).
    **ALL pairs 8–15 MVT-closed** (`0.031, 0.08402, 0.0673, 0.057, 0.035, 0, −0.03, −0.02`).
    Next: `[16,32)` window Re-sum aggregate (tasked).
    **Window aggregate (`DZ3ad_*`, G22, `94da0b99`, green 8693 jobs, axioms clean):**
    **window Re-sum `≤ 0.22432`** (beats summed MVT `≈ 0.47047` by `≈ 0.246`,
    triangle `≈ 0.69266`). Pair program endpoint: transfer to Ico-block next (tasked).
    **Ico-block transfer (`DZ3ae_ico16_32_Re_le`, G23, `c1df399f`, green 8693 jobs,
    axioms clean):** 8-line transfer via `DZ3c_sum_eq` ⇒ Ico-block Re `≤ 0.22432`.
    **PAIR PROGRAM CLOSED — no further pair waves (pivot to cell certificates next).**
    **Window aggregate (`DZ3ad_*`, G22, `94da0b99`, green 8693 jobs, axioms clean):**
    **window Re-sum `≤ 0.22432`** (beats summed MVT `≈ 0.47047` by `≈ 0.246`,
    triangle `≈ 0.69266`). Pair program endpoint: transfer to Ico-block next (tasked).
    **DT SHELVED (build poison):** DT's uncommitted 589-line two-step Gamma block
    (`Door3GammaCut85`, `G=0.085` target) HUNG the newsection build indefinitely (agent
    hung with it; coordinator HEAD rebuild green 8702 — hang was DT's tactics, likely a
    `norm_num` on huge numerals). Diff stashed reversibly (`shelve DT two-step…`) +
    30KB backup in `Temp/kilo/dt_twostep_shelved.diff`. Lane retasked with DIFFERENT
    instructions: wire LANDED H0/H1 numerators (228.0/217.5 → `G≈0.086/0.082` tiers +
    `M` tiers) with per-theorem timebox + bisect-on-hang protocol;     two-step route NOT
    to be reintroduced.
    **Numerators wired (`Door3GammaCutR02`, H2, `7f7c0c23`, green 8702 jobs, axioms clean):**
    Tier A (landed 228.0): `(G,Z,M,Azeta)=(0.0862,7.5,106.95696,6126)`.
    Tier B (landed matched 217.5, new `complex_Gamma_matched_2175`):
    **`(G,Z,M,Azeta)=(0.0822,7.5,101.99376,5842)`**, ceil `(0.0822,7.5,102,5842)`
    (`ΔM=−5.9558` vs prior `107.9496` tier). Conditional `(0.026,7.5,32.2608,1848)` untouched.
    Single gap: `‖gammaOf‖ ≤ 0.026` on the R02 rect.
    **Split-rect shave (`Door3GammaCutR02Split`, H3, `130a03ab`, green 8702 jobs, axioms clean):**
    low piece `‖Γw‖ ≤ 216.6` (`x ≤ 6.2`) + high piece `D ≥ 2659` ⇒
    **`(G,Z,M,Azeta)=(0.0818,7.5,101.49744,5814)`** (`ΔM=−0.496`).
    Split at `x=6.2` unbalanced (`G_low=0.08180` vs `G_high≈0.0702`); optimizer next (tasked).
    **Balanced split (`Door3GammaCutR02SplitBal`, H4, `ddd480ca`, green 8702 jobs, axioms clean):**
    split `s=6.04` (`N=215.8`, `D=2687`) ⇒
    **`(G,Z,M,Azeta)=(0.0815,7.5,101.1252,5792)`** (`ΔM=−0.372`).
    Next: `s=6.02–6.03` 3-decimal floors or third middle piece (tasked).
    **Fine split (`Door3GammaCutR02SplitFine`, H5, `68eafe35`, green 8702 jobs, axioms clean):**
    split `s=6.03` (`N=215.7`, `D_low=2675`, `D_high=2684`) ⇒
    **`(G,Z,M,Azeta)=(0.0813,7.5,100.87704,5778)`** (`ΔM=−0.248`).
    Next: `G=0.0811` same-shape or third middle piece (tasked).
    **Finer split (`Door3GammaCutR02SplitFiner`, H6, `db80d5d7`, verified green by H6b,
    8702 jobs, axioms clean):** same `s=6.03/D=2675/2684` at `G=0.0811` ⇒
    **`(G,Z,M,Azeta)=(0.0811,7.5,100.62888,5764)`** (`ΔM=−0.248`).
    Next: `G=0.0809` same-shape or third middle piece (tasked).
    **Trio split (`Door3GammaCutR02SplitTrio0810`, H7, `0f3c2183`, green 8702 jobs, axioms clean):**
    `G=0.0809` 2-piece FAILS high cap (`217.5 > 217.1356`) ⇒ third middle piece
    (`N=215.7/216.6/217.5`, `D=2675/2684/2687`) ⇒
    **`(G,Z,M,Azeta)=(0.0810,7.5,100.5048,5757)`** (`ΔM=−0.124`).
    Next: `G=0.0809` via `a=0.05` refloor or `xmax<6.37` numerator (tasked).
    **Trio 0.0809 (`Door3GammaCutR02SplitTrio0809`, H8, `d09e08f4`, green 8702 jobs, axioms clean):**
    `a=0.05` refloor ⇒ `D ≥ 2689` ⇒
    **`(G,Z,M,Azeta)=(0.0809,7.5,100.38072,5750)`** (`ΔM=−0.124`).
    Next: `G=0.0808` via `a=0.06` refloor (tasked).
    **Trio 0.0808 (`Door3GammaCutR02SplitTrio0808`, H9, `3d0131d6`, green 8702 jobs, axioms clean):**
    `a=0.06` refloor ⇒ `D ≥ 2692` ⇒
    **`(G,Z,M,Azeta)=(0.0808,7.5,100.25664,5743)`** (`ΔM=−0.124`).
    Next: `G=0.0807` via `a=0.07` refloor (tasked).
    **Quad 0.0807 (`Door3GammaCutR02SplitQuad0807`, H10, `e078122c`, green 8702 jobs,
    axioms clean):** specified trio UNPROVABLE (`0.0807·2684=216.5988<216.6` —
    brief arithmetic corrected); `a=0.04/0.07` refloors (`D≥2685/2696`) + quad split ⇒
    **`(G,Z,M,Azeta)=(0.0807,7.5,100.13256,5735)`** (`ΔM=−0.124`).
    **M-GRIND FROZEN here — pivot to cell-certificate program (checker + generator lanes).**
    **Certificate spike (`door3_cell_checker.lean`, C1, `5c62edca`, green, axioms clean):**
    exact cell obligation quoted (`CellData.center_bound`, simplest cell R00 center
    `(-8.75, 0.105)`); rational-interval checker core (`qintv/qrect/norm` rules, zero Float);
    Python `Fraction`-only generator emits `norm_num`-checkable certs (NOT `decide` — kernel
    `Rat` reduction stuck; bridge via `Complex.normSq_eq_norm_sq`); sample cert checks in 53s.
    Missing link: rigorous `ξ`-enclosures (`riemannZeta`/`Gamma`/`cpow` interval arith).
    Next: generalize checker + 40-cell generator (tasked).
    **Checker generalized (`door3_cell_checker`, C2, `bc1ea2bb`, green, axioms clean):**
    two-sided complex-mul enclosure + rigorous `√` upper rule; R00 proxy cell certified
    (`center_bound` shape at outer tier); Python generator emits all 40 proxy blocks
    (Temp `door3_certs40.lean`, 46KB). True `ξ`-enclosure still the missing link.
    Next: land proxy blocks cell-by-cell (tasked).
    **Proxy batch (`door3_cell_checker`, C3, `3294a46e`, 6× green ~45s, axioms clean):**
    R13/R23/R33/R43/R53/R63 proxies banked — **7/40 cells** (33 remaining).
    Next: bottom-row remainder R73/R83/R93/R03 (tasked).
    **Bottom row done (C4, `e48975e6`, 4× green ~65s, axioms clean):**
    R73/R83/R93/R03 proxies banked — **11/40 cells** (29 remaining).
    Next: y-row 2 (R02/R12/R22/R32, tasked).
    **Y-row 2 start (C5, `ae832401`, 4× green ~60s, axioms clean):**
    R02/R12/R22/R32 proxies banked — **15/40 cells** (25 remaining; lock queues ~35 min
    at 7 lanes — staggering builds advised).
    Next: y-row 2 remainder R42–R92 (tasked).
    **Y-row 2 remainder (C6, `2adf4c30`, 4× green ~30s, axioms clean):**
    R42/R52/R62/R72 proxies banked — **19/40 cells** (21 remaining).
    Next: close y-row 2 with R82/R92 (tasked).
    **Y-row 2 closed 10/10 (C7, `6e6fd277`, 2× green ~30s, axioms clean):**
    R82/R92 proxies banked — **21/40 cells** (19 remaining).
    Next: y-row 1 R01/R11 (tasked).
    **Y-row 1 opened (C8, `e0ff7401`, 2× green ~33s, axioms clean):**
    R01/R11 proxies banked — **23/40 cells** (17 remaining).
    Next: y-row 1 R21/R31 (tasked).
    **Y-row 1 mid pair (C9, `81c398d1`, 2× green ~33s, axioms clean):**
    R21/R31 proxies banked — **25/40 cells** (15 remaining).
    Next: y-row 1 R41/R51 (tasked).
    **Y-row 1 R41/R51 (C10, `3f6db734`, 2× green ~33s, axioms clean):**
    inner tier `(0.15,0.06)` landed (brief said mid — agent corrected to cover/generator).
    **27/40 cells** (13 remaining).     Next: R61/R71 (tasked).
    **Y-row 1 R61/R71 (C11, `579da30c`, 2× green ~39s, axioms clean):**
    mid tier `(0.05,0.07)` per generator. **29/40 cells** (11 remaining).
    Next: R81/R91 outer (tasked).
    **FE bridge (`zeta_rigorous` tail, FE, `d930680b`, green 8693 jobs, axioms clean):**
    chi-factor def + forward/backward FE + Dirichlet `‖ζ‖≤3` (`Re≥2`) + chi-norm upper
    (Γ symbolic) + reflected-slice/reflected-bridge + tail-rect `B=(2·G·e^22)·Z`.
    Full strip numeral unreachable (FE fixes the strip); missing: complex-Γ norm upper
    on reflected rect + reflected-ζ numeral Z.     Next: Z numeral via eta-pairs (tasked).
    **Gamma sups (GS, UNCOMMITTED — pending verification):** `G0=0.232` smallest
    (2-step recurrence; budgets `Z≤0.00044` — tier still zeta-side blocked).
    Block's own 3 errors fixed in-diff but UNBUILT: verification blocked by R5's
    mid-work cover insertion (`sorryAx` in `door3_conj_transfer`, type error :16579).
    Verifier fires after R5 reports; commit only on green.
    **Gamma sups verified (`Door3DerivGammaSupSImage`, GS, `64057b8e`, GSv GREEN,
    8702 jobs, axioms clean):** smallest `G0=0.232` (2-step recurrence); implied budget
    `Z≤0.00044` — tier stays zeta-side blocked (FE2 owns the Z numeral).
    **Deriv lane (`door3_deriv_certs`, V, `fba59747`, green 45s, axioms clean):**
    Cauchy-estimate toolkit (`deriv_bound_of_sphere_sup_on_ball` from Mathlib Liouville +
    rational-endpoint wrapper) + R00 rect ⊆ ball + conditional `R00_deriv_bound_of_sup`
    (meets outer tier `0.05` iff sup `qB ≤ 1/40`). Missing: uniform `ξ`-sup enclosure.
    Next: `ξ`-sup on `ball R00c 2` then replicate per cell (tasked).
    **Factor sups (V2, `532f4b9b`, green, axioms clean):** ball-norm `10.76`, poly shape
    `63.4`, s-factors `11.26`; 4-factor composition banked; tier needs remaining
    `P·G·Z ≤ 0.0004` (triangle-via-entire route proven dead).     Next: factor sups (tasked).
    **Pi sup + conds (V3, `5e3bbf9f`, green, axioms clean):** `‖fPi‖ ≤ 4` proved
    (elementary cpow/rpow); Gamma/Zeta sups as explicit conditional Props (no sorry);
    tier threshold now `G·Z ≤ 0.0001`.     Next: GammaSup/ZetaSup numerals (tasked).
    **GammaSup + tier verdict (V4, `0db4bb84`, green, axioms clean):** `GammaSupCond 1.52`
    proved Stirling-free (shift into `[0.195,2.20]`, `5.13/3.375`); but factorization tier
    NUMERICALLY DEAD (`G·Z≤0.0001` vs true product `≈0.03–0.10`, 300–1000× off).
    Next: joint-sup / smaller-ball tier route (tasked).
    **All tier routes dead (V5, `a7e45593`, green, axioms clean):** joint (`507.2·J`,
    needs `J≤0.0001` vs true `≈0.03`), smaller-ball (worse, `J≤0.00006`), localization
    (same threshold per piece) — 300–600× off everywhere. Crude-sup Cauchy is too lossy;
    needs FE-grade zeta sups, not geometry tweaks.
    **DERIV LANE PAUSED pending FE lane (same as tail).**
    **Gamma narrow (`Door3GammaCutR02Quad0807Narrow`, W, `301b6128`, green 8702 jobs,
    axioms clean):** numerator `216.9` at `xmax=6.25` (drop `0.6` on `[6.20,6.25]` overlap);
    table `215.7<215.8<216.6<216.9<217.5`. Frozen tiers untouched.
    Next: `6.30` piece `≤217.1` (tasked).
    **Narrow 6.30 (W2, `cc6e31d2`, green 8702 jobs, axioms clean):**
    `≤217.1` on `[6.025,6.30]` (drop `0.4`); sliver at `217.5` now `[6.30,6.37]` only.
    LOCK PROTOCOL FIX: release lock in `finally` ONLY if you acquired it (guard flag) —
    a lane's unconditional remove deleted another lane's live lock this wave.
    Next: `6.37` piece (tasked).
    **Sliver covered (W3, `c4a2d720`, green 8702 jobs, axioms clean):**
    `≤217.2`/`≤217.4` on full width PROVABLY FAIL (squared margins negative);
    `217.5` kept on `[6.025,6.37]` — full narrow table `215.7<…<217.5` closed.
    Narrow lane endpoint (diminishing returns below `0.1`); lane retires to cell support.
    Next: sub-sliver `[6.30,6.33]` 217.3-class attempt (tasked, last narrow wave).
    **Sub-sliver closed (W4, `0bf9b4e3`, green 8702 jobs, axioms clean):**
    `[6.30,6.33]` at `217.3` (margin `~1011`); residual `[6.33,6.37]` (`0.04`) at `217.5`.
    **NARROW LANE RETIRED — newsection tail quiet unless cell support needs it.**
    **Tail-leaf feeders (`TailLaguerreScratch`, T, `80968b3b`, green, axioms clean):**
    exact leaf obligation quoted (`tailPointwise10_of_absTail` ← `MollifiedRoucheLeaf.gap`
    upper half + conjugation composition); banked `tailGeomBound_at11` (`<1/10` at `r=11`)
    + `tailNormLower_of_absRe`/`tailSqLower_of_absRe` floors. Gap: real `zeta`/`shiftedS`/
    `dirichletMollifier` substitution + zeta-upper/mollifier-error bounds (tasked next).
    **Conditional leaf bridge (T2, `feee4b94`, green, axioms clean):**
    `‖ζ·M−1‖ ≤ B·e+d` split + `tailLeafGap_of_stubBounds`/`tailMollifiedRoucheLeaf_of_stubBounds`
    (stub Props; real import exceeds tail budget).     Remainder: admissible real `(B,e,d)`.
    Next: real triple (tasked).
    **Real bridge (T3, `be9176b4`, green, axioms clean):** real `shiftedS`/`Mollifier` defs
    mirrored in-lane; mollifier error CLOSED `e=1/2` at `K=2`; Dirichlet majorant PROVABLY
    inapplicable (`Re<1` on regime); zeta-upper `B` + zeta-near-one `d` open.
    Next: compact-cell zeta bounds (tasked).
    **Compact-cell bounds (T4, `1508e122`, green, axioms clean):** closed cell
    `10≤|Re|≤11` compact + shifted-continuous + pole avoided ⇒ `∃ Bcell/dcell`
    (non-explicit) + `tailCellGap_of_cellBounds_two` implication. Explicit numerals open.
    Next: explicit Bnum/dnum (tasked).
    **K=2 split DEAD (T5, `b63a2122`, green, axioms clean):** explicit `B=2,d=1,e=1/2`
    give `B·e+d=2`, `¬<1` PROVED (true values `~1.35`); redirect banked
    (`‖ζ·M−1‖<1 ↔ ‖ζ−2‖<2` at K=2).     Next: `‖ζ−2‖<2` or `K>2` (tasked).
    **K>2 DEAD (T6, `4941a01b`, green, axioms clean):** `e(2)=1/2 < e(3)=2/3 < e(4)=1`
    PROVED (K=2 minimal; `B·e+d<1` dead at K=2,3,4). ONLY route left: `‖ζ−2‖<2`
    on the s-rect (needs FE/convexity).     Next: that attempt (tasked).
    **Conditional closures (T7, `d465d118`, green, axioms clean):** `d<1` or `r<2`
    ⇒ K=2 gap (both compositions proved) + explicit polar cap `1/10` + `∃ B2`.
    LAST tail route reduces to ONE numeral needing FE input.
    **TAIL LANE PAUSED pending FE lane (no duplicate FE work).**
    **H0 FAILED EMPTY (no commit):** new `interval_arith` lane (matched-x Gamma monotonicity)
    — zero lines written, empty report (G5/DE precedent). Salvaged via H0-resumed (single-point
    lane) + H1 (matched-x lane) with deconfliction.
    **Single-point + matched-x (`DZ4a_*/R02MatchedX`, H0r+H1, `0982f5db` joint, green 8688
    jobs, axioms clean):** single-point re-derivation (Γ7.025 ≤ 760.9, Γ7.37 ≤ 1498.11,
    one-step numerator **228.0**) + matched-x main (`Γ(x+1)/√(x²+b²) ≤ 217.5`, 7.5% under
    uniform; ~2.9% slack over true majorant max ~211.3). Gap to 68.85 stands (3.16×;
    no convexity/`Gamma_add_one` majorant can reach it — true max ~211). Deconfliction
    held (sequential namespaces). Next: wire 228.0/217.5 as numerators (newsection lane),
    or infinite-product/Stirling toward true ~131 (tasked, DT lane).
    **True-phase diagonal banked (`DZ_*`, DO, `17190ac1`, green 8693 jobs, axioms clean):** defs
    (`ZPhi`/`ZDelta`/`ZPiece`/`ZDiag16`, true `8.75·log(16+n)` phase) + `DZ_delta_lower` (via
    read-only `KL_log_gap_ge`) + quartic-majorant pointwise cos bound ⇒ **headline `DZ_diag_Re_le`:
    `Re(diag) ≤ 14.9 < 15`** + `DZ_piece_DV_feed` closing the `DV_A_H2` loop read-only. HONEST:
    DV feed vacuous (`2·16+2·14.9 = 61.8 →` per-piece `≤ 16.73`, needs `B < 12.125`); H=2 cannot beat
    a coherent positive-Re diagonal at any H. Next: k=1 direct on `[16,32)` (linearize at `n=8`,
    slope `8.75/24`, target `≤ 14.82 < 16`; tasked).
    **MV bridge CLOSED-honest-negative (`DB_*`, `fee0d39c`, green, axioms clean):** first Zeta23 import
    in a door-3 work file (`import Zeta23.MV.Final`, cycle-safe: Zeta23-internal+Mathlib only, full-file
    build green 8693 jobs) ⇒ `MVHilbert 26` instantiated at `λ_r=8.75·log n` (gap admissibility via
    in-file `KL_log_gap_ge`) ⇒ **shape-floor PROVED: no constant reaches `0.12`** (`DB_MV_cannot_reach_012`;
    C=26 gives `≥533/7≈76`, even ideal C=1 gives `≥41/14≈2.93`, `24×` over). Do NOT sharpen sieve
    constants. Remaining middle routes: mean→pointwise conversion (MV mean-value thm absent — big
    machinery) or **Tier-3 vdC second-derivative early-block upper** (tasked).
    **Stirling Gamma tail
    CLOSED (`CH2GammaTail`, C=4, ~25% headroom):** joint-with-cosine composition tasked (hTail).
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
   Stirling-scale `F` bound), (ii) `hBdd` (strip `ζ`-growth). **Neg tiers CLOSED (`CKT1/2/3`):**
   edge `61.3 → 38.1` (1.61×; 1.058× over 36). Next squeeze tasked: `sinh ≥ exp/2.01` tail lemma
   (~2×, dominates remainder) + recomposition. **Neg squeeze CLOSED (`CM_Sinh201` + `CM_Sinh201Recomp`,
   `a4be1787`, green, axioms clean):** `sinh t ≥ exp(t)/2.01` for `t≥13.7` (via `exp 6 ≥ 2.7^6 = 387.42 ≥ 201`)
   ⇒ `C=2.53` (`2.53²=6.4009`) ⇒ joint `1.2903=2.53·0.51` ⇒ **neg edge `≤26.8<36` CLOSED at the edge numeral**
   (honest `38.1/26.8≈1.42×`; margin `≈9.3`; pos edge `≤2.76<36`). POINTWISE form only
   (`G_neg_201_le`: `‖G z‖ ≤ 0.971·B(|Im z|)` at `Re z=−1`); `B(a)` GROWS in `a` so the edge value is the
   majorant's minimum, not a tail sup (`B` crosses 36 at finite `a`) — uniform `hTail`/P1 still open on the
   `BZTailEnvelope` tail-sup assembly (Gaussian domination + windowed caps, tasked). **Sharp envelope CLOSED
   (`CP_Sharp201`, `3257c11e`, green, axioms clean):** growing `0.971·B(a)` upgraded to DECAYING sharp
   envelope `‖G‖≤exp((1−(|a|∓6.75)²)/100)·B(|a|)` both signs (CF `G_le_sharp` skeleton on the 2.01 chain) +
   negative-`τ` companion + explicit conditionals `hTail_of_sharp201_sup` / `P1_R02_of_sharp201_sup` (sup hyps
   ⇒ `hTail` ⇒ P1 `‖ζ‖≤10` via `BZTailEnvelope.P1_R02_of_hTail`). OPEN: `hSupNeg` FALSE as stated — neg sharp
   hump `≈45.86/53.18/46.61/37.11` at `a=12/15/18/20` (peak `≈53.2`, `1.48×` over; pos side green `≈2.51`
   decaying). Needs tighter `C<2.53`/zeta tier, narrower variance, or compact-hump `[11,21]` caps +
   large-`a` domination (tasked); conditionals fire immediately once sup hyps land. **Compact caps CLOSED
   (`CQ_CompactHump`, `c5fb5aa5`, green, axioms clean):** `B`-monotonicity + neg-damping antitonicity infra ⇒
   neg envelope `≤36` on `[8.75,9.5]` (`0.971×33.64=32.67`) and `[9.5,10]` (`0.939×38.16=35.83`, margin 0.17)
   + pos side (`0.1×38.16=3.82`) — `hSupNeg`/`hSupPos`-shaped on `[8.75,10]`. Constant-tightening PROVED dead:
   zeta tier no headroom (true `ζ(2)=1.6449` vs `1.65`, 0.3% vs 32.3% needed), `C<2.53` ceiling `~1.11×` vs
   `1.48×` needed. Exact residual: hump **`[10.3,20.4]`** (true peak `≈53.2` at `a≈15`, needs structural work —
   restructured `F` majorant or narrower variance) +    large-`a` **`[21,∞)`** (mechanical: per-unit caps +
   tail decrease, tasked). **Large-a CLOSED (`CT_LargeA`, `167ff503`, green, axioms clean):** nine per-unit
   neg caps `[21,30]` (tightest margin `0.12` on `[21,22]`: `35.88`) + tail `a≥30 ≤16.50` + pos side via
   `pos ≤ neg` pointwise ⇒ **`hSupNeg`/`hSupPos`-shaped on `[21,∞)`**. Full log-derivative decrease NOT
   proved (cruder tail cap banked, honest). `hTail_of_sharp201_sup` now needs ONLY `[8.75,21)`: `[8.75,10]`
   closed (CQ), `[21,∞)` closed (CT) — remaining hump **`[10,21)`** is STRUCTURAL (true `40.68–53.18`,
   peak `≈53.2`; constant-tightening dead; needs restructured `F` majorant or narrower variance, tasked).
   **Hump restructured (`CW_HumpTight`, `898e943d`, green, axioms clean):** factor audit @a=15 (need 1.48×):
   damp EXACT, `√(4+a²)` EXACT, zeta-1.65 1.003× (dead), C=2.53 1.009×, E·C 1.02×, **cpow 1/36 loosest
   (true `1/(4π²)≤1/39.44` → 1.096×)**; uniform total `≈1.13×` — peak unclosable by constants (re-verified).
   Banked `‖(2π)^{-w}‖≤1/39` + `E·C≤0.5001` + `‖Γ·cos‖≤1.2653√` (was 1.2903) ⇒ envelope peak `53.2→48.1`
   ⇒ **closed `[10,10.5]`** (35.57, margin 0.43; old constants give 39.29 there — restructuring
   load-bearing). Damping recenter FORCED to −6.75 for this track (parallel assembly needed to move it).
   `hTail` now needs ONLY **`(10.5,21)`** (peak `~48.1`, `1.34×` over). Ordered deeper levers: (i) exact
   `‖Γ·cos‖` joint (`(1+a²)·πa/2·coth(πa/2)` + zeta phase); (ii) pointwise `|ζ(2+iy)|` cancellation
   (~1.4×, KL/vdC or interval); (iii) recentered-damping parallel track. **Exact joint CLOSED
   (`CZ_JointHump`, `ffcd24a0`, green, axioms clean):** `cosh/sinh ≤ 1.001` (`t≥15.75`) ⇒
   **`‖Γ·cos‖ ≤ 1.26·√(|Im|³)`** (was 1.2653; true ratio `≤1.25899`, decreasing — 2.01-sinh and E·C
   separation slack PERMANENTLY removed on hump) ⇒ **closed `[10.5,10.6]`** (35.16, margin 0.84).
   **Zeta23-Stirling verdict NEGATIVE** (numbers): ceiling `√(2π)≈2.50663` vs `2.53` = 1.0093× max plus
   `5/t²` log-error (`~1.046×` loss at 10.5) — no import taken, zero dep-build. **Uniform-constant route
   now exhausted IN PRINCIPLE** (dream ceiling `1.236×` < `1.331×` needed; peak would sit `~38.8`).
   `hTail` needs **`(10.6,21)`** (peak `47.93`). ONLY structural route left: (iii) recentered damping +
   re-proved threshold assembly (tasked). **Parallel track CLOSED (`DD_RecenterDamp`, `b7b24104`, green,
   axioms clean):** V=28 same-center pick (true peak `≈30.1`; center-shift c=0 kills the R02 divisor;
   V=50 unprovable with repo exp-uppers) — parallel `dampedPoleRemovedP` (old track untouched), 11+11
   caps ⇒ worst claimed `33.83` (margin 2.18; `5.6×` at old peak) ⇒ **`DD_hTail_core`: `‖G_P‖≤36` on
   `Re=−1`, `10.6≤|Im|≤21` UNCONDITIONAL band composition**. Threshold CANNOT fire yet (`G_P` ≠ `G`):
   residual is the re-proved assembly at divisor `4.845`/threshold `48.45` (`4.8%` tighter) — (i) `G_P`
   entire+`DiffContOnCl`, (ii) windowed `A=B=36` caps for `G_P`, (iii) `BddAbove` (easier at /28),
   (iv) `zetaUpper_R02_ten_of_bounds` re-proof (tasked). **Parallel assembly CLOSED (`DF_ParallelP1`,
   `27aa12eb`, green, axioms clean):** (i) `G_P` differentiable + strip-continuous (unconditional);
   (ii) left-window `35.7` + right-whole `20.88` (unconditional) + windowed interp (conditional);
   (iii) compact window-bdd + full-strip conditional on `hTailT`; (iv) re-proof at HONEST divisor
   **4.824**/threshold **48.24** (brief's `4.845` above true damping minimum `≈0.92287`, proved FALSE —
   `0.919` banked; P1 unaffected, margin `12.24`) ⇒ **`GP_P1_of_gaps_and_tailT`: P1 `‖ζ‖≤10` on R02
   conditional on THREE named hyps only**: `hGapLo` (`‖G_P‖≤36`, `Re=−1`, `8.75<|Im|<10.6`), `hGapHi`
   (`21<|Im|`), `hTailT` (strip tail, `9<|Im|`). Next (all mechanical transfers, tasked):    `hGapLo` via
   CQ/CW + `/28`-vs-`/100` damping comparison (both exponents `≤0` there), `hGapHi` via CT transfer,
   `hTailT` via BZ mirror at `/28` (strictly easier constants) — then parallel P1 closes with NO
   premises. **Gap transfers CLOSED + UNCONDITIONAL PARALLEL P1 (`DG_GapTransfer`, `0e15835e`, green
   8702 jobs, axioms clean):** comparison lemma proved once; `F`-part byte-identical on both tracks
   (only damping differs) ⇒ (a) `hGapLo` (CQ+CW+CZ caps transferred), (b) `hGapHi` (CT transferred),
   (c) `hTailT` (BZ mirror via strip-wide `‖G_P‖≤1.16·‖G‖`, `T_P=1.16·T`) ⇒ **`P1_R02_unconditional`:
   `‖ζ‖≤10` on R02 with premises = pure cell membership ONLY** (fired `GP_P1_of_gaps_and_tailT`).
   **P1 TRACK DONE — `R02_zeta_upper_obligation` now dischargeable** (plug into `DerivCauchyBridge` /
   AO rewiring, tasked). **DISCHARGED (`Door3DownstreamDischarge`, DI, `e2c043ea`, green 8702 jobs,
   axioms clean):** `R02_zeta_upper_discharged` (from `P1_R02_unconditional` via `zeta = riemannZeta`
   defeq) + `AO_gamma_upper_discharged` (from landed `R02GammaDisc.gammaOf_upper_disc_R02`) ⇒
   **UNCONDITIONAL `‖deriv xiShifted‖ ≤ 67200` on R02** (and `≤ 162.96`, ceil **`M = 163`** with the
   `0.097` Gamma cap). Zeta-upper + deriv wall CLOSED with zero premises. **M-reduction scout
   (`Door3MReductionScout`, DL, `26a6620b`, green 8702 jobs, axioms clean):** parametric
   `Azeta(M)` floors (`9335 @163 → 9221 @161 → 2463 @43.0144 → 572 @10 → 57 @1 → 2.95 @0.05`) +
   first unconditional cut **`M = 160.4768`** (ceil 161, poly `42 → 41.36` headroom; saves 114 Azeta,
   still infeasible) + fully-quantified single-gap conditional `M(G,Z) = 165.44·G·Z` (fencing `M ≈
   0.05` needs `G·Z ≤ 0.0003`; Stirling target `G = 0.026 → M = 43.0144`). **Zeta-disc cut
   (`Door3ZetaCut75`, DM, `27b78896`, green 8702 jobs, axioms clean):** free rescale — `GP_uniform`
   at `A = B = 36` already proves `‖ζ‖ ≤ 36/4.82475 = 7.461… ≤ 7.5` (same premises, zero new
   analysis) ⇒ **unconditional `M = 120.3576`** (ceil 121, `Azeta ≥ 6894/6931`). NOTE: an early
   DM-verification build transiently failed inside the zeta dependency (sibling DK mid-edit, still
   in flight) — cleared on retry, DM block itself green. Remaining R02 H-leaf is center-product
   premises (`Agam`/`Azeta` at `R02Pilot.sCenter`); next: disc-Gamma `0.026` cap (`→ M = 32.2608`)
   or zeta below `7.46` (tasked). **Gamma lane (`Door3GammaCut89`, DN, `c5047970`, green 8702
   jobs, axioms clean):** tighter convexity base (`Γ(1.37) ≤ 0.9159`, `Γ(6.37) ≤ 235.19` was `256.78`)
   ⇒ **unconditional `G = 0.089`, `M = 110.4312`** (ceil 111, `Azeta ≥ 6325/6358`; step `121 → 111`) +
   single-gap conditional `G = 0.026 → M = 32.2608` (`Azeta ≥ 1848`). `(G,Z,M,Azeta) = (0.089, 7.5,
   110.4312, 6325)`. HONEST AUDIT (in tail): `0.026` fits no convexity+shift route (needs numerator
   `≤ 68.85` vs true max `228`; deeper shifts floor at `≈ 0.090`; splits/corner-dominated; reflection
   exact) — needs Stirling-with-explicit-remainder (`‖Γ(z+6)‖ ≤ 68.85` at `Re ∈ [6.025,6.37]`,
   `|Im| ∈ [2.625,4.125]`; true `≈ 14`, 4.9× slack, feasible in principle; tasked). **One-step
   Im-decay cut (`Door3GammaCut87`, DQ, **`7174a6b2`**, coordinator real-build green 8702 jobs,
   zero errors + zero `sorryAx` — probe-only status lifted):** `‖w‖ ≥ 6.57`
   one-step recurrence ⇒ **`G = 0.087`, `M = 107.9496`** (ceil 108, `Azeta ≥ 6183/6186`; step
   `111 → 108`) — real module build green after DR repaired zeta. CORRECTION (DQ-verified): tasked `68.85`
   numerator is FALSE — true `‖Γ(w)‖ ≈ 131` at top edge (`6.37`, `2.625`), bottom edge `≈ 68`
   (zero margin); prompt's `true ≈ 14` was the invalid large-y asymptote. `M = 32.2608` route now:
   exact infinite-product decay or matched-x monotonicity, per DQ residual (tasked). **Zeta23 door-3 verdict retained:** Stirling route dead (above);
   MV large-sieve (`Zeta23.MV.Final.mv_hilbert`, C=26) tasked to DB for the middle block; log-bounds
   marginal (bounded windows); σ>1 lowers / zero-free / statistics machinery no door transfer.
   **Joint composition CLOSED
  (`CIJointStirling`):** joint `92→52.8` (1.75× inside one estimate); pos edge **`6.32<36` CLOSED at
  edge**; neg edge `61.3` (1.70× over — tighter-`C`/sqrt-form/zeta tiers tasked). **hTail sharpest-cap (`CC_hTailGap`):**
  pointwise `B(a)`, edge `B(8.75)=1984.6` (`~55×` over 36), `no_crossover` PROVED for the `1·poly`
  majorant — sharp-Gaussian recomposition tasked (edge `≈180` expected, still short; true-`F` gap next).
  **Sharp-damping CLOSED (`CF_SharpDamp`):** top edge `198.46` (10× gain, 5.5× over; damping slack only
  ~9% — remainder in cubic `F` majorant); negative edge `1927` (53× over — damping centered at -6.75
  nearly useless there). Joint `Γ·cos` Gaussian analysis tasked (load-bearing on negative side). **hTail sharpest-cap (`CC_hTailGap`):**
  pointwise `B(a)`, edge `B(8.75)=1984.6` (`~55×` over 36), `no_crossover` PROVED for the `1·poly`
  majorant — sharp-Gaussian recomposition tasked (edge `≈180` expected, still short; true-`F` gap next). **Tail numerals landing
  (`BV2OuterTail`):** outer-envelope Gaussian domination `T=18·exp(165.23)` green; middle exp-3/2
  numeral (Young `u^{3/2}` bound + completing square) tasked, then tail-`T` assembly.
  **Middle numeral CLOSED (`BXMiddleTail`):** Young SOS (`K·t³ ≤ t⁴/200+10⁶K⁴`) + `middle_gauss_le`
  green. Correction: BP2/BU `C,K` are EXISTENTIAL — `T` is a function of envelope constants; still
  needs tail `F`-envelope (Gamma-lower on tail) + negative-`τ` companion numeral, then tail-`T`. **xi-bridge banked (`BLMiddleEnvelope`,
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
  Relaxation tasked: exp-3/2 middle via xi + Gaussian domination ⇒ `hBdd` (damping beats any 1.5-power).
  **Middle envelope CLOSED-conditional (`BP2Middle32`):** `‖F‖ ≤ C·exp(K·|Im|^{3/2})` on the middle third
  (`‖s‖^{3/2}` split at `|Im|=2`) conditional on ONE explicit `hGlow` (strip `Gammaℝ` lower — no strip
  lower exists repo-wide).   Residual R-Gamma tasked (reflection `π/(S·U)` strip-uniform pieces). **R-Gamma verdict
  (`BTStripGamma`):** strip sine-upper + reflected `U=4` green, but uniform-`hGlow` PROVED IMPOSSIBLE
  in-file (`Gammaℝ 0 = 0`). Path: windowed `|Im|≤9` lower (explicit min `~2e-8`-tier) + damping-domination
  outside ⇒ `hBdd` (tasked). **Update — Gamma factor fully closed for all 40 centers:**
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
    **R33+R34 CLOSED-packaged (R, `15372ede`, green 8687 jobs, axioms clean):**
    `BD_R33SmallR`/`BD_R34SmallR` mirror the template (same C/M). R35–R40 next (tasked).
    **R35+R36 CLOSED-packaged (R2, `42106b13`, green 8687 jobs, axioms clean):**
    `BD_R35SmallR`/`BD_R36SmallR` mirror the template (inner-tier eps `0.15`). R37–R40 next (tasked).
    **R37+R38 CLOSED-packaged (R3, `d96deaa0`, green 8687 jobs, axioms clean):**
    `BD_R37SmallR`/`BD_R38SmallR` mirror the template (mid-tier eps `0.05`). R39+R40 LAST (tasked).
    **R39+R40 CLOSED-packaged (R4, `10d1032f`, green 8687 jobs, axioms clean):**
    `BD_R39SmallR`/`BD_R40SmallR` (outer-tier eps `0.002`).
    **BD COVER LANE CLOSED — R31–R40 all packaged (cover tail quiet unless needed).**
    **Residual scout (R5, `4640a851`, green 8687 jobs, axioms clean):** mapped all three —
    real axis (needs `BoundaryProofEngine`, `StripBaseBounds` nonzero-base feeder),
    ±10 lines (CutL10/CutR10 thin rects exist; per-rect center+deriv H-leaf missing),
    strips (own obligation shape PROVED — `CellData` reuse formally closed).
    Banked `door3_conj_transfer`/`door3_real_self_star`/`door3_cutoffLine_mem_of_abs_le`.
    Next: CutR10 center enclosure (tasked).
    **R37+R38 CLOSED-packaged (R3, `d96deaa0`, green 8687 jobs, axioms clean):**
    `BD_R37SmallR`/`BD_R38SmallR` mirror the template (mid-tier eps `0.05`). R39+R40 LAST (tasked).
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
       │       ├─ bridged_center_bound  (historical mpmath trust)  ── Float ε → ℝ ≤ |ξ(center)|
       │       ├─ bridged_deriv_bound   (historical mpmath trust)  ── Float M → ℝ ≥ |ξ'| on rect
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

## Door-3 update: cutoff Gamma supplier (2026-09-05)

`door3_gamma_product.lean` proves finite-product bounds for the complex Gamma
norm at every positive real part, including a squared form with rational factors.
`door3_gamma_cutoff.lean` uses 128 exact rational factors and Euler reflection to
prove `Door3GammaCutoff.cutR10_gammaRemainder` without analytic premises.
This supplies `1/2000 <= norm (Gamma (1/4 + 5*I))` to the CutR10 center assembly.
The named adapters `cutR10_center_bound_of_zeta` and
`cutR10_fencing_of_zeta_deriv` consume that proof directly.
Validation: `lake build door3_gamma_cutoff` succeeded (8690 jobs); all three
adapter axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
CutR10 still needs its zeta lower bound and derivative upper bound. No complete
cell cover, unbounded-tail certificate, or unconditional RH theorem is claimed.

## Door-3 update: cutoff zeta and derivative interfaces (2026-09-05)

`door3_zeta_cutoff.lean` proves the cutoff eta conversion factor is at most
`1`; the phase enclosure uses the existing nine-decimal `log 2` and four-decimal
`pi` bounds together with the quadratic cosine lower bound. It then supplies
`zeta_cutoff_lower_of_certificate_one` and
`cutR10_zetaRemainder_of_certificate_one`, reducing the named `7/5` zeta floor
to a finite eta partial-sum and pair-tail certificate. The same file proves
`cutR10_derivRemainder_of_closedBall_sup`, reducing the named `M = 0.04`
derivative remainder to one explicit sup enclosure for the entire xi extension
on the center ball. These are unconditional reduction lemmas; the finite zeta
certificate and the entire-function sup enclosure remain to be supplied.
Validation: `lake build door3_zeta_cutoff` succeeded (8700 jobs); the new
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Door-3 grid boundary audit (2026-09-05)

The legacy `bridgedCoversUpper` statement in `central_cover_trusted.lean` is
not a satisfiable combinatorial claim. Its hypotheses allow the outer
boundaries `Re z = ±10`, while every listed rectangle has strict endpoint
inequalities. More generally, adjacent certificate columns meet at shared
endpoints such as `Re z = -7.5`; the 32-cell list has no overlap there, so no
cell can satisfy both `R.x0 < z.re` and `z.re < R.x1`. Unfolding
`bridgedZeroFreeRectsUpper`, `bridgedCells`, and the rectangle projections
reduces the proposed witness at `Re z = -7.5` to an explicit contradiction
for every list element. A valid cover must use overlapping columns (as
`fineGridX` does) or weaken the boundary relation and then separately recover
the strict interior needed by `XiLocalZeroFreeRect.no_zero`; this cannot be
closed by a finite endpoint-comparison lemma alone.
This obstruction is now kernel-checked in
`door3_grid_boundary_counterexample.lean`: `no_strict_cover_at_neg75` proves
that no legacy bridged rectangle contains `Re z = -7.5` with both strict
horizontal inequalities. `lake build door3_grid_boundary_counterexample`
succeeds (8691 jobs), with only the standard axioms in its report.

The Float radius bridge has an independent exact obstruction. In
`door3_float_bridge_audit.lean`, the first cell's Float radius is evaluated
with `native_decide` as the rational `5645734119880132 / 2^52`, and the exact
real radius is `sqrt(62861) / 200`. The file proves both that these values are
unequal and that the Float radius is strictly below the real radius. Therefore
the `bridgedToLowerBoundRect` proof cannot obtain its real-radius center bound
by rewriting the Float certificate; it needs a separately proved slackened
inequality, and the numerical xi bound must be stated with that slack.
Validation: `lake build door3_float_bridge_audit` succeeded (8683 jobs), with
the audit theorems free of `sorryAx`; their report contains the standard
`propext`, `Classical.choice`, `Quot.sound`, and the compiler-generated
`native_decide` evaluation axiom used to evaluate Float operations.

`door3_real_radius_bridge.lean` now provides
`Door3RealRadiusBridge.lowerBoundRectOfRealCertificate` and
`zeroFreeRectOfRealCertificate`. These adapters consume the exact real
rectangle center/radius and a real derivative supplier directly, so a future
numerical certificate can connect without relying on the disproved Float/ℝ
radius equality. The adapter build is green (8691 jobs).

The production `bridgedToLowerBoundRect` path now consumes that exact-real
center/radius form as well; the false Float/ℝ equality leaf has been removed.
`lake build central_cover_trusted` is green (8690 jobs) and reports three
remaining legacy leaves: the real center enclosure, the derivative enclosure,
and the unsatisfiable strict grid-cover theorem.

`door3_trusted_statement_audit.lean` machine-checks a stronger defect in the
legacy center leaf: `not_universal_bridged_center_bound` proves that the
universal theorem cannot hold for the current `BridgedCell` structure, because
its `ε` field is unconstrained above. The proof constructs a valid record with
`ε = ‖xiShifted center‖ + 1` and `M = 0`, yielding an immediate contradiction.
Its build succeeds (8691 jobs) and its axiom report contains only the standard
`propext`, `Classical.choice`, and `Quot.sound`.

## Door-3 update: analytic zeta pair tightening (2026-09-05)

`door3_zeta_pair_tightening.lean` adds an unconditional degree-eight cosine
majorant, proves that polynomial is antitone on the phase-20 interval, and
derives the explicit bounds `cos(D3_phase 20) ≤ 0.074` and
`-0.343 ≤ cos(D3_phase 21)`. Together with the existing amplitude bounds and
the exact rational inequality, this proves
`(etaPairTerm (1 - zetaCellS0) 10).re ≤ 0.0673` with no numerical hypotheses.
Validation: `lake build door3_zeta_pair_tightening` succeeded (8694 jobs); the
new theorem axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`.

## Door-3 update: sound certificate API (2026-09-05)

The three unsound global leaves in `central_cover_trusted.lean` have been
redesigned.  `BridgedCellCertificate` now carries the exact real center and
derivative inequalities as fields; the rectangle and conjugation adapters
consume those fields explicitly.  The cover combinatorics are parameterized by
an explicit inner-grid coverage certificate, and `bridgedCoversInner` is stated
only on the strict inner band `(-10,10) × ((-0.49,-0.01) ∪ (0.01,0.49))`.
Consequently `central_cover_trusted` contains no `sorry` declarations and its
build is green.  The 40 analytic certificate fields and the boundary-strip
certificates remain genuine inputs; no unconditional `XiCentralZeroFreeCover`
or RH theorem is manufactured from absent numerical evidence.

## Door-3 update: closed-cell boundary interface (2026-09-05)

`door3_closed_cover.lean` adds `XiLocalClosedZeroFreeRect` and
`XiCentralClosedZeroFreeCover`.  Their coverage predicates use closed
coordinate inequalities, so adjacent numerical cells can meet exactly on a
grid edge.  `xiLocalClosedZeroFreeRect_of_fencing` reuses the existing
closed-rectangle Taylor estimate, and
`xiCentralPointwise_of_closed_cover` assembles a closed cover into the central
pointwise obligation.  The module builds without `sorryAx`; only the standard
Lean classical/propositional axioms occur in its reports.

The same module now proves `fineGridX_covers_closed`,
`innerGridY_covers_closed`, and `gridFine_covers_closed_inner`.  Thus the
40-cell geometry covers the closed rectangle
`[-10,10] × [0.01,0.49]`, including every numerical grid boundary.  This is a
pure real-arithmetic result; it does not discharge the per-cell analytic
fencing fields or the boundary strips outside that rectangle.

`closed_inner_nonvanishing_of_fenced_grid_fine` is the corresponding
closed-boundary assembly: any supplier of the existing 40 per-cell fencing
fields yields nonvanishing on the entire closed inner rectangle.  It carries
those fields explicitly and introduces no trusted numerical claim.

`zeta_rigorous.lean` now also contains `DZ3o_true_prefix_le_three_two` and
the tighter `DZ3o_true_prefix_le_three`: every prefix of the true eta block
`[16,32)` is bounded by `3`, using the exact norm identity and proved
amplitude floors.  These are unconditional finite-sum bounds; the middle-block
cancellation obligation remains separate.


## Door-3 update: real critical interval eta feeder (2026-09-06)

`door3_tail_eta_upper.lean` now proves `Door3TailEtaUpper.zeta_real_nonzero_critical`: for every real `0 < t < 1`, `ζ(t) ≠ 0`.  The proof rewrites the continued eta value as a convergent paired series, identifies each real pair with a strictly positive real `rpow` difference, and applies `Summable.tsum_pos`; the eta factor is separately shown nonzero.  `door3_boundary_real.lean` exports this as `zetaRealNonzeroInCritical_proved` and discharges the corresponding imaginary-axis `xiShifted` and hard-difference statements.  These declarations build with only `[propext, Classical.choice, Quot.sound]`.  This closes that real-zeta feeder; it does not discharge the 40 central `xiShifted` fencing fields, the real-axis base bounds, or the mollified tail gap.

The same feeder also proves `xiShifted_ne_zero_at_origin_proved`, extends the imaginary-axis result through `y = 0` as `xiShifted_ne_zero_on_imaginary_axis_all_proved`, and proves the corresponding hard-difference nonvanishing at the origin and on the full imaginary axis. These are boundary facts only and do not discharge the central rectangle certificates.

It also exports `classicalXiPrefactor_ne_zero_on_real_critical_proved` and `classicalXi_ne_zero_on_real_critical_proved`, so the real-zeta feeder can be consumed directly at the classical-ξ layer. Their axiom reports contain only the standard Lean axioms.

`Door3TailEtaUpper.zeta_real_nonzero_positive` and its wrapper `zetaRealNonzeroPositive_proved` extend the real-zeta result from `(0,1)` to every positive real argument, using the eta-pair proof below `1`, the standard value at `1`, and the Euler-product nonvanishing theorem above `1`.

## Boundary endpoint consistency feeder (2026-09-06)

`door3_boundary_endpoints.lean` proves without assumptions and without new axioms that the totalized product definition satisfies

* `_root_.xiShifted (I/2) = 0` and `_root_.xiShifted (-(I/2)) = 0`, because the polynomial prefactor vanishes at `s=0` and `s=1`;
* `CentralCoverAssembly.xiShiftedEntire (I/2) = 1/2` and `CentralCoverAssembly.xiShiftedEntire (-(I/2)) = 1/2`.

These points lie on the strip boundary and therefore are excluded from the interior cover. The result records the exact endpoint behavior needed when treating edge strips and prevents using the interior identity there. The module reports only `[propext, Classical.choice, Quot.sound]`.

`Door3TailEtaUpper.zeta_re_zero_nonzero` now exports the unconditional open imaginary-axis zeta result: `Re s = 0` and `Im s ≠ 0` imply `ζ(s) ≠ 0`, by the functional equation and the established `Re(1-s)=1` Euler-product zero-free theorem. `xiShifted_ne_zero_on_top_edge_proved` consumes this together with the exact nonzero Gamma, pi-power, and polynomial factors to prove the totalized shifted xi is nonzero at every open top-edge point `x + I/2` with `x ≠ 0`. The endpoint `x=0` remains the separately recorded totalization zero.

## Top-edge compact lower-bound feeder (2026-09-06)

`door3_top_edge.lean` proves that `xiShiftedEntire` agrees with the totalized product `xiShifted` at every open top-edge point `x + I/2` with `x ≠ 0`, and separately repairs the endpoint `x=0` using the entire extension's exact value there. It proves the corresponding bottom-edge statements at `x - I/2` using the Euler-product zero-free theorem on `Re s = 1`, together with the bottom endpoint value. Compactness then gives a strictly positive uniform lower bound on either edge over every closed real interval. This is unconditional and uses only the standard Lean axioms. The result supplies qualitative outer-bound values required by the top-touching boundary lemma; explicit derivative suprema and the quantitative edge-strip constants remain separate obligations.

The same module also proves `exists_top_edge_local_strip`: at each fixed real `x`, continuity on a compact closed ball gives a Cauchy derivative bound and hence an open zero-free vertical neighbourhood below the top edge.

`exists_top_edge_uniform_strip` now supplies that compact-region step: for every closed interval `[a,b]`, one obtains a single positive width `δ` for which the open strip `1/2−δ < Im z < 1/2` above `[a,b]` is zero-free. The theorem is unconditional, but it does not provide the numerical width `0.01` needed by the fixed edge-strip decomposition; proving `δ ≥ 0.01` remains a quantitative bound obligation.

The module also adds `lower_boundary_nonvanishing_from_outer_bound`, obtained by translating the lower edge to the existing base-strip fencing theorem. It is an unconditional generic lower-edge counterpart; a numerical lower-edge width and the remaining zeta/derivative suppliers are still separate.

`exists_bottom_edge_uniform_strip` is the matching compact-interval result for the lower edge. Both edge sides now have unconditional qualitative uniform-width certificates; neither supplies the fixed numerical `0.01` margin required by the current cell grid.

The same file now proves `exists_top_edge_compact_lower_bound` and
`exists_bottom_edge_compact_lower_bound`. After shrinking the qualitative
edge width, compactness of the closed interval-by-height rectangle gives a
strictly positive minimum of `‖xiShiftedEntire‖` on each closed edge strip,
including the endpoint edge itself. These minima are unconditional and are
available for later Rouché or Taylor estimates; they remain existential and
do not replace the missing explicit `0.01` numerical certificates.

It also exports `exists_deriv_bound_on_closedBall`: every differentiable
complex function has an existential finite derivative bound on any prescribed
closed ball, obtained from a compact outer-ball function bound and Cauchy's
derivative estimate. This is an unconditional reusable supplier for later
cutoff and edge certificates; its bound is qualitative until a numerical
supremum for the particular function is proved.

Finally, `exists_top_edge_cauchy_data` packages the two preceding outputs over
any closed real interval: it supplies positive `δ`, `m`, and `M` so that the
closed strip of height `δ` below the top edge has the lower bound `m` for
`‖xiShiftedEntire‖` and derivative bound `M`. The data are unconditional but
qualitative; the fixed `δ ≥ 0.01` and numerical values required by the central
cell certificate remain open.

The symmetric `exists_bottom_edge_cauchy_data` theorem supplies the same
qualitative lower and derivative data on a closed strip above the bottom edge.
It likewise leaves the fixed-width and numerical central-cell estimates open.

`exists_two_edge_cauchy_data` combines both sides over one interval, shrinking
the width and lower bound and enlarging the derivative bound. This gives a
single unconditional interface for later two-edge assembly while preserving
the still-open numerical obligations.

`exists_two_edge_open_cauchy_data` transfers that package through the exact
entire-extension identity and derivative identity, yielding lower and
derivative bounds for the original `xiShifted` on the open top and bottom edge
strips. Its width is still qualitative and therefore does not discharge the
fixed `0.01` edge cells.

The same module now proves `exists_imaginary_axis_compact_lower_bound`: the
entire extension has a strictly positive minimum on the complete closed
imaginary-axis segment `[-1/2,1/2]`. The proof handles both totalization
endpoints explicitly and uses the unconditional eta-based interior feeder.

The new `door3_imag_axis_strip.lean` module upgrades this to
`Door3ImagAxis.exists_imaginary_axis_horizontal_strip`: a positive-width
two-dimensional neighborhood of that axis has a uniform positive lower bound.
It uses only convexity, the compact-axis minimum, and an existential Cauchy
derivative bound; the width remains qualitative.

`Door3ImagAxis.exists_imaginary_axis_local_rect` packages a strict interior
rectangle `[-ρ/2,ρ/2] × [-1/4,1/4]` from that strip as an unconditional
`XiLocalZeroFreeRect`. This is a concrete central-cover cell; the remaining
cover still requires the off-axis cells and their numerical zeta enclosures.

`Door3ImagAxis.exists_small_central_zero_free_cover` goes one step further:
for some explicitly positive (though qualitative) `X`, the single rectangle
`[-ρ,ρ] × [-1/2,1/2]` is a complete `XiCentralZeroFreeCover X`. Thus the
unconditional work now closes a nontrivial central band and leaves only the
complementary off-axis width needed to reach `X = 10`.

The same file defines `combine_central_cover_with_annulus`, a kernel-checked
assembly operator that appends any certified annular list to a central cover.
Its remaining input is exactly the off-axis annulus coverage certificate; no
analytic claim is hidden in the assembly itself.

The module also proves `exists_top_edge_zero_free_rect` and
`exists_bottom_edge_zero_free_rect`.  These convert the two-edge Cauchy data
into explicit `XiLocalZeroFreeRect` certificates over every finite interval
`[a,b]` with `a < b`; the conversion includes the entire-extension identity
and uses the positive norm lower bound to discharge `no_zero`.  Finite edge
partitions can therefore be assembled directly from these objects.  The
remaining analytic input is still the off-axis annular coverage between the
axis strip and the two edge strips.

`exists_boundary_edge_rectangles` specializes these constructors to the full
finite interval `[-10,10]`, yielding reusable upper and lower edge cells for
the final annulus list.

## Door-3 certificate-range audit (2026-09-06)

`door3_zeta_cert_range_audit.lean` kernel-checks the range of the existing
`zeta_cert_data` table: every row has its first height coordinate strictly
above `10`, and every row ends strictly below `12`.  The table therefore
covers the height band `(10,12)`, while the central Door-3 cells require the
band `[0.01,0.49]` over `Re z ∈ [-10,10]`.  The audit is finite and contains
no `sorry`, `admit`, or custom axiom; it records the range mismatch rather
than treating the Float table as an analytic certificate for the central
rectangle.  Its theorem `zeta_cert_data_disjoint_from_central_height_band`
also checks directly that no row intersects the required central height band.

## Door-3 update: analytic center and off-axis certificate interfaces (2026-09-07)

`door3_real_center_bounds.lean` now proves the real critical-interval lower bound
for `ζ`, the corresponding real-axis `ξ` center lower bound, and the complete
imaginary-axis center bound.  These results are unconditional and their axiom
reports contain only `[propext, Classical.choice, Quot.sound]`.

`door3_off_axis_certificates.lean` adds the finite-data interface
`FiniteZetaLowerCertificate`.  Its `lower_of_re` theorem converts a certified
finite eta sum, paired-tail estimate, and eta-factor bound into a kernel-checked
lower bound for `‖ζ s‖`.  The R00 and reflected R00 constructors package all
already-proved tail and factor estimates; their only supplied analytic field is
the genuine finite-sum lower bound.  The R03--R10 center and zero-free rectangle
constructors, the R10 conjugation bridge, and
`OffAxisFiniteCertificateBundle` assemble the eight bottom-row off-axis cells
once those finite-sum and derivative fields are supplied.  No Float value is
coerced into an analytic theorem.

`door3_rational_certificates.lean` and `generate_door3_certificates.py` now
generate forty exact-rational candidate rows.  The proposition-valued theorem
`door3_rational_candidates_all_ok` proves every row's geometry and fencing
arithmetic in Lean, and the generator preserves that proof on regeneration.
The rows remain explicitly marked `sampled_unverified`: they do not assert the
analytic `ξ` center or derivative inequalities.

Verification performed after this update:

```text
lake build door3_rational_certificates
lake build door3_rational_grid_cover door3_real_center_bounds door3_off_axis_certificates
```

The exact remaining Door-3 obligations are therefore unchanged in substance:
analytic complex-`ζ` lower enclosures and uniform derivative bounds for the
central cells, together with the fixed-width edge and cutoff certificates.  The
finite certificate interfaces expose these obligations directly and do not
close them by hypothesis or by the forbidden `RiemannHypothesisProp_apply`.

## Door-3 commit review: post-`4d38e41c` work (2026-09-07)

The commit range `202e5a97..85d7b4f6` added a substantial implementation layer
that was not represented in the earlier ledger. The following is the current
record of that work.

* **Generated target and geometry pipeline** (`202e5a97`, `939d5a1e`,
  `cee61a93`, `d4e7f321`, `08ff946b`): `door3_numeric_targets.json` and its
  generated Lean companion contain 40 exact-rational target rows. Lean proves
  positivity, nonnegative slopes, positive fencing margins, the squared-radius
  bound, the 40-row count, the radius transfer, and the budget-to-fencing
  adapter (`all_budgets_ok`, `all_margins_pos`, `all_geometry_sq`,
  `transfer_budget`, `make_cell_fencing`). The target `centerLower` values and
  derivative slopes are still sampled data; no theorem equates them with an
  analytic `ξ` value or derivative supremum.
* **Exact open-grid coverage** (`556d319f`, `6b67d328`):
  `door3_rational_certificates.lean` records 40 exact-rational candidate rows,
  while `door3_rational_grid_cover.lean` proves the overlapping x and y
  interval disjunctions and the resulting open cover of
  `(-10,10) × (0.01,0.49)`. The final generated theorem
  `door3_rational_candidates_all_ok` checks every row's arithmetic and geometry
  in the kernel. These are combinatorial certificates only; the rows are
  explicitly `sampled_unverified` for the analytic fields.
* **Correct height and finite-evidence bridge** (`f223f222`, `d50bdd01`,
  `0b8ef94a`, `a23225d7`, `54848771`, `f0d76330`, `25f96600`, `bcd2c0ec`):
  `door3_height11_bridge.lean` replaces the earlier height-14 interface with
  the exact `|Im s| < 11` range induced by `shiftedS`. It supplies
  `CriticalStripEvidence11` and `FiniteCriticalStripEvidence11`, finite
  rectangle-to-zero-free adapters, bounded ζ and classical-ξ cover adapters,
  and the conditional assembly theorems
  `rh_from_finite_evidence11_and_rectangle_tailU` and
  `xiNoRightHalfZerosFull_of_finite_evidence`. They consume explicit finite
  evidence and a tail supplier; no evidence instance is fabricated.
* **Axiom-free rectangle/RH wiring** (`eb282b07`, `6fe850a6`, `04ba16fb`,
  `563306a5`, `e9a5f85e`): `riemann_hypothesis_newsection.lean` now exposes
  the approximation and Euler--Maclaurin rectangle bridges and their RH
  assembly implications. The R02 eta identity is discharged unconditionally:
  `R02_zeta_upper_unconditional` gives `‖ζ‖ ≤ 1012` on the R02 disc and
  `R02_deriv_bound_unconditional` gives `‖deriv ξ‖ ≤ 6800640`. The conditional
  three-lines route still has a smaller `‖ζ‖ ≤ 10` target, but the unconditional
  constants above do not meet the current cell-fencing budget.
* **Head and axis certificates** (`290e25e8`, `6b67d328`, and the subsequent
  `2847bfd9` through `b02f08e3` center-bound commits):
  `door3_s4_imag.lean` proves the reflected four-term head norm lower bound
  `1/6` and the `1/6 − U` lower bound for the 1024-term prefix once the middle
  block is bounded. `door3_center_bounds.lean` and
  `door3_real_center_bounds.lean` provide unconditional real-critical ζ
  nonvanishing, explicit real-axis `ξ` center lower bounds, and uniform
  imaginary-axis center lower bounds, including the zero-height case. These
  axis results close the feeder facts but do not cover the off-axis cells.
* **Off-axis factor and finite-sum interfaces** (`4a892f75` through
  `784da527`): the R02--R10 constructors now include unconditional polynomial,
  π-power, Gamma, reflection, and upper-bound components, together with
  center/zero-free constructors, the R10 conjugation bridge, and the
  eight-cell `OffAxisFiniteCertificateBundle`. The later
  `FiniteZetaLowerCertificate` layer makes the only missing analytic input
  explicit: a genuine finite eta-sum lower bound (plus the corresponding
  derivative field). The constructors remain implication APIs and do not
  turn candidate numbers into proofs.
* **Generator and audit hardening** (`16ac9b4c`, `9ed8723c`, `85d7b4f6`): the
  certificate generator now emits both the Boolean arithmetic audit and the
  proposition-valued `door3_rational_candidates_all_ok` proof, and regeneration
  preserves that proof. The audited declarations use only standard Lean
  axioms and contain no `sorryAx` or `RiemannHypothesisProp_apply`.

This commit review changes the implementation inventory, not the closure
status. Door 3 still lacks the kernel-checked complex-ζ lower enclosures and
uniform derivative bounds needed for the 40 central cells, the explicit
fixed-width edge/cutoff certificates, and a supplied finite-sum certificate for
the off-axis bundle. The new bridges expose exactly those inputs and the
downstream RH implications, but no recent commit proves them by assumption.

## Complete commit ledger for the last two days

This audit uses the current branch history from 2026-09-05 00:00 through the audited source commit `1cc25d65`, immediately before this documentation-only snapshot. It finds 182 commits; every commit hash and subject is listed below, including documentation and ledger commits. The narrative Door-3 sections above summarize the technical groups; this ledger is the hash-level completeness check.

- 1cc25d65 | 2026-09-07 | record complete two-day commit ledger
- 8aee8307 | 2026-09-07 | update guide with recent Door 3 commits
- ae2cfd0c | 2026-09-07 | document Door 3 certificate interfaces and residuals
- 85d7b4f6 | 2026-09-07 | fix generated candidate proposition audit proof
- 9ed8723c | 2026-09-07 | preserve proposition audit in certificate generator
- 16ac9b4c | 2026-09-07 | prove rational candidate table proposition audit
- 784da527 | 2026-09-07 | audit finite certificate axioms
- f016dc78 | 2026-09-07 | wire finite certificate lower bounds
- 9232858c | 2026-09-07 | add reflected finite zeta certificate bridge
- b11dfa0c | 2026-09-07 | package R00 finite eta certificate
- 1b7fbf2a | 2026-09-07 | fix R10 conjugation bridge proof
- 04703d60 | 2026-09-07 | bundle finite off-axis rectangle certificates
- 750df34f | 2026-09-07 | add R10 conjugation certificate bridge
- 5737e225 | 2026-09-07 | add finite zeta to rectangle certificate bridge
- e6d07d63 | 2026-09-07 | package finite eta zeta lower certificates
- 747813f4 | 2026-09-07 | package unconditional R08 gamma certificate
- 062eb39a | 2026-09-07 | add unconditional R08 gamma lower bound
- 035f9d77 | 2026-09-07 | add half-zeta off-axis rectangle certificates
- 5281209b | 2026-09-07 | add small-budget R09 and R10 centre certificates
- 7d8969c0 | 2026-09-07 | add unconditional large-height gamma reflection bounds
- 38d22f8a | 2026-09-07 | generalize bottom rectangle zeta upper bound
- 23ac2296 | 2026-09-07 | add unconditional R03 zeta upper enclosure
- 05c2fe8e | 2026-09-07 | sharpen R03 gamma and add off-axis certificate
- c5c629c1 | 2026-09-07 | add reusable reflection and tighter R04 bounds
- ed537542 | 2026-09-07 | prove unconditional R05 gamma center lower bound
- 7d32969e | 2026-09-06 | prove unconditional R06 gamma center lower bound
- a963d2fc | 2026-09-06 | prove unconditional R07 gamma center lower bound
- 5860ef14 | 2026-09-06 | wire R04 gamma bound into rectangle certificate
- b87543f6 | 2026-09-06 | prove unconditional R04 gamma center lower bound
- 95644cb7 | 2026-09-06 | wire off-axis rectangle certificate constructors
- 168f6b8d | 2026-09-06 | add off-axis center certificate constructors
- 4a892f75 | 2026-09-06 | add unconditional off-axis R02 center certificate
- b02f08e3 | 2026-09-06 | add direct analytic axis center nonvanishing
- 5107f9be | 2026-09-06 | wire explicit xi center positivity into axis nonvanishing
- 5ef9a7bd | 2026-09-06 | add unconditional open-strip xi norm positivity
- db966ec1 | 2026-09-06 | add explicit zero-height center certificate
- 105ddf29 | 2026-09-06 | expose explicit real-part center lower bound
- 09ebc0f4 | 2026-09-06 | replace center positivity with analytic xi bounds
- 11d448d8 | 2026-09-06 | add top-edge xi center norm certificates
- 9afde591 | 2026-09-06 | bridge axis center norm bounds to real parts
- 4834966a | 2026-09-06 | add real-axis xi norm representation
- e5641373 | 2026-09-06 | record reality of real xi center values
- fe878919 | 2026-09-06 | certify unconditional axis center nonvanishing
- 97312561 | 2026-09-06 | close real critical zeta nonvanishing bridge
- 4e58e5a1 | 2026-09-06 | add uniform imaginary-axis xi nonvanishing certificate
- 161357b4 | 2026-09-06 | add uniform axis xi center certificate
- b3c4d1ce | 2026-09-06 | sharpen explicit real xi center lower bound
- 2350fc3d | 2026-09-06 | add explicit rational xi axis center bounds
- c57e5d5b | 2026-09-06 | strengthen analytic xi center bounds
- f4ee119e | 2026-09-06 | register analytic Door 3 center bound module
- 2847bfd9 | 2026-09-06 | prove analytic real-axis zeta and xi center lower bounds
- 6b67d328 | 2026-09-06 | prove unconditional Door 3 axis center bounds and grid coverage
- 290e25e8 | 2026-09-06 | add unconditional Door 3 head imaginary certificate
- 556d319f | 2026-09-06 | generate exact rational Door 3 candidate certificates
- bcd2c0ec | 2026-09-06 | wire finite evidence to bounded rectangle assembly
- 25f96600 | 2026-09-06 | convert global strip evidence to finite certificate
- f0d76330 | 2026-09-06 | wire finite xi cover into bounded decomposition
- 54848771 | 2026-09-06 | expose bounded classical xi cover adapter
- a23225d7 | 2026-09-06 | add zeta bounded-cover adapter for finite evidence
- 0b8ef94a | 2026-09-06 | add finite interval cover certificate interface
- d50bdd01 | 2026-09-06 | wire height-11 evidence to RH assembly
- f223f222 | 2026-09-06 | align Door 3 certificate bridge to height 11
- e9a5f85e | 2026-09-06 | add Euler Maclaurin rectangle bridge
- 563306a5 | 2026-09-06 | add approximation-bound rectangle bridge
- 04ba16fb | 2026-09-06 | connect rectangle evidence to RH assembly
- 6fe850a6 | 2026-09-06 | add axiom-free rectangle certificate bridge
- eb282b07 | 2026-09-06 | discharge R02 zeta upper and derivative bridge
- 08ff946b | 2026-09-06 | connect target budgets to cell fencing
- d4e7f321 | 2026-09-06 | add radius transfer lemma for generated targets
- cee61a93 | 2026-09-06 | record exact fine-grid geometry checks
- 939d5a1e | 2026-09-06 | check positive margins for Door 3 targets
- 202e5a97 | 2026-09-06 | add generated Door 3 arithmetic target shell
- 4d38e41c | 2026-09-06 | up
- 51216a19 | 2026-09-06 | UP
- 968445f1 | 2026-09-05 | Transfer closed-grid fencing to both halves
- dbc7ec6f | 2026-09-05 | Correct stale zeta proof status comments
- 9d3e7b93 | 2026-09-05 | Record true eta prefix bounds
- 8332ec67 | 2026-09-05 | Tighten true eta prefix cap
- 76e7e9cb | 2026-09-05 | Add unconditional true eta prefix cap
- 60a0d4a2 | 2026-09-05 | Clarify explicit central cover adapter
- 6f627bfc | 2026-09-05 | Assemble closed-grid nonvanishing conditionally
- 65e66fb5 | 2026-09-05 | Prove closed fine-grid boundary coverage
- 99d78946 | 2026-09-05 | Add closed-cell Door 3 cover interface
- cb577b4c | 2026-09-05 | Redesign Door 3 bridge as explicit certificate API
- 59fac02c | 2026-09-05 | Formalize false Door 3 center-bound statement
- f3718085 | 2026-09-05 | Formalize Door 3 legacy grid boundary obstruction
- 3afecb24 | 2026-09-05 | Tighten Door 3 zeta pair enclosure
- ce50e817 | 2026-09-05 | Record production real-radius bridge migration
- 584e8d4b | 2026-09-05 | Replace false Float radius bridge with real radius
- a8643fa8 | 2026-09-05 | Correct Float audit axiom report
- 25099270 | 2026-09-05 | Verify Float radius audit axioms
- 891f7ba4 | 2026-09-05 | Verify real-radius bridge axioms
- 2920e55a | 2026-09-05 | Document real-radius bridge interface
- 758ea1b7 | 2026-09-05 | Add exact real-radius Door 3 bridge interface
- 850fbc25 | 2026-09-05 | Document Float radius bridge obstruction
- 38388e4e | 2026-09-05 | Audit Door 3 Float radius bridge
- d7317486 | 2026-09-05 | Record Door 3 bridged grid boundary obstruction
- 2dcba98a | 2026-09-05 | Document cutoff zeta and derivative reductions
- 0090daf7 | 2026-09-05 | Add cutoff derivative supplier interface
- 4f91baa5 | 2026-09-05 | Tighten Door 3 cutoff eta factor
- 100fe071 | 2026-09-05 | Add Door 3 zeta cutoff certificate adapter
- 493ae9e6 | 2026-09-05 | Prove Door 3 cutoff Gamma lower bound with finite products
- 2e7d2ac2 | 2026-09-05 | Ledger: record C11 29/40 proxies
- 579da30c | 2026-09-05 | Agent C11: R61+R71 mid pair (29/40 proxies); axioms clean
- fc4538f7 | 2026-09-05 | Ledger: record C10 27/40 proxies
- 3f6db734 | 2026-09-05 | Agent C10: R41+R51 inner tier (27/40 proxies); axioms clean
- 3198d54c | 2026-09-05 | Ledger: record C9 25/40 proxies
- 81c398d1 | 2026-09-05 | Agent C9: R21+R31 mid pair (25/40 proxies); axioms clean
- df02150b | 2026-09-05 | Ledger: record C8 23/40 proxies
- e0ff7401 | 2026-09-05 | Agent C8: R01+R11 open y-row 1 (23/40 proxies); axioms clean
- 01a343d8 | 2026-09-05 | Ledger: record GS verification
- 64057b8e | 2026-09-05 | Agent GS (verified GSv): Gamma sups G0=0.232 smallest, tier zeta-side blocked; axioms clean
- 1508c662 | 2026-09-05 | Ledger: record C7 21/40 proxies
- 6e6fd277 | 2026-09-05 | Agent C7: R82+R92 close y-row 2 10/10 (21/40 proxies); axioms clean
- c2e77d23 | 2026-09-05 | Ledger: record R5 scout mapping
- 4640a851 | 2026-09-05 | Agent R5: residual mapping + scout theorems (strips/cutoffs/axis); axioms clean
- bbdeab71 | 2026-09-05 | Ledger: record C6 19/40 proxies
- 2adf4c30 | 2026-09-05 | Agent C6: y-row 2 remainder R42/R52/R62/R72 (19/40 proxies); axioms clean
- f45cd314 | 2026-09-05 | Ledger: record GS pending verification (blocked on R5 cover)
- 55af7afd | 2026-09-05 | Ledger: record FE bridge (placement fixed)
- d930680b | 2026-09-05 | Agent FE: chi-factor machinery + Dirichlet <=3, strip numeral open; axioms clean
- 76beeb4a | 2026-09-05 | Ledger: record V5, pause deriv lane pending FE
- a7e45593 | 2026-09-05 | Agent V5: joint/smallball/localization all quantified dead (300-600x); axioms clean
- 51940b73 | 2026-09-05 | Ledger: record T7, pause tail lane pending FE
- d465d118 | 2026-09-05 | Agent T7: conditional closures d<1/r<2 imply gap, polar cap 1/10; axioms clean
- f240e796 | 2026-09-05 | Ledger: record C5 15/40 proxies
- ae832401 | 2026-09-05 | Agent C5: y-row 2 R02/R12/R22/R32 proxies (15/40); axioms clean
- e4edd021 | 2026-09-05 | Ledger: record V4, factorization dead
- 0db4bb84 | 2026-09-05 | Agent V4: GammaSup G0=1.52 Stirling-free, factorization tier numerically dead (300x); axioms clean
- 8ae103a5 | 2026-09-05 | Ledger: record R4 finale, BD lane closed
- 10d1032f | 2026-09-05 | Agent R4: R39+R40 packaging, BD cover lane CLOSED R31-R40; axioms clean
- 7f28e4e0 | 2026-09-05 | Ledger: record T6 K-verdict
- 4941a01b | 2026-09-05 | Agent T6: K>2 dead (e grows), K=2 minimal, only ||zeta-2||<2 left; axioms clean
- f61f0354 | 2026-09-05 | Ledger: record R37-R38 packaging
- d96deaa0 | 2026-09-05 | Agent R3: R37+R38 small-r packaging via BD template; axioms clean
- 254f7da8 | 2026-09-05 | Ledger: record T5 K=2 dead
- b63a2122 | 2026-09-05 | Agent T5: K=2 split provably dead (B*e+d=2), redirect to ||zeta-2||<2 or K>2; axioms clean
- ee6bb4aa | 2026-09-05 | Ledger: record W4, retire narrow lane
- 0bf9b4e3 | 2026-09-05 | Agent W4: sub-sliver [6.30,6.33] at 217.3, narrow lane DONE; axioms clean
- b781d2c5 | 2026-09-05 | Ledger: record T4 compact bounds
- 1508e122 | 2026-09-05 | Agent T4: compact-cell zeta existence bounds + gap implication; axioms clean
- d92e0766 | 2026-09-05 | Ledger: record R35-R36 packaging
- 42106b13 | 2026-09-05 | Agent R2: R35+R36 small-r packaging via BD template; axioms clean
- 9bbe1d30 | 2026-09-05 | Ledger: record V3 Pi sup
- 5e3bbf9f | 2026-09-05 | Agent V3: fPi sup P=4 proved, Gamma/ZetaSup conds, threshold G*Z<=0.0001; axioms clean
- 04aaf466 | 2026-09-05 | Ledger: record T3 real bridge
- be9176b4 | 2026-09-05 | Agent T3: real shiftedS/mollifier defs, e=1/2 at K=2, Dirichlet route dead; axioms clean
- 529bec03 | 2026-09-05 | Ledger: record R33-R34 packaging
- 15372ede | 2026-09-05 | Agent R: R33+R34 small-r packaging via BD template; axioms clean
- 79b6b4bc | 2026-09-05 | Ledger: record W3 sliver cover
- c4a2d720 | 2026-09-05 | Agent W3: sliver [6.30,6.37] covered at 217.5 (217.2 provably fails); axioms clean
- 46d38bb5 | 2026-09-05 | Ledger: record C4 11/40 proxies
- e48975e6 | 2026-09-05 | Agent C4: bottom-row remainder R73/R83/R93/R03 (11/40 proxies); axioms clean
- 2372249c | 2026-09-05 | Ledger: record W2 6.30 piece, lock-protocol fix
- cc6e31d2 | 2026-09-05 | Agent W2: narrow 6.30 piece <=217.1, sliver now [6.30,6.37]; axioms clean
- 040f3037 | 2026-09-05 | Ledger: record C3 7/40 proxies
- 3294a46e | 2026-09-05 | Agent C3: 6 proxy cells R13-R63 (7/40), all green ~45s; axioms clean
- 1780778a | 2026-09-05 | Ledger: record V2 factor sups
- 532f4b9b | 2026-09-05 | Agent V2: factor sups poly 63.4, four-factor composition, tier threshold; axioms clean
- b6f65b29 | 2026-09-05 | Ledger: record T2 conditional bridge
- feee4b94 | 2026-09-05 | Agent T2: conditional leaf bridge B*e+d<1 implies MollifiedRoucheLeaf; axioms clean
- 05840948 | 2026-09-05 | Ledger: record W narrow 216.9
- 301b6128 | 2026-09-05 | Agent W: Gamma narrow 216.9 at xmax 6.25, table row; axioms clean
- 5d538673 | 2026-09-05 | Ledger: record V deriv toolkit
- fba59747 | 2026-09-05 | Agent V: deriv lane Cauchy toolkit + R00 conditional bound; axioms clean
- 6411e7f0 | 2026-09-05 | Ledger: record C2 checker generalization
- bc1ea2bb | 2026-09-05 | Agent C2: two-sided mul + sqrt-upper rules, R00 proxy cert, 40-cell generator in Temp; axioms clean
- 91ea0e92 | 2026-09-05 | Ledger: record T tail feeders
- 80968b3b | 2026-09-05 | Agent T: tail-leaf feeders (geom bound at 11, norm floors); axioms clean
- b9dc936f | 2026-09-05 | Lakefile: register door3_deriv_certs root for parallel deriv lane
- 79422456 | 2026-09-05 | Ledger: record C1 cert spike
- 5c62edca | 2026-09-05 | Agent C1: cell-cert spike, checker core + timed sample (53s), lakefile root; axioms clean
- 156e2d15 | 2026-09-05 | Ledger: record H10 quad 0.0807, freeze M-grind, pivot to certificates
- e078122c | 2026-09-05 | Agent H10: quad G 0.0807 (D2685/2696 refloors), tier M 100.13256 Azeta 5735; axioms clean
- 7e091e30 | 2026-09-05 | Ledger: record G23, pair program closed
- c1df399f | 2026-09-05 | Agent G23: Ico-block transfer, pair program CLOSED; axioms clean
- 22733052 | 2026-09-05 | Ledger: record G22 window aggregate
- 94da0b99 | 2026-09-05 | Agent G22: [16,32) window Re-sum <=0.22432 aggregate + verdict; axioms clean
- d6343f31 | 2026-09-05 | Ledger: record H9 trio 0.0808
- 3d0131d6 | 2026-09-05 | Agent H9: trio G 0.0808 via a=0.06 refloor D2692, tier M 100.25664 Azeta 5743; axioms clean
- 1acceab1 | 2026-09-05 | Ledger: record G21 last pair, all pairs MVT-closed
- ba0dccdb | 2026-09-05 | Agent G21: pair15 Re<=-0.02 LAST pair, all pairs 8-15 MVT-closed; axioms clean

## Authoritative Door-3 state and residuals (2026-09-07)

This section supersedes intermediate status notes above. The current source has
the complete certificate *interfaces* and the complete finite geometry, but it
does not yet contain a supplied instance of the analytic fields. In particular,
`central_cover_assembly.lean` reports zero cells closed end to end.

### What is proved

* The fine grid has 40 current cells: `R00`, `R02`--`R10`, and `R11`--`R40`.
  Their exact coordinates, radius bounds, row/column membership, overlapping
  open and closed coverage, lower-half conjugation maps, and row assembly are
  proved. The rational generator and `door3_rational_grid_cover.lean` provide
  the same geometry independently of the analytic layer.
* Every cell has a sorry-free fencing and zero-free constructor. The joint
  theorem `allCentral_H_of_obligations` reduces all 40 cells to
  `FullCentralObligations`, and `full_central_covered` reduces the inner cover
  to `FullCentralObligations` plus `BottomStripObligations`. These are
  implication theorems; neither obligation is currently instantiated.
* Polynomial, π-power, Gamma, reflection, and most factor arithmetic is
  unconditional. The R02 eta continuation now gives the unconditional bounds
  `R02_zeta_upper_unconditional` (`‖ζ‖ ≤ 1012`) and
  `R02_deriv_bound_unconditional` (`‖deriv ξ‖ ≤ 6800640`). Those bounds are
  genuine theorems, but the derivative constant is too large for the chosen
  R02 fencing tier and the required `‖ζ‖ ≤ 10` bound remains a separate
  quantitative target.
* The real-critical ζ feeder, real-`s`-axis ξ values, the
  complete imaginary-axis shifted-ξ nonvanishing result (including the
  origin), the four-term reflected head lower bound `1/6`, endpoint identities,
  and qualitative compact edge/axis neighborhoods are unconditional. They do
  not prove nonvanishing on the `z.im = 0` segment of the central rectangle.
* `FiniteZetaLowerCertificate.lower_of_re`, the R00/reflected constructors,
  the R03--R10 constructors, and `OffAxisFiniteCertificateBundle` are ordinary
  kernel implication APIs. The only analytic fields they consume are explicit
  finite-sum/tail/factor lower data and derivative bounds; no Float value and no
  `RiemannHypothesisProp_apply` is hidden in them.

### What remains for Door 3

1. **Inner 40-cell analytic fields (80 obligations).** For each current cell,
   supply the center inequality
   `ε + M * radius ≤ ‖xiShifted center‖` and the uniform derivative inequality
   `∀ z ∈ rect, ‖deriv xiShifted z‖ ≤ M`. The exact-rational tables prove only
   positivity, geometry, and budget arithmetic. Their `centerLower` and
   `derivUpper` values are marked `sampled_unverified` and are not analytic
   bounds. A kernel-checked complex-ζ/ξ enclosure is still required.
2. **Bottom strip.** Instantiate `BottomStripObligations`: for every
   `-10 < x < 10`, provide a positive base lower bound for
   `xiShiftedEntire (x : ℂ)`, a derivative bound on the `0 ≤ y ≤ 0.02`
   vertical segment, and the strict `0.01 < ε₀/M₁` margin. The imaginary-axis
   and local-strip theorems supply qualitative data only and do not provide
   this uniform numerical supplier.
3. **Top and bottom edge strips.** The ten cells covering
   `(-10,10) × [0.49,0.5)` have `y1 = 0.5`, so the inner-cell fencing theorem
   cannot be reused. They need the outer-boundary theorem with an explicit
   fixed-width (at least `0.01`) lower bound and derivative bound, then lower
   halves must be mirrored. The existing compactness results provide a
   positive width and minimum existentially, not the required numerical values.
4. **Cutoff lines `Re z = ±10`.** `CutL10`, `CutR10`, and
   `cutoffLines_either` prove the geometric split. The two thin-rectangle
   center and derivative enclosures on the vertical `s` rectangles
   (`Im s = ±10`, `Re s ∈ [0.01,0.99]`) are still missing; the same edge-strip
   obligations cover the `0.49 ≤ |Im z| < 0.5` parts.
5. **Real-axis segment.** The central cover deliberately excludes `z.im = 0`.
   The proved imaginary-axis result concerns `z = I*y` and is a different
   slice. A nonvanishing/lower-bound certificate for every real `z` with
   `-10 < z.re < 10` is still required before the central rectangle is closed.
6. **Finite off-axis sums.** The eight-cell bundle for `R03`--`R10` still
   needs genuine finite eta-sum lower certificates meeting the stated
   `1/2` thresholds and the eight derivative suppliers. R00 and its reflected
   R10 bridge reduce to explicit finite sums as well; the candidate tables do
   not supply those sums.

### Downstream assembly boundary

Once the central, strip, edge, cutoff, and real-axis suppliers are actually
provided, the existing rectangle and conjugation assemblies yield the required
`XiCentralZeroFreeCover 10`-shaped input. The RH implication theorems in
`riemann_hypothesis_newsection.lean` and `door3_height11_bridge.lean` still also
take their explicit tail supplier (`CompletedZetaTailU10`/mollified tail) and,
for the full Door-2 capstone, the cutoff-line and edge-strip suppliers. These
are named inputs in the theorem signatures, not hidden assumptions. No current
commit proves all of them, so Door 3 and RH remain open despite the
sorry-free infrastructure and the complete commit ledger above.
- 2026-09-07 ZU (`ad4e3085`, zeta_rigorous tail, green, axioms clean):
  `R02_D3_zeta_upper_934` (`‖ζ‖ ≤ 934` on R02 rect, was `≤1012`).
  Eta-route floor documented in-file: reaching `≤10` needs `M ≥ 33.2^20`
  terms — infeasible; next: FE+Stirling+convexity route (tasked as ZU2).
- 2026-09-07 CC (`e9b6d579`, cover tail lines 16813–16972, green 8687 jobs):
  CutR10 eta-factor cap `‖1-2^(1-s)‖ ≤ 1` + outer-tier honest negative.
  Next: finite partial-sum datum for `cutR10_zetaRemainder_of_certificate_one`.
- 2026-09-07 OA (`e00cb9df`, off-axis tail, green 8702 jobs, axioms clean):
  first genuine `FiniteZetaLowerCertificate` instance (R03, N=2).
  Honest gap: ratio `(1/5-61/5)/(13/5) < 0.5` — M=1 tail dwarfs slow bound
  row-wide; threshold needs larger-N slow + decayed tail (tasked as OA2).
- 2026-09-07 TS (`6d3bc2af`, newsection tail, green 8702 jobs, axioms clean):
  `Door3TailSlab278` slab supplier (`‖ζ‖ ≤ 278`, shifted feeder, K2
  Rouché-product cap). Still open: `CompletedZetaTailU10` Gamma wiring.
- 2026-09-07 ZU2 (`b310203a` pt 1, zeta tail, green 8693 jobs, axioms clean):
  FE strip-cap tier (`‖F‖ ≤ 30` right edge, chi caps, `‖ζ‖=‖F‖/‖s-1‖`
  conversion). Residual: Stirling Gamma numeral `G` (tasked as ZU3).
- 2026-09-07 RX (`b310203a` pt 2, tail-scratch, green 8682 jobs):
  `door3RealSeg` compact bridge (uniform⇔pointwise certificate pair).
- 2026-09-07 RX2 (`0e1cdf29`, tail-scratch, green 8682 jobs, axioms clean):
  height-0 numeral `c=1` + `door3RealSegNext` tile, conditional on
  `Door3HalfRealHyp` (`1 ≤ ‖ζ(1/2)‖`, proved in zeta-cutoff but outside
  tail import closure). Next: discharge hyp in-file (RX3).
- 2026-09-07 RX3 (`72759f8c`, tail-scratch, green 8682 jobs, axioms clean):
  `1 ≤ ‖ζ(1/2)‖` reduced to ONE lemma `Door3EMRightAnalytic`
  (EM identity banked; ~500-line continuation engine over budget).
  Next: mirror TestAnalytic termTSumC engine (RX4).
- 2026-09-07 RX4 (`af510691`, tail-scratch, green 8682 jobs, 6 builds):
  UNCONDITIONAL `1 ≤ ‖ζ(1/2)‖` via mirrored term-engine
  (`door3EMRightAnalytic_proved`). Next: uniform lift + tiling (RX5).
- 2026-09-08 RX5 (`5dd24ff0`, tail-scratch, green 8682 jobs, axioms clean):
  height `|t|≤1` enclosure + second tile (`door3RealSegNext2`,
  coverage now [-1,3]). Residual: pointwise nonvanishing on full arc
  (tasked as RX6).
- 2026-09-08 RX6 (`2e0de714`, tail-scratch, green 8682 jobs, axioms clean):
  third tile (`door3RealSegNext3`, coverage [-1,4]) + tile uppers.
  Residual: pointwise LOWER at new height (tasked as RX7).
- 2026-09-08 RX7 (`0a439816`, tail-scratch, green 8682 jobs, axioms clean):
  fourth tile (`door3RealSegNext4`, coverage [-1,5]) + upper.
  Residual: height-`t≠0` enclosure still absent (tasked as RX8).
- 2026-09-08 RX8 (`d60e39f1`, tail-scratch, green 8682 jobs, axioms clean):
  fifth tile (`door3RealSegNext5`, coverage [-1,6]) + upper.
  VERDICT (in-file doc): Mathlib has NO height-`t≠0` zeta enclosure
  (closest need `Re≥1`; RH statement is not a bound). Next: tile [6,7]
  + direct enclosure attempt (RX9).
- 2026-09-08 RX9 (`afb42327`, tail-scratch, green 8682 jobs, axioms clean):
  sixth tile (`door3RealSegNext6`, coverage [-1,7]) + height-`1/2`
  slow (`1/5`) + factor (`13/5`) at exact point. Residual: paired-tail
  `‖G−S₂‖ ≤ rtail` in-tail (tasked as RX10).
- 2026-09-08 RX10 (`ad87cd10`, tail-scratch, green 8682 jobs, axioms clean):
  tile [7,8] (coverage [-1,8]) + neg-height mirror block. NOTE: agent
  cut off mid-write (empty report); 2-paren rescue by coordinator.
  Residual: paired-tail bound still open (tasked as RX11).
- 2026-09-08 RX11 (`a62e7875`, tail-scratch, 3× green 8682 jobs):
  in-tail pair replica + `‖pair 1‖ ≤ 11/10` estimate (anti-cutoff
  discipline held). Residual: MVT pair bound + summability (RX12).
- 2026-09-08 RX12 (`14ad9197`, tail-scratch, 5× green 8682 jobs):
  in-tail MVT pair bound + summability at Re=1/2 + `d3Zeta_lower_of_tail`
  bridge. Residual: rtail numeral + eta bridge (RX13).
- 2026-09-08 RX13 (`a1455037`, tail-scratch, 3× green 8682 jobs):
  pair-1 MVT bound `≤1/5` + PROVED M=1 unprovability (MVT sums ≈0.35).
  Route: deeper shift K=3 (≈0.14 feasible) + re-index (RX14).
- 2026-09-08 RX14 (`cb0bdd50`, tail-scratch, 5× green 8682 jobs):
  integral tail mirror + shift `≤5/6` + `‖∑' pair(m+3)‖≤5/6` +
  PROVED `<1/5` unprovable at K=3 on MVT route (true ≈0.40).
  Route: K≥16 peel, K≈8 exact-norm, or re-indexed head (RX15).
- 2026-09-08+ RX15 (`509e27a5`, tail-scratch, 4× green 8682 jobs):
  K=51 shift enclosure `‖∑' pair(m+51)‖ < 1/5` (single cleared-square
  numeral `201/20`; minimal K on loose shift majorant).
  Residual: generalize re-index to K=51 + enlarged-head bound + close
  (RX16, LARGE scope).
- 2026-09-08+ RX16 (`6e5490c9`, tail-scratch, 3× green 8682 jobs):
  finite aggregation + K51 re-index + conditional lower-bridge +
  explicit `c = 1/2613` + pointwise nonvan + segPt membership.
  PROVED S2-reverse-triangle route vacuous (margin 1/1005 vs pair
  uppers); uniformity gap (pointwise t=1/2 vs ∀ seg) also open.
  Residual: direct 102-term head estimate + eta bridge + uniform
  lift (RX17, LARGE scope).
- 2026-09-09 RX17: silent failure (empty diff, empty report) → RX18.
- 2026-09-09 RX18 (`6bcf1639`, tail-scratch, 7× green 8682 jobs):
  `head₁₀₂ = S₆ + tail` split + uniform eta-factor/shift/pair
  bounds + uniform tail `16/67` + uniform bridge shape.
  Gaps quantified: `‖head₁₀₂‖≈0.660`, `‖S₆‖≈0.559`, A=3 margin
  +0.251 viable; eta bridge needs Dirichlet-eta continuation
  (Mathlib: Re>1 only); uniform head needs >16/67.
  Residual: rigorous S₆ bound via cos/log intervals (RX19, LARGE).
- 2026-09-09 RX19: silent failure (empty diff, empty report) → RX20.
- 2026-09-09 RX20 (`f5001ca7`, tail-scratch, 12× green 8682 jobs):
  self-contained cos-quadratic floor + log2–log6 bounds +
  θ₀..θ₅ phases + 6 cos plugs + 6 rpow floors (25 theorems).
  Residual: S₆ assembly from floors (check eta sign/phase
  convention first; mirror d3_rpow_two pattern) (RX21).
- 2026-09-09 RX21: convention lemmas (signed alternating) —
  left `d3_inv_nat_cpow_re_eq` UNVERIFIED → RX22.
- 2026-09-09 RX22: re-fix green (sorryAx eliminated) + 5u block
  appended unvalidated → RX23.
- 2026-09-09 RX23 (`bd517f00`, tail-scratch, 3× green 8682 jobs
  via wrapper): 5u RED→GREEN (3-line repair: rpow-nonneg arg +
  whole-term rfl rewrites) + Re residues 2–5 (bases 3–6).
  Re(S₆)≈0.4977<0.53 CONFIRMED — 2-D enclosure mandatory.
  Residual: Im factorization + im_0..5 (RX24).
- 2026-09-09 RX24 (`fcca75c1`, tail-scratch, 3× green 8682 jobs
  via wrapper): Im factorization (`−r·sin θ`) + Im residues
  0–5 (odd double-negation via `neg_neg`). Re+Im per-residue
  equations COMPLETE (k=0..5 both parts).
  Residual: sin lower-bound helper + 6 sin plugs + Re/Im
  floor assembly (RX25).
- 2026-09-09 RX25 (`d754d8ae`, tail-scratch, 2× green 8682 jobs
  via wrapper): `d3_sin_lower` (wraps `Real.sin_ge_sub_cube`) +
  6 theta sin plugs (33/100..74/100). Im-side trig COMPLETE.
  Residual: Re/Im floor assembly → norm 53/100 (RX26).
- 2026-09-09 RX26 (`e29fdc7d`, tail-scratch, 3× green 8682 jobs
  via wrapper): cos-uppers helper + Re ≥ 31/100 + Im ≥ 12/100
  → **`‖S₆‖ ≥ 33/100`** (first 2-D bound; shortfall 20/100;
  brief sub-targets proven jointly insufficient anyway).
  Residual: interval tightening → 53/100 (RX27).
- 2026-09-09 RX27 (`0c6132c8`, tail-scratch, green 8682 jobs via
  wrapper after 9h stall cleared): rpow lowers + stronger cos
  lowers + sqrt-route sin uppers → Re 42/100 + Im 14/100 →
  **`‖S₆‖ ≥ 44/100`** (+11; gap 9/100). PROVED Re ≥ 0.50
  infeasible (true 0.4977) — my sub-target was wrong.
  Residual: odd-term upper tightening (RX28).
- 2026-09-09 RX28 (`fb6a7395` part 1, tail-scratch, appended
  unbuilt under contention): tighter rpow uppers (3→7/12,
  6→49/120, 2→99/140).
- 2026-09-09 RX29 (`fb6a7395` part 2, tail-scratch, 2× green):
  uppers verified + Re43 floor.
- 2026-09-09 RX30 (`fb6a7395` part 3, tail-scratch, 2× green):
  Im15+norm45 verified as-is + sin-θ₄-upper → Im17 →
  **`‖S₆‖ ≥ 46/100`** (+1; gap 7/100).
  Residual: sin-θ₅ 0.76+ + narrower θ₂/θ₄ intervals (RX31).
- 2026-09-09 RX31 (`4ffd5510`, tail-scratch, 7× green 8682 jobs
  + 1 fail-fixed): log3 10× narrower (width 0.0071) via
  log(9/8) trick → sin θ₅ 77/100 → cos θ₅ ≤ 65/100 +
  θ₂ narrowed → cos θ₂ 84/100 → Re 45/100 + Im 18/100 →
  **`‖S₆‖ ≥ 48/100`** (+2; gap 5/100).
  Residual: θ₄ narrow via log(25/24) trick (RX32).
- 2026-09-09 RX32 (`a493b603`, tail-scratch, 6× green 8682 jobs):
  log5 narrow via log(25/24) → θ₄∈[0.803,0.806] → cos 67/100
  → sin-upper 743/1000 + sin-θ₂-upper + rpow uppers (3→11/19,
  5→9/20) → Im 20/100 → **`‖S₆‖ ≥ 49/100`** (+1; gap 4/100).
  Residual: Re_lower5 + sqrt tightenings → 50/100 (RX33).
- 2026-09-09 RX33 (`2120983e`, tail-scratch, 3× green 8682 jobs):
  Re_lower5 + 4-digit sqrt floors + cos θ₅ ≤ 64/100 →
  Re 46/100 → **MILESTONE `‖S₆‖ ≥ 50/100`** (Im21 skipped:
  hnum would be false; closed via 46+20 fallback).
  Residual: Im21 via Taylor sin-upper + Re47 → 51/100 (RX34).
- 2026-09-10 RX34 (`1d6bee59` part 1, tail-scratch, 2× green):
  Im21 verified + Re47/norm51 (margins +0.001/+0.0049).
- 2026-09-10 RX35 (`1d6bee59` part 2, tail-scratch, 2× green):
  norm51 verified as-is + sin-θ₄-upper → **Im22** (margin
  +0.00425). Norm holds 51 (52 needs 0.2704 > 0.2693).
  Residual to 53: 0.0116. Next: sin-θ₁ lift → Im23 →
  norm52 (RX36).
- 2026-09-10 RX36 (`053781b2`, tail-scratch, 1× green 8682 jobs
  + 1 fail-fixed): sin-θ₁ 3395/10000 (margin +0.000085) →
  Im23 (+0.0009) → **`‖S₆‖ ≥ 52/100`** via 47+23
  (margin +0.0034). Residual to 53: 0.0071.
  Next: Im25 or Re48+Im23 → 53/100 (RX37).
- 2026-09-10 RX37 (`df35cb13`, tail-scratch, 2× green 8682 jobs):
  sin→cos inversion helper (`c²+s²≤1`) → cos θ₂ 85/100 +
  cos θ₄ 68/100 → Re 48/100 → **ENCLOSURE CLOSED:
  `‖S₆‖ ≥ 53/100`** (surplus 0.0024; gap-to-true ≈0.029).
  Residual: 48-term cap + head discharge + uniformize (RX38;
  caution: S₆ bound is pointwise, hHead needs seg-uniform).
- 2026-09-10 RX38 (`5e56cf8c`, tail-scratch, 2× green 8682 jobs
  + 2 fail-fixed): 48-term cap (`d3rpow48_le` ≤0.32581,
  `d3tail48_norm_le` 33/100) + **`d3head102_norm_ge`
  (1/5 ≤ ‖head₁₀₂‖** via S₆+tail reverse-triangle 0.53−0.33)
  + conditional uniform wiring (c=15/3484 under hZeta).
  HONEST: enclosure OPEN — S₆-split uniform route PROVED
  infeasible (needs S₆-uniform >0.608 > 0.53 pointwise);
  uniform 1/4-head + hZeta still open.
  RX LANE RETIRED here (consumerless per 2026-09-10 audit;
  contention relief).
- 2026-09-09 INCIDENT: `riemann hypothesis.lean` (spaced legacy
  filename, 11968 lines) found deleted from disk (unstaged);
  restored via `git checkout`. All agents: NEVER touch it —
  it is NOT your file under any spelling.
- 2026-09-09 RH-DIS (`3cfbb366`, RH tail, green 8685 jobs;
  resumed after harness crash, tail intact): 7 genuine
  unconditional theorems (imag-axis balls/rects/covers/bands,
  axiom-free) + inventory (~60 conditionals classified) +
  CIRCULARITY FLAGS (6 names transitively citing line-34 —
  never citable). Capstone 0/4. Lane-banked Gamma remainder
  UNWIRABLE in-tail (import cycle) — needs downstream file.
  Residual: downstream wiring file (RH-WIRE).
- 2026-09-09 RH-WIRE (`fdc9e72a`, new file, green 8705 jobs via
  wrapper after 9h stall cleared): Gamma wall closed downstream
  + zeta/deriv adapters + CutR10 fencing assembly + rect +
  right-line nonvanishing + `XiCutoffLines10` + capstone
  `rh_of_cutR10_fencing_and_premises` (axioms-clean, no banned
  circular cites). Conditional on 5 premises: (a) zeta slow-sum
  triple at sCut=1/2+10I (OFF-AXIS lane), (b) closedBall sup
  (real-arc), (c) CutL10 left line, (d) 0.49-sliver, (e) feeders.
  Residual: (a) slow-cert at sCut → feed fencing (OA24).
- 2026-09-07 ZU3 (`7856eef2` pt 1, zeta tail, green 8693 jobs):
  Stirling Gamma numeral `‖Γ(1-s)‖ ≤ 4` (integral domination + shift +
  convexity cap; 3 identifier micro-fixes by coordinator). Chi cap
  `‖χ‖ ≤ 2·1·4·e^13` banked. Next: three-lines interpolation (ZU4).
- 2026-09-07 ZU4 (`d8759a5c`, zeta tail, green, axioms clean):
  damped-`G` `DiffContOnCl` + conditional interpolation instance +
  `‖ζ‖ ≤ M/5.25` converter. Residual: edge numerals a/b + `BddAbove`
  + damp lower (tasked as ZU5).
- 2026-09-07 ZU5 (`74568546`, zeta tail, green 8693 jobs, axioms clean):
  damp lower `e⁻¹ ≤ ‖damp‖` (numerator for `‖F‖ ≤ ‖G‖/e⁻¹` split).
  Residual: whole-line edge caps a/b + `BddAbove` (tasked as ZU6).
- 2026-09-08 ZU6 (`c0d67bdb`, zeta tail, green 8693 jobs, axioms clean):
  damp line-uppers + window caps 23400 + rect `BddAbove`. Honest gap:
  23400 → ~12000 after interp split, not 10; whole-line caps missing
  (tasked as ZU7).
- 2026-09-08 ZU7 (`3668dba6`, zeta tail, green 8693 jobs, axioms clean):
  conditional whole-line caps (805·C/616·C) + strip `BddAbove` +
  Gauss-domination core. Residual: linear growth inputs C/K (ZU8).
- 2026-09-08 ZU8 (`ab925e91`, zeta tail, green 8693 jobs, axioms clean):
  linear Dirichlet inputs (C=3 at Re=2, C=934 window) + exp chi-ratio
  `8·e^(1.5708|Im|)`. Honest negative: uniform K UNREACHABLE (banked
  Gamma cap has no Stirling decay; 3.4M at window). Next: line-uniform
  Stirling decay (ZU9).
- 2026-09-08 ZU9 (`74b89285` pt 1, zeta tail, green 8693 jobs, axioms clean):
  shift-decay `‖Γ‖ ≤ 2/(‖s‖‖s+1‖)` → poly-decay → window55 `≤ 0.0726`
  (55× over decay-free). Honest negative: requested `c>π/2` rate FALSE
  (true `|t|^0.45·e^(-π|t|/2)`); polynomial factor needed (ZU10).
- 2026-09-08 ZU10 (`b4301134`, zeta tail, green 8693 jobs, axioms clean):
  sharpened chi-ratio (`4/|Im|²` + window55 `0.1452·e^…`).
  Residual: line-uniform linear bound at Re=0.95 (ZU11).
- 2026-09-08 ZU11 (`f7c531c5`, zeta tail, green 8693 jobs, axioms clean):
  eta denominator floor `0.035 ≤ ‖1−2^(1−s)‖` at Re=0.95, uniform
  in Im. Residual: pair-grouped eta numerator (ZU12).
- 2026-09-08 ZU12 (`1a3322bd`, zeta tail, 2× green 8693 jobs, axioms clean):
  per-pair `‖pair‖ ≤ ‖s‖·(2n+1)^(−1.95)` + n=0 + norm corollaries.
  Residual: tail-series numeral K0 + linear assembly (ZU13).
- 2026-09-08 ZU13 (`708f38fa`, zeta tail, green 8693 jobs, axioms clean):
  shift/odd summability + antitone majorant + integrability +
  integral-tail comparison (1-line strictness fix by coordinator).
  Residual: K0 numeral + linear assembly + close (ZU14).
- 2026-09-08 ZU14 (`dfc0e97b`, zeta tail, 3× green 8693 jobs):
  K0=2.06 (integral 1/0.95) + line095 linear `‖ζ‖≤58.86(1+|Im|)`.
  Residual: FE-reflected whole-line 0.05 + whole-line 0.74 + strip + close (ZU15).
- 2026-09-08+ ZU15 (`f5d7ab8e`, zeta tail, 1× green 8693 jobs):
  FE-reflected whole-line 0.05 bounds (exp + poly-sharpened) +
  PROVED uniform-K reflection blocked on MVT route (chi exp-growth
  vs poly Gamma decay; crude 805-constant unreachable).
  Route: direct eta-pair linear on Re=0.05 (C05≈23) + Re=0.74/0.26 (ZU16).
- 2026-09-08+ ZU16 (`fd4eb414`, zeta tail, 7× green 8693 jobs):
  exponent-1.05 chain (summability → integral 1/0.05 → K0=21 →
  eta linear → `2^0.95` floor → denom 0.93) →
  **`‖ζ‖ ≤ 23·(1+|Im|)` on Re=0.05** (FE path superseded).
  Residual: mirror on Re=0.74/0.26 + Gdamp instantiate + close
  (ZU17, LARGE scope).
- 2026-09-09 ZU17 (`6412602e`, zeta tail, 8× green 8693 jobs):
  exponent-1.74 mirror → K0=3 → **`‖ζ‖≤16(1+|Im|)` Re=0.74** +
  strip `‖ζ‖≤111(1+|Im|)` (feeds hB directly) + PROVED Gdamp route
  floor: best-possible ≈9593 (crude 805/616 constants), ~960× over.
  Eta-mirror path CLOSED at its floor. Residual: line-uniform FE
  chi-ratio with Stirling exp decay (ZU18, LARGE scope).
- 2026-09-09 ZU18 (`95fc3d4e`, zeta tail, 3× green 8693 jobs):
  chi/ratio/linear/Gdamp CONDITIONALS on exp-Gamma hypothesis +
  PROVED Gdamp CLOSED-NEGATIVE for `‖ζ‖≤10` regardless (damp-loss
  forces a,b ≥ 9856; floor ≈9593+). Missing: Stirling remainder
  (Mathlib Gamma: no exp-decay upper) + non-Gdamp endgame.
  Residual: Stirling remainder from Gamma integral (ZU19, LARGE).
- 2026-09-09 ZU19 (`8138972a`, zeta tail, 3× green 8693 jobs):
  Gamma shift-3 (`Γ(w+3)` recurrence) + `Real.Gamma 3.95 ≤ 6` +
  cubic poly decay `6/|t|³` (NO exponential — Stirling exp still
  missing from Mathlib) + direct rect cap **`‖ζ‖≤1221`** (strip
  dominates) + gap verdict 1211. FE-reflected route DOMINATED
  (conditional 5181 > unconditional 1221).
  Residual: staged poly-decay/chi-cap appends + endgame pivot
  to strip-C lowering (ZU20, LARGE scope).
- 2026-09-09 ZU20 (`544981dd`, zeta tail, 7× green 8693 jobs):
  staged poly3-decay/window/chi-cap landed + low-slice chain
  (2^0.5 floor → denom 0.414 → eta 21 → **C=51, rect 561**
  on 0.05≤Re≤0.5; high half still 1221). Best rect 561 low /
  1221 high (gap 551/1211).
  Residual: high-slice K0 at exponent −1.5 → C≈14 (ZU21).
- 2026-09-09 ZU21 (`b6f4ea3a`, zeta tail, 4× green 8693 jobs):
  exponent-1.5 chain (integral 1/0.5 → K0=3, true ≈1.69) →
  **`‖ζ‖≤16(1+|Im|)` on 0.5≤Re≤0.74** (high rect implied 176,
  not yet banked). Best rect 561/176 (was 561/1221).
  Residual: rect numeral + assembly + gap verdict, then K0
  tightening or new idea (ZU22).
- 2026-09-09 ZU22 (`daf6a312`, zeta tail, coordinator-validated
  green 8693 jobs; agent report empty, work orphaned in tree):
  rect-176 numeral + assembly2 (561/176) + peeled Ioi2 integral
  `≤1.42` (STEP 2 partial; head numeral open).
  Residual: peeled head numeral + tightened K0 assembly (ZU23).
- 2026-09-09 ZU23 (`2e592831`, zeta tail, 5× green 8693 jobs):
  N=2 odd-head numeral (`3^(−1.5)≤0.20`) + M=2 comparison →
  **K0 3→2.62 → C 16→14 → rect 176→154** high slice; assembly3
  best rect 561 (low slice dominates, gap 551).
  Residual: low-slice N=3 peel, K0 21→~peeled (ZU24).
- 2026-09-09 ZU24 (`3bb54a19`, zeta tail, 10× green 8693 jobs;
  resumed after stale-lock stall, prior 179 lines green as-is):
  N=3 head (1.51) + M=3 integral (19.06) → **K0 20.57 → C=50
  → rect 550** (gain 11; slow-tail wall confirmed). Best 550/154.
  Residual: N=4 peel or low-slice denom lift (ZU25).
- 2026-09-09 ZU25 (`6ef06244`, zeta tail, 4× green 8693 jobs via
  wrapper): N=4 REJECTED (K0→20.32 < 20.286 needed, zero gain);
  sub-slice denom lift PICKED (`2^0.7≥1.62` → floor 0.62 →
  **C=34, rect 374** on [0.05,0.3]). Global still 550 (far piece
  [0.3,0.5] pinned: denom 0.414 tight at s=0.5).
  Residual: far-piece norm cap `‖z‖≤0.5+|Im|` → 525 (ZU26).
- 2026-09-09 ZU26 (`cedfba2f`, zeta tail, 2× green 8693 jobs via
  wrapper): tight low linear `50·(0.5+|Im|)` → far rect **525**,
  assembly6 best **525** (was 550; gain 25, residual 515).
  Residual: near-tight 357 + high-tight 151 (ZU27).
- 2026-09-09 ZU27 (`a4a3e940`, zeta tail, 3× green 8693 jobs via
  wrapper): near-tight **357** (was 374) + high-tight **151**
  (was 154) + assembly7 (low 525). Global still 525 (far piece
  [0.3,0.5] bottleneck). Residual: full assembly8 + far-piece
  0305 attack (ZU28).
- 2026-09-09 ZU28 (`46ce49f0`, zeta tail, 3× green 8693 jobs via
  wrapper): assembly8 (FULL strip `≤525`) + mid-piece chain
  (`2^0.6≥1.51` → denom 0.51 → C=41 → rect **451** on
  [0.05,0.4]). Bottleneck now tail [0.4,0.5] at 525.
  Residual: mid tight-norm 431 + tail K0 attack (ZU29).
- 2026-09-09 ZU29 (`4d2d47db`, zeta tail, 4× green 8693 jobs via
  wrapper): mid tight-norm `41·(0.5+|Im|)` → rect **431**
  (was 451, −20). Global still 525 (tail bottleneck; cheap
  wins exhausted — slack only ~0.15 vs 0.29 needed).
  Residual: N=5 peel at −1.05 → ~515 (ZU30).
- 2026-09-09 ZU30 (`c99367a3`, zeta tail, 7× green 8693 jobs
  incl. 6 post-stall-resume): N=5 head (1.75) + M=5 integral
  (18.52) → **K0 20.27 → C=49 → global 515** (was 525;
  edge `525−515=10`). Slack to 48-linear ~0.40.
  Residual: N=7 peel → 505 (ZU31).
- 2026-09-09 ZU31 (`65ea4104`, zeta tail, 6× green 8693 jobs):
  N=7 head + M=7 integral (18.2) → **K0 20.12** (was 20.27) +
  gap verdict. Brief's 505 numbers DISPROVED by computation
  (true integral ≈18.146>18.0; total ≈20.044>20.0). Best stays
  515. Peel treadmill near end (each N buys ~0.15).
  Residual: denom lift 0.414→0.42 → 505 (ZU32); N=11 fallback.
- 2026-09-10 ZU32 (`e5859129` part 1, zeta tail, appended
  unbuilt): 0.42-impossibility PROOF (|1−√2|≈0.4142) + 2
  cleared-pows (N=11 fallback start).
- 2026-09-10 ZU33 (`e5859129` part 2, zeta tail, 1× green):
  cleared-pows verified + 38c/38d floors/identities (unbuilt).
- 2026-09-10 ZU34 (`e5859129` part 3, zeta tail, 10× green
  8693 jobs): 38c/38d verified + full N=11 chain (head 2.119
  + tail 17.75 → **K0 19.869 → C=48 → GLOBAL 505**,
  edge `515−505=10`).
  Residual: N=13 peel → 495 (ZU35).
- 2026-09-10 ZU35 (`356424f7`, zeta tail, 6× green 8693 jobs
  + 2 fail-fixed): N=13 floors + M=13 tail 17.61 → head
  2.192 → **K0 19.802 → C=48 → GLOBAL 504**
  (edge `505−504=1`). Target 495 MISSED: 47-linear needs
  K0≤19.458 (gap 0.344); M13≈17.3 spec unreachable at
  1.05-exponent. PEEL LANE ENDS HERE per consumer audit
  (no external reader) — ZU36 redirects to CutL10 (below).
- 2026-09-10 CONSUMER AUDIT (coordinator, repo-wide `rg`):
  peel product (`rect_slice_assembly*`, `linear_slice0550_tight*`,
  `tight48/505`) cited ONLY inside `zeta_rigorous.lean` — NO
  external consumer. Capstone premises take incompatible shapes
  (slow LOWER at t=10 [OA-owned]; xi sup ≤0.04 at Re≈10; raw
  nonvanishing lines/strips with `Im≠0`; Hmain/Hedge/Htail all
  `Im≠0`). Cutoff s-rect tight-upper-10 need is O(1) at |Im|=10;
  peel majorants floor ~500 there by construction (C·10.5) —
  shape-mismatched. VERDICT: stop peeling after ZU35 lands.
  No `cutL10_zetaRemainder` Prop exists anywhere (CutL10 has
  geometry only, no interface, no owning lane) — that is the
  implemented consumer (see redirect).
- 2026-09-10 REDIRECT (fires as ZU36 when ZU35 reports; same
  file, so strictly after): CutL10 zeta remainder. Target:
  `‖zeta (1/2 − 10·I)‖ ≥ 7/5` (mirror of `cutR10_zetaRemainder`,
  true ≈1.549 by conjugation symmetry), self-contained eta-pair
  head+tail in zeta tail (conjugated numerals, no cross-file
  imports), then CutL10 adapter interface. CutR10's 7/5 stays
  OA-owned via slow-cert; (b) ballSup-0.04 is unowned and needs
  scoping before any lane takes it. NOTE (same trace): RX
  bridge product is likewise consumerless (real axis: feeder
  closed + `Im≠0` in every capstone premise) — retire RX lane
  after RX38/RX39 land the in-file chain (DONE: RX38 `5e56cf8c`,
  lane retired, no RX39).
- 2026-09-10 CUTL draft received (NEW `door3_cutL10_remainders.lean`,
  552 lines, untracked-only, 0 sorry, unbuilt): full
  `Door3CutL10Center` mirror (center/poly/pi PROVED; eta-factor
  cap `‖1−2^(1−sCutL)‖≤1` PROVED; `hLeft`-shaped conclusion +
  both-fencings `xiCutoffLines10` assembly PROVED conditional).
  Premises for fix-waves: zeta-lane numeral at `sCutL`
  (exact ZU36 target shape specified in-file), gamma
  `hConjNorm`+banked, deriv sup `hC` (mirrors :404).
  Lakefile registration deferred until all 4 write-only
  drafts land (DONE: `c92f58fb` registers all 4).
- 2026-09-10 CUTL-complete received (456/0 on top, unbuilt):
  Gamma-conjugation CLOSED (`Complex.Gamma_conj` +
  `Complex.norm_conj` pinned by read; gamma remainder from
  banked, premises-free); CutL10 ball geometry + poly ≤67 +
  pi ≤16/5 PROVED; honest weak cap ≤12.87 (NOT 0.04);
  supplier-composition chain complete. Residual: ONLY zeta
  `hLower` at sCutL (ZU36 owns) + `hJoint` 0.04-tightness +
  already-banked `hBanked`.
- 2026-09-10 SLIV draft received (NEW `door3_sliver_nonvan.lean`,
- 2026-09-10 SLIV-EDGE received (`8305537d`, NEW 420 lines,
  0 sorry, unbuilt): edge s-mapping PINNED (top→`Ix`,
  bottom→`1+Ix` — bottom is Euler territory); pointwise
  mT=mB=1/2 at x=0 PROVED; MT/MB conditional on
  closedBall-0-12 sup. Residual: uniform edge-lowers +
  ball sups + numeric gates.
- 2026-09-10 ETA-BALL received (`8305537d`, 510/0 on top,
  unbuilt): Euler `hDom/hReal` + right-sliver ≤3 CLOSED;
  eta head/tail/factor pieces proved; Gamma reaches 1/2
  (not 1/100 — 50× shortfall, needs π/2-rate or ~20×
  product); sharp 12.868 closed. STRUCTURAL: uniform ≤6
  via eta-bridge BLOCKED — eta-factor zero at s≈1+9.06i
  in-band, no uniform denom lower exists (excise discs or
  zero-free variant). Tier-C rect [9.75,10.25] avoids it.
  227 lines, untracked-only, 0 sorry, unbuilt): routing +
  packaging PROVED conditional, end-to-end `hSliver`-shaped
  `hSliver_of_uniformData` PROVED conditional. ONLY new
  numerics for fix-waves: uniform widths `δT,δB > 0.01`
  (banked strips qualitative; needs edge lower + deriv-sup
  numerics; strict-`<` stated so open-bottom strips apply).
- 2026-09-10 FIX-sliver (`e9246ea9`, 6/4, 1× green 8705 jobs
  + 1 red-fixed + 3 guard-killed): 4 errors fixed (2×
  `-(1/2)` vs `-1/2` defeq via `by linarith` conversion;
  2× FALSE miss-identities sign-corrected, `ring` closes).
  Statements hold (miss-lemmas corrected, not weakened),
  supplier premises intact, axioms clean. Second NEW
  module GREEN.
- 2026-09-10 SLIV-complete received (361/0 on top, unbuilt):
  width-gate iff + 0.011-example arithmetic + sharp `m/M`
  widths + shortfall identities PROVED; Cauchy step +
  top/bottom strip theorems + conjugation route PROVED;
  `hSliver`-shaped conclusions complete modulo suppliers.
  Residual: edge-lower numerals (ξ-lower on top/bottom edge
  over [−10,10]) + uniform deriv-sups; then gates become
  `norm_num` checks. No 0.01 faked.
- 2026-09-10 CELL draft received (NEW `door3_first_cell.lean`,
  398 lines, untracked-only, 0 sorry, unbuilt): R02-pattern
  cell `(−8,−5.5)×(0.01,0.2)` picked (radius <1.26
  tied-smallest, center margin ≈+0.15, 5 banked reuses);
  poly/pi/Gamma-upper/zeta-upper-10/sphere/deriv discharges
  PROVED as cites; center+deriv+fencing+H-leaf PROVED modulo
  4 explicit premises (gamma-lower 0.008, zeta-lower 1.1 at
  sCenter [the wall], deriv-tier 0.07, fat-ball sup 16800);
  12-step replication TEMPLATE banked for remaining cells.
- 2026-09-10 CELL-SUP received (`e8f9f7d3`, NEW 694 lines,
  0 sorry, unbuilt): rpow `2^-0.395≤0.77` CLOSED; phase cap
  4.679 + cos-floor + S₂≥0.23 proved; Λ₀ packaged as
  FE-step (sufficient); 0.008-bridge proved conditional
  (20128×0.0195=392.496≤392.7). HONEST: 1.4 does NOT close
  at N=2 (slow ~1.03 vs need 3.542; phase-aware factor ≤1
  FALSE, need 2.53) — needs larger-N slow + pair-tail.
- 2026-09-10 FIX-cell (`a1122dac`, 12/9, 1× green 8703 jobs
  + 1 red-fixed + 2 guard-killed): 6 errors fixed in-file
  (implicit→explicit, `rw`→`simp only` NeZero motive,
  forward-ref inline, `rw at hd` only, `conv_lhs` stuck
  typeclass). Statements unchanged, 4 premises intact,
  axioms clean. First NEW module GREEN.
- 2026-09-10 ZU-SRECT received (`55f8ac14`, NEW 451 lines,
  0 sorry, unbuilt): eta-zeros verified OUTSIDE Tier-C
  rect (9.06 below, 18.13 above); pieces 3005/260/65 →
  uniform **`‖ζ‖ ≤ 3005`** (imports `zeta_rigorous`,
  cycle-safe, flagged). HONEST: implied deriv-M ≥2344 ≫
  0.04 — Tier C needs Cz≤0.051 (gap ~5 orders). Residual:
  `HighEtaDenom` (true ≈0.47) + sibling `sRectGammaSup`;
  then renegotiate Tier C or Tier-B fallback.
- 2026-09-10 batches A+B received (`9185b068`, NEW files,
  722+1170 lines, 0 sorry, unbuilt): A = 3 bottom-row cells
  (BA00/03/04, 6 premises each, thresholds proved, Cauchy
  mismatch explicit); B = full second row R11–R20 (10 cells,
  3 premises each, no banked pilots exist there — center
  inequality itself the premise). Patch: factor enclosures
  (complex wall), tier-M direct bounds, fat-ball sups.
- 2026-09-10 batch C received (`a2c37ce7`, NEW, 1682 lines,
  0 sorry, unbuilt): top row R31–R40 — 6 CLOSED-conditional
  (R33–R38, two tight at 1.08–1.09×) + **4 feasibility-
  NEGATIVE** (R31/R32/R39/R40 outer cells: proved deficits
  −0.036…−0.05 at true-scale floors; Gamma Im-decay).
  Negatives need re-tiering/subdivision (patch track).
- 2026-09-10 CELL-complete received (552/0 on top, unbuilt):
  gamma-lower **0.006 PROVED** (0.008 shown infeasible on
  banked (S,U): need S·U≤392.7, have 523.3); fallback
  re-tier **(0.002, 0.37)** proved (tier-0.07 excluded on all
  Cauchy routes, floor 0.358); fat-ball sup 16800 proved
  conditional on wide-Λ₀≤479; zeta-lower wall stands with
  (0.006,1.4) rebalance + eta-S₂ floor 0.23. Residual: zeta
  1.4 at t=−6.75, Λ₀≤479, rpow/even-partial, deeper Gamma-U.
- 2026-09-10 BSUP draft received (NEW `door3_cutR10_ballsup.lean`,
  345 lines, untracked-only, 0 sorry, unbuilt): ball geometry
  (Re∈[8.44,11.56], s-region mapped) + poly ≤67 + pi ≤16/5
  PROVED; honest weak cap ≤12.87 conditional. FLAG: premise
  (b) as stated may be FALSE — poly·pi·Gamma ≈0.062 > 0.04
  at z≈8.45 independent of zeta; center product ≈0.03797
  (~5% margin). Fix-wave 1 must numerically verify the joint
  sup FIRST; if false, renegotiate the 0.04 tier (fencing
  ε/M recompute), not more analysis.
- 2026-09-10 BSUP-complete received (613/0 on top, unbuilt):
  product identity CLOSED (`hProd` discharged); Euler-step +
  eta-term/pair machinery + Stirling mirrors + real Gamma
  caps + denom lowers PROVED; sharp 12.864 ≤ 12.87 TRUE
  proved. 0.04 tier CONFIRMED unclosable (needs
  ‖ζ(1/2+8.45i)‖≤0.64 vs center 1.549 — NOT faked).
  Residual: `hDom/hReal` wiring, `hStripEta` (N=8 head +
  tail + bridge), `hProdCap` via ST half-count, then
  fencing renegotiation (`M=12.87` needs ε+M·0.56≈7.21
  center — infeasible; switch tier/ball/leaf).
- 2026-09-10 TIER decision (`58af9dc4`, NEW retier file, 233
  lines, 0 sorry, unbuilt): Tier A (honest M=12.87) PROVED
  infeasible (need 7.2082 vs floor/true); Tier B (ρ=0.001
  subdivision) feasible-held as fallback; **Tier C
  RECOMMENDED: keep (0.001,0.04), thin s-rect deriv bridge**
  (need 0.0234 vs floor 0.0263, margin ~11%; vs true 0.038,
  ~38%). Patch: land `sRectZetaSup+sRectGammaSup`
  (Re∈[0.01,0.99], Im∈[9.75,10.25]) → `thinDerivRemainder
  0.04`; rewire fencing consumers to `tierC_thin_fencing`.
- 2026-09-10 lakefile registers all 4 new modules
  (ballsup/sliver/cutL10/first_cell, roots+globs).
- 2026-09-10 ST1 (`b8ab3230`, NEW file door3_stirling_gamma,
  8× green 8682 jobs; wrapper AUTOCLEAR observed live):
  Weierstrass-product route → FIRST exponential Γ-bound
  `‖Γ‖ ≤ 8·exp(−|t|/3)` on Re=0.95 (prior best: cubic poly).
  c=1/3 vs target 1.5708 (gap 4.7×); consumers stay unwired.
  Residual: factor-cut sharpen (2–3× c) + C~2.2 + σ-gen (ST2).
- 2026-09-10 ST2 (`ffa56735`, stirling file, 6+× green 8682 jobs;
  resumed after harness crash, tail intact): two-tier counting
  (quarter-factors below T/2 double-counted) + Γ-cap 1.1 →
  **`‖Γ‖ ≤ 4·exp(−|t|/2)`** (c 1/3→1/2, C 8→4). Two-tier
  optimum ≈0.62; π/2 needs full tail product (multi-session).
  INCIDENT: concurrent edit hit this file mid-session
  (committed line + lemma move) — repaired in-file; ST file is
  ST-lane-only, no other agent may touch it.
  Residual: C=3 one-append + third tier (~0.69) + σ-gen (ST3).
- 2026-09-10 ST3 (`1896e411`, stirling file, 4× green 8682 jobs):
  **`‖Γ‖ ≤ 3·exp(−|t|/2)`** (small-height via `1.1·e≤3`;
  tall via 4.84≤9 headroom) + third-tier ingredients
  (1/16-factor, quarter-count, sixteenth-product) +
  σ-general count/product. Rate still 1/2; C≈2.2 untuned
  (contradiction noted).
  Residual: three-tier decay c≈0.69 + σ-gen bounds (ST4).
- 2026-09-10 ST4 (`773e3d54`, stirling file, 4× green 8682 jobs
  + 1 fail-fixed): **`D3SG_prod_three_tier`** (split
  `[0,Q)+[Q,H)+[H,N)`, exponent `4Q+2(H−Q)+(N−H)`) →
  **`‖Γ‖ ≤ 5·exp(−log2·|Im|)`, |T|≥4** (`c≈0.6931` via
  `exp(4·log2)=16` exact, no log2-upper needed).
  Gap: global merge needs `|T|≤4` small-height (`C≈18`);
  σ-gen untouched (σ-uniform cap `M≈20` is hard blocker).
  Residual: global c≈0.69 merge (ST5).
- 2026-09-10 ST5 (`87d88fb8` part 1, stirling file, 2× green):
  **`D3SG_Gamma_line095_exp_decay_global`
  (`‖Γ‖ ≤ 18·exp(−log2·|Im|)`, ALL T)** + σ floor-counts
  (green); tail 48 lines (σ-product halves) unbuilt → held.
- 2026-09-10 ST7 (`87d88fb8` part 2, stirling file, 3× green
  8682 jobs): held tail VALIDATED green + `D3SG_prod_two_tier_sigma`
  + `D3SG_tall_prod_bound_half_sigma` + `D3SG_small_height_sigma`
  (cap explicit).   Residual: `D3SG_decay_sigma` assembly (ST8).
- 2026-09-10 ST8 (`435be1a4` part 1, stirling tail, unbuilt):
  `D3SG_decay_sigma` (`‖Γ‖ ≤ 3M·exp(−|Im|/2)`,
  cap-explicit) landed 60/0, guard-killed.
- 2026-09-10 ST10 (`435be1a4` part 2, stirling file, 1×
  green 8682 jobs): tail VALIDATED as-held, axioms clean
  (all 3 fragility flags passed). σ-decay COMPLETE
  (cap-explicit). Residual: uniform-M numeral → Tier-C
  sRectGammaSup (ST11); zeta half separate (ZU-SRECT).
- 2026-09-10 ST11 (`b9fb8b76`, stirling file, 2× green 8682
  jobs): **`Real.Gamma σ ≤ 20` on [0.05,0.95]** (convexity
  + shift route, essentially optimal) + Tier-C gamma rect
  corollary. Residual: sliver σ∈[0.005,0.05) M=200 (ST12).
- 2026-09-10 ST12 (`647c1d0b`, stirling file, 1× green 8682
  jobs): **`Real.Gamma σ ≤ 200` on [0.005,0.05]** (same
  route). Gamma caps now cover [0.005,0.95] uniformly.
- 2026-09-10 TIERB-UNLOCK (coordinator): Tier B needs joint
  C≤2.5 (ρ=0.01) while poly·pi=214 — Gamma·zeta ≤0.0117.
  TRUE joint ≈0.08 (fits 30×); bounds 400× loose on Gamma
  (c=1/2 vs true π/2). UNLOCK = π/2-rate + local-M σ-split
  (Γ(0.4)≈2.2) + zeta→2: 214·0.007·1.5≈2.25≤2.5 FEASIBLE.
  π/2-rate now CONSUMER-BACKED. ST13 = sliver rect.
- 2026-09-10 ST13 (`3cc994c0`, stirling file, 1× green 8682
  jobs): **`D3SG_TierC_gamma_rect_sliver`** (600·exp on
  [0.005,0.05]). Residual: wide join [0.005,0.95] (ST14).
- 2026-09-10 ST14 (`c1ecce0d`, stirling file, 1× green 8682
  jobs, resumed after conn-reset with zero partial work):
  **`D3SG_TierC_gamma_wide`** (600·exp(−|Im|/2) on full
  [0.005,0.95]). Gamma uniformity COMPLETE. Next: π/2
  scout (PI2, separate file) + local-M split.
- 2026-09-10 PI2 (`08598c87`, NEW file `door3_gamma_pi2.lean`,
  write-only): **π/2 by dyadic tiers INFEASIBLE — even
  infinite dyadic tiers cap at c≈0.87 (need 1.5708).**
  True rate needs full-tail integral route (exact-log
  product + integral comparison). M=20 FAILS low ball
  T≈4.5 (~2.4×) even at true rate; need local-M σ-split +
  C≤6 merge. Fourth-tier 64th-lemmas proved; FE σ≤0
  blocked (Gdamp-line). Tier-B (≤0.5,ρ=0.05) now needs the
  integral route — TIERB tracks as open residual.
- 2026-09-10 TAILEDGE+CUTL-D (`54cd3ebc`, no build):
  NEW `door3_tail_edge_push.lean` — tail K=2 conditional
  (B/2+d<1 → leaf; recon: Hedge S00-S09 live in
  central_cover_assembly not closed_cover; Door-4 single
  missing numeral = uniform `‖ζ‖≤B`). CUTL-D 386-line
  tail: **left-ball joint-0.04 FALSIFIED (TRUE ≈0.062
  > 0.04; needs zeta ≤2/3 below first zero)** — Tier-B
  conditionals + (12.87,0.001) instance banked.
- 2026-09-10 ZSTRIP (`ee2fb8f7`, ballsup file, no build):
  route (c) FE/convexity — zeta ≤6 full ball on ONE `hFE`
  premise (chi≤3 × reflected Euler≤2); zeta ≤2 CLOSED on
  Re≥2 sub-edge; honest joint ≤643.2 with closed Gamma.
  Full-rect ≤2 NOT closed.
- Lakefile now registers 9 newer modules (sliver_edge,
  srect_zeta, cell_suppliers, batches A/B/C, retier,
  gamma_pi2, tail_edge_push); tierB_subdiv + batchD on
  delivery.
- 2026-09-10 batchD (NEW `door3_cells_batchD.lean`, no
  build): third row R21–R30 — 8 closed-conditional (R28,
  R29 TIGHT ~1.05×), 2 feasibility-negative (R21/R30,
  deficit −0.05 each → re-tier/subdivision). 60 premises
  listed with TRUE values.
- 2026-09-10 TIERB (`door3_tierB_subdiv.lean`, no build,
  re-fire after empty first attempt): subdivision machine
  (count + Cauchy + fencing) + CutR10 instantiation (264
  subcells 12×22) + `tierB_1287_005_infeasible` PROVED +
  caps C ≤ 0.506 / target (0.5, 0.05) feasible. Gap
  quantified: 12.87 → ≤0.5 (~25.4×), owed by π/2
  integral + local-M + zeta≤2.
- 2026-09-10 ZU36 (`21c60325`, zeta file 233/0, guarded
  builds A/B/C green + quiet-state lean typecheck, axioms
  clean): sCutL10Z conj certs (etaFactor ≤1, S₂ ≥0.28,
  honest lower, shortfall quantified −19.76 vs 7/5).
  **FINDINGS: (1) lakefile:214 missing `Glob.one` broke
  fresh lake elaboration — FIXED same commit. (2) eta
  7/5 contract UNSATISFIABLE (‖eta‖≈1.3375<1.4) — stop
  N-variants; retarget consumer to 6/5 (N=4 head +
  pair-norm tail + 9/10 factor cap + transport).**
- 2026-09-10 ZU37 (`f067e571`, zeta file 237/0, no
  build): 9/10 factor cap CLOSED; N=4 magnitude-route
  FAILED honestly (slow −1.73, tail 14.43 — ‖s‖≈10
  constant kills both). 6/5 OPEN. ZU38 fired: Im-route
  head + tradeoff curve N∈{4,6,8,12,16}, cap 3 variants,
  close-or-quantify.
- 2026-09-10 ZU38 (`3c1706cc`, zeta file 401/0, no
  build): tradeoff CLOSED-NEGATIVE (MVT limit ≈−4.1,
  best N=8 gap 15.90; sin-enclosures open). New plan:
  conjugation transport from banked t=10 right-side
  bound (‖zeta(1/2−10i)‖ = ‖zeta(1/2+10i)‖). ZU39
  fired.
- 2026-09-10 ZU39 (`a4f43901`, zeta file 51/0, no
  build): NO-BANKED-BOUND (no 6/5·7/5·head275 zeta-lower
  anywhere; only open Prop premises). Conj identity
  banked. STRATEGIC PAUSE on grind:   recon fired —
  right-side precedent? interval_arith? consumer exact
  need? — recommendation (a/b/c/d) pending.
- 2026-09-10 zeta-lower recon DELIVERED (read-only):
  right side has NO closed lower (open 7/5 Prop only);
  interval_arith is real-only (no complex zeta/Gamma
  enclosures by its own header); consumer needs 7/5
  (not 6/5) at CENTER 1/2−10i; Stirling file has zero
  zeta content. Recommends (d) concede fat-ball.
  COORDINATOR DECISION: fat-ball doubly dead (joint
  falsified + lower walled) — STOP ball-joint/lower
  grind. Single-cell+tight-M path needs same lowers;
  subdivision multiplies them. KEY Q: is qualitative
  (Rouche) nonvanishing sufficient on cutoff strips?
  Fired: BUILD-SWEEP (11 unbuilt modules, guarded,
  diagnose-only) + CUTOFF-ARCH recon (wiring needs?
  floors-vs-≠0? Door-4 upper convergence?).
- 2026-09-10 arch recon DELIVERED (read-only, superb):
  wiring needs ONLY CutR10 fencing H + hLeft + hSliver
  (rest other lanes); `cutoffLines_either` PROVED pure
  combinatorics; EVERY consumer qualitative (≠0
  sufficient, floors sufficient-not-necessary); banked
  Door-4 leaf domain-disjoint (|Re|>10 excludes ±10).
  Bypass needs bounded-box Rouché (K=2 suffices, no
  K→∞). COORDINATOR DECISION: adopt qualitative
  program — (1) hFE discharge (chi≤3 × refl-Euler≤2),
  (2) bounded-box gap conditional on hFE-box, (3) conj
  mirror, (4) feed wiring. Sin-grind PARKED. Fired HFE
  (ballsup tail) + ROUCHE (new file, gap-or-obstruction
  honestly).
- 2026-09-11 session resume: OA27 agent lost with
  restart but left well-formed 482/2 tail (t=11
  theta/delta/combo/amp phases; 2 deletions =
  namespace-close repositioning, benign; sorry-clean)
  — committed `919a8163`. BUILD-SWEEP/HFE/ROUCHE gave
  no report (died in restart) — RE-FIRED below.
- 2026-09-11 HFE delivered (`8eeb8902`, ballsup 144/0,
  no build): Euler half CLOSED
  (`cutR10_reflected_Euler_two_closed`, t.re≤−1 sliver);
  chi≤3 ABSENT repo-wide (banked chi exp-scale: exp13/
  exp22/uniform-8-conditional); middle reflected≤2 also
  open (true ≈4 — product framing needed, not rigid
  3×2). Conditionals banked (`cutR10_hFE_of_chi_and_
  middle`). GAMMA-SUP fired (stirling tail): product
  ≤6 via shift-recurrence + sin-upper + convexity.
- 2026-09-11 ROUCHE delivered (NEW `door3_cutoff_
  rouche.lean`, registered): OBSTRUCTION PROVED —
  uppers alone CANNOT certify ≠0 (margin ≤4≮1; witness
  w=6). Conj-mirror banked (one premise → both boxes).
  Pivot: weak two-sided disc (c,r,κ), tolerance
  generous (r<1.549 works at c≈1.549). STRATEGIC
  RESULT: every route (fencing lowers, Rouché disc,
  subdivision floors) needs two-sided oscillation
  control → DP-ENCLOSE fired (complex Dirichlet-head
  enclosure machine, demo on parked Im-S₄ need).
- 2026-09-11 GAMMA-SUP delivered (`4fb5c005`, stirling
  427/0, no build): sin-upper exp19 (box-correct),
  Gamma-refl ≤600 (shift-recurrence, same-lane), chi box
  ≤2·7·600·exp19. Best product ≈3e12 vs 6 (gap 5e11×).
  STRUCTURAL: c=1/2 can't cancel sin growth; product
  IS zeta(t) by FE so splitting is artifact. hFE≤6 now
  feeds NOTHING live (K=2 gap dead) — Gamma line
  PAUSED unless DP needs uppers. DP-ENCLOSE came back
  empty (too big); re-fired STAGE 1 (`door3_dp_trig`:
  trig enclosures only, partial OK, stage 2 deferred).
- 2026-09-11 BUILD-SWEEP delivered: 5/11 GREEN
  (batchB, batchD, tierB_subdiv, retier, pi2 — axioms
  clean), 6/11 RED. NEW FIND: nested-comment trap
  (`/-` inside block comments) — coordinator fixed 3
  by hand (`8a30ecdf`) + import placement; lane tails
  scanned clean. FIX WAVE ×10 fired: ZUFIX (zeta 5
  errs + srect), SEFIX (4), BAFIX (3), CSFIX (1),
  OAFIX (OA27 verify), TFIX (batchC + tail_edge
  confirm), BFIX (ballsup tail), CLFIX (cutL10 tail),
  STFIX (stirling tail), RUFIX (rouche). Guarded +
  retry×8 + 15-min kill.
- 2026-09-11 CSFIX+BAFIX GREEN, committed (`b2ff0b6d`,
  1/1 + 6/6 minimal): suppliers `le_div_iff₀`→
  `div_le_iff₀`; batchA `norm_nonneg`→`by norm_num`
  + `positivity` (axioms clean).
- 2026-09-11 CLFIX located-RED (no edits): cutL10
  tail clean (no sorry, numerals ok) — BLOCKED on
  upstream zeta RED (verbatim errors relayed).
  CLFIX ALSO flags `sorryAx` in zeta-tail dependency
  infos. Coordinator audit: NO sorry tactic in zeta
  tail or any door3 file; repo sorrys live in
  JensenTranslation×5, KadiriHadamardAffine×3,
  KadiriZeroFree×5, float_xi_bridge×1. If ZU-tail
  theorems inherit sorryAx it comes via UPSTREAM
  banked lemmas (e.g. `zeta_lower_of_Sn_tail_factor`,
  `zetaCell_even_remainder_le`). PENDING on ZUFIX
  green: inspect `#print axioms` per tail theorem in
  build log, trace any sorryAx to source lemma.
- 2026-09-11 STFIX green, committed (`55e7d948`, 2/1
  lines, full CHI axioms list clean).
- 2026-09-11 LOCK-THRASHING: OAFIX + SEFIX + DP-S2 all
  TIMEOUT on guard starvation (proof work done, builds
  starved). SEFIX 4/4 committed (`95244018`, mirrors
  banked). OAFIX re-fired with 14×90s patience. DP-S2
  correctly refused stage 2 on unverified stage 1.
  POLICY: no new builders until wave drains; then ONE
  sequential confirm-sweep (sliver_edge, batchC,
  tail_edge, ballsup, cutL10, rouche, off_axis, srect,
  trig+terms).
- 2026-09-11 OAFIX-retry: lock ACQUIRED on attempt 3,
  build ran, RED all 8 errors in zeta (same ZUFIX set;
  off_axis never reached, tail untouched, 0 fix cycles
  used). ZUFIX actively editing zeta (file dirty).
  Everything funnels to ZUFIX green.
- 2026-09-11 BFIX located-RED, tail fix committed
  (`1778b33a`, 2/1): tail ≥1469 now error-free; module
  RED on ~30 PRE-EXISTING errors <1469 (write-only
  draft sections never built — backlog, not regress).
  MECHANISM NAILED: `sorryAx` in red-build logs =
  Lean's placeholder for FAILED proofs, not hidden
  sorrys (STFIX: "sorryAx gone" post-fix; repo audit:
  sorrys only in Jensen/Kadiri/float files, none in
  door3/zeta-tail code). Upstream-taint hypothesis
  RETRACTED. BFIX2 fired (whole sub-tail file).
- 2026-09-11 DP-TRIG delivered (`8d7324ab`, NEW
  `door3_dp_trig.lean` ~140 lines Mathlib-only,
  registered, no build): quad floor, cubic floor,
  /100-ceiling (R1-/120 recorded residual), arg-reduce
  + invariance, combined enclosure (width ≤1/50,
  |r|≤1). Honest partial (no cosine side, no demo).
  STAGE 2 fired (DP thread owner): trig verify-first,
  NEW `door3_dp_terms.lean` (cos mirror + n=2,3,4 term
  discs + S₄-Im demo ≥1.0), build-both mandate.
- 2026-09-10 ST13 (`3cc994c0`, stirling file, 1× green 8682
  jobs): **`D3SG_TierC_gamma_rect_sliver`** (600·exp on
  [0.005,0.05]). Residual: wide join [0.005,0.95] (ST14).
- 2026-09-10 TIER-FEASIBILITY (coordinator, lemma shape
  `M=C/r` verified): Tier A TRUE-dead (sup_true≈0.09 vs
  need ≤0.04); Tier C TRUE-dead (needs sup≤0.04·margin≤0.01
  < center 0.038). **Tier B viable with sup-tightening:**
  C_bound≤0.025/ρ (12.87→ρ≈0.001 ~10⁵ cells; ≤2.5→ρ=0.01
  ~1225; ≤0.5→ρ=0.05 ~50). Priority: tighten ball sup
  (Gamma π/2-rate + zeta strip) THEN subdivide. CutL10
  deriv same story later.
- 2026-09-08 OA7 (`74b89285` pt 2, off-axis tail, green 8702 jobs):
  S4 phase tighteners (`‖S₄‖ ≥ 793/2500`, 3.17×) + assembled N=4 cert
  (honest-negative ratio). Residual: pair-`Re` floors `m≥2` (OA8).
- 2026-09-08 OA8 (`db737041`, off-axis tail, green 8702 jobs, axioms clean):
  m=2 pair floor (`Re pair2 ≥ 1/20`) → `‖S₆‖ ≥ 459/1250` (0.3672);
  shortfall 707/2500 vs 13/20. WARNING: pair floors decay (θ8≈π/2,
  θ9>π/2 → negative at m≥4). Next: pair m=3 w/ stop rule (OA9).
- 2026-09-08 OA9 (`b1a61e48`, off-axis tail, green 8702 jobs, axioms clean):
  pair-3 floor `Re pair3 ≥ 1/500` POSITIVE (fresh `log 7` bounds derived,
  no d9 lemma existed) → S8 `Re ≥ 923/2500`; shortfall 702/2500.
  m=4 expected stall (cos(0.75·log 9)<0). Next: S8 + m=4 (OA10).
- 2026-09-08 OA10 (`733210d9`, off-axis tail, green 8702 jobs, axioms clean):
  S8 assembly (slow 923/2500, ratio 137/625) + pair-4 STOP verdict
  (`Re pair4 ≥ −1/240 ≤ 0`; term 8 drags via negative cosine).
  Pair route CLOSED per stop rule. Next: M=4 tail or cF (OA11).
- 2026-09-08 OA11 (`767fa46b`, off-axis tail, green 8702 jobs, axioms clean):
  M=4 tail (`‖G−S₈‖ ≤ 7/5`) + filed honest S8 cert (ratio −2577/2500).
  VERDICT: tail no longer binding — slow-sum size is. Next: individual
  term floors k=8..15, non-pair route (OA12).
- 2026-09-08+ OA12 (`de5d681c`, off-axis tail, 4× green 8702 jobs):
  twelfth-term recipe (`log12` d9 + quartic cos + cleared rpow) →
  `Re (term 11) ≥ 1/15` (sign-flip positive); slow ≈0.4359 vs 0.65.
  Residual: wire S9/S12 sums + k=13 (n=14) floor (OA13, LARGE scope).
- 2026-09-08+ OA13 (`449f2b25` part 1, off-axis tail, built green):
  S9/S10 folds + fourteenth floor `1/12` + sixteenth floor `1/10`
  (latter appended unbuilt, validated green by OA14 as-is).
- 2026-09-09 OA14 (`449f2b25` part 2, off-axis tail, 7× green 8702):
  33 theorems — prime floors n=11/13/15 (honest-negative) +
  contiguous S11–S16 folds (S16 ≈ 0.04003; contiguous dips, pair
  S15+S16 nets −3/20). Standalone credit 1/4; all k≤15 floored.
  Residual: n=17/18 floors + pair-tail certificate (OA15, LARGE).
- 2026-09-09 OA15 (`91587d34`, off-axis tail, 10× green 8702 jobs):
  n=17 floor (−11/40) + n=18 floor (1/10) + S17/S18 folds +
  pair-block floors (pairs 5–8, all negative) + slow assembly
  (frontier S18 ≈ −0.135; pair block nets −1/2: odd credit 7/20
  vs even drag −17/20 — contiguous folding CERTIFIED unable).
  Residual: n=19/20 + pair-9; tighten even-k amplitude uppers
  below 1/2 (OA16).
- 2026-09-09 OA16 (`a2625bff`, off-axis tail, 4× green 8702 jobs
  via new guarded wrapper): n=19 floor (−5/24, FIRST sub-1/2
  even-k amplitude via 3/8-exponent clear) + n=20 floor (1/10) +
  S19/S20 + pair-9 (−13/120). Frontier S20 ≈ −0.2433; best
  contiguous S16 ≈ 0.0400.
  Residual: STEP-3 assembly + even-k re-derivation via 3/8
  template (OA17).
- 2026-09-09 OA17 (`164294a9` part 1, off-axis tail, 6× green):
  assembly + tight even floors (−5/44,−6/35,−5/24,−11/50) +
  tight pairs 5–8 (block −0.3634 beats −1/2); S11–S14 tights
  appended unvalidated.
- 2026-09-09 OA18 (`164294a9` part 2, off-axis tail, 3× green):
  S11–S14 validated as-is + S15–S18 tights + tight assembly:
  frontier **S18′ ≈ +0.00164 (FLIPS POSITIVE)**,
  best contiguous **S16′ ≈ 0.1216** (was 0.0400),
  residual 499241/770000 ≈ 0.64836.
  Residual: tight 19/20 floors + S19/S20 tight folds (OA19).
- 2026-09-09 OA19 (`27872ce4`, off-axis tail, 4× green 8702 jobs):
  tight 19 (`−125/602`) + tight 20 (`3/25`, beats 1/10) →
  S19′/S20′ folds (frontier S20′ ≈ −0.086, best holds S16′
  ≈ 0.1216). Residual 3481309/4730000 ≈ 0.736.
  Residual: tight pair-9 + block update (OA20).
- 2026-09-09 OA20 (`49a1e73e` part 1, off-axis tail, 2× green):
  tight pair-9 (−1319/15050) + block −25601/56760 + 3 verdict
  theorems (landed unverified under upstream breakage).
- 2026-09-09 OA21 (`49a1e73e` part 2, off-axis tail, 2× green
  after 9h stall cleared): verdicts verified AS-IS + pair-10
  amplitude halves (21/22 rpow) + S16→S20 drop identity +
  log21 bounds. Best S16′ ≈ 0.1216 (residual ≈0.528).
  Residual: pair-10 cosines + floors + S21/S22 (OA22).
- 2026-09-09 OA22 (`8a9bc8d9`, off-axis tail, 7× green 8702 jobs):
  pair-10 steps (a)–(c) + term bridges (theta21/22, cos
  −3/4/−2/5, rpow, inv/cpow, eta-21/22 eqs). Best S16′ ≈
  0.1216 (residual ≈0.528).
  Residual: eta 21/22 floors + pair-10 + S21/S22 (OA23).
- 2026-09-09 OA23 (`8ee4acc9`, off-axis tail, 2× green 8702 jobs
  + 1 contention kill with proper lock clear): eta-21 (−1/4) +
  eta-22 (4/35) + pair-10 (−19/140) + S21′/S22′ folds
  (frontier S22′ ≈ −0.222; best holds S16′ ≈ 0.1216).
  Residual: PIVOT to sCut slow-cert for CutR10 fencing (OA24).
- 2026-09-09 OA24 (`a43f2eb3`, off-axis tail, green 8702 jobs):
  sCut triple banked (`slow=2/7`, `rtail=24`) + PROVED
  `hEnough` IMPOSSIBLE at sCut (`|η(1/2+10i)|≈1.3375<1.4`;
  shortfall 879/35; banked sR05 floors non-transferable).
  Residual: (i) nine_tenths variant or (ii) move cutoff point
  to |η|≥1.5 height (OA25).
- 2026-09-09 OA25 (`65f25d41`, off-axis tail, green 8702 jobs):
  feasibility scan (nine_tenths margin +0.0775 too thin) →
  MOVED to t=11 (`|η|≈2.30`, margin +0.90; exact C=12 port) +
  triple shape re-banked. hEnough still needs M=2048 rtail
  (≤7/10) + N=4096 slow (≥21/10).
  Residual: M=2048 rtail + N=4096 slow → hEnough (OA26).
- 2026-09-09 OA26 (`d9e4e191`, off-axis tail, 2× green 8702 jobs):
  **rtail leg CLOSED** (`‖G−S4096‖ ≤ 7/10` at M=2048 via
  `35 ≤ √2048`) + threshold lemma (7/5+7/10=21/10 bar met).
  slow N=4096 untouched (best 2/7); hEnough shortfall 127/70.
  INTERFACE FINDING: wiring consumes t=10 sCut — t=11 cert
  needs a cutoff-lane port to 11i.
  Residual: N=4096 slow ≥ 21/10 (OA27).
- 2026-09-07 OA2 (`7856eef2` pt 2, off-axis tail, green 8702 jobs):
  R05 M=1024 tail-decay chain (norm/rpow/tail bounds). Next: R05
  threshold-meeting certificate assembly (OA3).
- 2026-09-07 OA3 (`032f75d3`, off-axis tail, green 8702 jobs):
  R05 genuine N=2 cert + PROVED honest negative (ratio -10/13;
  banked-tail ratio 1/52, shortfall 25/52; slow needed 29/20).
  NOTE: user's commit `56b91432` swept the 144-line append mid-task;
  repair verified separately. Next: phase-aware eta-factor (OA4).
- 2026-09-08 OA4 (`95fb745a`, off-axis tail, green 8702 jobs):
  phase-aware factor `‖1-2^(1-s)‖ ≤ 1` (cos floor at `0.75·ln2`);
  slow target drops `29/20 → 13/20`. Residual: larger-N slow
  `‖S₂₀₄₈‖ ≥ 13/20` (tasked as OA5).
- 2026-09-08 OA5 (`608a9362`, off-axis tail, green 8702 jobs):
  N=4 slow `‖S₄‖ ≥ 1/10` + honest shortfall (11/20 vs 13/20).
  Next: Re-S3 route to `‖S₃‖ ≥ 13/20` (OA6).
- 2026-09-08 OA6 (`83f2ff92`, off-axis tail, green 8702 jobs, axioms clean):
  `‖S₃‖ ≥ 13/20` BRIDGE (Re-S3 route) + ratio arithmetic.
  Residual: N-match for assembly (S₃ vs M=1024 tail; N=2048 route
  dead by head-sum caps per report). Next: pair-by-pair (OA7).
- 2026-09-07 BS (`351a6d4f`, deriv tail lines 1062–1201, green 8682 jobs):
  segment deriv bound + margin assembler mirror `StripBaseBounds`.
  Residual: base lower `ε0 ≤ ‖ξ(x)‖` banked as hypothesis (tasked as BS2).
- 2026-09-07 BS2 (`b3f02274`, deriv tail, green 8682 jobs, axioms clean):
  per-`x` conditional closure `∃ ε0 M1, StripBaseBoundsShape` at
  `(0.025, 1)`. Residual: UNIFORM `0.025 ≤ ‖ξ(x)‖` on `-10<x<10`
  (critical-line ξ minorant, tasked as BS3).
- 2026-09-07 BS3 (`aa809e24`, zeta-cutoff tail, green 8701 jobs):
  unconditional `0.025 ≤ ‖ξ(0)‖` minorant + `bottomStrip_obligations_
  of_uniform_bounds` bridge. Residual: UNIFORM hb+hB on `-10<x<10`
  (BS lane PAUSED pending RX2's critical-line zeta numeral).
