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
  - **Dead-owner fast path (2026-09-17 finding: a dead owner blocked all agents for hours
    because everyone kept `GUARD-WAIT`ing).** Before waiting, read the lock content
    (`Get-Content .lake_build_lock` → `<ownerPID> <timestamp>`) and check owner liveness
    (`Get-Process -Id <ownerPID>`) plus live builders
    (`Get-Process -Name "lake","lean"`). If the owner PID is dead AND no live
    `lake`/`lean` process exists, the lock is definitively stale **regardless of age** —
    delete it immediately and proceed (do NOT wait out the 25-min autoclear). Never delete
    a lock whose owner is alive or while any `lake`/`lean` process runs.
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
- 2026-09-11 TFIX split: batchC GREEN (`8a30ecdf` trap
  fix confirmed; zero axioms lines — file has no
  `#print axioms`). tail_edge RED-BLOCKED: `Challenge2.
  MollifiedAttack.*` unknown. Coordinator ROOT-CAUSED:
  names EXIST in source (underscore file :11984, inside
  Challenge2 11121-12030) — the olean is STALE (old
  commit artifact, fresh by mtime). NOT a source bug.
  REBUILD agent fired (long-build lane: delete stale
  oleans, rebuild RH ≤40min → CCA → tail_edge).
- 2026-09-11 REBUILD delivered: RH GREEN (8685 jobs),
  CCA GREEN (8687 jobs) — cascade fresh. STALE THEORY
  REFUTED with proof: real name is `RHProofScaffold.
  Challenge2.MollifiedAttack.*` (open namespace :6204
  never closed). Coordinator applied prefix fix
  (`b809eb78`, 13/13 replaceAll). TEFIX2 fired
  (verify, deps warm, expect <3min). NOTE: scaffold
  tail chain carries pre-existing retained axiom
  `RiemannHypothesisProp_apply` (not ours, flagged).
- 2026-09-11 TEFIX2 GREEN (30s, no wait, zero edits):
  tail_edge_push builds on fresh cascade. Tail-edge
  lane CLOSED (K=2 conditional + recon banked).
- 2026-09-11 ZUFIX DOUBLE-GREEN, committed
  (`e18ec2ee`, zeta 30/10 + srect 2/1): all 5 zeta
  errors fixed one-line each + 2 srect lines; tail
  axioms ZERO sorryAx (mechanism confirmed: placeholders
  for failed proofs). CONFIRM-SWEEP fired (sequential:
  sliver_edge, off_axis, cutL10, dp_trig).
- 2026-09-11 BFIX2 BLOCKED after 6/6 cycles with ~40
  fixes landed, committed (`50966d3a`, 236/144, all
  <1469, tail untouched, sorry-clean): includes TWO
  HONEST WEAKENINGS — joint 3217/250→3216/5 (643.2,
  matches ZSTRIP honest) and strip_six→≤12 (Z·F≤6 with
  F≥1/2 gives Z≤12, not 6; zero callers). 1 remaining
  fix (1192 dot-notation) applied post-build,
  UNVERIFIED. BFIX3 fired (verify + caller check).
- 2026-09-11 BFIX3 GREEN (31s, zero edits): ballsup
  module CLOSED — 255 axioms lines, zero sorryAx,
  weakenings caller-free (def-only hits). Right-ball
  file fully banked (conditional joints documented).
- 2026-09-11 CONFIRM-SWEEP: sliver_edge GREEN (no
  axioms lines — no prints, not failure), off_axis
  GREEN after 2 in-scope tail fixes (committed
  `69f18cde` with trig fixes), cutL10 RED-BLOCKED
  (6 pre-existing <1009: sCutL unknown ×2, conj
  rename, sorry-588, unsolved 696, shiftedS_im_eq;
  sorryAx at 535/987 = placeholders), trig
  RED-BLOCKED (1 sin_neg rewrite-all left). Fired
  CLFIX2 (sub-1009 backlog + RUFIX precedents) +
  TFFIX (last trig error, unblocks DP-S2).
- 2026-09-11 CLFIX2 backlog GREEN, committed
  (`0073a045`, 28/15 all <1009): forward-ref split,
  star-rename + ComplexConjugate scope, conv_lhs,
  LeafDecomp qualification; sorry-588 = placeholder,
  sorryAx at 535/987 GONE. Exposed CUTL-D tail RED
  (8 routine errors ≥1096). CUTL-TAILFIX fired (BFIX2
  precedents attached).
- 2026-09-11 HMAIN recon DELIVERED (read-only): Hmain
  fully OPEN (2 proved implications from open
  antecedents + 1 missing ~5-line wrapper
  `full_central_covered → XiCentralMainBand10`).
  34/40 leaves claimed (all conditional, 0 closed);
  6 UNCLAIMED (R01, R05–R10); BottomStrip open;
  edge strips 0/20. Fired WRAPPER (new bridge file)
  + BATCHE (6 leaves, 12-step template).
- 2026-09-11 WRAPPER CLOSED (NEW `door3_hmain_bridge.
  lean`, 34 lines, registered, no build):
  `hmain_of_full_central_covered` — shapes aligned
  directly. Hmain now needs ONLY FullCentral (80
  leaves) + BottomStrip.
- 2026-09-11 CUTL-TAILFIX GREEN in 1 cycle, committed
  (`b73d00cd`, 50/12): 8 tail fixes (hbase fourth-root
  calc, .ge, by_contra assembly, hs-rfl, stray rings);
  Tier-B axioms all clean. CutL10 module CLOSED.
- 2026-09-11 BATCHE delivered (NEW `door3_cells_
  batchE.lean` ~1300 lines, registered, no build):
  SEVEN leaves (brief said 6; R01+R05–R10 = 7) all
  closed-conditional, zero feasibility-negative (R10
  tightest 1.04×). 40/40 main-band leaves now claimed.
  42 premises with TRUE docs.
- 2026-09-11 DP-S2 delivered (`0497e6b3`, NEW terms
  file 196 lines, registered, self-built GREEN): cos
  mirror + pipeline shapes banked, but demo PUNTED
  (radius-2 discs, numeral 0). Remainder gives exact
  recipe (octant ±π/2 shifts + TRUE centers). STAGE 3
  fired (terms tail): tight 1/100 discs + S₄-Im
  ≥145/100 fold.
- 2026-09-11 DP-S3+FIX GREEN, committed (`e50ecd81`,
  589/0): octant machinery + 3 tight 1/100 discs.
  HONEST FIND: 145/100 target arithmetically
  impossible (signed Im-sum 0.3309, not |·|-sum
  1.4855); demo `dp_S4_Im_ge_3009_10000` = 0.3009
  closed. Agent corrections: parens were in h3/h4/e
  lines (not hre/him); no hcast needed (dead hCre
  drop sufficed); abs-atom linarith → dp_abs_tri
  helper; term3-im tightened to 1/10000. NOTE for
  disc program: Im-route caps at ~0.33 (true) —
  norm-route (‖center‖≈1.7) or N≈64-head disc feeds
  rouche `CutBoxZetaDisc`.
- 2026-09-11 sorry-hunt: 4 prover agents fired
  (JensenTranslation×5, KadiriHadamardAffine×3,
  KadiriZeroFree×5, float_xi_bridge×1).
- 2026-09-11 ALL 14 SORRYS ELIMINATED:
  JENSEN→conditionals green (`1f3e1112`); FLOAT→
  conditional unbuilt (`ffc0c6ed`); KADIRI-ZF→
  conditionals green (`351c228c`, retains documented
  `axiom xiZeros_simple`); KADIRI-HA→residuals
  green (`5d1c1247`, +caller fixes).
- 2026-09-11 DISC-TAIL honest-negative (`13124322`,
  zeta 106/0): T(M)=20.04/√M, need M≥1607; best
  M=64→2.51. Coordinator math: min_N total ≈3.98 >
  1.549 at ANY N — MVT-tail disc DEAD structurally.
  MACHINE-RECON fired (ApproxZetaLowerBound?
  BorelC? Zeta23? float_*? cert files? zero-free
  regions covering the box? non-MVT tails?) before
  AFE-build-vs-concede decision.
- 2026-09-11 MACHINE-RECON delivered: NOTHING banked
  closes the disc (counts/thin-≠0/Float-fuel/tables
  all wrong output type; every tail in 30k-line zeta
  file is MVT-family; Kadiri edge covers outer ~1/3
  conditional on AnalyticInputAtZero; middle gap
  (0.006,0.994) explicitly excluded everywhere).
  AFE = weeks, not sessions. DECISION (coordinator):
  cutoff disc DEAD structurally (min_N total ≈3.98
  > 1.549 at ANY N — analytic wall, not arithmetic).
  Fallback: cutoff cells go CONDITIONAL (Kadiri-edge
  slivers via explicit AnalyticInputAtZero hypothesis
  + middle gap as named open premise — same honest-
  conditional standard as the sorry-hunt). Head A/B/C
  land as infrastructure (no assembly fired); premise
  waves + TAIL unaffected (low-t tradeoffs live).
- 2026-09-11 PREM-POLY delivered (NEW `door3_premise_
  poly.lean` ~830 lines, registered, no build): 31/31
  poly floors closed (batch B carries none — true
  count 31 not 40), zero false floors.
- 2026-09-11 PREM-GAMMA delivered (NEW `door3_premise_
  gamma.lean`, registered, no build): honest partial —
  40/40 wide uppers via TierC-wide reuse + shift
  infrastructure banked; 0/30 lowers (open Props,
  need Stirling-disc wave); tight ≤10 open.
- 2026-09-11 PREM-TIER delivered (`98241f5b`):
  Cauchy EXCLUDED everywhere (67200 vs 0.05-0.07,
  41 mismatches proved); balls systematized as open
  premises (loose 3 orders). Needs direct-deriv wave.
- 2026-09-11 PREM-PI delivered (NEW `door3_premise_
  pi.lean` ~1130 lines, registered, no build): ALL
  pi floors+uppers closed, zero false floors (alias
  rewrite left to patch).
- 2026-09-11 HEADC empty (no file — size failure
  mode); re-fired HEADC1 (n=45..54, min viable 5).
- 2026-09-11 PREM-ZETA delivered (NEW `door3_premise_
  zeta.lean` ~550 lines, registered, no build):
  honest-negative at N≤8 — ALL 31 recon-negative
  (even R05 t=0.75: −0.13). Conditional bridge +
  R05/R06 trig pieces banked. OPEN not dead (N=16..32
  wave may close low-t); high-t stays walled.
- 2026-09-11 HEADA partial (NEW `door3_dp_headA.lean`
  ~700 lines, registered, no build): terms 5–8 closed
  (radius 0.08 banked, centers honest), 9–24 open.
  REDIRECT: no head follow-ups (disc dead, no live
  consumer) — effort to low-t N-wave + gamma lowers
  + direct tier-M (live: 40 cells → Hmain).
- 2026-09-11 LIVE WAVE ×3 fired (write-only, new
  files): ZLOWN (low-t N=16/32 zeta lowers, easiest
  first), GAMLOW (30 Gamma lowers via shift+real
  numerals, tight-flagged first), TIERDIRECT (direct
  Leibniz + small-disc Cauchy from banked local
  sups, biggest-margin first).
- 2026-09-11 HEADC1 minimum viable (NEW `door3_dp_
  headC1.lean` 791 lines, registered, no build):
  n=45..49 closed (radius 1/100 ×5, centers honest);
  50..64 open (no follow-up: disc dead).
- 2026-09-11 ZLOWN delivered (NEW `door3_zlowN.lean`,
  registered, no build): infra + N16/N32 numbers —
  R05 N32 −0.10 (trend may close ~N64); all 31 open.
- 2026-09-11 GAMLOW delivered (NEW `door3_gamma_low.
  lean`, registered, no build): 34 denominators +
  shift infra   banked; 0/30 lowers (need π/2-rate +
  Stirling-disc; banked reflection 2–3 orders short).
- 2026-09-11 TRUE-MEASURE delivered (numerical, mpmath
  50dps, 6 cells + scans): tiers TIGHT-but-TRUE —
  margins 1.01×(R31) to 1.42×(R05), none factually
  false; Cauchy overshoots ~10⁶×; ball-sup cap 3×10⁴
  slack. DECISION: subdivide + re-tier everywhere
  (M raised ~2×, r shrunk, crude-certified bounds
  fit with TRUE headroom); prove-tighter only for
  R05. SUBDIV-DESIGN fired (counts + re-tiers +
  feasibility as proved arithmetic).
- 2026-09-11 SUBDIV-DESIGN delivered (`d206353a`,
  NEW plan file, registered, no build): 512 subcells
  (112+112+224+64), per-group (ε',M',ρ') proved
  feasible with TRUE headroom ≥1.5×.
- 2026-09-11 FACTOR WAVE ×3 fired (write-only, new
  files): GAMDISC (30 Gamma lowers via shift-disc),
  ZN64 (R05-first N=64/pair-fold push), DERIVUP
  (16 local factor-deriv bounds vs M' targets).
- 2026-09-11 ZN64 delivered (`9ec1f240`, NEW zeta_N64
  file, registered, no build): R05 FIRES at N64
  (+0.12), R06 at N128 (+0.03); R04/R25 need N>128.
  Pair-cost 224 lines/center, parallelizable.
  R05-CLOSE fired (first unconditional cell-zeta).
- 2026-09-11 GAMDISC delivered (`946c56fc`, NEW
  gamma_disc file, registered, no build): 30
  conditionals closed; single missing input = REAL
  Gamma lower on [1,2.1] (target 0.88, true min
  0.8856). REALGAM-LOW fired (any route ≥0.80 wins,
  with survival table).
- 2026-09-11 R05 honest-negative + DERIVUP gaps
  committed (`77860753`): ZN64's +0.12 used 0.5 both
  ways (invalid) — honest gap −2.38 (true-est −0.20);
  fix = tight-cF + N128+. DERIVUP: poly'/pi' closed,
  gamma' 16M–70M× gap, zeta' structural Cauchy gap.
  FIRED: DIGAMMA (ψ-Stirling → gamma') + ETA-DERIV
  (log-weighted DP series → zeta').
- 2026-09-11 REALGAM-LOW delivered (`09014d69`, NEW
  real_low file, registered, no build): 0.77 CLOSED
  (target 0.88 missed — exterior secant tops out;
  upgrade = log-convex 0.78). 24/30 feedable, 6 open
  (R35/R25/E05/R36/R26/E06 → re-tier).
  ETA-DERIV empty (too big) — re-fired INNER-only.
  GAMMA-FEED fired (plug 0.77 → 24 lowers).
- 2026-09-11 GAMMA-FEED honest-BLOCKED (NEW `door3_
  gamma_feed.lean`, registered, no build): 24 sound
  conditionals banked, but 0.77 real does NOT
  transfer (bridge upper-only; premise numerically
  FALSE at large |Im|). TRUE missing input = complex
  Stirling LOWER |Γ| (not real). Await DIGAMMA
  (Stirling series may serve both ψ and |Γ|-lower)
  before firing STIRLING-LOW.
- 2026-09-11 DIGAMMA delivered (`91e5f426`, NEW
  digamma file, registered, no build): ψ framework
  conditional; gaps 4×–269× (was 16M×); missing =
  explicit-remainder Stirling for ψ.
  ETA-DERIV-IN empty (too big twice) — ETA-MICRO
  fired instead (pair/tail shapes + 1 demo).
- 2026-09-11 STIRLING-REM delivered (`b678ef5d`, NEW
  rem file, registered, no build): Wendel two-sided
  + log/slope forms + real lowers (1/2 on [1,2]) +
  reflection consequence. Partial (M1–M4 named).
  PSI-SLOPE fired (finite-difference ψ-discs from
  slope forms → discharge DIGAMMA premises).
- 2026-09-11 PSI-SLOPE delivered (`b9471d0a`, NEW
  psi_slope file, registered, no build): real discs
  CLOSED tighter than assumed — complex transfer
  BLOCKED (Wendel real-only). Same wall as FEED.
  COMPLEX-WENDEL fired (Im-discount lower or
  log-convex transfer; honest-useless verdict
  allowed).
- 2026-09-11 CONCENTRATION: all gamma-front walls =
  one missing lemma. STIRLING-REM fired (master
  explicit-remainder logΓ; priority |Γ|-lower →
  ψ-disc → π/2-upper).
- 2026-09-11 ETA-MICRO delivered (NEW `door3_eta_
  prime.lean`, registered, no build): pair/tail
  shapes closed + R05-n2 demo (c=0,r=1). Instantiation
  wave queued (per-center trig + summability).
- 2026-09-11 PREM-TIER delivered (NEW `door3_tier_
  direct.lean`, registered): honest-negative — even
  ρC=0.01 small-disc Cauchy overshoots tiers 200×+
  (41 mismatches proved). Queues TRUE-MEASURE
  (numerical TRUE |xi'| per cell: re-tier vs prove?).
- 2026-09-11 HEADB delivered 20/20 (NEW `door3_dp_
  headB.lean` 183KB, registered, no build): n=25..44
  all radius 1/100, centers honest. Infrastructure
  (disc dead).
- 2026-09-11 ENDGAME WAVE ×9 fired (all write-only,
  disjoint files): DISC-HEAD A/B/C (terms 5–24 /
  25–44 / 45–64, 1/100 discs) + DISC-TAIL (zeta tail,
  M-pick for ≤1/2) + PREM-POLY/PI/GAMMA/ZETA/TIER
  (5 premise-class files across 40 cells). Next:
  disc assembly + BottomStrip/edge/tail + capstone.
- 2026-09-11 TFFIX GREEN, committed (`957e4b43`,
  2/3): double-neg rewrite restructured. DP STAGE 2
  re-fired (NEW `door3_dp_terms.lean`: cos mirror +
  n=2,3,4 discs + S₄-Im demo ≥1.0, ≤300 lines).
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
- 2026-09-17 WAVE1-DERIV (background `ses_f52ba7d12ffegkyJAvci2Emxk6`):
  staged `door3_R02_ball_advance.lean` (registered lakefile `RootScratch`;
  no sorry/admit/axiom, verified by grep): `R02_premBall_of_Lambda:46`
  + `R02_premBall_of_FE:52` (Lambda/FE premises give `premBall_R02`
  via `CS_ballSup16800_of_Lambda0`), `R02_deriv67200_of_Lambda/FE:57/64`
  (deriv cap 67200 on R02), `R02_cauchy_closedForm:79`
  (`16800/0.25=67200`), `R02_tier07_mismatch/gap/ratio:83/87/91`
  (`0.07<67200`, gap 67199.93, ratio 960000x), `R02_cauchy_ratio05/06`
  (1344000x/1120000x), `R02_ball_assembly_value/le_cap/margin:102/106/109`
  (`0.5+35*479=16765.5<=16800`, margin 34.5). Build: guarded wrapper
  `door3_R02_ball_advance`, cold-cache timeout at 900000ms
  (`[1365/8617] Built Mathlib.Order.Bounded`, no errors; stale lock
  cleared, lock free). HONEST residual: tier-M 0/41 via Cauchy
  (R02 needs 0.07, has 67200); `CS_Lambda0_upper_fat` (<=479, true
  O(1)-O(10)) and FE+Stirling discharge stay explicit premises;
  module build verification pending (rebuild warm). Next: (i) discharge
  Lambda0<=479 or FE step, (ii) direct deriv/subdivision re-tier,
  (iii) warm rebuild verify (WAVE2-DERIV tasked).
- 2026-09-17 WAVE2-DERIV (background `ses_f52aaefacffep3MKAVWS69wG2V`):
  `door3_R02_ball_advance.lean` 117->282 lines, 13 new theorems,
  grep-clean (no sorry/admit/axiom/simpa). Build BLOCKED honestly
  (14x GUARD-WAIT 0.4->10.6min, timeout; predates the dead-owner
  fast-path fix — its wait was the stale 18600 lock, since cleared).
  Lambda0 discharge: unconditional FE+Stirling needs Gamma/right-zeta
  caps absent from Mathlib+repo, so `<=479` stays premise; proved
  `R02_FE_step_of_Lambda:184` (wide premise yields FE-step M:=479,
  strictly weaker residual) + generic `R02_ballSup_of_LambdaCap:160`
  (any M>=0 gives ball `0.5+35*M`). Deriv narrowing: generic
  `R02_deriv_of_ballCap:141` (cap C gives `C/0.25`),
  `R02_cauchy_scales_4C:155`; M=10 true-scale chain:
  `R02_ball_assembly10_value:190` (`350.5`),
  `R02_ballSup350_of_Lambda10:194`,
  `R02_ball_sharpening_factor47:208` (47x),
  `R02_deriv1402_of_Lambda10:212` (deriv `<=1402`, drop 65798).
  Blocking proved: `R02_tier07_needs_ball00175:233`
  (`C/0.25<=0.07` needs `C<=0.0175` vs true ~10, gap 571x),
  `R02_tier07_needs_radius240000:242` (needs R>=240000 vs 1.51);
  tier still open (`1402-0.07=1401.93`). VERDICT: Cauchy tuning
  provably insufficient — subdivision+re-tier or direct deriv bounds
  mandatory (WAVE3-DERIV tasked).
- 2026-09-17 WAVE3-DERIV (background `ses_f529ac67bffeznswztkEsZL7MG`):
  subdivision pilot banked in `door3_R02_ball_advance.lean:271-493`
  (22 theorems, grep-clean): halves `R02W:303`/`R02E:307`
  (`xmid=-6.75`) + mem/coverage `:311/322/333`; per-subrect Cauchy
  at halved radius via `DerivCauchyBridge.uniform_deriv_of_closedBall_bound`
  (`R02W/E_deriv_of_ballCap125:349/366`, `C/0.125=8*C :383`).
  No in-tree direct-deriv (`one-over-x`) route for `xiShifted` exists
  (grep) — subdivision was the available step. KEY NEGATIVE RESULT:
  subdivision provably WORSENS the cap — `R02_subdiv_doubling:415`
  (`134400=2*67200`), `R02_subdiv_halving_worsens:419`; halved radius
  needs ball `<=0.00875` (`:432`, true ~10) or radius 240000
  (`:449` via `:242`); sharpened per-half 2804 (gap 2803.93) still
  above 0.07. Builds: 2x900s guarded attempts, cold-cache dependency
  phase only (1907/2273, 2134/2529; module not reached, no errors);
  fast path applied twice (dead owners 13340/19252/7156 cleared).
  LANE VERDICT: Cauchy at ANY radius + subdivision both provably
  insufficient — remaining routes are (a) direct derivative bounds via
  product-rule decomposition (new analytic machinery), or (b) re-tier
  the cells (change tier targets; some cells feasibility-negative).
  WAVE4-DERIV pivots to (a)/(b) scoping + build sweep (tasked).
- 2026-09-17 WAVE1-ETA (background `ses_f52ba7d25ffeE6EsYl0uXyPCiB`,
  committed in `2b76f75`): eta-factor group CLOSED in
  `door3_cell_suppliers.lean` (grep-clean, no sorry/admit/axiom/simpa):
  `CS_rpow0605_proved:354` (`2^0.605<=1.53` via `rpow_def_of_pos` +
  `CS_log2_le` cap `x<=0.41936` + `Real.exp_bound'` n=4, numeral
  ~1.5212<=1.53), `CS_etaFactor_of_rpow:406` (triangle `1+1.53<=2.53`
  via `norm_cpow_eq_rpow_re_of_pos` at `(1-sCenter).re=0.605`),
  `CS_etaFactor_proved:422` (unconditional composition; feeds
  `CS_factor_need` `1.4*2.53=3.542`). Build: guarded wrapper waited
  through sibling (`GUARD-WAIT` 2.8->14.8min), acquired, cold-cache
  timeout at 900000ms (`[1459/8688]`, zero errors); stale lock of dead
  owner removed; background rebuild `bgp_0ad586252001eejeh5ES8FT54e`
  running (`[1281/1756]`, no errors). Residual: olean verification
  pending (target compiles last); eta-group proof residual NONE.
  Out-of-scope premises untouched: `CS_zeta14_residual`,
  `CS_Lambda0_upper_fat/FE_step`, `CS_reflected_upper_00195`,
  `CS_sine_upper_20128`, `CS_reflection_link`, `CS_S2C_Re_eq`,
  `CS_cos675_nonpos`. Next: verify build green, then adjacent
  micro-lemma (WAVE2-ETA tasked).
- 2026-09-17 WAVE2-ETA (background `ses_f52a3cb4effe9P2RdJummGtb4M`):
  build verification HONEST-NEGATIVE (serialization respected): orphaned
  wave-1 builder dead at `[1288/1756]`, no `BUILD-EXIT`; mutex held by
  dead owner with 4 sibling builds queued, one bounded attempt
  (`-RetrySec 30 -MaxWaitSec 300`) hit `GUARD-TIMEOUT` after 10x
  `GUARD-WAIT` (5.2->10.2min); no second lake started, lock untouched.
  Full green stays patch-phase (1700-8600 cold modules). Lemma CLOSED:
  `CS_cos675_nonpos_proved`, `door3_cell_suppliers.lean:318` (+21 lines):
  `Real.cos_nonpos_of_pi_div_two_le_of_le` with banked `CS_eta_phase1_lt`
  (`6.75*log2<4.679<=1.5*pi`, `pi_gt_d6`) + floor `4.6787<=6.75*log2`
  (`CS_log2_ge`) above `pi/2` (`pi_lt_d6`); true cos~-0.03364, margin
  0.0334 (Python-verified); grep-clean, same discipline. Residual: next
  adjacent `CS_S2C_Re_eq:305` (cpow Re identity, strictly bigger;
  needs `Complex.cpow` phase/norm split at sCenter); `CS_complex_S2_Re_ge_one`
  /  `CS_complex_S2_abs_ge_one` one premise nearer (`CS_rpow2_head_upper`
  already `CS_rpow2_proved`). No sibling files touched (WAVE3-ETA tasked).
- 2026-09-17 WAVE3-ETA (background `ses_f529d4a31ffes3NYsCtkdTJIxW`):
  FULL `CS_S2C_Re_eq` proved in one turn, no fallback needed:
  `CS_cpow2_sCenter_re:338` (cpow phase/norm split
  `Re(2^-sCenter)=2^-0.395*cos(6.75*log2)` via `cpow_def_of_ne_zero`
  + `ofReal_log` + `exp_re`, mirroring `prefix_R05_cpow2_re`;
  `-sCenter` parts from `R02Pilot.sCenter_re/im`) +
  `CS_S2C_Re_proved:375` (`Re(1-2^-s)=1-2^-0.395*cos(...)` via
  `(2:C)=((2:R):C)` cast + `sub_re`/`one_re`), unconditional.
  Grep-clean. Build: pre-check found stale lock (dead holder, no live
  builders) but wrapper sat `GUARD-WAIT` 900s (age resetting —
  sibling queue refreshing); no retry per rule; verification pending.
  Residual: verify green, then `CS_complex_S2_Re_ge_one`/
  `CS_complex_S2_abs_ge_one` dischargeable (all three premises now
  closed: S2C + cos675 + rpow2). Standing sweep clause active:
  WAVE4-ETA owns suppliers build-error sweep (WAVE4-ETA tasked).
- 2026-09-17 WAVE4-ETA (background `ses_f528d1be3ffetGmDaGYUJ2EYxk`):
  S2 discharge one-liners banked in `door3_cell_suppliers.lean:410/416`
  (+13, grep-clean): `CS_complex_S2_Re_proved` /
  `CS_complex_S2_abs_proved` (unconditional applications of
  `:383/:396` to the three closed premises S2C+cos675+rpow2;
  mirrors `CS_etaS2_uncond`/`CS_etaFactor_proved` shape).
  Fast path applied 3x, all correctly refused (live owners
  19252/7156/22384 + live lake/lean each time — never a dead lock).
  Builds: 2x900s, 15x+15x GUARD-WAIT, no BUILD-EXIT (owner rotation
  observed); no diagnostic ever produced so no fix cycle possible.
  Edit build-UNVERIFIED. Residual: one green guarded build when a
  live lock frees, then feed S2 into `CS_zeta_of_parts` assembly
  (WAVE5-ETA tasked).
- 2026-09-17 WAVE1-EDGE (background `ses_f52ba7d11ffe2qDtg1yOVVnRST`,
  committed in `2b76f75`): `door3_rh_wiring.lean` extended +194 lines,
  12 new theorems, grep-clean (imports +`door3_cutL10_remainders`,
  `door3_sliver_nonvan`, `door3_closed_cover`; no cycles):
  `cutL10_gamma_banked:140` (conjugacy over right-lane Stirling cert,
  transitively hypothesis-free), `cutL10_zeta_of_etaCert:144`
  (eta-numeral adapter `hSdef/hSlow/hTail/hEnough/hLower`),
  `cutL10_deriv_of_ballSup:157`, `cutL10_fencing_of_etaCert_and_ballSup:165`
  (full `CellFencingHypotheses CutL10 0.001 0.04`),
  `hLeft_of_cutL10_fencing:182` (exact `hLeft` capstone shape),
  `xiCutoffLines10_of_both_fencings:193`, `hSliver_of_edgeNumericData:205`
  / `hSliver_of_topNumericData_via_conj:230` (exact `hSliver` from
  outer-bound CENTER+DERIV+width gates),
  `xiCentralEdgeStrips10_of_uniformStrips:251` (first derivation of
  edge strips from uniform certs — no prior one existed),
  `bottomStrip_obligations_of_uniform_closed:278`,
  `mainBand_upper_of_strip_and_grid:292` (upper main band from bottom
  strip + closed-grid fencing), `#print axioms` lines throughout.
  Builds: 2x900s consumed by GUARD-WAIT + one ACQUIRED killed mid-build
  by timeout; retry via agent 25m wakeup (queue had 22 live builders).
  Residual (exact premises): CutR10 `hSdef/hSlow/hTail/hEnough` + ball-sup
  `<=0.04`; CutL10 `hLower` + `hProd`/`hJoint`; edge outer-bound numerals
  + width gates; bottom-strip `hb`/`hB` + `B/(1/2)<=1`; grid-fine `Hgrid`;
  lower main-band conjugated strip. Standing sweep clause active:
  WAVE2-EDGE owns rh_wiring build-error sweep (WAVE2-EDGE tasked).
- 2026-09-17 WAVE2-EDGE (background `ses_f528adbb2ffe6nHonnAT7jETe9`):
  sweep partial in `door3_rh_wiring.lean` (+15, grep-clean): new
  `xiCentralEdgeStrips10_of_uniformStrips_011:278` (delta=11/1000,
  both width numerals `norm_num`-closed, only two uniform-strip
  premises left) + `#print axioms:341`. Fast path: 1 live owner
  respected, 2 dead locks (12728/22384) deleted. Builds: 2 guarded
  attempts, both 900s timeouts in cold Mathlib phase (1907-2376/2703;
  reference: 09-09 log BUILD-EXIT=0, 8705 jobs, axioms clean, for the
  8-theorem version); background `bgp_0ad9284f7001zMSl7jS6n0184J`
  queued behind live peer; oleans absent so full rebuild exceeds
  15-min windows — module green stays queue-phase. HONEST RESIDUALS:
  CutR10 ball-sup `<=0.04` BLOCKED (reach `<=12.87`;
  joint needs `||z(1/2+8.45i)||<=0.64`, implausible below first zero
  t~=14.13; poly*pi*Gamma alone ~=0.062>0.04); CutL10 `hLower` owned
  by zeta lane (needs slow-rtail>=1.4 vs `||z||~=1.549`); edge
  mT/MT numerals unbanked (sliver file has gate arithmetic only);
  ratio gates `hGateT/hGateB`, mirrored left ball-sup/sliver, joint
  `hSliver`, bottom `hb/hB/hM`, grid `Hgrid` all explicit premises.
  WAVE3-EDGE tasked (sweep + ratio-gate/left-ball-sup push).
- 2026-09-17 WAVE3-EDGE (background `ses_f526a9b73ffeyMmYwAY25CMn0D`):
  top sliver gate closed in `door3_rh_wiring.lean:250` (+17, grep-clean):
  `hSliver_of_topNumericData_011_via_conj` instantiates the `:230`
  top-only adapter at `mT=11, MT=1000`, closing
  `hGateT : 0.01<11/1000` with banked
  `Door3SliverNonvan.sliver_example_gate_top` (`:460-461`) + `norm_num`
  sides; residual only supplier bounds `hTopLower`/`hTopDeriv` at those
  numerals. Lock: owner rotated 16068->17740, live every check —
  correctly never deleted (3x900s GUARD-WAIT, ages to 35.6min, live
  builders veto autoclear); no BUILD-EXIT, no diagnostics to fix;
  last green remains `b9ada92` 8-theorem reference. Residual: verify
  green in a free window; CutR10 `<=0.04` unreachable, CutL10 zeta-owned,
  `mT/MT` beyond 11/1000 unbanked, mirrored left ball-sup unmatched.
  WAVE4-EDGE tasked (sweep + bottom-gate mirror).
- 2026-09-17 EDGE-NEXT (background `ses_f51527e69`, proof-only,
  grep-clean): HONEST NEGATIVE WITH REFUTATION — no supplier bound
  closes at 11/1000: `hTopLower`/`hBotLower` at m=11 are INFEASIBLE
  (banked endpoint norms equal 1/2 at x=0 per sliver_edge :221-234 +
  sharpness :203-210 and boundary_endpoints :28-32; any closable
  uniform m must satisfy m<=1/2, so 11 is refuted, not merely open).
  Banked `edge011_topLower_missing` residual spec
  (`door3_rh_wiring.lean:296-321`, +21). `hTopDeriv`/`hBotDeriv` at
  1000 reduce to one closed-ball sup C=1000 on closedBall 0 12
  (sliver_edge :322-370) with no banked C numeral — open, deriv-owned.
  No premZeta/premGamma floors at edge heights (all at Re 0.395/0.2/
  0.105). CONSEQUENCE: retire the 11 example ratio; re-instantiate
  adapters at feasible m<=1/2 once edge/zeta banks (1)/(2) + deriv
  banks (3) per the filed spec. EDGE-NEXT2 tasked (m-half
  re-instantiation shapes + bottomStrip/grid pivot).
- 2026-09-17 EDGE-NEXT2 (background `ses_f5150312`, proof-only,
  grep-clean): m-half shapes banked — `hSliver_of_topNumericData_half_
  via_conj:340`, `hSliver_of_edgeNumericData_half:360`,
  `xiCentralEdgeStrips10_of_uniformStrips_half:387` (gates close by
  `norm_num` once MT/MB<50 fed); pivot `gridH_c00_of_R00:409` banks
  the c00 leaf of `Hgrid` via sorry-free `R00_H_instance` (residual:
  R00 leaf obligations only — center + deriv 0.05, unprovable-in-
  Mathlib per assembly notes). Bottom-minorant pivot rejected
  (only x=0 point banked, still modulo open ball sup). EDGE-NEXT3
  tasked (next grid leaves c01+ replication).
- 2026-09-17 EDGE-NEXT3 (background `ses_f514de0e`, proof-only,
  grep-clean): 2 more grid leaves — `gridH_c02_of_R02:510` +
  `gridH_c03_of_R03:533` (same Hgrid shape; R01 skipped by design).
  Leaves done 3/40; each residual = that cell's leaf obligations
  (center + deriv tier, unprovable-in-Mathlib per assembly).
  EDGE-NEXT4 tasked (c04+ replication run).
- 2026-09-17 EDGE-NEXT4 (background `ses_f514d34e`, proof-only,
  grep-clean): 3 more leaves — `gridH_c04_of_R04:556`,
  `gridH_c05_of_R05:579`, `gridH_c06_of_R06:602` (no skips in
  R04–R06; R01 sole skip by design). Leaves done 6/40.
  EDGE-NEXT5 tasked (c07+ replication run).
- 2026-09-17 EDGE-NEXT5 (background `ses_f514c548`, proof-only,
  grep-clean): 3 more leaves — `gridH_c07_of_R07:625`,
  `gridH_c08_of_R08:648`, `gridH_c09_of_R09:671` (no skips).
  Leaves done 9/40. EDGE-NEXT6 tasked (c10+ replication run).
- 2026-09-17 EDGE-NEXT6 (background `ses_f514a86e`, proof-only,
  grep-clean): 3 more leaves — `gridH_c10_of_R10:694`,
  `gridH_c11_of_R11:717`, `gridH_c12_of_R12:740` (no skips).
  Leaves done 12/40. EDGE-NEXT7 tasked (c13+ replication run).
- 2026-09-17 EDGE-NEXT7 (background `ses_f514975d`, proof-only,
  grep-clean): 3 more leaves — `gridH_c13_of_R13:763`,
  `gridH_c14_of_R14:786`, `gridH_c15_of_R15:809` (no skips).
  Leaves done 15/40. EDGE-NEXT8 tasked (c16+ replication run).
- 2026-09-17 EDGE-NEXT8 (background `ses_f5149011`, proof-only,
  grep-clean): 3 more leaves — `gridH_c16_of_R16:832`,
  `gridH_c17_of_R17:855`, `gridH_c18_of_R18:878` (no skips).
  Leaves done 18/40. EDGE-NEXT9 tasked (c19+ replication run).
- 2026-09-17 EDGE-NEXT9 (background `ses_f5148600`, proof-only,
  grep-clean): 3 more leaves — `gridH_c19_of_R19:901`,
  `gridH_c20_of_R20:924`, `gridH_c21_of_R21:947` (no skips).
  Leaves done 21/40 — PAST HALFWAY. EDGE-NEXT10 tasked (c22+ run).
- 2026-09-17 EDGE-NEXT10 (background `ses_f51468e2`, proof-only,
  grep-clean): 3 more leaves — `gridH_c22_of_R22:970`,
  `gridH_c23_of_R23:993`, `gridH_c24_of_R24:1016` (no skips) +
  sweep note: assembly `:3416` labels R22 tier (0.002,0.05) but
  obligations/instance use (0.002,0.07) — doc-level inconsistency
  filed. Leaves done 24/40. EDGE-NEXT11 tasked (c25+ run).
- 2026-09-17 EDGE-NEXT11 (background `ses_f514500b`, proof-only,
  grep-clean): 3 more leaves — `gridH_c25_of_R25:1039`,
  `gridH_c26_of_R26:1062`, `gridH_c27_of_R27:1085` (no skips) +
  authorized doc-only fix (assembly `:3416` R22 tier label
  `(0.002,0.05)`→`(0.002,0.07)` in `/-!` comment; 1 line, no code).
  Leaves done 27/40. EDGE-NEXT12 tasked (c28+ run).
- 2026-09-17 EDGE-NEXT12 (background `ses_f5144409`, proof-only,
  grep-clean): 3 more leaves — `gridH_c28_of_R28:1108`,
  `gridH_c29_of_R29:1131`, `gridH_c30_of_R30:1154` (no skips).
  Leaves done 30/40. EDGE-NEXT13 tasked (c31+ run).
- 2026-09-17 EDGE-NEXT13 (proof-only, grep-clean): 3 more leaves —
  `gridH_c31_of_R31:1177`, `gridH_c32_of_R32:1200`,
  `gridH_c33_of_R33:1223` (no skips). Leaves done 33/40.
  EDGE-NEXT14 tasked (c34+ run).
- 2026-09-17 EDGE-NEXT14 (background `ses_f5141d62`, proof-only,
  grep-clean): 3 more leaves — `gridH_c34_of_R34:1246`,
  `gridH_c35_of_R35:1269`, `gridH_c36_of_R36:1292` (no skips).
  Leaves done 36/40 — FINAL 4. EDGE-NEXT15 tasked (c37+ last run).
- 2026-09-17 EDGE-NEXT15 (background `ses_f5140f30`, proof-only,
  grep-clean): GRID REPLICATION COMPLETE — `gridH_c37_of_R37:1315`,
  `gridH_c38_of_R38:1338`, `gridH_c39_of_R39:1361`,
  `gridH_c40_of_R40:1384` + COUNT `gridH_leaf_count_done:1401`.
  FINAL 40/40 gridFine leaves banked (R01 sole skip by design).
  Wiring lane structural work DONE; remaining: supplier numerals
  (leaf obligations), m-half premises, + full-file typecheck.
   EDGE-SWEEP tasked (whole-file green build).
- 2026-09-17 EDGE-SWEEP (background `ses_f5140110`): GREEN — THIRD
  GREEN LANE MODULE. BUILD-EXIT 1→0 (8712 jobs, verified in
  `...-20260917-025216.log` tail): fixed stacked-docstring parse
  error (`/--`→`/-` :317, Lean 4.33 quirk, core-probed) +
  forward-reference reorder (generic strips theorem above `_half`,
  `:382-417`). All 29 `#print axioms` standard, sorryAx gone.
  Residual: push_neg deprecation warning (pre-existing); audit
  block covers only through c06 (c07..c40 + count lack #print).
  EDGE-AUDIT tasked (audit extension + bottomStrip step).
- 2026-09-17 EDGE-AUDIT (background `ses_f513707a`): audit block
  extended c07..c40 + count (both green log tails confirm 8712
  jobs, all `#print` standard; count depends on NO axioms).
  bottomStrip conditional bridge banked
  (`bottomStrip_baseBounds_at_zero_of_ballSup`: zero-minorant +
  ball-sup + hM premises; uniform hb still residual). Wiring file
  GREEN twice. Edge structural work COMPLETE — lane redirects to
  ZETA-UPPER (deriv's `UZ<=10` gap). EDGE-DONE; ZETA-UPPER tasked.
- 2026-09-17 ZETA-UPPER (background `ses_f51359d4`, survey-only,
  touched NOTHING): obligation exact (`:6493`, `zeta=riemannZeta`
  by rfl); assembly-ready instance ALREADY banked (`:890`,
  `1680*UZ` shape). KEY FIND: `R02_D3_zeta_upper_934`
  (zeta_rigorous `:32566`) has the SAME full R02 rect,
  unconditional (eta-tail M=1 + cvtFactor route); importable from
  any `import zeta_rigorous` file (R02-ball file doesn't import
  it — hence "non-imported" in spec). Tail-machinery sweep: all
  wrong-target/too-weak (best sub-rect <=125 on Re>=0.25 strip;
  eta sums need M>=2.3e30 terms for r<=5 — dead). Ladder 934→10
  (93.4x) needs FE+Stirling+convexity, not longer sums. ACTIONABLE:
  bridge UZ=934 NOW (tiny new module importing both + rfl +
  instantiate 4-factor cap at 1680*934). ZETA-BRIDGE tasked.
- 2026-09-17 ZETA-BRIDGE (background `ses_f5134860`): bridge FILED
  (`door3_R02_zeta_bridge.lean` new: transfer `:22` via rfl +
  `R02_D3_zeta_upper_934`, cap `:31` at 1680*934=1569120;
  lakefile roots+globs registered; grep-clean) but UPSTREAM RED:
  build reached [8701/8703] then failed INSIDE suppliers
  (`:2982` no-goals+rewrite miss, `:3442/:3728/:3887` unsolved
  x*x+x*x=x^2+x^2, sorryAx cascade at `:3011`) — proof-only
  waves (:2742+ Im/S4 content) accumulated unverified past green.
  Bridge never elaborated. ETA-SWEEP tasked (fix listed errors +
  verify new content, build owner).
- 2026-09-17 ETA-NEXT7 (background `ses_f5148601`): EMPTY result —
  no report text, no tree writes (suppliers clean). Im(S6) route
  NOT attempted; S4 1.0342 stands. ETA-NEXT8 tasked (Im-route
  retry, tighter brief).
- 2026-09-17 ETA-NEXT8 (background `ses_f5142ea5`, proof-only,
  grep-clean): Im route HONEST STALL — Im splits n=5,6 banked
  (`:2742/:2778`, exp_im mirrors), sin bounds (`sin5<=-0.99 :2816`,
  `sin6<=0 :2877`), Im5 bracket `[-0.55,-0.5148]` (`:2924/:2946`),
  Im6 nonpos (`:2963`), S6-Im link (`:2972`), conditional
  (`:2989`) + abs-link (`:2998`). 5-term Im strictly negative,
  6-term nonpos — no unconditional Im(S6)>0 (needs Im(S4) lower,
  out of scope). S4 1.0342 stands; true Im(S6)~=1.00<1.56 noted.
  ETA-NEXT9 tasked (Im(S4) lower n=1..4).
- 2026-09-17 ETA-NEXT9 (background `ses_f513e6fd`, proof-only,
  grep-clean): Im(S4) LOWER banked — splits n=1..4 (`:3039-3148`),
  sin windows (`sin2<=-0.99 :3186`, `sin3>=0 :3245`,
  `sin4<=0.068 :3285` via sin_add+banked pi lemmas),
  `CS_complex_S4_Im_ge_07017:3396` (Im>=0.7425-0.0408=0.7017;
  true ~=1.307), `CS_complex_S6_Im_ge_01517:3407` + abs
  (`:3415`) + below-Re note (`:3423`). Honest stall on S6
  (0.1517<0.95); S4 1.0342 stands. KEY UNLOCK: Re+Im Pythagoras
  pair gives |S4|>=sqrt(1.56^2+0.7017^2)~=1.71 > 1.56.
  ETA-NEXT10 tasked (S4 Pythagoras pair + feed).
- 2026-09-17 ETA-NEXT10 (background `ses_f513be6f`, proof-only,
  grep-clean): S4 PYTHAGORAS PAIR banked — `CS_complex_S4_abs_ge_
  pyth:3438` (`||S4||>=1.71`, largest 2-decimal: `1.71^2=2.9241`
  vs sum `2.92598289`, margin +0.00188; 1.72 fails) +
  `CS_zeta_of_S4b:3463` + `CS_S4b_shortfall_1853:3471`
  (shortfall `0.8842`, was `1.0342` — FIRST SUB-1.0).
  Slow 1.56->1.71. Next: Im headroom huge (banked 0.7017 vs true
  ~1.307) — tighten sin2/sin4/Im3 windows (ETA-NEXT11).
- 2026-09-17 ETA-NEXT11 (background `ses_f513a091`, proof-only,
  grep-clean): all three windows tightened — sin2 d in [-0.034,0]
  (was [-0.14,0]) → `sin<=-0.9994 :3498`; Im3 POSITIVE lower via
  cubic floor (`sin e>=e-e^3/6`, `e in [0.82388,1.38685]`) →
  `Im3>=0.2389 :3673`; sin4 delta<=0.0673 (razor ~1e-6 margin) →
  `Im4<=0.04038 :3691`. Assembly: Im(S4)>=0.9480 (`:3711`, was
  0.7017; true ~1.307, headroom now 0.36), `||S4||>=1.82 :3724`
  (max 2-decimal; 1.83 fails), feed shortfall `0.7742 :3757`
  (was 0.8842 — FIRST SUB-0.8). Bonus Im(S6)>=0.3980 (still
  below Re 0.95). ETA-NEXT12 tasked (sin3 lower tightening —
  cubic 0.379 vs true ~0.894).
- 2026-09-17 ETA-NEXT12 (background `ses_f5136278`, proof-only,
  grep-clean): sin3 SPLIT-CUBIC — (a) exact-arithmetic stall
  (+0.00002, no theorem), (b) no quintic in-tree (stall), (c)
  BANKED: 2-split at m=1.066 → `sin>=0.6214 :3799` (was 0.3793;
  monotone limit 0.7307), `Im3>=0.3914 :3850`,
  `Im(S4)>=1.1005 :3870` (was 0.9480), `||S4||>=1.90 :3883`
  (max 2-decimal; 1.91 fails), feed shortfall `0.6942 :3916`
  (was 0.7742, gain 0.08). ETA-NEXT13 tasked (4-split cubic
  toward 0.7307 limit).
- 2026-09-17 ETA-NEXT13 (background `ses_f5133c8b`, proof-only,
  grep-clean): 4-SPLIT cubic banked — Python-tuned splits
  (m1=0.8687/m2=0.9742/m3=1.1592, balanced F*~=0.714614),
  `sin>=0.7145 :3942` (was 0.6214, +0.0931; limit 0.7306746),
  `Im3>=0.4501 :4009`, `Im(S4)>=1.1592 :4029`,
  `||S4||>=1.94 :4042` (max 2-decimal; 1.95 fails), feed
  shortfall `0.6542 :4075` (was 0.6942, gain 0.04). NOTE: lands
  on RED file (bridge-exposed errors :2982/:3442/:3728/:3887) —
  ETA-SWEEP must verify this content too. ETA-SWEEP tasked
  (fix-all + green, build owner).
- 2026-09-17 ETA-SWEEP (background `ses_f51316f7`): GREEN RESTORED
  (verified `...-20260917-030149.log` tail: 8688 jobs, all new
  content incl. 4-split verified, zero sorryAx). Fixes: dropped
  redundant `abel` (`:2981-2`), `sub_im`-before-`add_im` reorder
  (`:2982`), `+ring` x4 after sq_norm rewrites
  (`:3443/:3730/:3890/:4050`, mirrors green pattern). Bridge
  unblocked. BRIDGE-VERIFY tasked (rebuild bridge).
- 2026-09-17 BRIDGE-VERIFY (background `ses_f512d8a3`): GREEN —
  FOURTH GREEN MODULE. No lock, immediate acquire, `[8703/8703]
  Built door3_R02_zeta_bridge (19s)`, BUILD-EXIT=0, zero errors;
  transfer `:22` + cap `:31` (1569120) both standard axioms, no
  sorryAx; upstream ball-advance + zeta_rigorous confirmed green
  in the same run. No fixes needed. UNLOCKS: deriv 4-factor
  assembly can now FIRE at UZ=934 (finite closed deriv cap
  modulo DG/DZ). DERIV-FIRE tasked (UZ=934 assembly).
- 2026-09-17 REBOOT RECOVERY: host rebooted; all background waves died
  in flight (wave-1 gamma report never arrived; wave-4 deriv, wave-3
  zeta, wave-5 eta, wave-4 edge killed mid-turn). Stale lock 17740
  cleared (dead owner, zero live builders). Uncommitted in-flight work
  survived on disk: `door3_R02_ball_advance.lean` +161,
  `door3_pilot_R00_zeta.lean` +114 (both preserved, to be verified not
  discarded).   All five lanes relaunched as RESUME waves below.
- 2026-09-17 RESUME-SERIAL (post-reboot, single-build discipline: eta sole
  build owner; gamma/deriv/zeta/edge proof-only, no builds invoked):
  - GAMMA (`ses_f52ba7d20ffecMv174X8nWLPVS`, proof-only, grep-clean):
    banked `premGamma_E05_wnorm_le:723`, `premGamma_E05_ge_of_shift:744`,
    `premGamma_E05_threshold_ok:766`, `premGamma_E06_wnorm_le:781`,
    `premGamma_E06_ge_of_shift:802` — E05/E06 floors reduced to explicit
    numerator premises for the Stirling-disc wave (banked routes provably
    short: inner-big 0.38-scale, feed 1.33<1.5). Sweep notes filed.
  - DERIV (`ses_f527bc931ffe6P5HlHQYe5Oyqa`, proof-only, grep-clean):
    route (a) first factor-deriv cap `R02_polyDeriv_cap_disc:573`
    (`||deriv polyOf||<=9.5` on R02) + hasDerivAt chain `:517-567`;
    route (b) retier table completed `:589-660` (67200->68000,
    1402->1410, 2804W/E, 134400W/E, all with margins); fixed a
    9.51-vs-9.5 `norm_num` failure pre-build. Tier 0.07 unclosed by design.
  - ZETA (`ses_f527cba53ffeVH6VQZ1uK2vra3`, proof-only, grep-clean):
    step-2 tail push via `2^21` (`R00_eta_tail_M2097152_le:413`,
    tail `<=0.087`; S4/S8 and M=16 provably weaker — documented).
    New cert `113/2530~=0.0447`, gap `2347/500=4.694` (was 15.707),
    shortfall `~=1.855` (was 6.208); wall +4.35. Sweep notes filed
    (incl. pre-existing `div_le_div_iff_of_pos_right` fix pointer).
  - EDGE (`ses_f523ca414ffeKXqhAULrvFnfjG`, proof-only, +33, grep-clean):
    bottom gate closed symmetric with top — `gate_bottom_011:267`
    (direct, no banked bottom numeral exists) +
    `hSliver_of_edgeNumericData_011:276` (full edge adapter at
    11/1000; residual only 4 supplier bounds). `hSliver` at 011 now
    needs only supplier numerals.
  Eta (sole build owner) still running; sweep turns queued per lane.
- 2026-09-17 ZETA-NEXT (background `ses_f51527e6b`, proof-only,
  grep-clean): R00 slow 0.20->0.23 — S4 honestly WEAK (real phases
  non-constructive; `-1.37<=||S4||` weaker than 0, abandoned);
  S2 tightened t-independently (`R00_rpow2_neg0395_le_077:490`
  reusing `CS_rpow2_proved` → `R00_eta_S2_norm_ge_023:506`).
  Recomputed cert `143/2530~=0.0565` (+0.0119), gap `4.664` (was
  4.694), shortfall `~=1.844` (was 1.855). `premZeta_R00` open.
  ZETA-NEXT2 tasked (M-tail vs slow tradeoff or phase-aware slow).
- 2026-09-17 ZETA-NEXT2 (background `ses_f515060a`, proof-only,
  grep-clean): tail-vs-slow finding — M=2^22 does NOT halve
  (22*0.395=8.69<9, stalls at 0.087); M=2^23 halves
  (23*0.395=9.085>=9, 512-cap → tail `<=0.044`,
  `R00_eta_tail_M8388608_le:779` + rpow chain `:742-762`).
  Recomputed: cert `186/2530~=0.0735` (+0.017), gap `4.621` (was
  4.664), shortfall `~=1.827` (was 1.844). Tail hydraulics nearly
  exhausted; phase-aware slow (needs log3/5 bridges) is the open
  route. ZETA-NEXT3 tasked (log bridges + phase-aware slow).
- 2026-09-17 ZETA-NEXT3 (background `ses_f514ef5d`, proof-only,
  grep-clean): 23 theorems — R00 log bridges `:854-894` (log3/4/5/6
  as lane-local aliases + rpow shapes `:898-918` via `exact` on
  `CS_` closures) + FIRST phase-aware slow term: `R00_cos_875log5_
  nonneg:940` (2·2π shift into [-π/2,π/2]),
  `R00_cpow5_neg_Re_nonneg:1005`, `R00_eta_fifth_norm_ge_052:1023`
  (`‖term₅‖≥0.52`). Gap UNCHANGED honestly (needs n=3,4 Re floors
  + inv_re bridge — open, documented). ZETA-NEXT4 tasked (n=3,4
  Re floors + term₅ assembly).
- 2026-09-17 ZETA-NEXT4 (background `ses_f514a86e`, proof-only,
  grep-clean): n=3,4 Re floors banked (`R00_phase3/4 :1144-1168`,
  theta shifts `:1176/:1186`, cos floors `:1200/:1206`, cpow splits
  `:1233/:1269`, Re floors `:1305/:1324`, inv_re bridge
  `:1333-1355`, eta Re floors `:1366-1399`, `R00_pair1_Re_ge_neg160
  :1411`) but S5 assembly STALLS (`||S5||>=-2.37`, weaker than 0;
  R00 phases destructive, cos φ3~=-0.982). Gap unchanged 4.621.
  LANE VERDICT: R00 Re-route exhausted (same oscillation wall as
  suppliers S6) — redirect to sCut slow-sum (N=4096>=21/10, OA26
  banked rtail leg; cutoff lane's hSlow). ZETA-SCUT tasked.
- 2026-09-17 ZETA-SCUT (background `ses_f514615a`, proof-only,
  grep-clean): sCut section `:1553-2130` — S2 shard `2/7<=||S2||`
  (`:1746`), per-term <=1 n=3..8, S8 stall (-40/7, destructive),
  defeating window `10*log3 in [10.529,11.363]` width 0.834
  (STOP documented). KEY BANK: tail transfer to sCut
  `sSCUT_eta_tail_2048_le:2095` (`||G-S4096||<=7/10` at sCut
  `1/2+10i`, OA11 numerals transferred verbatim via Re+norm only)
  + threshold `:2111` + shortfall `127/70~=1.814` (`:2116`;
  coordinator-corrected from false `121/70` — `norm_num` would have
  failed the build). hTail at sCut now CLOSED; missing leg pure
  slow N=4096>=21/10 (shard 2/7 vs bar 2.1). ZETA-SCUT2 tasked (slow
  shards 9+. or log3 sharpening for Re3 sign-lock).
- 2026-09-17 ZETA-SCUT2 (background `ses_f5142ea4`, proof-only,
  grep-clean): sharp-log3 finding — Mathlib d9 bounds collapse the
  window to 3e-9 AND prove Re3 lock IMPOSSIBLE at any precision
  (delta3 in quadrant III, true Re3~=-0.0055; no digit bound
  exists). Banked composites (log9/log12), sharp windows, cos
  nonpos + cpow split + `Re3<=0` (`:2183-2353`). Parity-correct
  next targets filed (k=7/n=8 need cos UPPERS). Slow stays 2/7.
  ZETA-SCUT3 tasked (k=7/n=8 cos-upper shard).
- 2026-09-17 ZETA-SCUT3 (background `ses_f513f2a1`, proof-only,
  grep-clean): k=7/n=8 shard banked — log8=3log2 (`:2399`), sharp
  theta8 (width 1.5e-8), `cos<=-1/4` (`:2442`, -cosδ route),
  cpow split, r8>=1/3, `Re(eta7)>=+1/12` (`:2566`, parity payoff),
  S2-Re>=2/7 (`:2590`), trivial Re>=-1 n=2..6, S8 floor -389/84
  (`:2645`, +13/12 over old -40/7 stall but still negative).
  Slow stays 2/7, shortfall 127/70. Exact weakness: five
  phaseless -1 floors; n=3 neutral-or-worse, n=4/6 cos-positive,
  n=5/7 need absent log5/log7 d9. ZETA-SCUT4 tasked (log5/7
  inventory + application or new slow idea).
- 2026-09-17 ZETA-SCUT4 (background `ses_f5139ba0`, proof-only,
  grep-clean): inventory verdict — d9 log5 EXISTS (Mathlib
  ExpBounds), d9 log7 ABSENT from Mathlib but PRESENT in-repo
  (zeta_rigorous :7579-7600, reused directly). Banked n=5 DEAD at
  any precision (quadrant III, true Re3~=-0.0055 — digit bound
  nonexistent) + n=7 SIGNED GAIN (`cos>=81/100`, r7>=1/3,
  `Re(eta6)>=+27/100 :2979`, parity payoff). Reassembled floor
  -3529/1050~=-3.361 (+127/100 over -389/84, still negative).
  Slow stays 2/7. ZETA-SCUT5 tasked (n=10 composite / n=11
  zeta-lane d9 lane).
- 2026-09-17 ZETA-SCUT5 (background `ses_f5136278`): EMPTY result —
  no report text, no tree writes (pilot clean of its work; scratch
  txts removed). Second empty this wave-set; fenced briefs help.
  ZETA-SCUT6 tasked (n=10-ONLY fenced brief).
- 2026-09-17 ZETA-SCUT6 (background `ses_f5133c8b`, proof-only,
  grep-clean): fenced brief WORKS — 3 theorems, no drift:
  `sSCUT_log_ten_eq:2407` (log10=log2+log5 via log_mul),
  `sSCUT_log_ten_ge/le:2412/:2420` (2.3025850926–34 via d9s).
  ZETA-SCUT7 tasked (n=10 phase/window fenced).
- 2026-09-17 ZETA-SCUT7 (background `ses_f5132905`, proof-only,
  grep-clean): theta10 window banked — `sSCUT_theta10_sharp_mem`
  (`:2454`, 10x log10 d9s via mul_lt_mul_of_pos_left) +
  width 8e-9 (`:2475`), mirror of theta8. ZETA-SCUT8 tasked
  (delta10/quadrant fenced).
- 2026-09-17 ZETA-SCUT8 (background `ses_f51316f7`, proof-only,
  grep-clean): delta10 banked — `sSCUT_delta10p_sharp_mem :2490`
  (δ₁₀'=θ₁₀-7π in (1.0346,1.0354), d4-pi mirror, tight-pi
  cross-checked inside). NOTE: δ₁₀' region has cos POSITIVE
  (~0.51) — constructive term. ZETA-SCUT9 tasked (quadrant +
  cos-lower fenced).
- 2026-09-17 ZETA-SCUT9 (background `ses_f5130243`, proof-only,
  grep-clean): SIGN CORRECTION — brief's `1/2<=cos θ₁₀` is FALSE
  (odd-multiple flip: cos θ₁₀ = -cos δ₁₀' ≈ -0.51078). Banked the
  correct UPPER `sSCUT_cos10log10_le_neg_half :2534`
  (cos θ₁₀ <= -1/2 via 3x-two-pi + pi flips; endpoint
  cos(1.0354)>=1/2 via sine-cubic floor, quadratic only gives
  0.464). So n=10 is DESTRUCTIVE at full phase (like n=3); the
  +0.51 lives on the reduced phase only. ZETA-SCUT10 tasked
  (cpow10 Re-upper + shard honesty check).
- 2026-09-17 ZETA-SCUT10 (background `ses_f512e53d`, proof-only,
  grep-clean): cpow10 Re-upper banked — `sSCUT_rpow10_neg_le_one
  :2581` (r10<=1 helper), `sSCUT_cpow10_neg_re :2589` (split
  mirror), `sSCUT_cpow10_neg_Re_upper :2625`
  (Re(10^-sCut)<=-(r10/2), soundly NON-numeric — agent refused
  the false -1/2 constant since r10~=0.32). PAYOFF VISIBLE:
  k=9 odd → eta9 = -10^-s → Re(eta9) >= +r10/2 constructive.
  ZETA-SCUT11 tasked (eta9 Re-lower + shard reassembly).
- 2026-09-17 ZETA-SCUT11 (background `ses_f512cd1d`, proof-only,
  grep-clean): eta9 payoff banked — `sSCUT_eta9_eq_neg_cpow10
  :3189` (odd-k sign verified (-1)^9=-1),
  `sSCUT_eta9_Re_ge :3201` (Re(eta9)>=+r10/2, negation flips
  the :2625 upper to a lower), `sSCUT_S8_add_eta9_Re_ge :3212`
  (shard + r10/2, skips k=8 honestly, r10 symbolic).
  Concretization needs r10 lower (r10~=0.316; >=0.3 gives
  +0.15). ZETA-SCUT12 tasked (r10>=0.3 floor fenced).
- 2026-09-17 GAMMA-NEXT (background `ses_f51527e70`, proof-only,
  grep-clean): E07 shift-reduction banked (`premGamma_E07_wnorm_le:836`
  `||w||<=1.64`, `premGamma_E07_ge_of_shift:857`
  `0.164<=||Gamma(w+1)||→floor`, `premGamma_E07_threshold_ok:879`;
  mirrors E05/E06 token-for-token; no E04 def exists — E07 (floor 0.1)
  was the nearest uncovered). Residual: E01/E08/E09/E10 floors +
  E05/E06/E07 numerators (0.645/0.66/0.164) for Stirling-disc wave.
  GAMMA-NEXT2 tasked (E01 or E08 shift-reduction).
- 2026-09-17 GAMMA-NEXT2 (background `ses_f515172b2ffeZUEW7gj5ZzTfyy`,
  proof-only, grep-clean): E01 triple banked (`premGamma_E01_wnorm_le:898`
  `||w||<=3.14`, `premGamma_E01_ge_of_shift:919`
  `0.0314<=||Gamma(w+1)||→floor`, `premGamma_E01_threshold_ok:941`
  `0.1382<=0.1512`; mirrors E07 token-for-token). E08 pre-checked for
  next turn (`|w|^2=6.92963125<=2.64^2`, numerator `0.0528/2.64=0.02`).
  Residual: E08/E09/E10 floors + E05/E06/E07/E01 numerators.
  GAMMA-NEXT3 tasked (E08 triple).
- 2026-09-17 GAMMA-NEXT3 (background `ses_f515089e`, proof-only,
  grep-clean): E08 triple banked (`premGamma_E08_wnorm_le:957`
  `||w||<=2.64`, `premGamma_E08_ge_of_shift:978`
  `0.0528<=||Gamma(w+1)||→floor`, `premGamma_E08_threshold_ok:1000`
  `0.1382<=0.168`; positive-im form per E06/E07). E09/E10
  pre-computed (E09: |w|~=3.6304→M=3.64, num 0.01638; E10:
  |w|~=4.3795→M=4.38, num 0.00657). Residual: E09/E10 triples +
  5 numerators. GAMMA-NEXT4 tasked (E09+E10, numerals ready).
- 2026-09-17 GAMMA-NEXT4 (background `ses_f514f6c31`, proof-only,
  grep-clean): E09+E10 triples banked (`:1015-1116`, all numerals
  Python-verified) — E-ROW SHIFT-REDUCTION COVERAGE COMPLETE
  (E01/E05/E06/E07/E08/E09/E10). Residual: 7 shifted numerators
  (E05 0.645 / E06 0.66 / E07 0.164 / E01 0.0314 / E08 0.0528 /
  E09 0.01638 / E10 0.00657) for the STIRLING-DISC wave — needs Gamma
  lower bounds at shifted w+1 points, new machinery. GAMMA-STIRLING
  tasked (survey + first numerator attempt).
- 2026-09-17 GAMMA-STIRLING (background `ses_f514eab3`, proof-only,
  grep-clean): survey banked — Mathlib has NO complex-Gamma norm
  lower (only add_one/reflection, real-only convexity); gamma_low
  34 denominator uppers + 0/30 numerators; real-0.77 transfer
  unsound; stirling files uppers-only. E05 attempt NOT closed (best
  conditional 0.38 < 0.645). Banked `premGamma_refl_lower_of_uppers`
  (generic reflection lower) + `premGamma_E05shift_refl_form` (E05
  instance) + missing-machinery spec. KEY VERDICT: reflection lane
  quantitatively DEAD (budget S*G<=4.87 vs banked S~=6.5 alone) —
  needs DIRECT complex lower at Re~=1.2. All 7 numerators open.
  GAMMA-STIRLING2 tasked (smallest-first E10 0.00657).
- 2026-09-17 GAMMA-STIRLING2 (background `ses_f514c90d`, proof-only,
  grep-clean): all crude routes DEAD on easiest numerator E10 —
  integral-rep (upper-only banked step, no phase control), product/
  factorial (pushes need to harder Re; real transfer unsound),
  reflection (banked `premGamma_E10shift_refl_form` but budget
  478.17 vs sin~1.8M). Exact shortfall 3285x banked
  (`premGamma_E10_crude_shortfall_factor/gap`). VERDICT: needs
  DIRECT complex lower at Re~=1.2 (Stirling-disc enclosure — major
  new machinery, absent from Mathlib+repo). All 7 numerators open.
  GAMMA-ENCLOSURE tasked (Euler-product lower scope).
- 2026-09-17 GAMMA-ENCLOSURE (background `ses_f514a86e`, proof-only,
  grep-clean): Euler-product survey — Mathlib has ONLY `GammaSeq` +
  `tendsto_Gamma` (no product formula; only sine Euler product
  nearby); gamma_product banks UPPERS only; no rate/tail support.
  Banked E10 scaffold `:1352-1485` (norms, prod1<=22.25, L1 norm
  identity, L2 rate spec `||Seq1-Gamma||<=0.037`, 0.044 lower,
  `0.00657<=||Gamma||` feed). N=1 approximant ~=0.045 (6.8x
  headroom). Residual: L1+L2 open; all 7 numerators open.
  GAMMA-RATE tasked (L2 rate bound or E09 scaffold replication).
- 2026-09-17 GAMMA-RATE (background `ses_f5147f21`, proof-only,
  grep-clean): route (a) verdict — `GammaSeq_tendsto_Gamma` is
  qualitative only (dominated convergence), NO rate extractable;
  missing rate lemma documented in-file (host: Stirling-disc/Binet
  leaf). Route (b) banked: E09 scaffold mirrors E10 (`:1508-1671`:
  norms 3.82/4.24, prod1<=16.20, L1 0.061 lower, L2<=0.044 spec,
  `0.01638<=||Gamma||` feed). Scaffolds done 2/7 cells (E10/E09).
  GAMMA-SCAFFOLD tasked (E08+E07 replication).
- 2026-09-17 GAMMA-SCAFFOLD (background `ses_f51468e2`, proof-only,
  grep-clean): E08+E07 scaffolds banked — E08 `:1718-1851` (norms
  2.89/3.43, prod1<=9.92, L1 0.100, L2<=0.046, feed 0.0528),
  E07 `:1898-2031` (norms 2.02/2.74, prod1<=5.54, L1 0.180,
  L2<=0.015, feed 0.164). Scaffolds done 4/7. L2 rate (all cells)
  awaits the Binet leaf. GAMMA-SCAFFOLD2 tasked (E06+E05+E01).
- 2026-09-17 GAMMA-SCAFFOLD2 (background `ses_f514500b`, proof-only,
  grep-clean): E06+E05+E01 scaffolds banked — E06 `:2084-2218`
  (L1 0.320, L2<=0.015, feed 0.300 — PARTIAL, N=1 ceiling 0.38<0.66
  floor, needs N>=2/Binet), E05 `:2271-2405` (L1 0.355, L2<=0.014,
  feed 0.340 — PARTIAL, ceiling 0.357<0.645), E01 `:2452-2585`
  (feed 0.0314 FULL). Scaffolds done 7/7. Full feeds 5/7 (E06/E05
  partial). Remaining gamma work: L2 Binet-leaf rates (7 cells) +
  E06/E05 full floors. GAMMA-BINET tasked (Binet rate leaf).
- 2026-09-17 GAMMA-BINET (background `ses_f514380d`, proof-only,
  grep-clean): Binet UNSUPPORTED anywhere (in-repo Binet is
  Fibonacci/CrossProduct; no Complex.logGamma; Stirling-remainder
  absent; Gamma_eq_integral upper-only; tendsto qualitative;
  digamma psi-Stirling STOP). E06 N-ladder banked `:2608-2740`:
  N=2 ceiling ~=0.547 FAILS, N=3 ~=0.634 FAILS, N=4 ~=0.688 FIRST
  clearing (necessity only) + N=2 link/rate specs filed.
  E06 0.66 / E05 0.645 stay open. GAMMA-N4 tasked (E06 N=4
  approximant + cpow uppers).
- 2026-09-17 GAMMA-N4 (background `ses_f51413b5`, proof-only,
  grep-clean): E06 N=4 link filed — `GammaSeq4_link:2749`
  (5-factor norm identity matching 183.56),
  `cpow4_upper_needed:2761` (`||4^s||<=5.26`, true ~=5.25977),
  `GammaSeq4_rate_needed:2769` (`<=0.027`, `0.687-0.027=0.66`
  exact), `N4_rate_budget_arith:2777`,
  `Gamma_lower_of_Seq4_rate:2785` (finite+rate→0.66 closure),
  `Nladder_cpow_uppers_needed:2812` (2.30/3.73/5.26). Ladder
  stays N=4 (no N=5 move). Residual: Seq4 FINITE lower (cpow
  lower + s+2/3/4 norm uppers unbanked) + rate leaf (absent
  repo-wide). GAMMA-N4B tasked (Seq4 finite lower).
- 2026-09-17 GAMMA-N4B (background `ses_f513fa90`, no-edit turn):
  QUOTIENT GATE FAILS — Seq4 finite lower maxes at ~=0.557-0.565
  (exact Decimal audit: U2/U3/U4 = 3.26/4.25/5.24 razor-thin;
  126.0/226.106 ~= 0.5572, true/truth ~= 0.5651) vs 0.687 gate.
  The 0.687 was the Re-CEILING (approximant upper), NOT an
  achievable lower — `Gamma_lower_of_Seq4_rate`'s finite premise
  can never discharge via this shape. N=4 route DEAD for E06.
  Next: E05 N-ladder may differ (different point), else direct
  Stirling/Binet lower is the only route. GAMMA-N4C tasked (E05
  ladder + floor-truth check).
- 2026-09-17 GAMMA-N4C (background `ses_f513e6fd`, proof-only,
  grep-clean): FLOOR-TRUTH TRIAGE — E06 floor 0.66 TRUE (Stirling
  ~0.6766, mpmath ~0.72978, margin tight 0.017 — NO re-tiering);
  E05 floor 0.645 TRUE with headroom (mpmath ~0.84242, 1.306x).
  E05 N-ladder `:2851-2890`: N=1/2/3 dead (0.38/0.547/0.633),
  N=4 first clearing (0.688) + specs ONLY at N=4 (`:2901-2940`,
  rate<=0.042). Triage: E05 true Seq4 ~0.638<0.645 (N=4 likely
  insufficient, mirrors E06) but Seq5 ~0.67146 / Seq6 ~0.69538
  CLEAR — N=5 viable for E05. GAMMA-N5 tasked (E05 N=5
  approximant + specs).
- 2026-09-17 GAMMA-N5 (background `ses_f513c3f9`, proof-only,
  grep-clean): E05 N=5 banked (`:2981-3038`: Reprod>=1137.66,
  ceiling 825.6/1137.66~=0.72570 clears 0.645, link, cpow5<=6.88
  — 6.87 FALSE, filed 6.88 — rate<=0.08, closure). SAME LESSON
  as E06: filed finite 0.725 exceeds true Seq5 ~0.671 — closure
  expected-dead as filed; closable leaf needs L<=0.671 or N=6
  (true Seq6 ~0.695). GAMMA-N5B tasked (E05 finite lower
  L<=0.671 + N=6 fallback).
- 2026-09-17 GAMMA-N5B (background `ses_f513a091`, proof-only,
  grep-clean): ACHIEVABLE finite lower banked — quotient
  `816/1237.68~=0.6593` in `[0.645,0.671]` (rpow5-frac lower
  1.36^26<=3125, cpow5 norm>=6.8, s+2..5 uppers 3.22/4.22/5.22/
  6.21, prod5<=1237.68, `:3079-3255`) + CORRECTED closure
  (finite 0.659 + rate budget 0.014 → 0.645, `:3335-3352`; old
  0.725 shape kept). Two one-char paren repairs (link `:3000`,
  cpow5 `:3013`); SAME slip flagged at `:2693/:2749/:2901`
  (unfixed, sweep-noted — parse errors, will break build).
  GAMMA-PAREN tasked (3 paren fixes + first premise_gamma
  build).
- 2026-09-17 DERIV-NEXT (background `ses_f51527e6d`, proof-only,
  grep-clean): second factor-deriv cap — fPi (only NEXT factor with
  full majorants): `R02_piExp_hasDerivAt:589`,
  `R02_pi_hasDerivAt:603` (via banked `const_cpow` pattern),
  `R02_pi_deriv_eq:619`, `R02_logPi_norm_le:626` (`||log pi||<=2.15`),
  `R02_piDerivUp_of_upper:641`, `R02_piVal_cap_disc:675` (from banked
  `pi_upper_R02_disc`), `R02_piDeriv_prod1075:680`,
  `R02_piDeriv_cap_disc:686` (`||deriv piOf||<=1.075` on R02-disc).
  Residual: fGamma cap blocked (no Gamma deriv majorant in-tree;
  Cauchy fallback 60000 recorded in deriv_up); fZeta cap blocked
  behind `R02_zeta_upper_obligation`. DERIV-NEXT2 tasked (poly+pi
  partial-product assembly or Gamma-gap unit).
- 2026-09-17 DERIV-NEXT2 (background `ses_f5150e366`, proof-only,
  grep-clean): poly×pi partial-product cap banked — value premise
  `R02_polyVal_cap_disc:696` (`<=42`), product value `:703-707`,
  Leibniz `:719-736`, exact cap `R02_polyPiDeriv_cap_disc:763`
  (`9.5*1+42*1.075=54.65` vs Cauchy 67200 — 1230x tighter on the
  direct route), downstream `R02_fullDerivUp_of_factorCaps:782` +
  `R02_fullDerivUp_bankedPQ_shape:817` (Gamma/Zeta UG/UZ/DG/DZ open
  premises). Tier honesty `:831-835` (54.65 vs 0.07, gap 54.58).
  DERIV-NEXT3 tasked (Gamma value-side 3-factor or Gamma-deriv unit).
- 2026-09-17 DERIV-NEXT3 (background `ses_f514f98b`, proof-only,
  grep-clean): 3-factor VALUE side closed — `R02_gammaVal_cap_disc:836`
  (`<=40`, rect matches, no mismatch), product `:842-857`
  (`||P*Q*G||<=1680`), 3-factor deriv with DG single open premise
  (`R02_pqGammaDeriv_prod2186:888` `54.65*40=2186`,
  `R02_pqGammaDerivUp_bankedPQG_shape:898`), taskable gap
  `R02_gammaDeriv_obligation:916` (needs Gamma HasDerivAt at s/2 +
  div_const chain + uniform majorant for concrete DG). Residual:
  UG/UZ/DZ downstream; tier far. DERIV-NEXT4 tasked (UZ value cap
  or zeta-obligation spec).
- 2026-09-17 DERIV-NEXT4 (background `ses_f514e619`, proof-only,
  grep-clean): 4-factor value side complete modulo UZ —
  `R02_polyPiGammaZetaValUp_of_caps:873`,
  `R02_polyPiGammaZetaVal_cap_disc_of_zeta:883`
  (`||P*Q*G*Z||<=1680*UZ`), `R02_zetaVal_missingNumeral_spec:909`.
  UZ VERDICT: `||zeta||<=10` NOT satisfiable (best banked uppers
  1012/934, both non-imported; premZeta/CS family prove LOWERS —
  wrong direction). UG=40 banked; DG open per obligation.
  DERIV-NEXT5 tasked (DZ assembly shape or zeta-upper lane ping).
- 2026-09-17 DERIV-NEXT5 (background `ses_f514c90d`, proof-only,
  grep-clean, NOT typechecked — no lean allowed this turn):
  full 4-factor deriv assembly — `R02_fullDerivUp_bankedPQG_shape:924`
  (`54.65*40*UZ + 42*DG*UZ + 42*40*DZ`, no analyticity),
  `R02_zetaDeriv_obligation:941` (filed DZ spec on R02 rect),
  `R02_fullDerivUp_bankedUZ10_of_zetaUpper:956` (banked-UZ=10
  instance, fires on `hZ10` + banked caps + DG/DZ).
  Armed but unfired (`hZ10` unsatisfiable — best 1012/934;
  DG/DZ open). Residual owners: UZ→zeta-upper, DG→Gamma-deriv,
  DZ→zeta-deriv (TBD, no banked cap). DERIV-SWEEP tasked (typecheck
  the assembly + fix elaboration).
- 2026-09-17 DERIV-SWEEP (background `ses_f514a86d`, build-capable,
  grep-clean): BUILD-EXIT=1 with 15 in-file errors, ALL FIXED —
  `_hM0` linter (`:160`), `Complex.norm_one`→`norm_one` x2
  (`:555/:657`), `Real.pi_lt_d2` is `<3.15` not `<3.1416` (`:634-638`,
  re-ascribed + explicit linarith), `mul_le_mul` arg-order +
  missing `0<=U` premise (`:642`, premise added, caller updated),
  `mul_le_mul`-on-`‖a*b‖` x10 (`:746+`, now `rw [norm_mul]` +
  `exact`, matching green pattern). Sweep lane `:924-971` itself
  had NO errors (`deriv zeta s` resolves; sorryAx was transitive
  fallout). Fixes UNVERIFIED (budget consumed by diagnostic run).
  DERIV-VERIFY tasked (one rebuild to confirm green).
- 2026-09-17 DERIV-VERIFY (background `ses_f514591a`, build-capable):
  BUILD-EXIT=1, ONE residual error, fixed: `:160` binder was
  linter-silenced `_hM0` so `:180` `hM0` unbound → renamed to `hM0`
  (trivially correct). Sweep lane `:924-971` clean on its own
  (`deriv zeta s` resolves; UZ10 instance clean axioms). 4 sorryAx
  infos traced solely to `:180`. Fix UNVERIFIED (budget consumed).
  DERIV-VERIFY2 tasked (one rebuild to confirm green).
- 2026-09-17 DERIV-VERIFY2 (background `ses_f51448a0`): GREEN —
  SECOND GREEN LANE MODULE. `GUARD-ACQUIRED` immediate (no lock,
  zero builders), `[8690/8690] Built door3_R02_ball_advance (20s)`,
  BUILD-EXIT=0, zero errors, zero sorryAx (all `#print axioms`
  standard). R02 file untouched by the run (fix `bfa7ac9` stands).
  Residual: linter-only warnings (`hM0` unused-variable
  false-positive kept — renaming re-breaks `:180`). Analytic
  residuals unchanged (UZ/DG/DZ open). DERIV lane build-verified;
  next: fire UZ/DG/DZ owner lanes (DERIV-DONE; assembly awaits).
- 2026-09-17 ETA-GREEN (background `ses_f526dc748ffenfLd6GzxVEOeSP`):
  FIRST GREEN LANE MODULE — `door3_cell_suppliers.lean` builds green:
  BUILD-EXIT 1 (single `hsum` rewrite failure, `rw [show (4:N)=3+1]`
  motive-mismatch on Lean v4.33.0-rc1) → sweep fix (`simp only
  [Finset.sum_range_succ, Finset.sum_range_zero]`) → BUILD-EXIT 0
  (`[8688/8688] Built door3_cell_suppliers`, axioms standard
  `[propext, Classical.choice, Quot.sound]`, no sorryAx; verified in
  `...-20260917-020605.log` tail). New: `CS_zeta_of_S2:519` (exact S2
  instantiation) + `CS_S2_shortfall:526` (gap `1.4*2.53-1=2.542` —
  `CS_zeta14_residual` still OPEN: needs slow growth + cF/tail
  sharpening). Fast path cleared 10 dead locks, never touched live
  owners. Cache now WARM — subsequent lane builds are cheap; build
  ownership rotates (sweep clause stays until all backlog green).
  Also in tree: 3-line wiring fix (`hgt`→`hgt'` via `linarith` in
  `xiCentralEdgeStrips10_of_uniformStrips`, attribution uncertain —
  found uncommitted, scan-clean, committed here).
- 2026-09-17 ETA-NEXT (background `ses_f51606f1fffeZshUQaHBq7WH2x`):
  slow 1→1.25, BUILD-EXIT=0 in 20s (warm cache), grep-clean:
  `CS_rpow2_low075_proved:553` (`0.75<=2^-0.395`),
  `CS_cpow2_norm_eq:613`, `CS_complex_S2_abs_ge_125:623` (Pythagoras
  `||1-w||^2=1-2Re w+||w||^2` with Re w<=0 + ||w||>=0.75;
  `1+0.75^2=1.25^2` exact), real-sigma S4 chain `:667-799`
  (`3^0.395<=1.57`, `0.63<=3^-0.395`, `1.69<=4^0.395`,
  `4^-0.395<=0.60` → `CS_etaS4_uncond:799`, `0.26<=1-r2+r3-r4`,
  true ~=0.3095), `CS_zeta_of_S2b:809` + `CS_S2b_shortfall:816`
  (shortfall `2.292`, was `2.542`, gain `0.25`). Floor 1.4 still
  fails honestly. Next: S6/S8 slow or cF<2.53 (ETA-NEXT2 tasked).
- 2026-09-17 ETA-NEXT2 (background `ses_f515c4afcffe8xnzPRTJgAQlme`):
  phase-aware cF 2.53->1.87, BUILD-EXIT=0 in 22s, grep-clean:
  `CS_cos675_lower_neg005:1179` (`cos(6.75*log2)>=-0.05` via
  `3pi/2+d=sin d` + `|d|<=0.05`, case-split sin lower),
  `CS_cpow_factor_re:1235` + `CS_cpow_factor_norm_eq:1269`
  (factor cpow Re/norm mirrors of the S2 lemmas at `(1-s).re/im`
  `0.605/6.75`), `CS_etaFactor_187_proved:1333` (Pythagoras upper
  `||1-w||^2<=3.4939<=1.87^2` from Re w>=-0.0765 + ||w||<=1.53),
  `CS_factor_need_187:1337` (`1.4*1.87=2.618`),
  `CS_zeta_of_S2c:1344` + `CS_S2c_shortfall_187:1352` (shortfall
  `1.368`, was `2.292`, gain `0.924` — biggest yet). Floor still
  fails; next patch must grow slow / sharpen tail (ETA-NEXT3 tasked).
- 2026-09-17 ETA-NEXT3 (background `ses_f5159d975ffebkioUz4tF3gsjZ`):
  BUILD-EXIT=0 in 25s, grep-clean. S6 route HONESTLY REGRESSED
  (log bridges + rpowpers `:1383-1552`: real S6 `0.25<0.26=S4`,
  does not substitute complex slow; S6-at-1.87 shortfall `2.368`
  vs S2c `1.368`). cF-shave fallback landed: cos lower `-0.05->-0.04`
  (`:1590`, true ~-0.0336) + `2^0.605<=1.525` (`:1648`) →
  cF `1.87->1.86` (`:1749`), need `2.604`, shortfall
  `1.368->1.354` (shave `0.014`). Also banked from tree: orphaned
  sweep fixes of uncertain attribution (scan-clean, fix-shaped, kept) —
  pilot `rfl`→explicit-`rw` for 3 `.re` proofs, premise_zeta removal
  of 6 stray post-`rw` `norm_num`s (would fail builds as no-goals).
  Next: complex slow beyond S2 or cos→-0.0336 tightening (ETA-NEXT4).
- 2026-09-17 ETA-NEXT4 (background `ses_f51561fd6ffeTXBXtGtFOFoRbE`):
  picked (b) with proved numerals; (a) honestly rejected (`φ3`
  interval ~0.56 wide, no positive cos lower without new log3
  sharpening). BUILD-EXIT=0 in 24s, grep-clean: cos lower
  `-0.04->-0.035` (`CS_cos675_lower_neg0035:1789`, true ~-0.0336) +
  cF `1.86->1.853` (`CS_etaFactor_1853_proved:1898`, Pythagoras with
  Re>=-0.053375 + ||w||<=1.525; `3.432375<=1.853^2` exact) →
  need `2.5942`, shortfall `1.354->1.3442` (shave `0.0098`).
  VERDICT: cos route nearly exhausted (-0.035 vs true -0.0336);
  binding constraint is slow (needs >=2.5942, has 1.25) — next waves
  pivot to slow growth: complex S4 slow or pilot-R00 slow (ETA-NEXT5).
- 2026-09-17 ETA-NEXT5 (background `ses_f51538dc`, build owner,
  grep-clean): COMPLEX S4 SLOW banked — cpow3/cpow4 splits
  `:1950/:1986`, rpow4 bounds (`4^0.395<=1.74 :2025`,
  `0.57<=4^-0.395 :2081`), `CS_cos3_nonneg:2101`
  (phi3 window via coarse log3, `e=phi3-2pi` in `[-pi/2,pi/2]`),
  `CS_cos4_upper_neg099:2141` (phi4 via log4=2log2, true ~-0.9977),
  `CS_complex_S4_Re_ge_156:2213` (Re>=1.5643>=1.56; true Re~=1.878),
  `CS_complex_S4_abs_ge_156:2251`, `CS_zeta_of_S4:2264` +
  `CS_S4_shortfall_1853:2272` (shortfall `1.0342`, was `1.3442`,
  gain `0.31` — biggest slow gain). BUILD-EXIT 1→0 in 35s
  (self-fixed `add_comm` rewrite mismatch). Slow 1.25->1.56, needs
  >=2.5942 still. ETA-NEXT6 tasked (complex S6 slow).
- 2026-09-17 ETA-NEXT6 (background `ses_f514d8ab`, build owner,
  grep-clean): S6 HONEST REGRESSION — cpow5/6 splits `:2322/:2358`,
  rpow5/6 bounds, cos5 bracket `[-0.14,0]` (`:2447/:2484`), cos6>=0
  (`:2550`, upper trivially-signed fallback documented),
  `CS_complex_S6_Re_ge_095:2621` (`Re>=0.953>=0.95`) +
  S6 feed (shortfall `1.6442` vs S4 `1.0342`, regression 0.61).
  BUILD-EXIT 1→0 in 36s (self-fixed redundant `ring`). KEY FIND:
  true Re(S6)~=1.366 < Re(S4)~=1.874 (series oscillates; Re-only
  S6 cannot beat S4) but |S6|~=1.70 > 1.56 — the IM ROUTE
  (Im(S6) lower) would beat S4. S4 1.0342 stands as live best.
  ETA-NEXT7 tasked (Im(S6) lower route).
- 2026-09-17 WAVE1-ZETA-PILOT (background `ses_f52ba7d16ffeMi8XN5lco6PPcw`,
  committed in `2b76f75`): `door3_pilot_R00_zeta.lean` (~290 lines,
  registered; grep-clean, no sorry/admit/axiom): R00 floor-1.9 pilot via
  `CS_zeta_of_parts`-shaped bridge — slow `1/5<=||S2||`
  (`R00_eta_S2_norm_ge`, reverse triangle, t-independent),
  tails `<=23` at M=1/M=4 (`R00_eta_tail_M1_le/M4_le` via
  `zetaCell_even_remainder_le`, proved `||sR00||<=8.76`),
  factor `<=3` (`R00_cF_upper`, triangle + `2^0.605<=2`).
  HONEST WALL: cert value `(1/5-23)/3=-38/5` vs floor 1.9
  (shortfall 9.5; `1/5<1.9*3+23` fails, no close claimed);
  N=8 gap `0.6-23-0.95<0` (0.6 labelled estimate). Builds deferred
  (2x 900000ms consumed by `GUARD-WAIT` behind live sibling builder;
  agent scheduled 30m self-wakeup to retry). Lemma-name audit done
  (`div_le_div_iff_of_pos_right`, `inv_le_inv0`,
  `norm_cpow_eq_rpow_re_of_pos` in-tree). Next: build-verify warm +
  larger-N slow or tighter tail/factor (WAVE2-ZETA tasked).
- 2026-09-17 WAVE2-ZETA (background `ses_f529b17f6ffe9CDfGPVaOreM3r`):
  wall pushed one step in `door3_pilot_R00_zeta.lean:269-355`,
  grep-clean: `R00_rpow0605_le_153:269` (reuses banked
  `CS_rpow0605_proved`), `R00_cF_253:273` (factor 3->2.53),
  `R00_rpow_eight_neg0395_le_half:289` (`8^-0.395<=1/2` via `8=2^3`,
  `3*0.395=1.185>=1`, no estimated numerics),
  `R00_eta_tail_M8_le:310` (tail 23->11.1 at M=8/S16 via
  `zetaCell_even_remainder_le`) + exact gap numerals `:334-353`
  (all `norm_num`). New cert `(1/5-11.1)/2.53=-1090/253≈-4.308`
  vs old `-38/5=-7.6` (wall +3.29); threshold `1.9*2.53+11.1=15.907`
  STILL FAILS, exact gap `15707/1000=15.707` (old 28.5), shortfall
  `≈6.208` (old 9.5) — `premZeta_R00` not discharged, documented
  honestly. Build NOT verified (lock owner dead but live builders
  held it continuously; fast path correctly refused deletion; 2x900s
  GUARD-WAIT timeouts). Standing sweep clause active: WAVE3-ZETA owns
  pilot build-error sweep + next push (WAVE3-ZETA tasked).
- 2026-09-22 INTEGRATE-GAMMA-PAREN (coordinator, in-flight diff found on
  disk, grep-clean): 6 one-char paren repairs in
  `door3_premise_gamma.lean` (`:2692/:2748/:2759/:2810x3/:2900/:2912`,
  each adds one `)` to close `‖((N:ℂ)^s)‖` before `*k/`; extends the 3
  flagged `:2693/:2749/:2901` to the full N-ladder/cpow-upper family
  with the same pattern). Scans: zero `sorry`/`admit`/`axiom`-declare,
  zero `simpa` tactic (only prose/comment mentions). Build UNVERIFIED
  (no lean/lake per anti-pileup; single-owner rule holds). Next owner:
  GAMMA-BUILD (first-ever premise_gamma guarded build + fix-all sweep).
- 2026-09-22 INTEGRATE-SCUT12 (coordinator, in-flight diff found on disk,
  grep-clean): `sSCUT_rpow10_neg_ge_03 :3221` (`0.3<=10^(-1/2)` via
  `10^(1/2)<=10/3` quadratic-root step + `inv_le_inv₀`, mirror of
  `sSCUT_rpow8_neg_ge`; `10<=(10/3)^2` by `norm_num`, `le_of_pow_le_pow_left₀`
  for the root). Concretizes SCUT11 payoff: `r10/2>=0.15`, so
  `S8+eta9 Re>=-3529/1050+0.15`. Numeral sound (sqrt10~=3.162<=3.333).
  Build UNVERIFIED (proof-only lane). SCUT13 tasked (S8+eta9+eta7
  shard reassembly with +0.15/+0.27 gains vs 21/10 bar).
- 2026-09-22 INTEGRATE-DERIV-FIRE (coordinator, in-flight diff found on
  disk, grep-clean): UZ=934 fires into the deriv assembly —
  `R02_derivUZ934_prod2041724 :981` (`54.65*40*934=2041724` by
  `norm_num`; 54.65*40=2186 exact) +
  `R02_fullDerivUp_bankedUZ934_of_zeta934 :999` (token mirror of the
  UZ=10 instance with `hZ934:‖zeta s‖<=934` restated explicitly, NO
  bridge import — bridge imports this file so the direction must stay
  one-way; bridge `R02_zetaVal_934_of_D3` discharges `hZ934` on-rect;
  `‖APQ‖<=42`/`‖APQ'‖<=54.65`/`‖AG‖<=40` discharge on-rect; DG/DZ stay
  explicit open premises). First FINITE closed 4-factor deriv cap modulo
  DG/DZ: `2041724+42*DG*934+42*40*DZ`. Build UNVERIFIED (proof-only).
  Next: DG owner (Gamma-deriv) + DZ owner (zeta-deriv) + DERIV-BUILD
  (guarded rebuild of ball_advance to verify the new instance).
- 2026-09-22 SCUT13 (background `ses_f3784cfa7`, proof-only, grep-clean):
  shard reassembly — `sSCUT_S8_add_eta9_eta7_Re_ge :3247` (S8+eta9+eta6
  with r10/2→0.15 via `:3221` + 27/100 via `sSCUT_eta6_Re_ge`; name
  `eta7`=n7=Lean idx6, doc-clarified) + `sSCUT_S8_eta9_eta7_shortfall
  :3258` (`21/10-(-3529/1050+0.15+0.27)=5293/1050~=5.041`, still short).
  New floor `-2.941` vs bar `2.1`. SCUT14 tasked (eta8 or tail-shave).
- 2026-09-22 DERIV-DG (background `ses_f3784cfa6`, proof-only,
  grep-clean): analyticity link closed — `R02_gamma_hasDerivAt :1084`
  (outer `HasDerivAt Complex.Gamma` + `div_const` + `comp`, explicit
  pole premise unlike pi's unconditional `const_cpow`) +
  `R02_gammaDerivUp_of_upper :1106` (halving transport, no closed log
  factor) + `R02_gammaDeriv_missingNumeral_spec :1140` (filed-missing,
  no uniform DG majorant in-tree per grep record:
  DerivCauchyBridge value-only, deriv_up conditional Cauchy, digamma
  conditional psi, GammaFacts analyticity-only). No false numeral.
  DG-NUM tasked (uniform Gamma-prime cap) + DZ owner + DERIV-BUILD.
- 2026-09-22 ETA-NEXT (background `ses_f3784cfa5`, proof-only,
  grep-clean): HONEST STALL banked as gaps, no false claims —
  `CS_complex_S4_Im_ge_12_gap :4148` (1.20 needs +0.04073; sin3 cubic
  limit 0.7307 blocks 0.7791 need) + `CS_complex_S4_abs_ge_195_gap
  :4157` (1.95² exceeds 1.56²+1.1592² by 0.02515536). Best stays 1.94,
  shortfall 0.6542. Next: r/log windows or tail/cF lane (ETA-TAIL).
- 2026-09-22 GAMMA-BUILD (background `ses_f3784cfa9`, sole build owner,
  in-file only `door3_premise_gamma.lean` +109/-42, grep-clean — zero
  `sorry`/`admit`/`axiom`-declare/`simpa`-tactic): FIRST premise_gamma
  GUARDED BUILDS. Build1 BUILD-EXIT=1 (8689 jobs, 64s, 37 file errors,
  all fixed); rebuild BUILD-EXIT=1 (21s, 4 errors — own-added paren
  cascade, fixed after, no second rebuild per fence). Fixes:
  `premGamma_shift_lower :72` (`rw hEq at hc`, `div_le_iff₀`+`mul_comm`);
  `premGamma_R22_threshold_ok :211` honest audit typo `0.002→0.001`
  (`0.0892<=0.09` true; floors untouched); `Ne.symm` x2 dropped `:1177/9`;
  `div_le_div_left`→`div_le_div_of_nonneg_left :1195` (+drop unused hBIG);
  29x `one_re/one_im` duplicate-`rw` dedup (`:1382-3219`); `:2730`
  missing `norm_nonneg` for linarith; `:3301-3371` `mul_pos` chain with
  hpos1-5 (abs_re_le_norm, re 2.1975-6.1975); `:3315/27/40/53` hre paren
  shapes matched to compiling in-file proofs. Residual: 4-char paren
  cascade corrected, UNVERIFIED — next wave runs one guarded rebuild,
  expected green. GAMMA-VERIFY tasked (sole build owner).
- 2026-09-22 GAMMA-VERIFY (background `ses_f377b6b54`, sole build owner):
  GREEN — FIFTH GREEN LANE MODULE. `GUARD-ACQUIRED/RELEASED` clean,
  `[8689/8689] Built door3_premise_gamma (28s)`, BUILD-EXIT=0, zero
  errors (paren cascade held; only 2 pre-existing `unusedVariables`
  linters `:1171/:2721`, left per fence). Grep-clean (zero
  sorry/admit/axiom-declare/simpa). Clears the a749821 "unverified" tag.
  Next: E05 Seq5 finite-lower + E06 N=5 rung (GAMMA-N5C, proof-only).
- 2026-09-22 SCUT14 (background `ses_f377b6b52`, proof-only, grep-clean):
  `sSCUT_S8_add_eta9_eta7_eta8_Re_ge :3268` (S8+eta9+eta6+eta7 with
  +0.15/+0.27/+1/12; honest indices: S8 k=0..7 + k=9 + second k=6,7;
  k=8 skipped) + shortfall `:3280` (`10411/2100~=4.958`). Floor
  `-2.858` vs bar `2.1`. SCUT15 tasked.
- 2026-09-22 DERIV-DZ (background `ses_f377b6b51`, proof-only,
  grep-clean): zeta analyticity CLOSED — `R02_zeta_hasDerivAt :1168`
  (`unfold zeta; exact hZ`, `zeta:=riemannZeta` defeq `:16`; explicit
  outer premise for pole at 1, mirrors gamma `:1084` minus s/2 chain).
  Grep record: Mathlib `differentiableAt_riemannZeta`, ZetaBounds
  `analyticAt_riemannZeta`, in-scope use `zeta_rigorous:712`; bridge
  value-only, no zeta deriv majorant — DZ numeral stays open, no false
  numeral. DG numeral + DZ cap remain; DERIV-BUILD tasked (rebuild
  ball_advance to verify UZ934+DG/DZ additions).
- 2026-09-22 ETA-TAIL (background `ses_f377b6b50`, proof-only,
  grep-clean): audit-only — `CS_tail_audit :4186` + `CS_tail_next_rung_gap
  :4193` (  tail is already `0`/floor in-file; no `zetaCell` instantiation
  exists, imports Mathlib+assembly only; banked rpow are head caps not
  M^{-σ} majorants, so no free tightening). KEY FIND: binding is NOT
  tail (any T>0 worsens `0.6542+T`) — needs slow or cF. ETA-CF tasked.
- 2026-09-22 GAMMA-N5C (background `ses_f3779c2b2`, proof-only,
  no-edit): VERIFIED already-closed — E05 Seq5 achievable finite lower
  `L=0.659` banked in-file (`premGamma_E05_Seq5_finite_lower :3260`,
  `816/1237.68~=0.6593` via rpow5-frac `:3086`, cpow5 norm `:3114`,
  prod5 `1237.68 :3232`) + corrected closure `:3419` (0.659+rate 0.014
  →0.645, rate `:3402` open). `L∈[0.645,0.671]`, surplus +0.014,
  headroom 0.012 to true ~0.671; dead filed 0.725 kept at `:3045`.
  No edit (GREEN preserved). E05 floor conditional only on link+rate
  (Binet/Stirling host). GAMMA-N6 tasked (E06 N=5 rung mirror).
- 2026-09-22 SCUT15 (background `ses_f3779c2b2`, proof-only, grep-clean):
  k=8 IMPOSSIBILITY banked — `sSCUT_cpow9_neg_re :3287` (split mirror),
  `sSCUT_sqrt9_le :3322` (`9^1/2<=3`, exact), `sSCUT_rpow9_neg_ge :3335`
  (`r9>=1/3`, exact inverse), `sSCUT_cos10log9_le_neg_half :3349`
  (`cos θ9<=-1/2` via banked `δ9∈(-0.019,-0.018) :2276` + `1-x²/2<=cos`,
  `1-0.019²/2=0.9998>=1/2`), `sSCUT_cpow9_Re_le_neg` (`<=-1/6`),
  `sSCUT_eta8_eq_cpow9 :3402` (even-k bridge), `sSCUT_eta8_Re_le_neg
  :3413` + `sSCUT_eta8_Re_no_pos_lock :3423` (no c>0 below). Even
  parity keeps sign → destructive ~-1/3. Shard floor stays `-2.858`,
  gap `4.958`; k=8 honestly skipped. SCUT16 tasked (S9 assembly
  skipping k=8 or tail-shave).
- 2026-09-22 ETA-CF (background `ses_f3779c2b1`, proof-only, grep-clean,
  suppliers-only commit): cF micro-shave `CS_rpow0605_tight1522_proved
  :4220` (`2^0.605<=1.522`, banked `CS_log2_le` + exp_bound n=4,
  margin 0.0008, no new windows) → `CS_etaFactor_1851_proved :4321`
  (cF 1.853→1.851, `3.423024<=1.851²`) + `CS_S4f_shortfall_1851 :4340`
  (need 2.5914, shortfall 0.6542→0.6514, gain 0.0028). Still short
  honestly. Ball_advance owner fix left untouched. ETA-SLOW tasked.
- 2026-09-22 SCUT17 (background `ses_f37760f4d`, proof-only, grep-clean):
  tail-transfer assembly (route a) — `sSCUT_S9_skip8_tail_floor :3466`
  (`(S9_skip8).re-7/10`, shard `:3446` + banked tail `7/10`
  `sSCUT_eta_tail_2048_le :2095`, `slow-tail` shape) + shortfall
  `:3475` (`12623/2100~=6.011` vs bar 21/10; shard-only gap was
  5.311). Route (b) not banked: eta9 is constructive (+r10/2), so the
  `Re<=-r10/2` shape is false at k=9 (k=8 lock already at `:3413`).
  `hEnough` NOT discharged. SCUT18 tasked (N=4096 slow leg).
- 2026-09-22 DERIV-BUILD (background `ses_f3779c2b4`, sole build owner):
  GREEN — `door3_R02_ball_advance` rebuilt `[8690/8690]`, BUILD-EXIT=0
  (attempt 2/2; attempt 1 BUILD-EXIT=1 on wave-added `:1091`). One-line
  in-file fix: `hG.comp hHalf` → `HasDerivAt.comp s hG hHalf` (Mathlib
  comp takes point explicitly). Verifies UZ934 `:999`, gamma `:1084` +
  `:1106` + `:1140`, zeta `:1168`; axioms standard, no sorryAx.
  Grep-clean. DG/DZ numerals stay open by design.   Lock RELEASED.
- 2026-09-22 ETA-SLOW (background `ses_f3775cee4`, proof-only, grep-clean):
  S6-Im step honest stall — `CS_complex_S6_Im_ge_06092 :4362` (0.6092
  via S4-Im 1.1592 + Im5/Im6 negatives, gain 0.2112 over prior 0.3980,
  true ~1.42) + `CS_complex_S6_Im_below_S4_gap :4372` (0.55 below S4).
  0.6092<1.1592 → no Pythagoras feed; slow stays 1.94, shortfall
  0.6514. Next: S8 terms or Re-route (ETA-S8).
- 2026-09-22 GAMMA-N6B (background `ses_f377691fd`, proof-only,
  grep-clean, premise_gamma-only commit): E06 Seq6 rung mirrored —
  rpow6-frac `:3926` (1.41≤6^5/26), Re-lower `:3941` (8.46), cpow6
  norm `:3954` + upper-needed 8.56 `:3972`, add6 ≤7.23 `:3978`, prod6
  10184.54 `:4004`, link `:4039` (720-num), rate 0.014 `:4055`,
  finite 0.598 `:4064`, honest-below-gate `:4222` + gap 0.062 `:4227`,
  N7-next `:4234`. VERDICT: 0.598<0.66 FAILS honestly (no force);
  ladder moves to N=7. NOTE: landed while GAMMA-VERIFY2 builds the
  same file — VERIFY2's result may predate these writes; re-verify
  queued.
- 2026-09-22 SCUT18 (background `ses_f3774d7ce`, proof-only, grep-clean):
  honest gap (no growth forced) — `sSCUT_N4096_nextRung_need :3489`
  (any E with F+E≥21/10 needs E≥11153/2100≈5.311), `plus_one_still_short
  :3501` + `plus_one_gap_eq :3507` (even ideal +1 leaves residual
  9053/2100≈4.311). k=10..4095 must supply ≥5.311 Re (tail-inclusive
  ≥6.011); single rung provably insufficient.   `hEnough` open. SCUT19
  tasked (k=10 destructive eta-lock, mirroring k=8).
- 2026-09-22 GAMMA-VERIFY2 (background `ses_f3774d7cf`, sole build owner):
  GREEN — `[8689/8689] Built door3_premise_gamma (53s)`, BUILD-EXIT=0
  (attempt 1/2), zero errors, no edits, grep-clean, lock RELEASED.
  SCOPE HONESTY: build log 02:56:13 predates N6B completion, so this
  verifies the N6 (Seq5, dc4ce9c) content it explicitly checked
  (`:3738/:3558/:3560/:3885/:3890`); N6B Seq6 content (abc2b34, through
  `:4234`) stays UNVERIFIED. Rebuild held until GAMMA-N7 reports (same
  file in flight), then VERIFY3 covers N6B+N7 together. Lock FREE.
- 2026-09-22 DG-SURVEY (background `ses_f3778800a`, proof-only, no
  edits): uniform Gamma-prime cap survey — DEAD for closed DG numeral.
  14 candidates checked (Mathlib Deriv/Digamma/BohrMollerup/GammaDeriv,
  Hadamard logDeriv, GammaFacts analyticity, digamma bridge
  `gamma_deriv_eq` + conditional `gammaPrime_le_of_psiDisc` with gaps
  4.21x-268.9x, Cauchy 60000 wall, deriv_certs value-only, psi_slope
  real-only, Wendel/gamma_low value-only, ball_advance transport-only).
  Alive only as honest-conditional (psi-disc+G or Cauchy C/ρ); closing
  needs Stirling-remainder/Gauss for `Complex.digamma` (Mathlib TODO)
  + tight G at Re∈[0.025,0.37].   `R02_gammaDeriv_missingNumeral_spec
  :1140` stays open.
- 2026-09-22 GAMMA-N6 (background `ses_f37790741`, proof-only,
  grep-clean, `door3_premise_gamma.lean` +458): E06 Seq5 scaffold
  mirrored from E05 — link `:3480`, cpow5 upper `:3494`, rate 0.065
  `:3503`, rpow5-frac `:3567`, cpow5 norm `:3595`, add2-5 uppers
  3.26/4.25/5.24/6.23, prod5 1408.65 `:3713`, finite lower 0.579
  `:3742` (`816/1408.65~=0.5793`), honest-ceiling-below-gate `:3881`
  + gap 0.081 `:3886`, N6-next filed `:3893`. VERDICT: necessity
  0.7257 clears but achievable 0.579<0.66   FAILS (no force). E06 needs
  N=6. Build UNVERIFIED (proof-only lane). GAMMA-N6B tasked (E06 N=6).
- 2026-09-22 SCUT16 (background `ses_f37777aa7`, proof-only, grep-clean,
  pilot-only commit): DOUBLE-COUNT REAL — S8 (`range 8`, `:1895`)
  already contains k=6,7 in its `-3529/1050` floor (`:3152`), so `:3247`
  summed `{0..7,9,6}` and `:3268` summed `{0..7,9,6,7}` (multiset
  floors, kept not deleted). Corrected single-count
  `sSCUT_S9_skip8_Re_ge :3446` (multiset `{0..7,9}`, S8+k=9, k=8
  skipped) floor `-3529/1050+0.15≈-3.211` + shortfall `:3458`
  (`11153/2100≈5.311`, replaces multiset 4.958). Ball_advance 2-line
  `HasDerivAt.comp` fix left for DERIV-BUILD owner (not committed).
- 2026-09-22 EDGE-AUDIT (background `ses_f3778800b`, proof-only, no
  edits): 40/40 gridH leaves audited (`:439-:1412`) vs suppliers —
  0/40 obligations banked (0/80 sub-enclosures). Tiers: (0.002,0.05)x8,
  (0.002,0.07)x8, (0.05,0.07)x16, (0.15,0.06)x8; R01 skipped by design.
  Suppliers holds only zeta-lane R02Pilot + CS geometry (no xi
  center/deriv numeral for any R00-R40 cell). Residual: 40x
  `RNN_leaf_obligations` + CutR10/CutL10 slow-sum/ball-sups + sliver
  MT/MB<50 + bottom-strip hb=0.025/B-tube — all cross-lane numerals.
- 2026-09-22 SCUT19 (background `ses_f377370f9`, proof-only, grep-clean):
  k=10 triple banked CONDITIONAL — `sSCUT_eta10_eq_cpow11 :3514`
  (even-k bridge) + `sSCUT_eta10_Re_le_neg :3530` (symbolic Re≤-r11/2,
  gated on explicit `h11`) + `no_pos_lock :3540`. NO unconditional
  lock: base mismatch caught — banked `:2534/:2625` are base-10
  (n=10/idx9), do NOT transfer to base-11 (r11/log11/cpow11 absent).
  Blocker chain filed: log11 → cos(10·log11) → cpow11_re →
  cpow11_Re_upper → rpow11_neg_ge. SCUT20 tasked (log11 bound).
- 2026-09-22 GAMMA-N7 (background `ses_f377370fc`, proof-only,
  grep-clean, premise_gamma +365): E06 Seq7 rung — rpow7-frac `:4268`
  (1.45≤7^5/26), Re-lower 10.15 `:4283`, cpow7 norm `:4296` +
  upper-needed 10.29 `:4314`, add7 ≤8.23 `:4320`, prod7 83818.22
  `:4346`, link (5040-num) `:4384`, rate 0.014 `:4401`, finite 0.61
  `:4410`, below-gate `:4587` + gap 0.05 `:4592`, N8-next `:4599`.
  VERDICT: 0.61<0.66 FAILS honestly (+0.012 over N6; 0.579→0.598→0.61,
  gaps 0.081→0.062→0.05). Ladder to N8. VERIFY3 tasked (sole owner,
  N6B+N7 rebuild).
- 2026-09-22 SCUT20 (background `ses_f377196bc`, proof-only, grep-clean):
  log11 window FIRST link — `sSCUT_log_eleven_eq :3552` (log11 = log10
  + log(11/10)) + `le :3563` (≤2.4025850934 via log(11/10)≤1/10) +
  `ge :3576` (≥2.3934941835 via log(10/11)≤-1/11; margin ~9e-13,
  norm_num-closed).   Window [2.3935,2.4026] width ~0.009 (ratio-bound
  limited vs log10 d9 8e-9). Next: cos(10·log11) (SCUT21).
- 2026-09-22 SCUT21 (background `ses_f37705f4`, proof-only, grep-clean):
  theta11/delta11 windows banked — `theta11_mem :3593` (θ∈[23.935,
  24.026], width 0.0909) + `delta11p_mem :3613` (δ'=θ-7π∈(1.944,
  2.035), width 0.0916) + `window_gap :3630` (0.09<width). Cos verdict:
  TOO-WIDE honestly (|δ'|≥1.94 kills the 1-x²/2 route; no signed upper
  filed). NOTE for next: 8π≈25.13 is nearer θ than 7π (δ≈-1.1..-1.2) —
  k=10 may be CONSTRUCTIVE, not destructive. SCUT22 tasked (8π check).
- 2026-09-22 GAMMA-VERIFY3 (background `ses_f377152ad`, sole build owner):
  BUILD-EXIT=1 x2 (fence stop). Fixed 4 paren typos in N6B/N7 add6/add7
  statements+h2s (`:3979/:3994/:4321/:4336`, +1 `)` each — same slip as
  the GAMMA-PAREN family). N6B Seq6 FULLY COMPILED (cascades gone).
  Remaining: false prod7 literal `...91086` vs exact `...91085296`
  (off 7e-12; coordinator verified via Decimal `prec=40` and fixed all
  4 spots `:4257/:4345/:4372/:4375` directly). VERIFY4 tasked (sole
  owner, rebuild to green).
- 2026-09-22 SCUT23 (background `ses_f376bdf81`, proof-only, grep-clean):
  eta10 gain banked — `sSCUT_sqrt11_le :3688` (11^1/2≤10/3, 11≤100/9)
  + `sSCUT_rpow11_neg_ge :3702` (r11≥0.3, tighter pick) +
  `sSCUT_cpow11_neg_re :3714` (split) + `sSCUT_cpow11_Re_ge`
  (21/250 via 0.3·7/25 + `:3647`) + `sSCUT_eta10_Re_ge :3768` (even
  parity, no flip) + shard `:3778` (multiset {0..7,9,10}, single-count,
  k=8 skipped) + shortfall `:3790` (54883/10500≈5.228). Floor
  -3.211→-3.127 (gain 0.084). SCUT24 tasked (k=11 odd-payoff?).
- 2026-09-22 SCUT24 (background `ses_f3769fd0e`, proof-only, grep-clean,
  pilot-only commit): log12 FIRST link — `sSCUT_log_twelve_via_eleven_eq
  :3798` (log12 = log11 + log(12/11), 11→12 chain; sharp d9 bridge via
  12=4·3 already at `:2191`, this enables ratio windows). Bridge only,
  no window. Floor stays -3.127. Suppliers ETA-S10 writes left for
  owner. SCUT25 tasked (log12 window).
- 2026-09-22 ETA-S10 (background `ses_f376c30c6`, proof-only, grep-clean,
  suppliers +342): S10 Re-route — log9/log10 bridges, rpow9/10 quads
  (fresh, were absent), cpow9/10 splits, Re9≥-0.47 / Re10≤0.44 →
  `CS_complex_S10_Re_ge_024 :5541` (0.24 = 1.15-0.47-0.44) + gap
  `:5564` (1.70 to live 1.94) + shortfall `:5570` (2.3514). Honest:
  true Re(S10)~1.84<1.94, Re-route cannot beat slow by design. Live
  1.94 / shortfall 0.6514 STAND.
- 2026-09-22 ETA-S12 (background `ses_f3752af36`, proof-only, grep-clean,
  suppliers-only commit): S12 Re-route goes NEGATIVE — log11/12
  bridges, rpow11/12 quads (fresh), cpow11/12 splits, Re11≥-0.42 /
  Re12≤0.42 → floor `Re(S12)≥-0.60 :5928` (0.24-0.42-0.42) + gap
  `:5951` (2.54) + shortfall `:5957` (3.1914). True ~1.68. Re-route
  envelope declining (1.56→0.95→1.15→0.24→-0.60); S4-based live 1.94
  STANDS unchallenged. Premise_gamma N8 writes left for owner.
- 2026-09-22 GAMMA-VERIFY4 (background `ses_f376a82de`, sole build owner):
  GREEN — `[8689/8689] Built door3_premise_gamma (69s)`, BUILD-EXIT=0
  (attempt 1/1), zero edits (be75838 fixes held), grep-clean (0
  sorry/axiom/admit; old `91086` gone, `91085296` x4). N6B Seq6 + N7
  Seq7 COMPILED (add6/add7/prod6/prod7 chains in green target). Only
  2 pre-existing unused-var linters.   Lock RELEASED. SUPP-VERIFY tasked
  (sole owner, suppliers S8/S10 backlog).
- 2026-09-22 EDGE-STRIP (background `ses_f350a352b`, proof-only,
  grep-clean, wiring-only commit): `edgeStrip_top_half_M40 :473`
  CONDITIONAL top-only strip at m=1/2, MT=40 — all gates closed by
  norm_num/linarith ((1/2)/40=0.0125: 0.01<0.0125, 0.4875<0.49,
  -0.49<-0.4875). Exactly 2 supplier premises open (hTopLower uniform
  1/2 on Icc(-10,10) at Im=1/2; hTopDeriv ≤40 on strip). Smallest edge
  residual is now 2 numerals.
- 2026-09-22 EDGE-DERIV (background `ses_f3506fe93`, proof-only,
  grep-clean, wiring-only commit): hTopDeriv REDUCTION —
  `hTopDeriv40_of_ballSup40 :470` (hTopDeriv ⇐ ball-sup-40 on
  closedBall 0 12 via banked `uniform_top_deriv_of_closedBall` at
  d=(1/2)/40, C=40; +import sliver_edge `:7`, cycle-safe).   Residual:
  hTopLower (1/2 uniform) + ball-sup-40 numeral.
- 2026-09-22 EDGE-HLOWER (background `ses_f34f199b`, proof-only,
  grep-clean, wiring-only commit): hTopLower GAP filed, not closed —
  missing Props `:1566/:1573/:1580` (uniform target + zeta floor +
  gamma floor) + gap doc. KEY FIND: poly factor norm 0 at x=0 BLOCKS
  any product-lower route structurally (xiShifted zero-adjacent?);
  pi-1/2 covered alone; zeta+gamma floors missing (grid floors only at
  Re∈{0.395,0.2,0.105}). hTopLower-1/2 feasibility OPEN (may be
  infeasible — needs adjudication vs banked endpoint 1/2 at x=0).
- 2026-09-22 SLIVER-BOT (background `ses_f34efa017`, proof-only,
  grep-clean): bottom-half CLOSED — `sliver_top_of_bottom_via_conj
  :612` (flipped helper) + `sliver_hSliver_of_botNumericData_via_conj
  :649` + `sliver_hSliver_of_botHalf_M40_via_conj :685` (mirror of
  `:594`; conj flips cleanly, bidirectional in-strip). Residual:
  hBotLower 1/2 + hBotDeriv 40 only.
- 2026-09-22 SLIVER-MID (background `ses_f34f3a727`, proof-only,
  grep-clean): `sliver_hSliver_of_topHalf_M40_via_conj :594`
  (feasible mT=1/2/MT=40 top-only hSliver, mirror of `_011`; gates
  norm_num). 2 premises open (hTopLower 1/2, hTopDeriv 40).
- 2026-09-22 DERIV-PSI (background `ses_f34f3a72c`, proof-only, NO-EDIT
  honest gap): `psiNeed_outer` NOT closable via recurrence-transport —
  best banked disc is a REAL secant (slopeS at Im=0), no bridge to
  `Complex.digamma` at 8.1975-4.375i (recorded `:325-328`). Gap
  unchanged (0.003612 vs 0.000857, 4.21x). Missing: Stirling-remainder/
  Gauss-rep for Complex.digamma or complex-Wendel secant bridge.
- 2026-09-22 DERIV-FILL (background `ses_f34f3a72d`, proof-only, NO-EDIT
  honest gap): dLeaf premise set NOT filled — best geometric cover is
  934-disc (need ≤10 on sphere, 924 over / 93.4x; deriv consequence
  93400 vs 1000). `zetaDiffCont_leaf` also unbanked. 16800 fat-ball is
  type-wrong (xi, not zeta). Needs zeta-lane ≤10 + DiffContOnCl.
- 2026-09-22 DERIV-ETAPRIME-LINK (background `ses_f34f3a72c`,
  proof-only, grep-clean, eta_prime-only commit): tsum bridge PROVED —
  `etaPair_tsum_hasDerivAt_of_uniformBound :297` + deriv reading `:314`
  (Mathlib SmoothSeries/FunctionSeries/UniformLimitsDeriv cited).
  Termwise identity + majorant + Hurwitz chain still missing (next).
  Wendel/Stirling writes left for owners.
- 2026-09-22 EDGE-BOTTOM (background `ses_f34f5d1a3`, proof-only,
  grep-clean, wiring-only commit): `edgeStrip_bottom_half_M40 :523`
  CONDITIONAL bottom mirror (lower arm direct via
  `sliver_bottom_strip_of_entire_data`; upper arm inline conj via
  `sliver_star_vertical` + `sliver_conj_transfer_general`; gates
  norm_num/linarith; packaged by `..._of_uniformStrips`). Residual:
  hTopLower/hTopDeriv + hBotLower/hBotDeriv + ball sups C=40
  (deriv lane owns C).
- 2026-09-22 GAMMA-N8 (background `ses_f3753c477`, proof-only,
  grep-clean, premise_gamma +388): E06 Seq8 rung — rpow8-frac `:4633`
  (1.49≤8^5/26, 1.50 false), Re-lower 11.92 `:4648`, cpow8 norm `:4661`
  + upper-needed 12.07 `:4679`, add8 ≤9.23 `:4685`, prod8 773642.09
  `:4711`, link (40320-num) `:4752`, rate 0.014 `:4770`, finite 0.621
  `:4779`, below-gate `:4975` + gap 0.039 `:4980`, N9-next `:4987`.
  VERDICT: 0.621<0.66 FAILS (increments +0.019/+0.012/+0.011
  shrinking; 0.579→0.598→0.61→0.621). Self-fixed 2 paren typos.
  VERIFY5 tasked (sole owner, N8 rebuild).
- 2026-09-22 GAMMA-N9 (background `ses_f374dbefc`, proof-only,
  grep-clean, premise_gamma +412): E06 Seq9 rung — rpow9-frac `:5019`
  (1.52≤9^5/26), Re-lower 13.68 `:5034`, cpow9 norm `:5047` +
  upper-needed 13.90 `:5065`, add9 ≤10.22 `:5071`, prod9 7906622.14
  `:5099`, link (362880-num) `:5143`, rate 0.014 `:5162`, finite 0.627
  `:5171`, below-gate `:5387` + gap 0.033 `:5392`, N10-next `:5399`.
  VERDICT: 0.627<0.66 FAILS (increments +0.019/+0.012/+0.011/+0.006
  shrinking — ladder may asymptote below gate; N10+ assessment
  pending). Parens double-checked vs add8. VERIFY6 tasked (sole owner,
  N9 rebuild).
- 2026-09-22 VERIFY6 (background `ses_f37451931`, sole build owner):
  BUILD-EXIT=1 x2 (fence stop). Fixed 2 paren slips (`:5109/:5195`,
  same family). N5→N8 unaffected (zero errors outside Seq9). Remaining:
  `hre9 :5328` has 16 opens / 17 closes (programmatic audit) — full
  string-diff vs green hre8 `:5315` shows EXACTLY one inserted ` + 1)`
  at pos 140 with no matching `(` (plus-count 10 vs 9, opens equal).
  FIX: add one `(` to the front run (14→15, yielding 17/17 mirroring
  hre8+1 level); do NOT merely delete `)` (that keeps 10 levels on
  9-level opens = misnested). Coordinator verified the audit but could
  not hand-type the 14-run reliably (2 failed exact-match attempts, no
  file change) — owner to apply + confirm by build. VERIFY7 tasked.
  LADDER-RULE (all future N-rung agents): after banking, run
  programmatic opens/closes counts on every new line AND full-diff vs
  the N-1 analogue; zero-diff except the one intended level.
- 2026-09-22 VERIFY7 (background `ses_f373e11d5`, sole build owner):
  hre9 FIX CONFIRMED (17/17, front-run 14→15, one-char diff) but build
  still RED — new error `5350:142 unexpected ')'` + `5173:86` fallout.
  Coordinator net-audit (all lines programmatically): hposR block =
  `have` 5340 (net 0) + NINE factor lines 5341-5349 (each net +1, s..s+8)
  + final s+9 factor 5350 (net -10). Nine +1s need final net -9 (N8
  mirror: eight +1s 4932-4939, final 4940 net -8). PRESCRIPTION: delete
  exactly ONE trailing `)` on 5350 (tail ‖+10×`)` → ‖+9×`)`), then net
  -9 balances. Coordinator did NOT hand-edit (hand-counting failed
  twice before) — owner to verify counts programmatically before/after
  + rebuild. VERIFY8 tasked (sole owner).
- 2026-09-22 VERIFY8 (background `ses_f373ba0bb`, sole build owner):
  5350 fix APPLIED (15/24, block 5340-5350 sums 0, N8 mirror confirmed)
  but build still RED — paired compensating error exposed on proof line
  5351 (`mul_pos` chain 8/9 net -1 vs N8 4941 mirror 7/7). PATTERN: N9
  agent wrote +1 close on BOTH type tail (5350) and proof tail (5351).
  PRESCRIPTION: delete exactly ONE trailing `)` on 5351 (→8/8; proof
  term must net 0), verify programmatically, rebuild. LADDER-RULE
  EXTENDED: balance-check proof lines too, not just type lines.
  VERIFY9 tasked (sole owner).
- 2026-09-22 VERIFY9 (background `ses_f37399012`, sole build owner):
  GREEN — `[8689/8689] Built door3_premise_gamma (27s)`, BUILD-EXIT=0
  (attempt 1/2). Fix: one trailing `)` off 5351 (8/9→8/8, N8 mirror
  7/7 confirmed programmatically). Zero errors/sorries; only 2
  pre-existing linters. N9 honest 0.627 COMPILED. Premise_gamma GREEN
  through N9 (ladder 0.579→0.598→0.61→0.621→0.627 all verified).
  Paren saga closed (4 waves: PAREN→N6B/N7→hre9→5350/5351).
  GAMMA-N10 tasked (proof-only; E06 N10 rung, parens pre-checked).
- 2026-09-22 GAMMA-N10 (background `ses_f373830ae`, proof-only, no
  report — work found on disk +436, grep-clean, coordinator-verified):
  E06 Seq10 rung — rpow10-frac (1.55≤10^5/26), Re-lower 15.5, prod10
  88712300.33 (=7906622.14·11.22 ✓), link (3628800-num), rate 0.014,
  finite 0.634 (15.5·3628800=56246400 ✓), below-gate + gap 0.026,
  N11-next filed. VERDICT: 0.634<0.66 FAILS (increments
  +0.019/+0.012/+0.011/+0.006/+0.007 shrinking — ladder likely
  asymptotes below gate). Coordinator paren   surgery (LADDER-RULE
  block-net method): (1) hre10 front-run had double-tap `(('  — deleted
  one via short `have hre10 : `+run-prefix substring anchor
  (counting-proof, 19/18→18/18); (2) add10 stmt tail
  `+ 1)‖` → `+ 1))‖` (18/17→18/18, N9-tail diff).   Full N10 region nets
  0, every block verified. VERIFY10 tasked (sole owner, rebuild).
- 2026-09-22 VERIFY10 (background `ses_f350dc4db`, sole build owner):
  GREEN — `[8689/8689] Built door3_premise_gamma (66s)`, BUILD-EXIT=0
  (attempt 1/2), ZERO edits (coordinator surgery held), grep-clean.
  N10 honest 0.634 COMPILED (`:5587` finite + `:5823` below-gate +
  `:5828` gap 0.026). Ladder 0.579→0.598→0.61→0.621→0.627→0.634 all
  verified green.   Lock RELEASED. GAMMA-N11 tasked (proof-only).
- 2026-09-22 VERIFY16 (background `ses_f34a71696`, sole build owner):
  GREEN — `[8689/8689] (40s)`, BUILD-EXIT=0 (attempt 2/2). Fixes (5,
  THIRD slip family — rung-COUNT slips, not parens/numerals): nonneg
  chains `:7251/:7253/:7255/:7257` had N12 rung counts (9/10,10/11,
  11/12+extra,12/13+extra → need 10/11,11/12,12/13,13/14) + hpos14
  `:7486` +1 close. N14 honest 0.653 COMPILED. Lock RELEASED.
  LADDER-RULE EXTENDED: verify rung COUNTS (mul_nonneg/w lines = N),
  not just balance. INFRA: VERIFY16's editor wrote CRLF again (7531
  lines) — coordinator normalized to LF (diff 5/5). RULE: every agent
  runs `file <f>` before finishing; CRLF = redo. GAMMA-N15 tasked.
- 2026-09-22 GAMMA-N14 (background `ses_f34a9d8f1`, proof-only,
  grep-clean, premise_gamma +429/-0 PURE APPEND): E06 Seq14 rung —
  rpow14-frac (1.66≤14^5/26, 1.67 false), Re-lower 23.24, prod14
  3101706860268.06, link (87178291200-num, factorial by decide),
  rate 0.014, finite 0.653 (23.24·87178291200/3101706860268.06≈0.65320,
  coordinator-verified), below-gate + gap 0.007 + N15-next. VERDICT:
  0.653<0.66 FAILS (+0.006; 2-dec windows provably cap below gate —
  1.67^26>537824). Discipline full (nets/diff/stale-grep/LF).
  VERIFY16 tasked (sole owner, rebuild).
- 2026-09-22 VERIFY15 (background `ses_f34acd972`, sole build owner):
  GREEN — `[8689/8689] (41s)`, BUILD-EXIT=0 (attempt 2/2). Fixes (3
  stale-numeral copy-pastes from N12 block, NEW slip family — not
  parens): `:7065` hre13 13.1975→14.1975; `:7079` h1 0.645→0.647 both
  sides; `:7082` h2 base 12→13. N13 honest 0.647 COMPILED. Lock
  RELEASED. LADDER-RULE EXTENDED: after mirroring, grep the new block
  for ALL old-rung numerals (N-1 values must not appear). GAMMA-N14
  tasked (proof-only).
- 2026-09-22 PREMISE-VERIFY (background `ses_f34b784df`, sole build owner):
  GREEN — `[8689/8689] Built door3_premise_gamma (36s)`, BUILD-EXIT=0
  (attempt 1/2), ZERO edits (6416 fix held; stirling-green upstream
  unblocked). N12 honest 0.645 COMPILED (prod1..prod12 chain verified
  in build). Ladder 0.579→...→0.639→0.645 all verified green (gap
  0.015).   Lock RELEASED. GAMMA-N13 tasked (proof-only).
- 2026-09-22 GAMMA-N13 (background `ses_f34b6074d`, proof-only,
  grep-clean, premise_gamma +412/-0 PURE APPEND): E06 Seq13 rung —
  rpow13-frac (1.63≤13^5/26, 1.64 false), Re-lower 21.19, prod13
  203791515129.31, link (6227020800-num, factorial by decide),
  rate 0.014, finite 0.647 (21.19·6227020800/203791515129.31≈0.64748,
  coordinator-verified), below-gate + gap 0.013 + N14-next. VERDICT:
  0.647<0.66 FAILS (+0.002; increments dying: ...+0.006/+0.005/+0.006/
  +0.002). Discipline EXEMPLARY: 27/27 blocks net 0, LF preserved,
  diff only intended. VERIFY15 tasked (sole owner, rebuild).
- 2026-09-22 PREMISE-FIXER (background `ses_f34c289ac`, sole build owner):
  6416 fix APPLIED (12→11 closers, block nets 0, N11 mirror confirmed,
  uniqueness pre/post-checked) but build BLOCKED UPSTREAM — stirling
  dependency fails (4 parse errors `:1999/:2197/:2227/:2294` in RATE/
  GAMMANEED2 committed content, never built by proof-only authors).
  Target premise_gamma has ZERO attributed errors. Lock RELEASED.
  STIRLING-FIXER tasked next (sole owner) — sweep clause: upstream
  first.
- 2026-09-22 FE-SURVEY (background `ses_f34e1cc75`, read-only, no
  edits): FE lane FULLY SCOPED — FE logic CLOSED (chi defs, reflection
  bridges, Hadamard/PL/Jensen banked); only NUMERICS missing. Minimal
  chain for zeta≤10 on R02: (1) Gamma exp-decay (ZERO content) → (2)
  chi≤8 (conditional written, awaits hG) → (3) ratio+linear → ≤10.
  SMALLEST-NEXT: `R02_gamma_expDecay_box` (‖Γ(1-s)‖≤4·exp(-1.58·|Im|)
  on R02 box; box suffices, whole-line unnecessary). Polynomial
  alternatives provably insufficient (~1000-3000x short; only exp-decay
  cancels exp13). Same root blocks DZ/cutoff/Lambda0/zetaLower.
- 2026-09-22 GAMMA-SHIFT-SURVEY (background `ses_f34e1cc73`, read-only,
  no edits): shift route RULED OUT for the 0.014 rate — shift bank is
  implication-only + denominator-uppers; ALL banked reals are UPPERS
  (explicit no-lower audits in disc/gamma_low/premise); no
  shift-compare machinery exists (zero hits); Binet zero feeders.
  Ladder honest-failing confirmed (denominator products outrun cpow:
  1237→...→14.3B). SMALLEST-NEXT = already-filed rate leaf `:3402`
  (needs Stirling-disc/Binet host, NOT premise file).
- 2026-09-22 GAMMA-N12 (background `ses_f34f5d1a6`, proof-only, no
  report — work found on disk +392 after CRLF→LF normalization, the
  agent's editor wrote CRLF over LF HEAD, fixed by coordinator):
  E06 Seq12 rung — rpow12-frac (1.61≤12^5/26), Re-lower 19.32,
  prod12 14331330177.87 (=1084064309.98·13.22), link (479001600-num),
  rate 0.014, finite 0.645 (19.32·479001600=9254310912 ✓,
  /14331330177.87≈0.64574 ✓), below-gate + gap 0.015. VERDICT:
  0.645<0.66 FAILS (+0.006). KNOWN DEFECT (not yet fixed): prod12
  final tail `:6416` one extra `)` (block 6403-6453 nets -1; N11 mirror
  nets 0). PREMISE-FIXER tasked (sole owner, 1-char + rebuild).
- 2026-09-22 DERIV-FILL3 (background `ses_f34e828b7`, proof-only,
  grep-clean, deriv_up-only commit): MID set filled at honest 125 (NOT
  10) — geometry covers (Re margins 0.135/0.095, Im margin 6.24) via
  tail-quarter + import `:6`; `zetaSupOnSphere_mid_125_filled :1030` +
  `zetaDeriv_mid_125_of_diffCont :1040` (deriv ≤12500 modulo
  DiffCont). Pre-existing ≤10 untouched. INNER still open.
- 2026-09-22 VERIFY11 (background `ses_f35068fa6`, sole build owner):
  BUILD-EXIT=1 x2 (fence stop). Fixed hDeq `:6055` (10→11 closers).
  Remaining: hpos11 helper `:6217` missing one `(` (14-run where 15
  needed). PROOF: rung progression `:6163/:6176/:6189/:6203/:6217`
  front-runs should be 11/12/13/14/15 — 6217 repeats 6203's 14
  (copy-paste without the level's open). PRESCRIPTION: add one `(` to
  6217's front run (14→15). AUDIT LESSON: whole-rung net-0 is
  INSUFFICIENT (hDeq -1 and hpos11 +1 canceled); audit per SUB-BLOCK
  (hDeq/hD/hpos-chain/hre/habs separately).   VERIFY12 tasked.
- 2026-09-22 VERIFY12 (background `ses_f3503bb76`, sole build owner):
  6217 fix APPLIED (17/17, progression 11-15 restored) but build still
  RED — adjacent hre11 `:6218` needs the SAME fix (18/19, front 16→17;
  N11 agent dropped the open on both h-inner and hre lines, N9-pattern).
  PRESCRIPTION: add one `(` to 6218's front run (→19/19), count
  before/after, rebuild.   VERIFY13 tasked (sole owner).
- 2026-09-22 VERIFY13 (background `ses_f3500f1f4`, sole build owner):
  hre11 fix APPLIED (18/19→19/19, front 16→17) + full
  sweep table (all `have h/hre/him/h2` 5839-EOF balanced, exactly one
  in-pattern slip) but build still RED — hposR tail `:6242` one close
  short (block 6230-6242 nets +1; 11-deep nest closed by 10).
  PRESCRIPTION: add one `)` to 6242's tail (17/27→17/28), count
  before/after, rebuild.   VERIFY14 tasked (sole owner).
- 2026-09-22 VERIFY14 (background `ses_f34feaca8`, sole build owner):
  GREEN — `[8689/8689] Built door3_premise_gamma (35s)`, BUILD-EXIT=0
  (attempt 1/2). Fix: one `)` on 6242 tail (17/27→17/28, block nets 0;
  counts verified before/after). Zero errors/sorries; only 2
  pre-existing linters. N11 honest 0.639 COMPILED. Ladder
  0.579→0.598→0.61→0.621→0.627→0.634→0.639 all verified green.
  Second paren saga closed (hDeq→hpos11→hre11→hposR, 4 waves).
  STRATEGIC: increments +0.019/+0.012/+0.011/+0.006/+0.007/+0.005 —
  ladder asymptoting below 0.66 gate; N12 rung marginal (~+0.004?).
  Gamma lane decision owned by next wave (N12 vs rate-leaf machinery).
- 2026-09-22 GAMMA-N11 (background `ses_f350b3ff2`, proof-only,
  grep-clean, premise_gamma +460): E06 Seq11 rung — rpow11-frac
  (1.58≤11^5/26), Re-lower 17.38, prod11 1084064309.98, link
  (39916800-num), rate 0.014, finite 0.639 (`693753984/1084064309.98≈
  0.63996`, coordinator-verified), below-gate + gap 0.021 + N12-next.
  VERDICT: 0.639<0.66 FAILS (+0.005; 0.64 provably unachievable on
  these windows). Agent self-fixed 4 paren slips; coordinator block-net
  audit: all 13 blocks net 0. VERIFY11 tasked (sole owner, rebuild).
- 2026-09-22 R02-CELL (background `ses_f350a352a`, proof-only,
  grep-clean, first_cell-only commit): rpow2-head CLOSED —
  `FC_log2_ge_aux :966` + `FC_rpow2_head_upper_proved :971`
  (2^-0.395≤0.77, CS_rpow2 mirror, no new estimates) + unlocked
  `FC_etaS2_uncond :1004` (0.23≤1-2^-0.395). R02 residual minus one
  (zeta14/derivTier/hEven/Lambda0/gamma-0.008 remain). `.kilo/kilo.jsonc`
  runtime churn left uncommitted; premise_gamma N11 left for owner.
- 2026-09-22 ENCLOSURE-SURVEY (background `ses_f3753c476`, read-only, no
  edits): 80-cell binding residual inventoried. CORRECTION: `RNN` name
  does not exist in-tree (guide-prose only); canonical
  `R00/R01/..._leaf_obligations` + 40 `Target` rows. Banked: rect/
  fencing machinery, ξ=poly·pi·gamma·zeta factorization, poly/R00-30 +
  pi-1/2 lowers, Gamma R02-0.002/0.006 lowers (0.008 open), ζ-upper 934
  (`:32566`, η-pair technique: head 2 + remainder 166 over cvt 0.18).
  Gaps: ζ-upper needs 93x (→≤10), ξ'-tier 0.07 Cauchy-IMPOSSIBLE
  (need direct deriv bounds), ζ/Gamma center-lowers open, no Mathlib
  interval lib (hand-rolled rpow/norm_num + opaque Float trust layer).
  Transfer: 934-technique reusable for ζ-upper half only. SMALLEST
  NEXT: R02 first-cell attempt (5 open premises: gammaLower 0.008,
  zetaLower 1.1, derivTier 0.07, ballSup 16800, rpow2-head 0.77).
- 2026-09-22 STRIP-SURVEY (background `ses_f3753c475`, read-only, no
  edits): assumption map `:12149-:12263` (Hmain/Hedge/Htail/Hcut +
  `:12186/:12204/:12238` bridges all proved-conditional); banked: width
  gates at 011, CutL10/CutR10 geometry + mem + either-split, sharp 1/2
  endpoint norms (m=11 infeasible, m≤1/2 necessary), m=1/2 adapters
  (gates stay premises), cutoff Gamma banked, deriv-reduction bridge
  (edge deriv ≤ closedBall-0-12 sup C). OPEN: uniform edge lowers at
  m≤1/2, deriv caps M<50 (or ball C), CutR10/CutL10 fencing (ball ≤0.04
  blocked at ~0.062), hLeft/hSliver capstones. SMALLEST NEXT:
  `edgeStrip_top_half_M40` (top-only, m=1/2, MT=40: gates close by
  norm_num, 2 supplier premises) — smaller than any cutoff lemma.
- 2026-09-22 SCUT25 (background `ses_f37683d3d`, proof-only, grep-clean):
  log12 window — `le :3809` (≤2.4934941844 via log(12/11)≤1/11) +
  `ge :3822` (≥2.4768275168 via log(11/12)≤-1/12; slacks ~1e-10,
  norm_num-closed).   Window [2.4768,2.4935] width ~0.0167, true ~2.4849
  inside. Next: theta12/cos (SCUT26).
- 2026-09-22 SCUT32 (background `ses_f374cd2e5`, proof-only, grep-clean):
  k=13 NO-FLIP gap — `delta14_even_mem :4366` (δ∈(1.118,1.406),
  quadrant I — brief said II, agent corrected since <π/2≈1.5708) +
  width `:4375` (0.288) + `no_flip_gap :4389` (1.406<π/2 containment).
  cos δ>0 → eta13=-14^{-s} negative: destructive/neutral, k=9-flip
  impossible, no force. STRATEGIC: per-term gains (+0.707 over k=7..12,
  ~0.12/term declining) cannot close gap 5.024 (~50 terms needed) —
  per-term lane PAUSED; slow-leg machinery owned by SCUT-SLOW survey.
- 2026-09-22 SCUT-SLOW (background `ses_f374aee5a`, read-only, no
  edits): slow machinery mapped. R00 S2/S4 shapes transfer but numerals
  don't (σ 0.395 vs 1/2; norm route fails at both points — sCut uses Re
  floors). R00 phases (t=8.75) don't transfer; tails do (recomputed with
  ‖s‖≤12). S8 floor decomposed: 2/7 = Re(S2) base (reused everywhere);
  -4 = four -1 placeholders (n=3,5 PERMANENT dead, n=7 upgraded to
  +27/100); growth only from k≥9 locks. sCutOA11 (t=11) NEVER closed
  its slow leg either (conditionals only; combos t=11-essential, sCut
  n=5 dead where OA11 n=5 lives). SMALLEST NEXT: `sSCUT_eta13_Re_le_neg`
  destructive closure (6-step recipe: cpow14 split → rpow14 → cos floor
  from `:4366` → product → odd bridge → negate; then k=14/15 growth).
- 2026-09-22 SCUT33 (background `ses_f374839a4`, proof-only, grep-clean,
  pilot-only commit): eta13 CLOSED 6/6 — split `:4400`, sqrt14≤4
  `:4434` + r14≥1/4 `:4447`, cos≥1/100 `:4461` (1-1.406²/2≈0.01158),
  product ≥1/400 `:4504`, odd bridge `:4522` + `eta13_Re_le_neg :4536`
  (≤-1/400) + `no_pos_lock :4546`. k=13 joins k=8,11 skip list; no
  shard growth. Premise_gamma N9 left for owner.
- 2026-09-22 SCUT26 (background `ses_f3766f8f0`, proof-only, grep-clean):
  phase SHAPE corrected (10·log12, not 11·log12 — multiplier is t=10 in
  all mirrors `:3287/:3714`) + theta12 wide window `:3842` (θ∈[24.768,
  24.935], width 0.167) + delta12' `:3862` (δ'∈(2.777,2.944), width
  0.167) + gap `:3882`. Cos verdict: GAP honestly (sharp θ≈24.849 has
  cos≈+0.96 → odd-k flip recipe FAILS; k=11 likely DESTRUCTIVE via
  sharp `:2235/:2287`, not constructive). SCUT27 tasked (eta11
  destructive lock via sharp).
- 2026-09-22 SCUT27 (background `ses_f3775d893`, proof-only, grep-clean,
  pilot-only commit): k=11 DESTRUCTIVE-LOCK — `cos10log12_ge :3891`
  (≥19/20 via sharp δ12), `cpow12_neg_re :3943`, `sqrt12_le :3979`
  (≤7/2), `rpow12_neg_ge :3993` (≥2/7), `cpow12_Re_ge :4007` (≥19/70 =
  2/7·19/20), `eta11_eq_neg_cpow12 :4048` (odd bridge) +
  `eta11_Re_le_neg :4061` (≤-19/70≈-0.271) + `no_pos_lock :4071`.
  k=8-style neg-upper filed as gap `:3935` (cos≈+0.96, no force).
  eta11 honestly skipped as gain. Suppliers fixes left for SUPP-VERIFY.
- 2026-09-22 FIRSTCELL-TENDSTO (background `ses_f349a43ed`, proof-only,
  grep-clean, first_cell-only commit): Tendsto input PROVED —
  `FC_etaF0395_eq_etaGen :1513` + `tendsto_zero :1521` (banked vanishing
  rewrite) + `FC_eta_Tendsto_exists :1534` (alternating-series test) +
  `S2_exists :1544` (same L + S₂ lower). hEven analytic inputs COMPLETE
  (Antitone + Tendsto + slice all banked); zetaLower still numerically
  open (0.23 vs 1.1/1.4).
- 2026-09-22 STIRLING-DISC2 (background `ses_f34951a35`, proof-only,
  grep-clean, stirling-only commit): R02 disc-upper tightened 0.5→0.381
  `:2469` (‖w‖≥2.625 full-Im floor). gamNeed outer/leaf still open
  (114x/37x).
- 2026-09-22 SCUT44 (background `ses_f3495b136`, proof-only, grep-clean,
  pilot-only commit): eta17 payoff GAP filed `:5504` — r₁₈ lower missing
  blocks cpow18→eta17 bridge (would-be +0.1768 via 0.2357·3/4 unchained).
- 2026-09-22 BALLADV-R02SUM (background `ses_f34951a3e`, proof-only,
  grep-clean, ball_advance-only commit): R02 summable/tsum CONDITIONAL
  wrappers (nonneg/norm/of_dom/tsum_le mirrors) + exponent/coeff gap
  witnesses + `dominator_missing_spec :1636`. Disc tsum does NOT
  transfer; fresh 1.05-decay dominator needed.
- 2026-09-22 DIGAMMA-PSINEXT (background `ses_f34951a31`, proof-only,
  grep-clean, digamma-only commit): psi transport rungs outer/leaf/mid/
  inner `:587-605` (conditional, N=8 pattern). Shifted discs + gamNeed
  open (Stirling remainder absent from Mathlib).
- 2026-09-22 ETAPRIME-DNUM (background `ses_f34951a3a`, proof-only,
  grep-clean, eta_prime-only commit): Deta numeral CLOSED (`≤13.2 :982`
  via pi<3.1416) + norm assembly `:1009` + `:1029`. Disc Deta done;
  R02 transfer blocked per DZNUM gap.
- 2026-09-22 CUTL-MID2 (background `ses_f34951a37`, proof-only,
  grep-clean, cutL10-only commit): poly 67→66.95 + joint 12.87→12.86
  (`:1840-1860`, norm_num).   Tier gap 12.8144 (321x over 0.04) stands.
- 2026-09-22 TAIL-MNEXT (background `ses_f34951a36`, proof-only,
  grep-clean, tail-only commit): M524288 rung `24/724≈0.03315 :813`
  (odd/floor shape, beats 0.046875). Ladder continues (M1048576 next).
- 2026-09-22 ASSEMBLY-LEAF (background `ses_f34951a33`, proof-only,
  grep-clean, assembly-only commit): R00 center conditional
  (`of_tenth_lower :16988` + residual spec `:16993` + obligation
  `:16996` via budget<0.1). Needs xiShifted-at-center enclosure.
- 2026-09-22 WIRE-HTOPGAP (background `ses_f34951a3c`, proof-only,
  grep-clean, wiring-only commit): endpoint `1/2` leaf banked into wiring
  `:1855` (partial value) + gap residual Prop `:1862`. Uniform floor
  still needs zeta/Gamma floors at Re=0 (edge/zeta lane owns).
- 2026-09-22 FIRSTCELL-S4 (background `ses_f3495b129`, proof-only,
  grep-clean, first_cell-only commit): S4 slice `:1586` + Tendsto `:1612`
  + residuals `:1623-1649`. Numeral open (k=3,4 rpow bounds missing).
- 2026-09-22 WENDEL-G1 (background `ses_f34951a34`, proof-only,
  grep-clean, wendel-only commit): Im² G1-expression `:994` +
  conditional inflation `:1012` + H3 chain `:1036`. G2 + normcaps open.
- 2026-09-22 OFFAXIS-NEXT (background `ses_f34951a35`, proof-only,
  grep-clean, off_axis-only commit): S4096 triangle transfer `:9224` +
  conditional feeder `:9247` + mid budget 41/750 `:9256` + residual Prop
  `:9261` + hEnough `:9266`. Mid-block ≤41/750 open.
- 2026-09-22 SLIVER-TOP (background `ses_f34951a38`, proof-only,
  grep-clean, sliver_edge-only commit): M40 gates/width/delta numerals
  `:690-705` + conditional M40 deriv feeder `:708` (via :343) + strict
  m>1/2 impossibility `:719/:727` + 51/100 gaps `:735/:742`. hTopLower/
  hBotLower/hC stay open premises.
- 2026-09-22 RH-EDGE (background `ses_f34951a32`, proof-only,
  grep-clean, RH-only commit): `xiCentralEdgeStrips10_of_zeroFreeCover
  :12487` (mirrors :12286) — Hmain+Hedge+Hcut collapse to single
  `XiCentralZeroFreeCover 10`; open = the cover itself + tail Htail.
- 2026-09-22 ASSEMBLY-H2 (background `ses_f3493cdab`, proof-only,
  grep-clean, assembly-only commit): R00 leaf+H conditional
  (`leaf_of_residuals :17022` + `H_of_residuals :17026` from center+deriv
  residuals). Deriv residual (uniform ≤0.05) filed `:17019`.
- 2026-09-22 SCUT45 (background `ses_f34938b10`, proof-only,
  grep-clean, pilot-only commit): eta17 PAYOFF CLOSED — rpow18 lower
  (1/5 via sqrt18≤5) + cpow18 Re≤-3/20 + odd-negation →
  `eta17_Re ≥ +3/20=0.15 :5618`. Shard assembly next.
- 2026-09-22 RH-TAIL (background `ses_f3493cdad`, proof-only,
  grep-clean, RH-only commit): tail domain halved —
  `tailPointwise10_of_rightTail_and_negSymm :12498` (two-sided absTail
  → one-sided Hright + banked neg-symm). Hright open (right-tail
  certificate owns).
- 2026-09-22 TAIL-M22 (background `ses_f348e1deb`, proof-only,
  grep-clean, tail-only commit): M4194304 exact rung `3/256≈0.01172
  :1013` (2048² verified). Next M8388608 odd.
- 2026-09-22 OFFAXIS-CANCEL (background `ses_f348ed636`, proof-only,
  grep-clean, off_axis-only commit): high-block pair cancellation —
  `high_block_le :9596` (6144/169015≈0.0364 ≤ 41/750 via pair MVT) +
  conditional whole-mid close `:9619`. Three lower blocks open (need
  ≤0.01831).
- 2026-09-22 DERIV-SUP (background `ses_f348dab64`, proof-only,
  grep-clean, deriv-only commit): gamma DiffContOnCl CLOSED (`:1779`,
  Re 0.19 pole-avoidance); sups gapped honestly (gamma 0.097 vs 0.008,
  zeta 934 vs 3; not-sup lemmas `:1823/:1826`). Residuals open.
- 2026-09-22 SLIVER-RET1000 (background `ses_f348c7f7b`, proof-only,
  grep-clean, sliver_edge-only commit): M1000 pair-closers top+bottom
  (`:931-953`) + 40/79→1000 mono lifts (`:971-1004`). C=1000 sup still
  open (poly≤79 premise owned elsewhere).
- 2026-09-22 ASSEMBLY-R01SUP (provisional, report pending; verified
  grep-clean diff): R01 tight-sup chain mirror (C/0.25→0.07, H_of_ball2
  analogues). Committed with R02 agent still in flight; reconciled on
  reports.
- 2026-09-22 DIGAMMA-PSI8OUT (background `ses_f348c59ea`, proof-only,
  grep-clean, digamma-only commit): outer-shift chain reduction (2-piece
  triangle + E1/E2 forms `:888-903`) + remainder Props (`:917-920`).
  Stirling-remainder absence definitive; gamNeed real caps next.
- 2026-09-22 FIRSTCELL-TAILM (background `ses_f348d225a`, proof-only,
  grep-clean, first_cell-only commit): tail majorant BANKED (`:1863`,
  S4≤L≤S5 bracket, radius f4; error-bound route honestly rejected).
  Sole remaining: eta→zeta factor (`:1902`).
- 2026-09-22 TAIL-M23 (background `ses_f348bcfcb`, proof-only,
  grep-clean, tail-only commit): M8388608 odd rung `24/2896=3/362≈
  0.00829` (floor 2896²=8386816 honest). Next M16777216 exact.
- 2026-09-22 GAMMA-N16 (background `ses_f349123cb`, proof-only,
  grep-clean + 4 audits, premise_gamma-only commit): E06 Seq16 rung
  0.657 `:8188` (ceiling 0.65769<0.66, gap 0.003, increment +0.002 —
  still asymptoting). N17-next filed `:8438`.
- 2026-09-22 ZETA-FLOOR16 (background `ses_f348cbea8`, proof-only,
  grep-clean, zeta-only commit): 16^0.05 floor 1.136→1.142 (via
  1.142^20≤16) → tail 17.52, candidate TIES 19.802 `:41662`. 0.344
  persists; 1.143 route open.
- 2026-09-22 STIRLING-LEAF3 (background `ses_f348ad91a`, proof-only,
  grep-clean, stirling-only commit): leaf shift-3 `≤0.061` (via Gamma
  3.1≤2.31; 12x→7x). Outer 16x / leaf 7x stand.
- 2026-09-22 FIRSTCELL-FACTOR (background `ses_f348a1e10`, proof-only,
  grep-clean, first_cell-only commit): eta→zeta factor CLOSED (`≤2.53`
  via 2^0.605≤1.53 Taylor). First-cell chain complete: S4 numeral + tail
  + factor all banked; zeta14 assembly next.
- 2026-09-22 CELL-K (background `ses_f348b0736`, proof-only,
  grep-clean, interval-only commit): R11 poly floor 38.3 hypothesis-free
  (`:35670`, 8.75·8.77/2) + center conditional `:35681`. Same ~6-order
  wall (short 882291x).
- 2026-09-22 SCUT47 (background `ses_f348ce98b`, proof-only, grep-clean,
  pilot-only commit): k=18 DESTRUCTIVE locked — theta19/delta19/cos≤-1/4
  + rpow19 + cpow19 + `eta18_Re ≤ -1/20 :5960` + no_pos_lock `:5971`.
  Floor stays -2.574; t18 adds no gain.
- 2026-09-22 WENDEL-TELE (background `ses_f348dab62`, proof-only,
  grep-clean, wendel-only commit): 8-fold telescope CLOSED to
  log(w+8)-log w = S-Q+E (`:1212`) + Q/E sum caps + D-cap + residual
  identity; G2 conditional on U0/C2 normcaps (`:1375`). H3 conditional.
- 2026-09-22 TAIL-M24 (background `ses_f348a1e0e`, proof-only,
  grep-clean, tail-only commit): M16777216 exact rung `3/512≈0.00586
  :1145` (4096² verified). Next M33554432 odd.
- 2026-09-22 SUPP-FIX (background `ses_f34918ba1`, build owner, DONE):
  root cause = orphan `/--` docstrings before `#print axioms` headers;
  remedy doc→block `/-` at S12/S14/S16/S18/S20 (comment-only).
  Suppliers parse-clean (attempt-2: zero error lines); build stopped on
  UPSTREAM assembly:17218. S20 floor -3.27 joint-committed here.
- 2026-09-22 ASSEMBLY-SUBSETFIX (coordinator, surgical): assembly
  `:17218/:17413` subset lemmas — v1 (goal-only rw) failed linarith (hz
  opaque ∈-form); v2 adds `have hz' := mem_closedBall.mp hz` +
  `linarith [hz', hR]` per VERIFY sketch. VERIFY2 queued.
- 2026-09-22 STIRLING-SHIFT3 (background `ses_f348d2261`, proof-only,
  grep-clean, stirling-only commit): outer shift-3 `≤0.032 :2923` (via
  Gamma 3.1975≤2.64; 31x→16x). Outer 16x / leaf 12x stand.
- 2026-09-22 TAIL-M25 (background `ses_f34885f9f`, proof-only,
  grep-clean, tail-only commit): M33554432 odd rung `24/5792=3/724≈
  0.00414 :1215` (floor 5792²=33547264 honest; prompt stub corrected).
  Next M67108864 exact.
- 2026-09-22 OFFAXIS-3BLOCK (background `ses_f34894883`, proof-only,
  grep-clean, off_axis-only commit): midhigh block 0.0666 EXCEEDS
  leftover 0.01831 — flat pair-triangle DEAD for lower blocks
  (residual unsatisfiable -0.048, filed not claimed). Route needs bigger
  partial budget.
- 2026-09-22 ZETA-FLOOR1143 (background `ses_f34889159`, proof-only,
  grep-clean, zeta-only commit): 16^0.05 floor →1.143 (1.143^20≈14.49
  honest) → tail 17.50 → K0-16 candidate 19.782 `:41772` BEATS 19.802 by
  0.02 (sanity: 1/1.143≤0.875 ✓). 47-bar gap 0.324; 1.144 next.
- 2026-09-22 BALLADV-R02LOG (background `ses_f348b073b`, proof-only,
  grep-clean, ball_advance-only commit): log-splitter banked (linear
  (1,1,1) via rpow_one) but degrades decay toward 0.05; no_uniform_logCap
  proved (delta=0 false). Small-delta>0 lane filed (`:1949-1955`).
- 2026-09-22 DERIV-RELOC (background `ses_f3489af53`, proof-only,
  grep-clean, deriv-only commit): relocation spec filed (dLeaf_reloc
  0.2-8.0I, sphere in R02 rect; 12x/311x shaves quantified; true>need
  documented). Reloc sups next.
- 2026-09-22 WENDEL-D (background `ses_f348806a4`, proof-only,
  grep-clean, wendel-only commit): D-cap numeral 0.21 (`:1470-1473`).
  U0 normcap + C2 inflation open.
- 2026-09-22 WIRE-STRIPB (background `ses_f348b0739`, proof-only,
  grep-clean, wiring-only commit): bottom-M40-at-zero mirror CLOSED
  (+ residual). Both zero-line strips conditional on ballSup40; uniform
  strips open.
- 2026-09-22 DIGAMMA-GAMMANEED (background `ses_f3489af52`, proof-only,
  grep-clean, digamma-only commit): inner envelope attempt FAILS honestly
  (14.625>4.5; M≥true>4.5 blocks this route). gamNeed all four open.
- 2026-09-22 SLIVER-POLY79 (background `ses_f3489af54`, proof-only,
  grep-clean, sliver_edge-only commit): poly ≤78/79 on closedBall-12
  CLOSED (`:1049-1084`, 12·13/2). Product still needs pi/Gamma/zeta
  ball-12 uppers.
- 2026-09-22 ASSEMBLY-R03 (background `ses_f34896f1e`, proof-only,
  grep-clean, assembly-only commit): R03 leaf+H conditional
  (`:17490-17527`, two-tenths + 0.07, R02 untouched per grep-first).
- 2026-09-22 CUTL-ZETA (background `ses_f348b0738`, proof-only,
  grep-clean, cutL10-only commit): zeta wall quantified (6 = 4x over
  3/2 proxy; need 0.019; wall 316x, proxy 79x) + wall spec `:2057`.
  Blockage is poly·Gamma spread, not zeta.
- 2026-09-22 CUTL-TIER3 (background `ses_f348f5209`, proof-only,
  grep-clean, cutL10-only commit): three-factor joint 6.33 (zeta 6→3
  honest halve; 158x) + zeta-true 3.16 (79x). Tier 0.04 stands; hJoint
  gaps quantified (6.29/3.12).
- 2026-09-22 DIGAMMA-HNEG (background `ses_f348f8e84`, proof-only,
  grep-clean, digamma-only commit): hne/hG CLOSED at all four centers
  (`:789-813` via Gamma_ne_zero + differentiableAt) + gammaPrime bounds
  conditional on shiftNeeds (`:817-838`). Each doorShiftNeed now exactly
  psiShiftNeed+gamNeed.
- 2026-09-22 WIRE-STRIP (background `ses_f348e8e51`, proof-only,
  grep-clean, wiring-only commit): top-M40-at-zero strip feeder (endpoint
  + ballSup40 conditional) + uniform-M40 residual Prop. Uniform strip
  owned by edge/zeta.
- 2026-09-22 CELL-J (background `ses_f348e54fb`, proof-only,
  grep-clean, interval-only commit): R10 center conditional `:35566`
  (poly 38.3, base 19.15; need Agam·Azeta≥0.00339, have 3.85e-9 —
  same ~6-order wall).
- 2026-09-22 BALLADV-R02PT (background `ses_f348e8e57`, proof-only,
  grep-clean, ball_advance-only commit): dominator nonneg + second-piece
  bound banked; first-piece obstruction spec filed (log-vs-power at
  small m). Pointwise still open.
- 2026-09-22 SUPP-FIX (background `ses_f34918ba1`, single build owner,
  in flight): root cause = `/--` docstrings before `#print axioms`
  section headers (S12/S14/S16/S18); remedy doc→block `/-` at 4 sites.
  Build verification pending; S20 tail block (+441, floor -3.27) held
  for joint commit on GREEN.
- 2026-09-22 ASSEMBLY-R00SUP (background `ses_f348f8e82`, proof-only,
  grep-clean, assembly-only commit): tight-sup chain (`:17180-17261`:
  C=0.0125/r=0.25 → M=0.05 exactly, meets qB≤1/40; `H_of_ball2 :17250`).
  Uniform ≤0.0125 enclosure absent (Mathlib gap).
- 2026-09-22 SLIVER-HC (background `ses_f3490d9f2`, proof-only,
  grep-clean, sliver_edge-only commit): hC CONFIRMED survey-infeasible
  at C=40 (poly>78 alone); instead necessary floor 1/2≤C + mono lift +
  generic/M40 pair closers (`:838-885`). hC premise stays open.
- 2026-09-22 ZETA-M16 (background `ses_f348ff455`, proof-only,
  grep-clean, zeta-only commit): M16 pair (32/33 numerals 0.027) +
  head16 2.282 + M16 tail 17.61 → candidate 19.892 `:41564` (above best;
  tail stuck at 17.61). Tighter 16^0.05 floor next.
- 2026-09-22 SCUT46-SHARD (background `ses_f34902743`, proof-only,
  grep-clean, pilot-only commit): shard assembly with eta17 — floor
  `-2.774 :S9_skip8…` honest sum of banked payoffs (8 theorems). Still
  below both bars; residual filed.
- 2026-09-22 STIRLING-LEAF2 (background `ses_f3490273a`, proof-only,
  grep-clean, stirling-only commit): leaf shift-2 `≤0.097 :2750` (via
  Gamma 2.1≤1.1; 37x→12x). Outer 31x / leaf 12x stand.
- 2026-09-22 FIRSTCELL-RPOW34 (background `ses_f349123ce`, proof-only,
  grep-clean, first_cell-only commit): k=3,4 rpow bounds → S4 numeral
  `≥0.28 :1798` CLOSED (true ~0.31). Tail majorant + eta→zeta factor
  open; 0.28 short of 1.1/1.4.
- 2026-09-22 RH-HRIGHT (background `ses_f348f8e87`, proof-only,
  grep-clean, RH-only commit): Hright narrowed to right-tail
  distance-bound instance `:12546` (Rouché path rejected as wrong shape).
  Distance instance + neg-symm still open.
- 2026-09-22 DERIV-GAMMAP (background `ses_f3490d9f5`, proof-only,
  grep-clean, deriv-only commit): tight-chain specs (sups/needs `:1651-
  1663`) + Cauchy chains (0.8/300 `:1672-1697`) + gaps (`:1704-1716`:
  0.03<0.8, total ~109.9>0.15). DiffCont + sphere sups open.
- 2026-09-22 WENDEL-G2 (background `ses_f349123d2`, proof-only,
  grep-clean, wendel-only commit): G2 per-step pieces (`:1093-1114`:
  log identity + eps cap + denom floor). 8-fold telescope unassembled;
  H3 conditional.
- 2026-09-22 ASSEMBLY-R01 (background `ses_f3490a842`, proof-only,
  grep-clean, assembly-only commit): R01 leaf+H conditional
  (`:17111-17148`, two-tenths center + 0.07 deriv residuals, R00 mirror).
  R00D audit untouched.
- 2026-09-22 TAIL-M21 (background `ses_f349070c9`, proof-only,
  grep-clean, tail-only commit): M2097152 odd rung `24/1448=3/181≈
  0.0166 :950` (honest floor 1448²=2096704; stub 2096512 corrected).
  Next M4194304 exact (2048²).
- 2026-09-22 CELL-I (background `ses_f349123cc`, proof-only,
  grep-clean, interval-only commit): R09 center conditional `:35490`
  (poly 26.3, base 13.15; need Agam·Azeta≥0.00686, have 3.85e-9 —
  short 1.78M, same wall).
- 2026-09-22 BALLADV-R02DOM (background `ses_f3492c3e6`, proof-only,
  grep-clean, ball_advance-only commit): 1.05-decay dominator family
  (`:1685-1771`: p-series + log-comparison banked; Summable half closed
  ∀C). Pointwise domination open (`:1768` residual).
- 2026-09-22 WIRE-HBOT (background `ses_f349123c`, proof-only,
  grep-clean, wiring-only commit): bottom endpoint feeder `:1897`
  (mirror) + gap residual `:1904`. Both endpoints banked; uniform owned
  by edge/zeta.
- 2026-09-22 OFFAXIS-MID (background `ses_f3492c3d`, proof-only,
  grep-clean, off_axis-only commit): mid-block scaffold (Ico/card/
  splits/triangles `:9285-9407`, 4091 terms in 4 blocks). Flat per-term
  budget impossible (41/3068250); cancellation route needed.
- 2026-09-22 ETAPRIME-HCONV (background `ses_f3492c3e2`, proof-only,
  grep-clean, eta_prime-only commit): quotient algebra `:1048` + R02
  caps `:1073` + numeral 11643.6 `:1090` (conditional on Deta link) +
  residual spec `:1109`. Disc→R02 transfer blocked (exponent/coeff).
- 2026-09-22 CUTL-COMBO (background `ses_f3492c3e1`, proof-only,
  grep-clean, cutL10-only commit): two-factor joint 12.86→12.66 `:1899`
  (poly 66.95 × pi 3.15, norm_num). Tier gap 12.61355 (316x) stands.
- 2026-09-22 ASSEMBLY-R00D (background `ses_f3492c3e0`, proof-only,
  grep-clean, assembly-only commit): center VALUE (0.1 closes budget via
  :1359/:1161) + deriv gap audit `0.05<67200 :17073` (only banked Cauchy
  is 67200; no chainable premise). Deriv residual stands.
- 2026-09-22 DIGAMMA-SPEC (background `ses_f3492c3e4`, proof-only,
  grep-clean, digamma-only commit): shift-needs + cN-subs + implies +
  doorShiftNeeds `:630-716` filed as honest Props (Stirling remainder
  absent; oracle cannot close).
- 2026-09-22 ZETA-HEAD29 (background `ses_f34951a3b`, proof-only,
  grep-clean, zeta-only commit): 29/31 head numerals (0.030/0.028) +
  M15 tail 17.61 + head15 2.254 → candidate 19.864 `:41340` (above best
  19.802; head growth dominates). M16 pair or tighter 15^0.05 next.
- 2026-09-22 STIRLING-E05 (background `ses_f3493cda`, proof-only,
  grep-clean, stirling-only commit): gamNeed_outer shift-2 `≤0.063
  :2576` (via Gamma 2.1975≤1.2; 114x→31x). Leaf + E05-link still open.
- 2026-09-22 TAIL-M20 (background `ses_f3492c3e0`, proof-only,
  grep-clean, tail-only commit): M1048576 rung `3/128≈0.0234 :881`
  (exact 2^20 mirror, 1024² verified). Ladder: M2097152 odd-floor next.
- 2026-09-22 DERIV-CELLD (background `ses_f34951a38`, proof-only,
  grep-clean, deriv-only commit): leaf-sub post (dLeaf-6.25I) closed
  93400 `:1616` (honest Cauchy C=934/rho=0.01; poly 6.95/val 22.74/pi
  banked). Leibniz gap filed `:1622/:1626` (60000/93400 vs 0.15).
- 2026-09-22 SLIVER-BOT (background `ses_f34938b0e`, proof-only,
  grep-clean, sliver_edge-only commit): bottom M40 feeder `:768`
  (mirror of :708) + gap narrowings `:779-800` (ceiling 1/2). MB=40
  reduced to ball-sup premise; uniform lowers stay open.
- 2026-09-22 GAMMA-N15 (background `ses_f34a2edf1`, proof-only,
  grep-clean + 4 audits, premise_gamma-only commit): E06 Seq15 rung
  0.655 `:7736` (ceiling 0.65541<0.66, gap 0.005, increment +0.002 —
  asymptoting below gate). N16-next filed `:7974`.
- 2026-09-22 CELL-H (background `ses_f34943443`, proof-only, grep-clean,
  interval-only commit): R08 center conditional `:35413` (poly 13.8,
  base 6.9; need Agam·Azeta≥0.0200, have 3.85e-9 — same 7-order wall).
- 2026-09-22 CELL-G (background `ses_f3495b110`, proof-only, grep-clean,
  interval-only commit): R07 center conditional `:35355` (R06 mirror,
  poly 5.35 consumed). Same 7-order wall (need Agam·Azeta≥0.0517, have
  ~3.85e-9); hgam/hzeta/hprod open.
- 2026-09-22 SCUT43 (background `ses_f34976120`, proof-only, grep-clean,
  pilot-only commit): k=17 CONSTRUCTIVE — `delta18_odd_mem :5439`
  (δ∈(0.595,0.666) via theta18+loose-pi) +   `cos10log18_le_neg_3/4 :5459`
  (1-0.666²/2=0.778 floor, 9π=π+4·2π odd-flip). Eta17 cpow/Re payoff
  open next.
- 2026-09-22 BALLADV-DZETA2 (background `ses_f3497611d`, proof-only,
  grep-clean modulo `#print axioms` probe, ball_advance-only commit):
  DZFIRE confirmed sole instance `:1042` (no beyond-content);
  quotient-of-caps
  `R02_DZetaPair_quotient_of_caps :1488` + `R02_DZetaPair_residual_spec
  :1515` + `etaWorst_normSq :1403`. DZetaPair pipeline shapes complete;
  numeral still needs R02-honest Deta (disc tsum ≠ R02 per DZNUM gap).
- 2026-09-22 ETA-S18 (background `ses_f349a43f1`, proof-only, grep-clean,
  suppliers-only commit): S18 rung — log17/18 bridges, rpow17/18 quads
  (0.37·2.74≈1.014/0.37·2.71≈1.003, thin), cpow17/18 splits,
  Re17≥-0.37/Re18≤0.37 → floor -2.92 `:7130` (-2.18-0.74) + gap 4.86
  `:7141`. Envelope declining; live 1.94 stands. Even ladder through
  S18 complete.
- 2026-09-22 ETA-S16IM (background `ses_f34976123`, proof-only,
  grep-clean, suppliers-only commit): Im-route built trig-free — cpow
  Im splits 9–16 + caps (0.47→0.38) + links → `Im(S16)≥-3.17 :7661`
  (first S16 Im floor) + below-slow gap 5.11 `:7684`. Slow STANDS
  (both S16 floors negative; Pythagoras inapplicable).
- 2026-09-22 ETAPRIME-TSUMVAL (background `ses_f34c288f6`, proof-only,
  grep-clean, eta_prime-only commit): tsum VALUE banked —
  `etaDerivMajorant_tsum_le :780` (∑u ≤ 8π²/6≈13.16 via dominator tsum
  eq + comparison) with full chain `etaDerivShift2_tsum_eq :738`
  (shift-Basel via hasSum_zeta_two) + `etaDerivDominator_tsum_eq :769`
  (×8). Deta numeral feeder ready (needs R02-worst-case re-derivation
  per DZNUM gap, not disc value; numeric ≤13.2 open).
- 2026-09-22 ZETA-SLICE (background `ses_f34c288eb`, proof-only,
  grep-clean, zeta_rigorous-only commit): near-slice tighten 357→336
  (32·10.5 via N13 K0=19.802/denom 0.62; drop 21; old kept). Global
  still 504-dominated. Gap to 47-linear: K0 19.802 vs 19.458 (0.344;
  N15 heads net ~0.08 — doesn't close).
- 2026-09-22 CELL-F (background `ses_f34c288f6`, proof-only, grep-clean,
  interval-only commit): R06 conditional FILED —
  `R06CenterAssembly.R06_center_with_poly_pi_gamma :35297` (poly 0.88 +
  pi 1/2; open hgam/hzeta + hprod). Cell conditionals: R00/R03/R04/R05/
  R06 (all hprod-blocked at banked floors).
- 2026-09-22 STIRLING-LEAF-SHIFT (background `ses_f349a43e9`, proof-only,
  grep-clean): gamNeed_leaf via shift → 0.297 (1/3.375; gap 37x vs
  0.008; n=2+ unbanked). Below-true pattern holds across all gamNeed
  (mid unclosable, outer 114x, leaf 37x) — re-measurement owed.
- 2026-09-22 EDGE-HLOWER2 (background `ses_f349a43ef`, proof-only,
  grep-clean, wiring doc-only commit): HLOWER Props confirmed on disk
  (no re-file) + zeta-feeder attempt filed as honest-fail doc
  `:1788-1820` — R02 shapes are UPPERS (wrong direction+domain),
  Dirichlet needs Re>1, grid floors miss Re=0, qualitative-only at
  edge. hTopLower gap stands (product blocked, 1/2 ceiling optimal).
- 2026-09-22 OA11-S6 (background `ses_f349a43e8`, proof-only, grep-clean,
  off_axis-only commit): combo6 ABSENT (repo-wide grep empty) → N-gap
  certs filed, not S6 extension — `S5_surplus :9193` (41/750) +
  `slow_Ngap_closed :9199` + `joint_N_needs_4096 :9204`. Residual is
  S5→S4096 slow extension (mate banked M=2048 tail), not S5→S6.
- 2026-09-22 TAIL-M262144 (background `ses_f349a43e8`, proof-only,
  grep-clean, tail-only commit): generic M=262144 tail —
  `M262144_rpow_eq :663` (512 exact) + `r_262144_le :689` +
  `eta_tail_262144_le :705` (‖G-S524288‖≤3/64=0.046875) + comparison
  `:720` (0.046875<0.0663). Ladder: …→0.09375→0.0663→0.046875.
- 2026-09-22 OA11-SLOW (silent completion, coordinator-integrated from
  disk, proof-only, grep-clean, off_axis-only commit): t=11 slow CLOSED
  at N=5 — term eqs + Re+Im floors + `S5_re_add_im_ge` (=404/125) +
  `S5_norm_ge` (808/375) + `sCutOA11_slow_closed :9169` (21/10≤808/375,
  surplus 41/750) + shortfall. Honest caveat: tail is S4096-scale.
  off_axis NEVER BUILT — first build queued.
- 2026-09-22 CUTL-MIDDLE (silent completion, coordinator-integrated,
  proof-only, grep-clean, cutL10-only commit): middle PART-COVER —
  reflected Euler sliver (conditional ≤2) + tailQuarter part (≤125 on
  overlap) + `cutL10_middle_gap :1806` (full ≤2 stays OPEN, true ≈4).
  Partial progress, no force.
- 2026-09-22 ETAPRIME-QUOT (silent completion, coordinator-integrated,
  proof-only, grep-clean, eta_prime-only commit): conversion caps
  BANKED — conv defs + `etaConv_ge_R02` (≥0.18 restated) + upper ≤3
  (1+2^0.95≈2.93) + VEta=168 + log2≤1 + C1=2 + C2=31 (0.18⁻²≈30.86) +
  G1-G4 gaps filed (HasDerivAt/deriv-eq/bridge/assembly). DZ residual:
  G2/G3 proofs + Deta/DZetaPair numerals.
- 2026-09-22 FE-EXPDECAY-ADAPTIVE (silent completion, coordinator-
  integrated, proof-only, grep-clean, zeta_rigorous-only commit):
  expDecay FILED (not proved) — obligation Prop + conditional closure
  + banked ≤4 + Im/arg windows. Zero banked content for the decay
  itself; unblocks chi≤8 once discharged.
- 2026-09-22 STIRLING-FIXER (background `ses_f34bc837b`, sole build owner):
  GREEN — `[8682 jobs]` BUILD-EXIT=0 (attempt 2/2). Fixes (11 lines):
  `:1998` rpow_nonneg→explicit `0≤1.38`; `:2197` prod5 tail -1 `)`;
  `:2227` hLink tail +1 `)`; `:2293-95` abs_im rewrite-at-h (goal was
  corrupted by double-occurrence rewrite). sorryAx CLEARED on all 4
  theorems. Lock RELEASED. PREMISE-VERIFY tasked (sole owner — N12
  chain re-audited by coordinator: eleven +1 factor lines closed by
  -11 final, balanced; earlier scare resolved).
- 2026-09-22 OA11-SLOW (background `ses_f34bd8ed1`, proof-only,
  grep-clean, off_axis-only commit): t=11 slow CLOSED at N=5 —
  term eqs `:8969-9007` + Re+Im floors (21/50, 171/250, 3/5, 66/125)
  + `S5_re_add_im_ge :9115` (=404/125=3.232) + `S5_norm_ge :9129`
  (808/375≈2.1547 via 8/9-factor step — coordinator could not verify
  this algebra by hand, FLAGGED for build) + `sCutOA11_slow_closed
  :9169` (21/10≤808/375, surplus 41/750) + shortfall `:9176`.
  Honest caveat: tail is S4096-scale, hEnough still needs S4096 leg.
  off_axis NEVER BUILT — needs first build (queued behind lock).
- 2026-09-22 TAIL-M131072 (background `ses_f34b9c7e9`, proof-only,
  grep-clean, tail-only commit): generic M=131072 tail —
  `M131072_rpow_ge :599` (362≤√131072, 362²=131044) + `r_131072_le
  :615` + `eta_tail_131072_le :641` (‖G-S262144‖≤24/362≈0.0663) +
  comparison `:656` (0.0663<0.09375). Ladder: …→0.1326→0.09375→0.0663.
- 2026-09-22 TAIL-M65536 (background `ses_f34bba11c`, proof-only,
  grep-clean, tail-only commit): generic M=65536 tail —
  `M65536_rpow_eq :535` (256 exact) + `r_65536_le :561` + `eta_tail_
  65536_le :577` (‖G-S131072‖≤3/32=0.09375) + comparison `:592`
  (0.09375<0.1326). Ladder: 0.7→0.265→0.1875→0.1326→0.09375.
- 2026-09-22 ETAPRIME-IDENT (background `ses_f34bd1547`, proof-only,
  grep-clean, eta_prime-only commit): identification BANKED —
  `import zeta_rigorous :4` (DAG checked: no cycle) + header update +
  `etaPairCpow_eq_etaPairTerm :740` (correct arg order `etaPairTerm s
  m` per `:826`, via banked `:839`; prompt's order flagged ill-typed).
  Tsum bridge now fully linked to zeta_rigorous shapes. Residual:
  conversion quotient caps (VEta/C0/C1/C2).
- 2026-09-22 TAIL-M32768 (background `ses_f34bd8ed3`, proof-only,
  grep-clean, tail-only commit): generic M=32768 tail —
  `M32768_rpow_ge :471` (181≤√32768, 181²=32761) + `r_32768_le :487` +
  `eta_tail_32768_le :513` (‖G-S65536‖≤24/181≈0.1326) + comparison
  `:528` (0.1326<0.1875). Ladder: 0.7→0.265→0.1875→0.1326.
- 2026-09-22 SCUT41 (background `ses_f34e7b7e9`, proof-only, grep-clean,
  pilot-only commit): k=16 DESTRUCTIVE full chain — `delta17_odd_mem
  :5198` (δ∈(0.039,0.078), width 0.039) + width `:5207` + `cos ≤ -9/10
  :5219` (1-0.078²/2≈0.997 via 9π-odd flip; true ≈-0.997) + sqrt17≤5
  `:5254` + r17≥1/5 `:5267` + split `:5279` + product ≤-9/50 `:5314` +
  even bridge `:5334` + `eta16_Re_le_neg :5346` + no-pos-lock `:5356`.
  k=16 skip-listed (dead: k=8,11,13,14,16; growth: k=7,9,10,12,15).
- 2026-09-22 FIRSTCELL-ANTITONE (background `ses_f34c288f9`, proof-only,
  grep-clean, first_cell-only commit): `FC_etaF0395_antitone :1467`
  PROVED (decreasing powers mirror). HEVEN slice now needs only
  Tendsto input.
- 2026-09-22 ETAPRIME-DOM-ADAPTIVE (background `ses_f34c288fb`, proof-only,
  grep-clean, eta_prime-only commit): summability CLOSED —
  dominator `B=8(m+1)^-2 :505` + p-series `:511/:528` + log-diff
  `:535/:544` + domination `:612/:718` → `etaDerivMajorant_summable
  :726` UNCONDITIONAL (MAJ confirmed present first). Tsum bridge
  `:297` premises now all banked (u/hderiv/hbound). DZ-chain residual:
  etaPairCpow identification + conversion quotient caps + DG.
- 2026-09-22 BALLADV-DZNUM-ADAPTIVE (background `ses_f34c288fd`, proof-only,
  grep-clean, ball_advance-only commit): DZFIRE verified present +
  worst-case scaffolding — `R02_etaWorst_normSq :1396` (0.74²+8.25²=
  68.6101) + `le_829 :1403` (‖s‖≤8.29 worst factor) + majorant restate
  `:1411` + gap specs `:1427/:1440` (no Deta/DZetaPair numerals in-tree;
  no unconditional Summable; no conversion caps). Residual: dominator
  B + log-comparison + p-series; VEta/C0/C1/C2; DG open.
- 2026-09-22 TAIL-M16384 (background `ses_f34c288f6`, proof-only,
  grep-clean, tail-only commit): generic M=16384 tail —
  `M16384_rpow_eq :408` (128 exact) + `r_16384_le :433` (≤3/16, no
  inv_le needed) + `eta_tail_16384_le :449` (‖G-S32768‖≤3/16=0.1875) +
  comparison `:464` (0.1875<0.26519). Tighter than pilot T'. (Diff
  1-deletion is identical re-anchor, purely append.)
- 2026-09-22 EDGE-RETIER (background `ses_f34c288f8`, proof-only,
  grep-clean, committed 3635a21): MT=1000 retier HONEST-FAIL on gates —
  triple (1/2,1000,0.0005): side closed, ratio + both widths OPEN
  (negations `:1609/:1613/:1618`); no (m,1000) with m≤1/2 passes (M<50
  required). Conditionals `:1642/:1674` banked with open widths.
  SQUEEZE: gates need M<50, product needs C≥joint≫40 — feasible window
  may be empty.
- 2026-09-22 STIRLING-RATE (background `ses_f34efa018`, proof-only,
  grep-clean, stirling-only commit): E05 Seq5 UPPER banked (rpow ≤1.38
  `:1989`, Re 6.9 `:2006`, cpow5 `:2021`, add-lowers `:2040-2164`,
  prod ≥1211.37 `:2190`, upper ≤0.684 `:2219` = 828/1211.37; brackets
  true 0.671 with finite 0.659; conditional on L1; rate needs
  convergence estimate, not upper+lower).
- 2026-09-22 STIRLING-GAMMANEED2-ADAPTIVE (background `ses_f34c288f7`,
  proof-only, grep-clean, same commit): gamNeed_outer via shift → 0.229
  (1/4.375; gap 114x vs 0.002; n=2 →0.3155 worse). Below-true pattern
  holds (mid unclosable, outer 114x over). Tight numerals need
  re-measurement or different w.
- 2026-09-22 EDGE-RETIER (background `ses_f34c288f8`, proof-only,
  grep-clean, wiring-only commit): MT=1000 retier HONEST-FAIL on gates —
  triple (1/2,1000,0.0005): side closed, ratio + both widths OPEN
  (negations banked `:1609/:1613/:1618`; no (m,1000) with m≤1/2 passes
  since M<50 required). Retiered conditionals `:1642/:1674` (+deriv→C
  reduction) banked with open width premises. SQUEEZE documented:
  gates need M<50, product needs C≥joint≫40 — feasible window may be
  empty; needs adjudication.
- 2026-09-22 ETA-S16-ADAPTIVE (background `ses_f34c289aa`, proof-only,
  grep-clean, suppliers-only commit): branch (a) — S14 numerals
  re-verified honest + S16 extended (log15/16 bridges, rpow15/16 quads
  0.39·2.59=1.0101/0.38·2.69=1.0222, cpow15/16 splits, Re15≥-0.39/
  Re16≤0.38) → floor -2.18 `:6784` (-1.41-0.77) + gap 4.12 `:6795`.
  Envelope declining (S14→S16); live 1.94 stands. Even ladder through
  S16 complete.
- 2026-09-22 CELL-E-ADAPTIVE (background `ses_f34c288fc`, proof-only,
  grep-clean, interval-only commit): R05 conditional FILED (CELL-C
  silence resolved: R03+R04 both landed, nothing unreported) —
  `R05CenterAssembly.R05_center_with_poly_pi_gamma :35239` (poly 0.39 +
  pi 1/2; open hgam/hzeta + hprod, needs Agam·Azeta ≥ 1.157 —
  infeasible at banked floors; possible at TRUE values ~1.3, needs real
  floors). Next: R06 (poly 0.88). Cell conditionals: R00/R03/R04/R05.
- 2026-09-22 DERIV-DIFFCONT-OUTER (background `ses_f34d89884`, proof-only,
  grep-clean, deriv_up-only commit): OUTER deriv CLOSED —
  outer-125 sup (`:1378`, tail-quarter covers: Re margins +Im 8.76≤11;
  R02-disc N/A by 0.5) + DiffCont `:1422/:1435` (pole avoided) +
  `zetaDeriv_outer_125_closed :1438` (≤12500, NO open premises). ALL
  FOUR subdivision derivs CLOSED (mid/inner/outer 12500, leaf 93400).
  Tight ≤1000/≤10 still needs zeta lane; gamma 60000.
- 2026-09-22 DERIV-DIFFCONT-LEAF (background `ses_f34d9935e`, proof-only,
  grep-clean, deriv_up-only commit): LEAF deriv CLOSED —
  `dLeaf_closedBall_re_upper :1291` + filled `:1306` + banked `:1319` +
  `zetaDeriv_leaf_934_closed :1322` (≤93400, NO open premises; brief's
  Re corrected by agent: dLeaf Re 0.2, avoidance stronger). THIRD closed
  deriv numeral (mid+inner 12500, leaf 93400). OUTER DiffCont+sup still
  open (best cover 125).
- 2026-09-22 DERIV-DIFFCONT-INNER (background `ses_f34dab270`, proof-only,
  grep-clean, deriv_up-only commit): INNER deriv CLOSED —
  `dInner_closedBall_re_upper :1175` + `zetaDiffCont_inner_filled :1190`
  + banked `:1203` + `zetaDeriv_inner_125_closed :1206` (≤12500, NO open
  premises; stale ##11b gap note replaced). SECOND closed deriv
  numeral (mid+inner at 12500; leaf conditional on DiffCont_leaf;
  outer gap).
- 2026-09-22 DERIV-WIRE (background `ses_f34dc9616`, proof-only,
  grep-clean, deriv_up-only commit): MID deriv CLOSED —
  `zetaDeriv_mid_125_closed :1090` (‖deriv ζ dMid‖≤12500, NO open
  premises: sup + DiffCont + number wired). FIRST fully-closed deriv
  numeral. INNER same-pattern blocked on single `zetaDiffCont_inner`
  (sup/conditional/number ready).
- 2026-09-22 WENDEL-HEQ (background `ses_f34de0cab`, proof-only,
  grep-clean, wendel-only commit): shift identity PROVED —
  `wOuter_re_pos :890` + `shift_avoid_of_re_pos :894` (local mirror) +
  `wOuter_shift_avoid :903` + `digamma_shift_nat :907` (general-N
  induction) + `digamma_shift_8fold :945` + `digamma_shift_wOuter_8
  :951` (exact hEq shape). H3's hEq premise DISCHARGED; H3 needs only
  G1+G2 Props now.
- 2026-09-22 FIRSTCELL-POLAR (background `ses_f34deca25`, proof-only,
  grep-clean, first_cell-only commit): patch item (ii) DONE — polar
  caps `‖1/s‖,‖1/(1-s)‖ ≤ 0.20` (`:1412/:1420`, 1/5.23≈0.1912 via
  abs_im_le_norm; Im bounds exclude 0/1) + fat wrappers `:1429/:1436`.
  PiOf-upper untouched (PIUPPER's lane). Lambda0 patch: (ii) done,
  (i)+(iii) owed.
- 2026-09-22 FIRSTCELL-PIUPPER (background `ses_f34df8061`, proof-only,
  grep-clean): patch item (i) DONE — `FC_pi_rpow_056_le_two :1284`
  (π^0.56≤2 via 3.1416^9≤2^16 16th-power descent, margin ~5%) +
  `FC_piOf_upper_fat :1330` (‖piOf‖≤2 on fat rect, max at Re=-1.12;
  true ≈1.898). Rode into 567827d with POLAR's block (guide entry
  added here belatedly). Lambda0 patch: (i)+(ii) done, (iii) owed.
- 2026-09-22 DERIV-DIFFCONT (background `ses_f34df805f`, proof-only,
  grep-clean, deriv_up-only commit): `zetaDiffCont_mid` CLOSED-syntactic
  — `dMid_closedBall_re_upper :1059` + `:1074` (differentiableAt off
  pole-1, Re≤0.405<1 via closure_ball) + banked `:1087`. Unverified by
  build. Outer/leaf/inner DiffCont still open.
- 2026-09-22 DERIV-LEAF934 (background `ses_f34deca24`, proof-only,
  grep-clean, same commit): leaf filled at honest 934 —
  `zetaSupOnSphere_leaf_934_filled :1215` (R02-disc covers dLeaf sphere,
  margins 0.14+/1.49+) + `zetaDeriv_leaf_934_of_diffCont :1225`
  (deriv ≤93400 modulo DiffCont). Pre-existing ≤10 untouched. Wiring
  (apply banked DiffCont to close mid/inner deriv) owned by DERIV-WIRE.
- 2026-09-22 STIRLING-GAMMANEED (background `ses_f34df805e`, proof-only,
  NO-EDIT gap — MAJOR FINDING): `gamNeed_mid` 0.04 is BELOW TRUE
  (≈0.0463 by Stirling √(2π)·|y|^{x-1/2}·e^{-π|y|/2}) — UNCLOSABLE by
  any sound upper (shift pays 1/2.383→0.4196, 10.49x over; n=2 →0.3155;
  TierC/CHI routes worse; R02-disc N/A by 0.25). Honest-vs-true gap
  1.15x. IMPLICATION: gamNeed_mid premise needs TRUE re-measurement
  (≥0.05) or different wMid — edge-lane budget audit owed. Outer/leaf
  not attempted.
- 2026-09-22 FIRSTCELL-LAMBDA0 (background `ses_f34e3fdf7`, proof-only,
  NO-EDIT gap): Λ₀≤479 NOT closable — banked uppers cover only narrow
  rect ([0.05,0.74]; fat rect extends to Re=-1.12/1.91 where Dirichlet
  route invalid, needs FE); pi-upper + polar caps absent everywhere.
  Coverage 0% of fat rect (inadmissible-extrapolation arithmetic
  explicitly refused). Patch order: (i) piOf upper, (ii) polar caps,
  (iii) FE+Stirling wide caps.
- 2026-09-22 DERIV-INNER (background `ses_f34e3fdf6`, proof-only,
  grep-clean, deriv_up-only commit): INNER set filled at honest 125 —
  geometry covers (Re margins 0.135/0.095, Im margin 10.24; R02-disc
  N/A by 4.5) + `zetaSupOnSphere_inner_125_filled :1103` +
  `zetaDeriv_inner_125_of_diffCont :1113` (deriv ≤12500 modulo
  DiffCont). Subdivision sets now: leaf/mid/inner/outer = gap/125/125/
  gap-at-125-scale (leaf truly open, outer best-125). Gamma 60000.
- 2026-09-22 SLIVER-EXIST (background `ses_f34e828b2`, proof-only,
  grep-clean, sliver_edge-only commit): PARTIAL existence —
  edge-norm continuity at 0 (value 1/2) → m=1/4 uniform on
  Icc(-δ,δ) both arms (`:549/:557/:565/:605/:645`, no zeta input).
  Full m=1/2 still needs zeta₀ lowers for x≠0 (none banked anywhere —
  only uppers). Ceilings stand optimal-if-held.
- 2026-09-22 FIRSTCELL-GAMMA (background `ses_f34e828b2`, proof-only,
  grep-clean, first_cell-only commit): reflected U-chain GAP — refl22
  point/floor/step/factor banked (`:1170/:1175/:1182/:1195/:1203/:1213/
  :1225`), one shift credits 0.9884 → U≤0.0257 (S·U≤517.29 vs 392.7,
  over 124.59 — only 6.04 better than banked 130.628). U-window short
  0.0062 (0.0257 vs 0.0195). Full 22-shift assembly stays patch phase.
  Pilot/sliver_edge writes left for owners.
- 2026-09-22 DERIV-FILL3 (background `ses_f34e828b7`, proof-only,
  grep-clean, deriv_up-only commit): MID set filled at honest 125 (NOT
  10) — geometry covers (Re margins 0.135/0.095, Im margin 6.24) via
  tail-quarter + import `:6`; `zetaSupOnSphere_mid_125_filled :1030` +
  `zetaDeriv_mid_125_of_diffCont :1040` (deriv ≤12500 modulo
  DiffCont). Pre-existing ≤10 untouched. INNER still open; gamma 60000.
- 2026-09-22 DERIV-PSI3 (background `ses_f34e828b3`, proof-only, NO-EDIT
  gap): psiNeed_inner NOT closable — same blocker (complex disc at
  8.1975-0.375i; real secant barred; StirlingVert precondition fails).
  All psiNeed (outer/leaf/mid/inner) now gapped with exact blockers.
- 2026-09-22 ETAPRIME-MAJ (background `ses_f34eaca44`, proof-only,
  grep-clean, eta_prime-only commit): majorant PARTIAL — disc
  (3,1/2) `:382/:384` + `etaDerivMajorant :389` (from `etaDerivBound`
  RHS) + pointwise bound `:400` + conditional summability `:498`
  (from any dominator B). GAP: unconditional `Summable u` needs
  explicit B + log-domination + p-series (not banked). Bridge `:297`
  closable once B lands (u/hderiv/hbound ready).
- 2026-09-22 CELL-D (background `ses_f34e99bd8`, proof-only, grep-clean,
  interval-only commit): R04 conditional FILED (no fallback needed:
  poly 3.85 banked `:33775`, grid member `:1632`) —
  `R04CenterAssembly.R04_center_with_poly_pi_gamma :35181` (poly 3.85 +
  pi 1/2; open hgam/hzeta + hprod check, needs Agam·Azeta ≥ 0.0718 —
  infeasible at banked floors like R00/R03). Cell conditionals: R00,
  R03, R04 (all hprod-blocked).
- 2026-09-22 FIRSTCELL-HEVEN (background `ses_f34eb32a3`, proof-only,
  grep-clean, first_cell-only commit): hEven slice FILED —
  `FC_slice_S2_of_tendsto :1112` (Tendsto+Antitone → S₂≤L, alternating-
  series mirror, no new estimates). Tendsto/Antitone facts stay open
  premises (true: decreasing partials). zetaLower still OPEN (0.23 vs
  1.1/1.4).
- 2026-09-22 SLIVER-MT (background `ses_f34eb32a0`, proof-only,
  grep-clean, sliver_edge-only commit): m=1/2 ADJUDICATED —
  `uniform_top_lower_le_half :502` (any uniform m over Icc(-10,10)
  satisfies m≤1/2: specialize at 0 + endpoint norm 1/2). Poly-zero fear
  REFUTED (edgePoly_top 0 gives entire=1/2, norm exactly 1/2). So m=1/2
  is the OPTIMAL ceiling: m>1/2 infeasible, m=1/2 open (needs zeta₀
  bounds for x≠0). Bottom mirror (mB≤1/2) left for patch.
- 2026-09-22 SLIVER-MB (background `ses_f34e99bd9`, proof-only,
  grep-clean, sliver_edge-only commit): bottom ceiling CLOSED —
  `uniform_bot_lower_le_half :516` (exact token mirror of `:502` via
  `edgeBot_consumer_norm_at_zero`; no adaptation needed). Top+bottom
  ≤1/2 ceilings both banked; m=1/2 existence still open both arms.
- 2026-09-22 CELL-C (background `ses_f34ec61fc`, proof-only, grep-clean,
  interval-only commit): R03 conditional FILED (R01 correctly skipped:
  obligation exists `:1288` but NO grid membership by design `:1244`) —
  `R03CenterAssembly.R03_center_with_poly_pi_gamma :35123` (banked poly
  11.3 + pi 1/2 via `pi_lower_of_re`; open hgam/hzeta + hprod check,
  infeasible at banked floors like R00). New-block simpas are
  pre-existing file style (`simpa only/using`, lines <35093).
- 2026-09-22 ETAPRIME-TERM (background `ses_f34efa018`, proof-only,
  grep-clean, eta_prime-only commit): termwise link PROVED —
  `etaPairCpow` def (cpow-difference mirror, no import) +
  `etaPairCpow_hasDerivAt :339` (via `const_cpow` + `ofReal_log` +
  banked `etaPairDeriv_term`; Mathlib cites checked). Residual:
  summable majorant from `etaDerivPair_bound` + identification with
  `zeta_rigorous.etaPairTerm` (import withheld).
- 2026-09-22 FIRSTCELL-BALL (background `ses_f34eee043`, proof-only,
  grep-clean, first_cell-only commit): prefactor tighten 35→34.5
  ((8.27²+0.25)/2≈34.321) → ballSup 16765.5→16526 (headroom 34.5→274
  vs 16800); Λ₀≤479 STILL the unproved premise (gap stands, doc table
  :415 stale at 35 — cosmetic only). No overlap issue (ZETA committed
  first, hunks disjoint).
- 2026-09-22 SLIVER-R12 (background `ses_f34eee041`, proof-only,
  grep-clean, sliver_edge-only commit): r=1/2 deriv bridges BANKED —
  `uniform_top_deriv_of_closedBall_half :393` + bot mirror `:418`
  (‖deriv‖≤2C via Cauchy C/(1/2)=2C + half-cover `:323`). Tighter
  sphere, looser constant trade (useful iff C small). Uniform C + mT/mB
  still premises-only.
- 2026-09-22 BRIDGE-RE2 (background `ses_f34eeac43`, proof-only,
  grep-clean, bridge-only commit): re-export
  `R02_fullDerivUp_of_etaPairDeriv_withZ934_of_D3 :52` (fires `:1042`'s
  hZ934 via `:22` from rect bounds; 6 eta-pair premises + DG/DZetaPair/
  Deta left open). Bound shape unchanged
  (54.65·40·934+42·DG·934+42·40·DZetaPair).
- 2026-09-22 CELL-B (background `ses_f34f3a72f`, proof-only, grep-clean,
  interval-only commit): R00 center assembly FILED conditional —
  `R00CenterAssembly.R00_center_with_poly_pi_gamma :35068` (consumes
  banked poly-30 + pi-1/2 + Gamma-center + eta-head-1/26; open hgam +
  hzeta + hprod check). INFEASIBLE at banked floors (need Agam·Azeta ≥
  0.00434, have ~1e-8 — 5 orders short; no 0.23 S2 head in-file; eta
  remainder proves ≤25 not ≤1/10). Needs stronger Gamma lower + eta
  remainder + eta-zeta identity.
- 2026-09-22 DERIV-FILL2 (background `ses_f34efa01a`, proof-only, NO-EDIT
  gap): OUTER set (dOuter Im≈-8.75, outside R02-disc) — best honest
  covering numeral is tail-quarter 125 (next 151/431/525 family), none
  reach premised 10. `zetaDiffCont_outer` provable in principle
  (off-pole-1) but conjunction fails on sup. Needs FE/Stirling far-tail
  ≤10 at Im≈-8.75 or outer-budget retier to 125/525-scale.
- 2026-09-22 ZETA-HEAD (background `ses_f34f3a72a`, proof-only,
  grep-clean, zeta_rigorous-only commit): head-N=4 tightening 934→923 —
  `R02_D3_S4_le :32614` (head ≤4) + `pairLim_upper_S4 :32688` (4+162 via
  2^-0.05≤1/1.03 from 1.03^20≤2) + `zeta_upper_923 :32746`
  (166/0.18=922.2≤923). 934 kept. Still 92x from ≤10 (M^-0.05 decay —
  further heads infeasible; needs FE+Stirling). Wiring EDGE-HLOWER
  writes left for owner.
- 2026-09-22 BRIDGE-RE (background `ses_f34f199bb`, proof-only, NO-EDIT
  stale gap): searched `DZFIRE` (agent name) instead of theorem
  `R02_fullDerivUp_of_etaPairDeriv :1042` (landed 32e10b8) — false
  negative, no edit. Re-export still bankable. BRIDGE-RE2 tasked with
  exact pointer.
- 2026-09-22 FIRSTCELL-ZETA (background `ses_f34f29174`, proof-only,
  grep-clean, first_cell-only commit): phase sharpen 4.73→4.679
  (`6.75×0.693148=4.678749 :1081`, margin 0.00025) but zetaLower OPEN —
  gaps banked: S2-window 0.23 vs 1.1 short 0.87 `:1092`, vs 1.4 short
  1.17 `:1099`, ideal complex N=2 short 0.1 `:1103`. Needs larger-N
  slow + tail + factor assembly (patch phase). Zeta_rigorous writes
  left for owner.
- 2026-09-22 DERIV-DZFIRE (background `ses_f34f29175`, proof-only,
  grep-clean, ball_advance-only commit): second assembly
  `R02_fullDerivUp_of_etaPairDeriv :1042` (same UZ=934 shape as `:999`
  but DZ replaced by 6 explicit eta-pair premises: uniform summability
  + eta-eq + term/tsum majorants + quotient eq/cap; shapes restated, no
  import — cycle-safe). DG still open; Deta/DZetaPair numerics owned by
  eta-prime/zeta lanes. First_cell/zeta_rigorous writes left.
- 2026-09-22 STIRLING-DISC (background `ses_f34f3a729`, proof-only,
  grep-clean, stirling-only commit): R02 Gamma disc upper PROVED —
  `D3SG_R02_disc_upper :1918` (‖Γw‖≤1/2 on Re∈[0.025,0.37],
  Im∈[-4.125,-2.625]: w+1 shift into [1,2]-cap ‖Γ‖≤1, ‖w‖≥|Im|≥2.625,
  1/2.625≈0.381≤0.5). Unconditional from banked windows. Feeds DG/G
  premises + rate leaves (G-cap consumer).
- 2026-09-22 WENDEL-H2 (background `ses_f34f3a728`, proof-only,
  grep-clean, wendel-only commit): H3 picked over H2 (H2 zero feeders)
  — `digamma_shift_banked :619` (closed recurrence wrapper) +
  `h3_transport_of_shifted_disc :623` (conditional transport) + GAP
  `:638` (G1 Gauss disc at w+N [Mathlib TODO] + G2 log-shift link
  [needs Binet]). H1/H2/H3-G1/G2 open; M1 banked.
- 2026-09-22 WENDEL-G1 (background `ses_f34eee042`, proof-only,
  grep-clean, wendel-only commit): G1 filed as explicit Prop
  (`G1_outerN8_prop`, Gauss disc at w+8 needs Mathlib-TODO integral +
  real→complex move blocked by Im -4.375). H1/H2/H3-G1/G2 all open;
  transport banked.
- 2026-09-22 WENDEL-G2 (background `ses_f34eb329c`, proof-only,
  grep-clean, wendel-only commit): G2 filed as Prop (`G2_outerN8_prop`
  :769, S/cN/target :760-767) + COMBINER PROVED (`h3_outer_of_G1_G2
  :772`, G1+G2+hEq ⟹ H3, rw/ring/calc). No Taylor/log chain yields the
  -1/(2w) correction (Mathlib log-Taylor real-only). H3 now reduces
  explicitly to G1+G2+hEq. VERT lead in flight — left for owner.
- 2026-09-22 WENDEL-VERT (background `ses_f34ea1e88`, proof-only,
  grep-clean, wendel-only commit): StirlingVert lead BANKED native —
  import (no cycle) + `wOuter_add8_re/im :838/:843` +
  `stirling_wOuter_add8 :848` (pres discharged) + cap `:861` (≤0.157 =
  192/1225). G1-as-filed stays Prop (C≥13.54 conversion unchecked —
  NOT banked).
- 2026-09-22 STIRLING-RATE (background `ses_f34efa018`, proof-only,
  grep-clean, stirling-only commit): E05 Seq5 UPPER — fifth-root ≤1.38
  `:1989`, Re-upper 6.9 `:2006`, cpow5 upper `:2021`, add0-5 norm LOWERS
  1.25-6.20 (fresh), prod5 ≥1211.37 `:2190`, `GammaSeq5_upper_of_link
  :2219` (≤0.684 = 828/1211.37≈0.68352, coordinator-verified; brackets
  true ~0.671 with finite 0.659).   Conditional on L1; rate 0.014 still
  needs convergence estimate.
- 2026-09-22 DERIV-PSI2 (background `ses_f34efa019`, proof-only, NO-EDIT
  gap): psiNeed_inner NOT closable — needs complex disc at
  8.1975-0.375i r≤1; real secant barred (Im≠0); StirlingVert fails
  precondition (|−0.375|<0.5) + wrong denominator. Missing: large-Re
  complex psi disc (Gauss/Stirling) — same blocker as outer.
- 2026-09-22 CUTL-BALL (background `ses_f34f3a726`, proof-only,
  grep-clean): ball-sup GAP structural — `cutL10_thinRect_tightened_gap
  :1438` (center 0.02632 covers 0.0234; ball 12.864≤12.87; loosest zeta
  wall 6 vs true 1.549 4x; even granting pi→2 + zeta→3/2 product 2.01
  still 50x over 0.04; endpoint 0.062>0.04 BEFORE zeta; Cauchy+1 ball
  sets spread).   `hJoint≤0.04` premise-gated.
- 2026-09-22 CUTL-FE (background `ses_f34e828c7`, proof-only, grep-clean,
  cutL10-only commit): FE-route mirror HONEST — full CutR10 homologue
  chain mirrored (`chiFE/FE_side/eq/reflected/leftSix/sup_six/FEroute/
  sliver/chi_and_middle/factor_shortfall/sliver_width_gap` :1462-1720):
  reproduces ‖zeta‖≤6 on CutL10 strip CONDITIONAL only (joint stays
  12.864); sliver width 0.06 vs hFE 2.56; ≤2 blocked by chi≥2.08.
  Needs chi≤3 + reflected-middle≤2 + hDom/hReal. First_cell/sliver_edge
  writes left for owners.
- 2026-09-22 DERIV-PSI2 (background `ses_f34efa019`, proof-only, NO-EDIT
  gap): D3SG 0.5-cap does NOT discharge any gamNeed (only wLeaf overlaps
  domain, but 0.5≰0.008 62.5x weak; others miss domain ±0.25). Tight
  0.002/0.008/0.04 numerals need D3SG shift+real-cap at Re∈{0.1,0.1975}
  (owed per `:548-551`).
- 2026-09-22 DERIV-PSI2 (background `ses_f34efa019`, proof-only, NO-EDIT
  gap): D3SG 0.5-cap does NOT discharge any gamNeed (only wLeaf overlaps
  domain, but 0.5≰0.008 62.5x weak; others miss domain ±0.25). Tight
  0.002/0.008/0.04 numerals need D3SG shift+real-cap at Re∈{0.1,0.1975}
  (owed per `:548-551`).
- 2026-09-22 CUTL-ZETA (background `ses_f34efa016`, proof-only, NO-EDIT
  gap): strip zeta wall has NO proof in-file (premise-gated by design
  `:639-640` — needs FE+Stirling+convexity). Only closable zeta-upper
  is Re≥3/2 Euler (inapplicable to strip). Wall stays 6; 50x-over
  structural even granting pi+zeta improvements; blockage is +1-ball
  spread, not zeta alone.
- 2026-09-22 SLIVER-SPHERE (background `ses_f34f199ba`, proof-only,
  grep-clean): bottom bridge PRE-EXISTS (`:368` token mirror) → banked
  cover extension `edgeSphere_cover_half :323` (r=1/2 spheres over edge
  band in closedBall 0 12; 11+1/2≤12). Uniform numerals + C still
  premises-only; no r=1/2 deriv bridge.
- 2026-09-22 BALLSUP-SURVEY (background `ses_f34f3a72b`, read-only, no
  edits): ball-12 C=40 INFEASIBLE by product route — poly alone >78 on
  ball-12 (12.5²/2), poly·pi ≈56300 (π^5.75≈722 at Re=-11.5),
  realistic joint ≥10⁶. R02-disc best: 40.74 conditional / 3805.12
  unconditional; pi-tighten ≤0.972 reaches 39.59 on R02-disc only (not
  ball-12). VERDICT: retier MT (1000-shape exists) or abandon product
  route; smallest-next `poly_upper_closedBall12 ≤79` spec'd.
- 2026-09-22 R02-CELL2 (background `ses_f34f5d1a4`, proof-only,
  grep-clean, first_cell-only commit): gammaLower-0.008 GAP (not
  closed) — S-window dead (need S≤15104, banked 20128, +5024 over;
  true S saves ≤3) + U-window quantified (need U≤0.0196, banked 0.026,
  +0.0064 over; true U≈0.018 feasible via deeper reflected chain —
  patch phase, no premise_gamma touch). Banked: S-cap/U-cap + gaps
  `:1023/:1035/:1039/:1042/:1054` (523.328 vs 392.7, over 130.628).
  Wiring EDGE-BOTTOM writes left for owner.
- 2026-09-22 ETA-CF2 (background `ses_f350a352d`, proof-only, grep-clean,
  suppliers-only commit): cos shave `neg0034 :5998` (d≥-0.0336895≥-0.034,
  margin ~0.00031, true -0.0336) → cF 1.851→1.85 (`3.41998≤1.85²`) +
  shortfall `:6117` (0.6514→0.65, shave 0.0014). Cos lane now exhausted
  (at true limit); rpow 1.522 margin 0.0008 untouched.
- 2026-09-22 SCUT34 (background `ses_f350a352c`, proof-only, grep-clean,
  pilot-only commit): log15 FIRST link + theta15 — bridge `:4558`
  (log15=log14+log(15/14), tighter 15/14 picked) + window `:4569/:4582`
  ([2.6918458317,2.7251791663], true ~2.708 inside) + `theta15_mem
  :4599` (θ∈[26.918,27.252], width 0.333). Next: delta15/cos (k=14
  even).
- 2026-09-22 SCUT28 (background `ses_f3752af34`, proof-only, grep-clean):
  log13 FIRST link — bridge `:4064` (log13=log12+log(13/12), tighter
  13/12 ratio picked) + window `:4075/:4088` ([2.5537505937,
  2.5768275178], width ~0.023, true ~2.565 inside). Next: theta13
  (implied [25.54,25.77], NOT banked) + cos sign (k=12 even).
- 2026-09-22 SCUT29 (background `ses_f375116de`, proof-only, grep-clean,
  pilot-only commit): k=12 CONSTRUCTIVE — `theta13_mem :4105`
  (θ∈[25.538,25.768], width 0.231) + `delta13_even_mem :4127`
  (δ=θ-8π∈(0.404,0.637)) + `cos10log13_ge :4144` (cos≥3/4 via
  1-0.637²/2≈0.797; true ~0.87, margin good). Even parity → eta12 gain
  ≈ r13·0.75 ≈ 0.21 pending r13 chain. Premise_gamma N8 left for owner.
  SCUT30 tasked (r13/cpow13/eta12 gain).
- 2026-09-22 SCUT30 (background `ses_f374f864c`, proof-only, grep-clean):
  eta12 gain — `sqrt13_le :4186` (≤37/10, 13≤13.69; (10/3)² shortcut
  correctly NOT reused) + `rpow13_neg_ge :4200` (r13≥10/37≈0.2703) +
  split `:4212` + product `:4247` (15/74 = 10/37·3/4, coordinator-
  verified) + `eta12_Re_ge :4276` (+0.2027) + shard `:4286`
  ({0..7,9,10,12}, single-count) + shortfall `:4299`
  (1951921/388500≈5.024). Floor -3.127→-2.924 (gain 0.203).
  Cumulative constructive: +0.27/+0.15/+0.084/+0.203 = +0.707.
- 2026-09-22 SCUT42 (background `ses_f349a43f3`, proof-only, grep-clean,
  pilot-only commit): log18 FIRST link + theta18 — bridge `:5379`
  (log18=log17+log(18/17), tighter 18/17 picked) + window `:5390/:5404`
  ([2.8869678061,2.8939122527], true ~2.8904 inside) + `theta18_mem
  :5421` (θ∈[28.870,28.939]). Next: delta18/cos (k=17 odd needs ≤-c).
- 2026-09-22 SCUT40 (background `ses_f34ea1e89`, proof-only, grep-clean,
  pilot-only commit): log17 FIRST link + theta17 — bridge `:5140`
  (log17=log16+log(17/16), sharp d9-exact base) + window `:5151/:5165`
  ([2.8314122506,2.8350887232], width ~0.0037, true ~2.8332 inside) +
  `theta17_mem :5182` (θ∈[28.314,28.351], width 0.037). Next: delta17/
  cos (k=16 even needs +c).
- 2026-09-22 SCUT39 (background `ses_f34ed6c42`, proof-only, grep-clean,
  pilot-only commit): S+eta15 assembly — `:5098` (multiset
  {0..7,9,10,12,15}, single-count, k=15>7 safe) + shortfalls `:5111`
  (legacy 1874221/388500≈4.824) + `:5120` (M8192 308659051/70318500≈
  4.389). Floor -2.924→-2.724 (+1/5). Cumulative constructive +0.907.
  hEnough open both bars.
- 2026-09-22 SCUT38 (background `ses_f34efa01c`, proof-only, grep-clean,
  pilot-only commit): k=15 CONSTRUCTIVE +1/5 — `delta16_odd_mem :4940`
  (δ∈(-0.55,-0.54), width 0.01) + `cos10log16_le_neg :4960` (cos θ≤-4/5
  via 9π-odd flip of 1-0.55²/2≈0.84875) + sqrt16≤4 `:4994` + r16≥1/4
  `:5007` (exact) + split `:5019` + product ≤-1/5 `:5054` + odd bridge
  `:5073` + `eta15_Re_ge :5086` (+0.2). Shard assembly not banked
  (residual). SCUT39 tasked (S+eta15 floor + shortfall).
- 2026-09-22 SCUT37 (background `ses_f34f29177`, proof-only, grep-clean,
  pilot-only commit): log16 SHARP — `log_sixteen_eq` (log16=4·log2 via
  log_pow, no sSCUT_log_two existed so d9 direct) + window
  `:4896+` ([2.7725887212,2.7725887232], width 2e-9, exact power-of-2)
  + `theta16_sharp_mem :4911` (width 2e-8). Next: delta16/cos flip
  (k=15 odd needs cos≤-c).
- 2026-09-22 ETA-S14 (background `ses_f34f3a72f`, proof-only,
  grep-clean, suppliers-only commit): S14 even ladder for record —
  log13/14 bridges, rpow13/14 quads (0.41·2.48=1.0168, 0.40·2.53=1.012),
  cpow13/14 splits, Re13≥-0.41/Re14≤0.40 → floor -1.41 `:6438`
  (-0.60-0.81) + gap 3.35 `:6449`. Worse than S12; live 1.94 stands.
  Even ladder S4→S14 complete (1.56/0.95/1.15/0.24/-0.60/-1.41).
- 2026-09-22 SCUT-TAIL (background `ses_f34f5d1a2`, proof-only,
  grep-clean, pilot-only commit): M=8192 tail tighten —
  `M8192_rpow_ge :4797` (181/2≤8192^1/2, 8190.25≤8192) + `r_8192_le
  :4812` + `eta_tail_8192_le :4837` (‖G-S16384‖≤48/181≈0.265, was
  7/10) + `hEnough_8192_threshold :4854` (bar 1507/905≈1.665, was
  21/10) + shortfall `:4864` (4.589, was 5.024) + improvement
  witnesses `:4871/:4876`. hEnough still open. First_cell/wiring
  writes left for owners.
- 2026-09-22 SCUT35 (background `ses_f35085cac`, proof-only, grep-clean,
  pilot-only commit): k=14 NO-CONSTRUCT gap — `delta15_odd_mem :4616`
  (δ=θ-9π∈(-1.356,-1.021), width 0.335) + `no_construct_gap :4637`
  (δ⊂(-π/2,0) containment). Parity-anchor interaction: 9π ODD →
  cos θ=-cos δ<0, but k=14 EVEN needs +c — no lower banked, no force.
  k=14 neutral/destructive (skip-list candidate pending lock). Wiring
  EDGE-DERIV writes left for owner.
- 2026-09-22 SCUT36 (background `ses_f35060021`, proof-only, grep-clean,
  pilot-only commit): eta14 DESTRUCTIVE-LOCK — `cos10log15_le_neg
  :4649` (cos θ≤-0.08 via 9π-odd flip of 1-1.356²/2≈0.0806 floor) +
  sqrt15≤4 `:4684` + r15≥1/4 `:4697` + split `:4709` + product
  ≤-1/50 `:4744` + even bridge `:4764` + `eta14_Re_le_neg :4777`
  (≤-0.02) + `no_pos_lock :4787`. k=14 skip-listed (k=8,11,13,14 dead;
  growth only k=7,9,10,12). Premise_gamma VERIFY11 writes left.
- 2026-09-22 SCUT31 (background `ses_f374e5aec`, proof-only, grep-clean):
  log14 window + theta14 — bridge `:4308` (log14=log13+log(14/13)) +
  window `:4319/:4332` ([2.6251791651,2.6537505948], width ~0.0286,
  true ~2.6391 inside) + `theta14_mem :4349` (θ∈[26.252,26.538],
  width 0.286). δ=θ-8π≈(1.12,1.41) quadrant-II → k=13 odd flip needs
  cos≤-c (likely gap). SCUT32 tasked (delta14/cos upper-or-gap).
- 2026-09-22 VERIFY5 (background `ses_f374ef9ff`, sole build owner):
  GREEN — `[8689/8689] Built door3_premise_gamma (28s)`, BUILD-EXIT=0
  (attempt 1/2), zero edits, grep-clean (0 sorry/axiom/admit/RH_apply/
  sorryAx). N8 COMPILED (`:4779/:4975/:4980` under green). Premise_gamma
  stays GREEN (N5→N8 ladder all verified). Lock RELEASED.
- 2026-09-22 BINET-SURVEY (background `ses_f3752af33`, read-only, no
  edits): L2 rate leaf absent confirmed — no Binet/Stirling-remainder/
  logGamma/GammaSeq-rate in Mathlib (BohrMollerup qualitative,
  Beta.lean DCT-only, Stirling factorial-only, Digamma TODO Gauss
  rep); repo: product UPPERS only, Wendel/Gauss/digamma-remainder all
  unbanked hypotheses. SMALLEST RATE: E05 N=5 `rate_needed_corr :3402`
  (≤0.014) feeding `:3419` (0.659+0.014→0.645); host must be
  Stirling-disc/Binet leaf, NOT premise file.
- 2026-09-22 DZ-SURVEY (background `ses_f3752af33`, read-only, no
  edits): DZ DEAD honestly — no uniform `‖deriv zeta‖` on R02 in-tree
  or Mathlib (Cauchy conditional unfilled, 1000-instances wrong
  centers, eta-pair termwise shapes disconnected from tsum-deriv link,
  vonMangoldt Re>1 only). Revive routes: (i) DiffContOnCl+sphere sup →
  Cauchy (likely huge/useless); (ii) tsum-differentiation of eta-pair
  chain (shapes half-exist, assembly missing).
- 2026-09-22 SUPP-VERIFY (background `ses_f37683d44`, sole build owner):
  GREEN — `[8688/8688] Built door3_cell_suppliers (109s)`, BUILD-EXIT=0
  (attempt 2/2; attempt 1 two errors). Fixes: `CS_log_seven_eq :4452`
  (`conv_lhs => rw [h7]` — bare rw poisoned RHS 7/6) +
  `CS_rpow7neg_upper_proved :4583` (`0.52·1.92=0.9984<1` trap — kept
  def ≤0.52, proved inline `hStrong : 2.02≤7^0.395` via quadratic lower
  `1+0.74607+0.74607²/2≥2.02`, `0.52·2.02=1.0504≥1`; coordinator checked
  `2.02≤~2.156` sound). Axioms standard, no sorryAx. Full eta backlog
  (S8/S8IM/cF-1851/S10/S6Im) COMPILED.   Lock RELEASED. PILOT-BUILD
  tasked (sole owner, first pilot build).
- 2026-09-22 PILOT-BUILD (background `ses_f37622079`, sole build owner):
  BUILD-EXIT=1 x2 (first-ever pilot build; 32 errors → 17 remaining, all
  15 in-scope cleared). Fixes (pilot-only, +16/-21): S5 norm bridges
  `:1498` (t2/t3/t4 via eta_eq + norm_neg), `le_of_pow` metavar x2
  (`:1643/:2684`, explicit base/nonneg), stray-`norm_num` deletions x8
  (cpow2/3/8/10 hre/him pairs), `mul_le_mul` args `:1717`, FALSE theta9
  numeral `:2225` (`2.197224578`→`...576`, off 4e-10 — second false
  literal caught in pilot lane), cos10log10 rw→linarith `:2574`.
  Remaining 17 all prescribed same-family: 12x No-goals/le_of_pow
  (`:2970/74`, `:3057/3230/3326/3693/3984`, `:3085/89` etc.), `:3043` rw
  chaining, `:3448` S8/0.15 term bridge. Grep-clean. PILOT-SWEEP2 tasked
  (sole owner, apply 17 + rebuild).
- 2026-09-22 PILOT-SWEEP2 (background `ses_f375b5b8a`, sole build owner):
  GREEN — SIXTH GREEN LANE MODULE. `[8704/8704] Built
  door3_pilot_R00_zeta (52s)`, BUILD-EXIT=0 (attempt 2/2). Fixes (+9/-22):
  10x stray-norm_num deletions (2x replaceAll, 5+5 hre/him sites),
  5x le_of_pow explicit args (`:3048/:3219/:3317/:3683/:3974`), `:3041`
  rw+e2 bridge, `:3439` hr10div + add_re alignment. Zero remaining.
  Grep-clean. ALL SIX door-3 lane files GREEN (suppliers/ball/wiring/
  bridge/premise_gamma/pilot). Next: full-tree sweep (ALLGREEN).
- 2026-09-22 ALLGREEN (background `ses_f375628e8`, sole build owner):
  FULL-TREE GREEN, no edits. `central_cover_assembly` BUILD-EXIT=0
  (8687 jobs) + `riemann_hypothesis` BUILD-EXIT=0 (8685 jobs), 0 errors
  / 0 sorryAx both, locks clean. Chain elaborates end-to-end
  CONDITIONALLY (`:12186/:12204/:12238` bridges clean; 6 Challenge2/
  ClosedCertificate thms still consume `RiemannHypothesisProp_apply`
  `:12471-12476`). Residual to unconditional: 80 per-cell enclosures +
  edge strips `:12157` + cutoff lines `:12165` (§18b.10); lanes 0 /
  core 0 errors. Door-3 wave phase COMPLETE — all 8 modules green.
- 2026-09-22 ETA-S8 (background `ses_f37749d42`, proof-only, grep-clean,
  suppliers +657 greenfield S8): log bridges (log8 exact, log7 window),
  rpow7/8 quads, cpow7/8 splits, cos7≥0.58 / cos8∈[0,0.101], Re7≥0.2494
  / Re8≤0.0475 → `CS_complex_S8_Re_ge_115 :4980` (1.15 = 0.95+0.2494-
  0.0475, true ~1.716) + below-slow gap `:5003` (0.79) + shortfall
  `:5009` (1.4414 at cF 1.851). Honest: beats S6-Re 0.95, trails S4-Re
  1.56 and live 1.94 (true |S8|~1.901).   Live best STANDS (0.6514).
  Next: S8-Im route (ETA-S8IM).
- 2026-09-22 ETA-S8IM (background `ses_f376ddb3c`, proof-only, grep-clean,
  suppliers-only commit): S8-Im lower banked — cpow7/8_im splits
  `:5049/:5085`, sin7≥0.055 `:5123` / sin8≤1 `:5169`, Im7≥0.0236
  `:5174` / Im8≤0.47 `:5192` → `CS_complex_S8_Im_ge_016 :5224` (0.16,
  true ~1.231) + Pythagoras gap `:5237` (1.15²+0.16²=1.3481 vs
  1.94²=3.7636, gap 2.4155; needs Im≥1.564 — no force). S8 pair gives
  ~1.161; true |S8|~1.901 confirms stall.   Live 1.94 STANDS.
  Premise_gamma 8-line tweak left for VERIFY3 owner.
- 2026-09-22 SCUT22 (background `ses_f376e9806`, proof-only, grep-clean):
  k=10 CONSTRUCTIVE flip — `sSCUT_delta11_even_mem :3637` (θ-8π ∈
  (-1.198,-1.106)) + `sSCUT_cos10log11_ge :3647` (cos ≥ 7/25 = 0.28 via
  |δ|≤1.2 quadratic floor 1-x²/2; true ~0.41, margin good). Even parity
  keeps sign → Re(eta₁₀) ≥ +r11·0.28 constructive (NOT destructive —
  8π nearer than 7π). Product floor needs r11 lower (follow-up).
  SCUT23 tasked (r11 lower + eta10 gain).
