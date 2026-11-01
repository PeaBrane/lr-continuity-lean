# No infinite cluster at criticality for long-range percolation: Lean formalization

Lean 4 formalization of the main theorem of the preprint

> Yan Ru Pei, *No infinite cluster at criticality for long-range percolation with fast-decaying
> interactions* ([paper/lr-continuity.pdf](paper/lr-continuity.pdf), source
> [paper/lr-continuity.tex](paper/lr-continuity.tex)).

For independent long-range bond percolation on $\mathbb Z^d$, where $x$ and $y$ are joined with
probability $1-e^{-\beta J(x-y)}$, take $d\ge2$ and a kernel $J$ that is invariant under coordinate
permutations and sign changes (Sym), has $J(e_1)>0$ (Pos), and satisfies
$\liminf_{n\to\infty}n^dT(n)=0$ with $T(n)=\sum_{\|x\|_\infty>n}J(x)$ (Tail). Then
$\theta(\beta_c)=0$: there is no infinite cluster at the critical parameter.

## The statement

```lean
-- Peapods/LongRange/Main.lean
theorem Peapods.LongRange.Kernel.theta_critical {d : ℕ} (K : Kernel d) (hd : 2 ≤ d)
    (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0)) (hT : K.TailSmall) :
    K.theta K.critical = 0
```

`Kernel.main` adds Lemma 2.4 of the paper, $0<\beta_c<\infty$:
`0 < K.critical ∧ (∃ β, 0 ≤ β ∧ 0 < K.theta β) ∧ K.theta K.critical = 0`.

| Paper | Lean |
|---|---|
| $J\ge0$, $J(-x)=J(x)$, $\sum_xJ(x)<\infty$ | `Kernel d` (`J : (Fin d → ℤ) → ℝ` with `nonneg`, `even`, `summable`); `J 0` plays no role |
| $\{x,y\}$ open with probability $1-e^{-\beta J(x-y)}$, independently | `Kernel.law β`, an infinite product of Bernoulli laws over `Sym2 (Fin d → ℤ)` (`Model.lean`) |
| $\theta(\beta)=\mathbb P_\beta(0\leftrightarrow\infty)$ | `Kernel.theta β`: the probability that the open cluster of `0` is infinite |
| $\beta_c=\inf\{\beta:\theta(\beta)>0\}$ | `Kernel.critical := sInf {β \| 0 ≤ β ∧ 0 < K.theta β}` |
| (Sym) | `Kernel.SignInvariant`: `K.J (S.linear z) = K.J z` for every signed coordinate permutation |
| (Pos) | `0 < K.J (unitAt 0)`, where `unitAt 0` is $e_1$ |
| (Tail) | `Kernel.TailSmall`: for every $\varepsilon>0$, frequently $n^dT(n)<\varepsilon$. `tailSmall_iff_liminf` proves it equivalent to $\liminf n^dT(n)=0$ with the liminf taken in $[0,\infty]$ |

A real-valued `Filter.liminf` would be the wrong reading of (Tail). In Lean's conditionally complete
order, the real liminf of a sequence tending to $+\infty$ is $0$, so that hypothesis would be vacuous.

## Building and checking

```bash
lake exe cache get
lake build
```

The project pins Lean `v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, the pins of
openai/math. To check the axioms, run `lake env lean Axioms.lean` with

```lean
-- Axioms.lean
import Peapods
#print axioms Peapods.LongRange.Kernel.theta_critical
```

It reports `propext`, `Classical.choice` and `Quot.sound` only. No file in `Peapods/LongRange/`
contains `sorry`, `axiom`, `native_decide` or heartbeat options.

## Layout

The proof follows the paper section by section. The parts of OpenAI's nearest-neighbour $\mathbb Z^3$
proof that do not depend on the lattice are reused unchanged from the vendored `OAI/` directory: the
product-law conditioning, Harris's inequality, the hyperedge gluing comparison, adaptive reveals and
the planar Peierls count.

| Module | Content | Paper |
|---|---|---|
| `Geometry`, `Model` | cubes, boxes, signed symmetries; the long-range model, $\theta$, $\beta_c$ | §1, §2 |
| `Supercritical`, `Subcritical`, `Seeds` | $\beta_c<\infty$ (planar Peierls), $\beta_c\ge1/\|J\|_1$, the zero-one law, seed cubes | Lemma 2.4 |
| `Faces` | outer thick quarter-faces, face events with a short last edge, the long-edge bound, Harris over the $d2^d$ faces | Def. 3.1, Lemma 3.2 |
| `Scales` | the constants (S1)–(S7) | Lemma 3.3 |
| `FinGraph` | finite graphs with long-range bits; Corollary 2.2 in a finite graph | §2 |
| `Layers`, `RelayQuality`, `Trials`, `Extension` | crossing weights and blocking, relay quality, residue classes and Chebyshev for unequal trials, the extension lemma | Lemma 4.1 |
| `RelayThick`, `Frames`, `RelayLemma` | the thick relay route, frames, the relay between neighbouring coarse cubes | Lemma 5.1 |
| `Coarse`, `Exploration`, `ExplorationBounds`, `Initial` | interfaces $I_{vw}$, the exploration, Lemmas 6.1–6.3, the Peierls step, $\theta(q)>0$ | §6 |
| `Main` | Theorem 1.1 | Theorem 1.1 |

These choices differ from the paper on purpose. Each is equivalent to the paper's version or stronger
than it:
- Lemma 3.2 is stated in power form.
- $(F_q(D))$ asks every pair of distinct points of $D$ to be an edge of the graph, with probability
  $0$ when $J=0$.
- The root event fixes the pairs of $Q_0$: open if $J>0$, closed otherwise.
- The relay's edge condition holds on all of $D$, which the exploration supplies.
- The Peierls step uses OpenAI's boundary encoding.

## Provenance

`OAI/Probability/CriticalZ3/` is OpenAI's formal proof of $\theta(p_c)=0$ for nearest-neighbour
percolation on $\mathbb Z^3$ (<https://github.com/openai/math>, commit `4eaee87`). It is vendored
unmodified under the Apache License 2.0; see [OAI/README.md](OAI/README.md) and
[OAI/LICENSE](OAI/LICENSE). Everything under `Peapods/` is new.
