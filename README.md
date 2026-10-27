# Adaptive random reshuffling: a matching worst-case lower bound

[Read the paper](paper/adaptive-random-reshuffling.pdf) · [TeX source](paper/main.tex) · [Formal theorem](formal/FinalTheorem.lean)

This repository contains a mathematical paper and a Lean formalization of a worst-case lower bound for smooth convex random reshuffling with adaptive scalar step sizes and selected convex averages.

## Result

Let $n\ge2$, $K\ge1$, $T=nK$, $L>0$, and $D,\sigma\ge0$. Each component $f_i$ is convex and globally $L$-smooth. The mean $f=n^{-1}\sum_i f_i$ has a minimizer $x_*$, with

$$
\|x_0-x_*\|\le D,
\qquad
\frac1n\sum_i\|\nabla f_i(x_*)\|^2\le\sigma^2.
$$

Each epoch uses a fresh independent uniform permutation. Updates and output are

$$
x_{t+1}=x_t-\eta_t\nabla f_{i_t}(x_t),
\quad 0<\eta_t\le 1/L,
\qquad
\widehat x=\sum_{t=0}^{T}w_t x_t,
\quad w_t\ge0,\quad \sum_{t=0}^{T}w_t=1.
$$

Steps and weights may depend on the instance, an independent private random seed, and **the entire bank of sampled permutations**, including future epochs. Thus the lower also applies to measurable current-gradient and history-adaptive scalar policies. Legality is required almost surely.

For every parameter tuple, **one instance of dimension at most $n$, fixed before every seed law and policy**, has

$$
\mathbb E[f(\widehat x)-f(x_*)]\ge \frac{\Psi}{524288},
$$

where

$$
\Psi=\min\left\{LD^2,\frac{LD^2}{nK}
+\min\left\{\frac{\sigma D}{\sqrt{nK}},
\left(\frac{L\sigma^2D^4}{nK^2}\right)^{1/3}\right\}\right\}.
$$

The function class permits arbitrary finite dimension; the dimension cap is a property of the hard instance. The theorem concerns the specified scalar-gradient updates and convex outputs. It does not cover chosen sample orders, momentum, vector preconditioners, or outputs outside the convex hull of the visited states.

## Matching upper and prior work

The upper $57\Psi$ is inherited from [Liu, COLT 2026](https://proceedings.mlr.press/v336/liu26d.html), using a tuned constant step, the uniform **pre-update average over $x_0,\ldots,x_{T-1}$**, and the separate option of returning $x_0$. It is an optimized upper, not a guarantee for every adaptive policy.

The rate powers and earlier cubic, weighted-output, and fixed-instance lower bounds have precedents, including [Cha, Lee and Yun, ICML 2023](https://proceedings.mlr.press/v202/cha23a.html) and [Rajput, Lee and Papailiopoulos, ICLR 2022](https://openreview.net/forum?id=YiBa9HKTyXE). The lower here covers adaptive scalar steps, trajectory-selected all-state convex outputs, and all parameter regimes in the uniform-$L$ model. It does not characterize every prescribed schedule or the separate nonuniform-smoothness refinements.

## Formal verification

The entrypoint is:

```text
Gate149.FinalTheorem.one_fixed_instance_fresh_epoch_lower
```

The 41 source modules include the actual convex smooth functions and gradients, all-component-count simplex construction, permutation geometry, paid auxiliary resets, interval trimming, parameter tuning, and joint probability law.

A clean serial replay rebuilt all 41 research modules from source without earlier research `.olean` files. All calls exited successfully. The [axiom reports](verification/axiom-reports.txt) contain 397 reports for 395 distinct declarations, using only `propext`, `Classical.choice`, and `Quot.sound`.

**Verification boundary:** the replay reused installed Lean, Mathlib and its dependency libraries; it did not rebuild those third-party libraries. The new lower is formalized. Liu's published upper proof is not: `PublicMinimax.sandwich_given_upper_strategy` explicitly takes that upper guarantee as a premise. See [verification details](verification/README.md).

Kernel acceptance does not establish priority, external peer review, or practical training improvements.

## Build

- Lean: `leanprover/lean4:v4.27.0`
- Mathlib: `a3a10db0e9d66acbebf76c5e6a135066525ac900`
- `lakefile.toml` explicitly registers all 41 flat source modules.

The following external Lake workflow is provided for reproduction:

```sh
lake update
lake exe cache get
lake build
```

**This Lake workflow has not been executed for the supplied descriptor.** Its configuration was statically checked; the successful replay used direct serial Lean invocations. These commands may download dependencies.

The unchanged 11-page PDF was compiled and visually checked. No compiled research artifacts or private campaign records are included. [SHA256SUMS](SHA256SUMS) covers the repository payload except that checksum file itself.
