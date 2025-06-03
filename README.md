# Verified hand-written Lean solutions to HumanEval

[HumanEval] is a collection of small programming tasks originally intended as a benchmark for LLMs.
In this repo, we collect hand-written *formally verified* [Lean 4] solutions to these problems.

The idea is to build a small set of simple examples for verified software development using Lean.
It is inspired by [human-eval-verus], which does a similar thing for the Verus Rust verification
platform.

## Contributions

Contributions are welcome! You can
[look at the open issues](https://github.com/TwoFX/human-eval-lean/issues) to see
which problems do not currently have a solution.

Feel free to add your thoughts about
a problem to the corresponding issue. A rough estimation of the difficulty is already
helpful; I will add the corresponding label to the issue.

PRs contributing new solutions to both unsolved and solved problems are welcome,
as are PRs improving the code of existing solutions. Golfing is welcome as long
as the resulting code can still be considered idiomatic.

We use the [Lean 4 standard library style guide and naming convention](https://github.com/leanprover/lean4/tree/master/doc/std),
but we won't be very strict about enforcing it.

One of the goals of the goals of this project is to assess the out-of-the-box
experience of Lean 4 as a software verification tool, so this project will not
take on dependencies such as Batteries.

[HumanEval]: https://github.com/openai/human-eval
[Lean 4]: https://lean-lang.org/
[human-eval-verus]: https://github.com/secure-foundations/human-eval-verus
