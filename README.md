# name-the-biggest-number

Name the biggest natural number you can. This is a Lean reboot of
[Cody Roux's original Rocq competition](https://github.com/codyroux/name-the-biggest-number),
whose precedent and rules we gratefully follow. The initial `0 → 42` ladder follows his too.

Submit a PR adding `contender_N : Nat` and a theorem
`contender_(N-1)_lt_contender_N : contender_(N-1) < contender_N` to `Contender.lean`.

- Contenders must be constructive and computable in principle: no Busy Beavers or the like.
- No `axiom` and no `sorry`. Mathlib is welcome.
- A definition should elaborate in 15 seconds and its proof in one minute on a reasonable machine.
- Do not define a contender using any previous `contender_*`. This is not checked automatically.
  Obviously no internet points for being lame.
- No shenanigans. Particularly good shenanigans may earn an honorable mention.

The project uses Lean and Mathlib v4.33.1. Build it with `lake build`.
