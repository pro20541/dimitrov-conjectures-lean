# Lean proofs of Dimitrov's Conjectures 1 and 3

This repository contains Lean 4 proofs of Conjectures 1 and 3 from
S. I. Dimitrov, *Lower bounds on expressions depending on the functions
phi(n), psi(n) and sigma(n), III* (arXiv:2606.12484v1).

The formalization proves both inequalities for every natural `k >= 1` and
`n >= 2`. It also proves that equality in each inequality holds exactly when
`n` is prime.

## Status and claim limits

The proofs compile with Lean and Mathlib v4.32.2 and have passed the checks
described in `VERIFICATION.md`. The four `sorry` terms in `Challenge.lean` are
intentional placeholders in Palomar's challenge/solution format; the
substantive development and `Solution.lean` contain no `sorry` or custom axiom.

Machine verification establishes that the stated results follow from the
listed foundations. It does not establish historical novelty. Searches have
not located an earlier full-range proof, but priority has not been confirmed by
the source author or an independent expert. This repository therefore does not
claim a first proof.

OpenAI Codex performed the substantive target selection, proof discovery,
literature searching, Lean formalization, and documentation under Michael
Mazur's direction. Michael Mazur maintains the repository. See
`formalization.yaml`, `PROVENANCE.md`, and `Conjecture3/PROVENANCE.md` for the
complete attribution and review status.

## Palomar submission surface

- `Challenge.lean` contains the four source-facing theorem statements.
- `Solution.lean` contains the corresponding proved declarations.
- `comparator.json` is the exact four-theorem comparison contract.
- `formalization.yaml` records sources, authorship, AI use, fidelity, and
  review status.
- `FrontierMathLean/` contains the complete supporting proof development.

## Reproduce the Lean checks

```text
lake exe cache get
lake build
lake env lean --trust=0 Solution.lean
lake env leanchecker Solution
```

The GitHub Actions workflow additionally runs placeholder checks, Comparator,
and an independent NanoDa replay. The project is licensed under Apache-2.0.
