# Provenance and claim discipline

- Candidate source: S. I. Dimitrov, https://arxiv.org/abs/2606.12484
- Source version initially examined: arXiv:2606.12484v1, submitted 10 June 2026 UTC.
- Source PDF retrieved from `https://arxiv.org/pdf/2606.12484v1` on 8 August
  2026: 241,249 bytes, SHA-256
  `125e2ede391f828555aa3dd2a191f668c0eb3d336437e73e89958c8c8274b259`.
- The displayed target and the following `k=2,3` remark occur on PDF page 3.
- Candidate target: Conjecture 1, for integers `n ≥ 2` and `k ≥ 1`.
- Discovery date for this independent argument: 8 August 2026.
- Human requester: Michael Mazur.
- AI assistance: OpenAI Codex generated and tested the mathematical reduction,
  researched the literature, and developed the Lean formalization.
- The theorem statement and completed Lean proof have received a separate
  AI-assisted formal audit. Historical priority still requires confirmation from the author
  and an independent number theorist before any public "first proof" claim.

The proof strategy uses the elementary bounds
`φ(n) ≤ n - 1`, `ψ(n) ≥ n + 1`, and `σ(n) ≥ n + 1`, followed by a normalized
three-variable inequality over the real numbers. Its algebraic engine is a
ratio-constrained corollary of the classical Lagrange identity; no novelty is
claimed for that identity or technique.

The Lean definition of `ψ` is the same canonical prime-factor product displayed
in the source, not an unproved alternate characterization.
