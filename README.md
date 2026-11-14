# Verifier smoke case: 3-SAT, `control`

Maintainer smoke case of the `3sat` profile of https://github.com/bigospeedrun/verifier
(see the `main` branch README). Test data, not a claim and not a submission.

This branch: the statement copy, Race.bound by sorry (must fail on sorryAx; with bound 3/5 it must fail at compare). The verifier must refuse it.

`Submission/SubexponentialSATDefinitions.lean` is OpenAI's lines 1 to 128 of
`lean/ComparatorChallenges/SubexponentialSAT.lean` at openai/math `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`
(Apache-2.0, LICENSE), unchanged.
`Submission/ThreeSatStatement.lean` is the verifier's `challenges/3sat/Statement.lean` with its import renamed.
