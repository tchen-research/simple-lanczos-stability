# A simple stability analysis of Lanczos in finite precision


## Lean formalization

The `lean` directory contains an annotated lean 4 verification of the results in the paper. 
The analysis is explicit, keep track of constants and powers supressed in the paper.
No attempt has been made to optimize the constants or powers.
Various LLMs were used to generate the verification.

## Lean audit

The `lean_audit` directory contains the outputs of an an independent LLM audit of the lean code.
The audit consited of:
- generating a human readable statement from the lean code (`verified_statements.pdf`), and 
- by directly checking the lean code against the paper's tex source (`body_lean_consistency_report.pdf`).


```
model: gpt-5.6-sol xhigh

> remove all comments from the lean code

> \new

> Create a human-readable PDF of the statements that are verified in this lean project. The document should be written as if it would be submitted to a numerical analysis journal. Make it clear what assumptions are used throughout.  A human expert will then compare this document against a human-written draft to ensure the lean code proves what is claimed.

> \new

> Check that the statements claimed in body.tex match the verified statements from the lean code. Return a pdf report.
```

Additional editorial changes were made to the final paper. The version of the paper's source we used in the audit is saved as `body.tex`.

## Numerical experiment

The code to replicate the figures can be found in the `experiment` directory
