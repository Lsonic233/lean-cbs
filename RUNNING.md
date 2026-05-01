# Running lean-cbs

## Requirements

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- The correct Lean toolchain is pinned in `lean-toolchain` and will be fetched automatically by elan

## First build (downloads Mathlib cache — takes a few minutes once)

```
lake exe cache get
lake build
```

## Demo

Runs the full capability pipeline end-to-end: orchestrator issues caps, the
parser verifies LLM-emitted JSON programs, and the verified programs execute
via `CapM.runSafe`. Includes v1 value-binding (`let_read`) demos and a
prompt-injection attack scenario showing that injected JSON is rejected before
any IO occurs.

```
lake exe lean-cbs
```

## Test suite

Run all suites:
```
lake exe lean-cbs-tests
```

Run a single suite by name:
```
lake exe lean-cbs-tests basic
lake exe lean-cbs-tests v1
lake exe lean-cbs-tests elab
lake exe lean-cbs-tests wallet
lake exe lean-cbs-tests injection
```

| Suite name | What it covers |
|------------|---------------|
| `basic` | Basic read/write/delete operations |
| `v1` | `let_read` value binding, nested lets, seq inside let body |
| `elab` | Elaboration errors such as `unknownCap`, `authorityMismatch`, `unboundVar`, scope isolation |
| `wallet` | cap not in wallet |
| `injection` | fabricated cap names, authority misuse, full injected payload, file survival check |


Exit code is 0 on all-pass, 1 if any test fails.

<!-- ## What the verification guarantees

Every program that reaches `CapM.runSafe` carries a `SafeProg env prog` proof
certifying that:

1. Every capability token it uses is present in the orchestrator's wallet (`env.valid c`)
2. Each token is used with the correct authority (`.read` / `.write` / `.delete`)
3. The `AllSafe` soundness theorem (`SafeProg.allSafe`) closes off the `.error`
   branch of the interpreter at every step — not just the first — so a
   `CapError` is provably unreachable on any `SafeProg` program

An LLM-emitted program that references a cap the orchestrator never issued, or
uses a cap with the wrong authority, is rejected at `parseAndVerify` time —
before any IO is attempted. -->

