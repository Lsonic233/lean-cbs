# lean-cbs: Verified Capability-Based Security for LLM Agents

## Origin

This project was built during the **LeanLang for Verified
Autonomy Hackathon** (April 17–18 + online through May 1,
2026) at the **Indian Institute of Science (IISc),
Bangalore**.
Sponsored by **[Emergence AI](https://www.emergence.ai)**
Organized by **[Emergence India Labs]
(https://east.emergence.ai)** in collaboration with
**IISc Bangalore**.

A Lean 4 implementation of a formally verified access control layer for LLM agents.

Agent frameworks typically enforce access policies with runtime checks such as whitelists,
tool gating, system prompt instructions. These are fragile: a policy is only as strong
as the check that enforces it, and prompt injection can cause an LLM to violate its
own stated policy. This project takes a different approach.

Every action an agent wants to take must be backed by an unforgeable capability token
issued by an orchestrator. When an LLM emits a program as structured JSON, a
verifier checks that every action is backed by a real, issued capability and produces a
proof (`SafeProg env prog`). The interpreter (`CapM.runSafe`)
cannot be called without this proof.

The file `leancap-report.pdf` contains a full project report. 
## Structure

| File | Contents |
|------|----------|
| `LeanCbs/Core.lean` | `Cap`, `CapEnv`, `SafeProg`, `AllSafe`, `mono_wallet` |
| `LeanCbs/Runtime.lean` | `CapM` interpreter, `runSafe`, soundness theorems |
| `LeanCbs/Parser.lean` | Three-pass JSON parser and proof synthesizer |
| `Main.lean` | End-to-end demo including a prompt injection attack scenario |
| `Tests.lean` | Test suite: 5 suites covering basic ops, value binding, elaboration errors, wallet validity, and injection attacks |
| `MultiAgent.lean` | multi-agent extension, currently in progress| 
| `leancap-report.pdf` | Project report |

## Running

See [RUNNING.md](RUNNING.md) for build instructions, demo, and test suite usage.

## Acknowledgments
This project was made possible by:
- **Emergence AI** — Hackathon sponsor
- **Emergence India Labs** — Event organizer and
research direction
- **Indian Institute of Science (IISc), Bangalore** —
Academic partner, hackathon co-design, tutorials,
and mentorship

## Links
- [Hackathon Page](https://east.emergence.ai/
hackathon-april2026.html)
- [Emergence India Labs](https://east.emergence.ai)
- [Emergence AI](https://www.emergence.ai)
