# lean-cordix

A formalization in Lean 4 of the formal core of:

> *A Programming Paradigm for Spatiotemporal Composability* — Yifan Shi,
> Wei Zhang, Tianyi Cui (Peking University, DeepSeek-AI).

[Paper](https://github.com/cordiverse/paper)

The active library is under `LeanCordix/`. The canonical full-context model
is split into flat modules `Basic`, `Step`, `Approx`, `Recovery`, and
`Trace`.

See [docs/design.md](docs/design.md) for the detailed design, proof
structure, theorem dependencies, and correspondence to the paper.

## Building

```
lake build
```
