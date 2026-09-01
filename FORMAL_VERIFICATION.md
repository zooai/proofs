# Zoo Formal Verification

89 Lean files stating properties of Zoo Network's critical systems, containing
595 theorems and lemmas, **116 axioms**, and 1 `sorry`.

**These are not machine-checked.** No prover runs in this repository's CI — the
one workflow deploys a website — and there is no build output here, so nothing
below has been confirmed by Lean rather than merely written in it. An earlier
version of this file called them "21 machine-checked proofs"; that was a
stronger claim than the repository supports, and a reader who cloned and ran
`lake build` would have discovered it before we did.

**Some headline properties are axioms, not theorems.** `Contract/AMM.lean`
appears in the table below as covering automated-market-maker solvency; the
property itself, `swap_preserves_invariant`, is declared with `axiom` and its
own comment says "stated as an axiom pending full mechanisation". An axiom is
an assumption. Assuming the property you set out to prove is a legitimate step
while the mechanisation is in progress, and it is not a proof of it.

What this corpus is worth is real: 595 stated theorems is a specification of
intended behaviour precise enough for a prover to check, which almost nothing
in this industry has. What it is not yet is checked. The distinction is the
whole value of the exercise, so this document states it first.

Two things would change that, in order: run `lake build` in CI so the file
fails when the proofs do, then discharge the axioms — starting with the ones
named in tables as though they were results.

## Inventory

### Lean 4

**AI Systems:**
| Proof | Property |
|-------|----------|
| `AI/DSO.lean` | Decentralized Semantic Optimization convergence and safety |
| `AI/Embedding.lean` | Embedding space metric properties |
| `AI/ExperienceLedger.lean` | Experience ledger Byzantine fault tolerance |
| `AI/Gym.lean` | Training platform correctness |
| `AI/Personalization.lean` | Privacy guarantees for personalization |

**Smart Contracts:**
| Proof | Property |
|-------|----------|
| `Contract/AMM.lean` | Automated Market Maker solvency invariants |
| `Contract/Bridge.lean` | Cross-chain bridge safety |
| `Contract/Staking.lean` | Staking mechanism security |
| `Contract/Token.lean` | Token contract properties |

**Governance:**
| Proof | Property |
|-------|----------|
| `Governance/AgentNFT.lean` | Agent ownership and transfer |
| `Governance/Compensation.lean` | Reward distribution fairness |
| `Governance/Contribution.lean` | Contribution tracking integrity |
| `Governance/Treasury.lean` | Treasury management invariants |
| `Governance/ZIP.lean` | Proposal mechanism correctness |

### TLA+ (2 specs)

| Spec | Property |
|------|----------|
| `tla/Wave.tla` | Protocol wave behavior |
| `tla/MC_Wave.tla` | Model checker configuration |

### Halmos (4 symbolic tests)

| Test | Property |
|------|----------|
| `halmos/AMMInvariant.t.sol` | AMM solvency under all inputs |
| `halmos/LiquidSolvency.t.sol` | Liquidity protocol solvency |
| `halmos/MarketsSolvency.t.sol` | Market solvency properties |
| `halmos/test/FHEInvariant.t.sol` | FHE noise budget invariants |

### Tamarin (1 protocol proof)

| Proof | Property |
|-------|----------|
| `tamarin/RNSHybridHandshake.spthy` | RNS hybrid handshake security |

### Property-Based Testing (Go)

| Test | Property |
|------|----------|
| `property/fhe_noise_test.go` | FHE noise growth bounds |

## Build

```bash
# Lean 4
cd lean && lake build

# Halmos
halmos --contract AMMInvariant

# TLA+
tlc MC_Wave.tla

# Tamarin
tamarin-prover RNSHybridHandshake.spthy
```

## Authors

Antje Worring & Zoo Labs Foundation — Zoo Labs Foundation

## Links

- https://zoo.ngo/research#proofs
- https://github.com/zooai/formal
