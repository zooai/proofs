# Zoo Formal Verification

21 machine-checked proofs for Zoo Network's critical systems.

## Proof Inventory

### Lean 4 (14 proofs)

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

Antje Worring & Zach Kelling — Zoo Labs Foundation

## Links

- https://zoo.ngo/research#proofs
- https://github.com/zooai/formal
