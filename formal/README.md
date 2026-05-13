# Lux Formal Verification

Machine-checked proofs for the Lux consensus stack and Solidity contract invariants.

## Structure

```
formal/
├── lean/                        # Lean 4 proofs (consensus + crypto)
│   ├── lakefile.lean            # Project config
│   ├── Consensus/               # Core consensus properties
│   │   ├── Safety.lean          # No two honest nodes finalize conflicting values
│   │   ├── Liveness.lean        # Progress under partial synchrony
│   │   └── BFT.lean             # f < n/3 threshold sufficiency
│   ├── Protocol/                # Per-protocol proofs
│   │   ├── Wave.lean            # Threshold voting + FPC convergence
│   │   ├── Flare.lean           # DAG cert/skip 2f+1 correctness
│   │   ├── Ray.lean             # Linear chain finality
│   │   ├── Field.lean           # DAG consensus driver
│   │   ├── Quasar.lean          # BLS+Ringtail hybrid aggregation
│   │   ├── Nova.lean            # Linear mode wrapping Ray
│   │   ├── Nebula.lean          # DAG mode wrapping Field
│   │   ├── Photon.lean          # Committee selection uniformity
│   │   └── Prism.lean           # Peer sampling unbiasedness
│   ├── Crypto/                  # Post-quantum crypto proofs
│   │   ├── Ringtail.lean        # Threshold lattice signature unforgeability
│   │   ├── MLDSA.lean           # ML-DSA correctness
│   │   ├── FROST.lean           # Schnorr threshold unforgeability
│   │   └── BLS.lean             # BLS aggregation correctness
│   └── Warp/                    # Cross-chain messaging proofs
│       ├── Delivery.lean        # Exactly-once delivery
│       └── Ordering.lean        # Causal ordering preservation
├── halmos/                      # Symbolic execution tests (Solidity)
│   ├── LiquidSolvency.t.sol    # xLUX shares <= underlying LUX
│   ├── AMMInvariant.t.sol       # x*y=k for V2, liquidity for V3
│   └── MarketsSolvency.t.sol    # Lending: borrows <= deposits
└── README.md
```

## Lean 4 Proofs

### What We Prove

**Core Consensus (Safety + Liveness + BFT)**

The three pillars. Every consensus protocol must satisfy all three or it is not a consensus protocol.

| Property | Statement | File |
|----------|-----------|------|
| Safety | If honest node A finalizes value v at height h, no honest node B finalizes v' != v at height h | `Safety.lean` |
| Liveness | If all honest nodes propose, eventually some value is finalized | `Liveness.lean` |
| BFT Threshold | Safety and liveness hold when f < n/3 nodes are Byzantine | `BFT.lean` |

**Per-Protocol**

| Protocol | Property | File |
|----------|----------|------|
| Wave | Threshold voting converges: if alpha fraction prefer v for beta consecutive rounds, v is decided | `Wave.lean` |
| Wave/FPC | PRF-selected theta produces alpha in [theta_min*k, theta_max*k] | `Wave.lean` |
| Flare | Certificate requires 2f+1 support; skip requires 2f+1 non-support; exactly one of {cert, skip, undecided} | `Flare.lean` |
| Ray | Linear chain: decided items form a total order consistent with Source ordering | `Ray.lean` |
| Field | DAG driver: committed prefix is a consistent cut of the DAG | `Field.lean` |
| Quasar | BLS aggregation: aggregated signature verifies iff all individual signatures verify | `Quasar.lean` |
| Photon | Committee selection is uniform over validator set | `Photon.lean` |
| Prism | Fisher-Yates sampling produces unbiased k-subsets | `Prism.lean` |

**Cryptography**

| Primitive | Property | File |
|-----------|----------|------|
| BLS | Aggregation correctness + rogue key attack resistance | `BLS.lean` |
| FROST | t-of-n threshold unforgeability in random oracle model | `FROST.lean` |
| Ringtail | LWE-based threshold unforgeability (post-quantum) | `Ringtail.lean` |
| ML-DSA | FIPS 204 signature correctness | `MLDSA.lean` |

**Cross-Chain (Warp)**

| Property | Statement | File |
|----------|-----------|------|
| Exactly-once | A valid Warp message is processed exactly once on destination | `Delivery.lean` |
| Causal ordering | If message A causally precedes B on source, A is processed before B on destination | `Ordering.lean` |

### Build

```bash
cd lean/
lake build
```

Requires Lean 4 toolchain (elan). Install: `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh`

## Halmos Symbolic Tests

Symbolic execution over Lux Standard Solidity contracts. These are not fuzz tests. Halmos explores all reachable states symbolically.

| Test | Invariant | Contract |
|------|-----------|----------|
| LiquidSolvency | totalAssets >= totalSupply * minSharePrice | LiquidLUX.sol |
| AMMInvariant | reserve0 * reserve1 >= k (before fees) | AMMV2Pair.sol |
| MarketsSolvency | sum(borrows) <= sum(deposits) for each market | Markets.sol |

### Run

```bash
pip install halmos
cd halmos/
halmos --contract LiquidSolvencyTest
halmos --contract AMMInvariantTest
halmos --contract MarketsSolvencyTest
```

## Methodology

1. Model the Go protocol as a Lean state machine (states, transitions, invariants)
2. Prove invariants hold across all transitions (induction on steps)
3. Do not model network -- assume adversarial scheduler with f < n/3 Byzantine nodes
4. Crypto proofs assume standard hardness (DLP, LWE) -- we prove protocol correctness, not cryptographic hardness
5. Halmos tests target economic invariants (solvency, conservation) not functional correctness (covered by Foundry)
