# Zoo Formal Proofs

Machine-checked and paper proofs for the Zoo Labs Foundation stack:
per-LLM training chains, the original 2021 NFT Liquidity Protocol,
homomorphic-DAO governance, and the 2026 adoption of Liquidity.io's
Liquidity Protocol.

## Provenance

- 2021-10: Zoo whitepaper (Worring & Kelling) coined "NFT Liquidity Protocol"
  for collateral-backed NFT lending. See `~/work/zoo/papers/zoo-2021-original-whitepaper/`.
- 2025: Zoo Securities & DAO paper.
  See `~/work/zoo/papers/zoo-2025-securities-and-dao/`.
- 2026-04-20: Zoo formally adopts Liquidity.io's Liquidity Protocol
  with explicit name disambiguation; the 2021 trade-name remains valid.

## Inventory

| File | Topic | Status |
|---|---|---|
| `zoo-per-llm-chain-soundness.tex` | per-LLM training chain: deterministic gradient ordering, attribution, reproducibility | paper |
| `zoo-nft-liquidity-protocol-soundness.tex` | 2021 NFT-LP: lending atomicity, sustainability tax flow, marketplace settlement | paper |
| `zoo-dao-governance-soundness.tex` | Homomorphic / holographic-consensus DAO: weighted voting, FHE-tallied secrecy, anti-Sybil | paper |
| `zoo-adopts-liquidity-protocol.tex` | 2026-04-20 adoption with composition theorem and trade-name disambiguation | paper |
| `lean/` | Lean 4 sources (shared with `luxfi/proofs/lean/`) | typecheck |

## Build

```bash
cd lean && lake build
tectonic zoo-per-llm-chain-soundness.tex
tectonic zoo-nft-liquidity-protocol-soundness.tex
tectonic zoo-dao-governance-soundness.tex
tectonic zoo-adopts-liquidity-protocol.tex
```

## ZIP cross-references

See `~/work/zoo/zips/INDEX.md` "Formal Proofs" section.

| ZIP | Proof |
|---|---|
| ZIP-0103 (NFT-LP) | `zoo-nft-liquidity-protocol-soundness.tex` |
| ZIP-0206 (Collateral-Backed NFTs) | `zoo-nft-liquidity-protocol-soundness.tex` |
| ZIP-0400-0418 (AI Assistant + per-LLM chains) | `zoo-per-llm-chain-soundness.tex` |
| ZIP-0500-0570 (Sustainability + DAO) | `zoo-dao-governance-soundness.tex` |
| ZIP-0103 / ZIP-0206 (composition with Liquidity Protocol) | `zoo-adopts-liquidity-protocol.tex` |

## Chronology

See `CHRONOLOGY.md`.
