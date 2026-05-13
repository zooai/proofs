import Lake
open Lake DSL

package luxFormal where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Consensus where
  srcDir := "."
  roots := #[
    `Consensus.Safety,
    `Consensus.Liveness,
    `Consensus.BFT,
    `Consensus.Quasar,
    `Consensus.Finality,
    `Consensus.Validator,
    `Consensus.ThresholdProof,
    `Consensus.PreferenceStability
  ]

lean_lib Protocol where
  srcDir := "."
  roots := #[
    `Protocol.Wave,
    `Protocol.Flare,
    `Protocol.Ray,
    `Protocol.Field,
    `Protocol.Quasar,
    `Protocol.Nova,
    `Protocol.Nebula,
    `Protocol.Photon,
    `Protocol.Prism,
    `Protocol.Handshake
  ]

lean_lib Crypto where
  srcDir := "."
  roots := #[
    `Crypto.BLS,
    `Crypto.FROST,
    `Crypto.Ringtail,
    `Crypto.MLDSA,
    `Crypto.Hybrid,
    `Crypto.SLHDSA,
    `Crypto.MLKEM,
    `Crypto.FHE.TFHE,
    `Crypto.FHE.CKKS,
    `Crypto.Threshold.CGGMP21,
    `Crypto.Threshold.LSS,
    `Crypto.Threshold.Composition,
    `Crypto.VerkleTree
  ]

lean_lib Warp where
  srcDir := "."
  roots := #[
    `Warp.Delivery,
    `Warp.Ordering,
    `Warp.Security
  ]

lean_lib Trust where
  srcDir := "."
  roots := #[
    `Trust.Authority,
    `Trust.Vouch,
    `Trust.Revocation
  ]

lean_lib Build where
  srcDir := "."
  roots := #[
    `Build.Coeffect,
    `Build.Attestation,
    `Build.Ecosystem,
    `Build.Reproducibility
  ]

lean_lib Compute where
  srcDir := "."
  roots := #[
    `Compute.CrossChain
  ]

lean_lib DeFi where
  srcDir := "."
  roots := #[
    `DeFi.OrderBook,
    `DeFi.AMM,
    `DeFi.HFT,
    `DeFi.FeeModel,
    `DeFi.LiquidStaking,
    `DeFi.Router,
    `DeFi.FlashLoan,
    `DeFi.Governance
  ]

lean_lib Network where
  srcDir := "."
  roots := #[
    `Network.PeerDiscovery
  ]

lean_lib Bridge where
  srcDir := "."
  roots := #[
    `Bridge.Teleport
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"
