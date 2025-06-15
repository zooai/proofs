import Lake
open Lake DSL

package zooFormal where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Zoo-native proofs (AI, agents, ecology, governance)

@[default_target]
lean_lib Contract where
  srcDir := "."
  roots := #[
    `Contract.Bridge,
    `Contract.Token,
    `Contract.Staking,
    `Contract.AMM
  ]

lean_lib Governance where
  srcDir := "."
  roots := #[
    `Governance.ZIP,
    `Governance.Contribution,
    `Governance.Compensation,
    `Governance.Treasury,
    `Governance.AgentNFT,
    `Governance.DSO
  ]

lean_lib AI where
  srcDir := "."
  roots := #[
    `AI.DSO,
    `AI.ExperienceLedger,
    `AI.Gym,
    `AI.Personalization,
    `AI.Embedding,
    `AI.FederatedWildlife,
    `AI.SpeciesClassification
  ]

lean_lib Agent where
  srcDir := "."
  roots := #[
    `Agent.GRPO,
    `Agent.NFTOwnership,
    `Agent.Gym,
    `Agent.EBM,
    `Agent.LogicAgent,
    `Agent.FunctionalAgent,
    `Agent.DeltaSoup,
    `Agent.RewardShaping
  ]

lean_lib Token where
  srcDir := "."
  roots := #[
    `Token.ExperienceLedger
  ]

lean_lib Data where
  srcDir := "."
  roots := #[
    `Data.Commons
  ]

lean_lib Ecology where
  srcDir := "."
  roots := #[
    `Ecology.Satellite
  ]

-- Infrastructure proofs (from Lux — shared L1 foundation)

lean_lib Consensus where
  srcDir := "."
  roots := #[
    `Consensus.PoAI,
    `Consensus.BFT,
    `Consensus.Safety,
    `Consensus.Liveness,
    `Consensus.Finality,
    `Consensus.Validator,
    `Consensus.Quasar
  ]

lean_lib Crypto where
  srcDir := "."
  roots := #[
    `Crypto.BLS,
    `Crypto.FROST,
    `Crypto.Hybrid,
    `Crypto.MLDSA,
    `Crypto.MLKEM,
    `Crypto.Ringtail,
    `Crypto.SLHDSA,
    `Crypto.VerkleTree,
    `Crypto.FHE.CKKS,
    `Crypto.FHE.TFHE,
    `Crypto.Threshold.CGGMP21,
    `Crypto.Threshold.Composition,
    `Crypto.Threshold.LSS
  ]

lean_lib DeFi where
  srcDir := "."
  roots := #[
    `DeFi.AMM,
    `DeFi.ImpactBonds,
    `DeFi.CarbonCredits,
    `DeFi.FeeModel,
    `DeFi.FlashLoan,
    `DeFi.Governance,
    `DeFi.HFT,
    `DeFi.LiquidStaking,
    `DeFi.OrderBook,
    `DeFi.Router
  ]

lean_lib Bridge where
  srcDir := "."
  roots := #[
    `Bridge.Teleport
  ]

lean_lib Build where
  srcDir := "."
  roots := #[
    `Build.Attestation,
    `Build.Coeffect,
    `Build.Ecosystem,
    `Build.Reproducibility
  ]

lean_lib Compute where
  srcDir := "."
  roots := #[
    `Compute.CrossChain
  ]

lean_lib Network where
  srcDir := "."
  roots := #[
    `Network.PeerDiscovery
  ]

lean_lib Protocol where
  srcDir := "."
  roots := #[
    `Protocol.Field,
    `Protocol.Flare,
    `Protocol.Handshake,
    `Protocol.Nebula,
    `Protocol.Nova,
    `Protocol.Photon,
    `Protocol.Prism,
    `Protocol.Quasar,
    `Protocol.Ray,
    `Protocol.Wave
  ]

lean_lib Trust where
  srcDir := "."
  roots := #[
    `Trust.Authority,
    `Trust.Revocation,
    `Trust.Vouch
  ]

lean_lib Warp where
  srcDir := "."
  roots := #[
    `Warp.Delivery,
    `Warp.Ordering,
    `Warp.Security
  ]

lean_lib GPU where
  srcDir := "."
  roots := #[
    `GPU.EVMScaling,
    `GPU.FHEScaling,
    `GPU.ConsensusScaling,
    `GPU.DEXScaling
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"
