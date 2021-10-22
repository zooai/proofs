import Lake
open Lake DSL

package zooFormal where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

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

lean_lib Consensus where
  srcDir := "."
  roots := #[
    `Consensus.PoAI
  ]

lean_lib Token where
  srcDir := "."
  roots := #[
    `Token.ExperienceLedger
  ]

lean_lib DeFi where
  srcDir := "."
  roots := #[
    `DeFi.ImpactBonds,
    `DeFi.CarbonCredits
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

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"
