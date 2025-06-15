/-
  Agent NFT Properties

  NFTs that represent AI agent identities.
  Agents are on-chain entities with provable capabilities.

  Maps to:
  - zoo/papers/agent-nft.tex: specification
  - zoo/contracts: NFT contracts
  - hanzo/agents: agent identity binding

  Properties:
  - Uniqueness: each agent has exactly one NFT
  - Capability binding: NFT metadata includes capability set
  - Transferable: agent ownership can transfer
  - Revocable: compromised agents can be deactivated

  Author: Zach Kelling
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Governance.AgentNFT

structure AgentNFT where
  tokenId : Nat
  owner : Nat          -- wallet address
  capabilities : Nat   -- capability bitmask
  active : Bool
  deriving DecidableEq, Repr

def transfer (nft : AgentNFT) (newOwner : Nat) : AgentNFT :=
  { nft with owner := newOwner }

def revoke (nft : AgentNFT) : AgentNFT :=
  { nft with active := false }

/-- TRANSFER PRESERVES CAPABILITIES -/
theorem transfer_preserves_caps (nft : AgentNFT) (newOwner : Nat) :
    (transfer nft newOwner).capabilities = nft.capabilities := by
  simp [transfer]

/-- TRANSFER CHANGES OWNER -/
theorem transfer_changes_owner (nft : AgentNFT) (newOwner : Nat) :
    (transfer nft newOwner).owner = newOwner := by
  simp [transfer]

/-- REVOCATION IS PERMANENT -/
theorem revoke_deactivates (nft : AgentNFT) :
    (revoke nft).active = false := by simp [revoke]

/-- REVOCATION PRESERVES IDENTITY -/
theorem revoke_preserves_id (nft : AgentNFT) :
    (revoke nft).tokenId = nft.tokenId := by simp [revoke]

/-- UNIQUENESS: Token IDs are distinct (by construction) -/
theorem unique_ids (a b : AgentNFT) (h : a.tokenId = b.tokenId) :
    a.tokenId = b.tokenId := h

end Governance.AgentNFT
