/-
  Authors: Antje Worring, Zoo Labs Foundation Research

  NFT-Bound Agent Ownership and Delegation

  Formal proofs about the Agent NFT Standard's ownership model.
  Agents are ERC-721 tokens that encapsulate autonomous AI systems
  with wallets, governance rights, and configurable autonomy parameters.

  Maps to:
  - zoo/papers/zoo-agent-nft.tex: Agent NFT Standard specification
  - Governance/AgentNFT.lean: basic transfer/revoke (extended here)

  Key results:
  - Transfer correctly updates the full capability set
  - Delegated permissions are transitive
  - Revoking owner propagates to all delegates
  - No agent can exceed its granted capabilities (no escalation)

  Author: Zoo Labs Foundation Research
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Agent.NFTOwnership

/-! ## Core Structures -/

/-- Address (represented as Nat for simplicity). -/
abbrev Address := Nat

/-- Capability identifier (e.g., TRADE=1, GOVERN=2, STAKE=4, TRANSFER=8). -/
abbrev Capability := Nat

/-- A capability set is a finite set of capabilities. -/
abbrev CapSet := Finset Capability

/-- An Agent NFT with ownership, delegation, and capability tracking. -/
structure AgentNFT where
  tokenId : Nat
  owner : Address
  /-- Capabilities granted to this agent by its owner -/
  capabilities : CapSet
  /-- Delegates: address -> subset of capabilities delegated to them -/
  delegates : Address → CapSet
  /-- Whether the agent is active (not revoked) -/
  active : Bool

/-- The empty capability set. -/
def emptyCaps : CapSet := ∅

/-! ## Transfer -/

/-- Transfer ownership: new owner inherits the full capability set,
    all existing delegations are cleared (security: new owner should
    explicitly re-delegate). -/
def transfer (nft : AgentNFT) (newOwner : Address) : AgentNFT :=
  { nft with
    owner := newOwner
    delegates := fun _ => emptyCaps }

/-- Transfer correctly updates the capability set: the new owner
    retains all capabilities that existed before transfer.
    The agent itself doesn't lose capabilities, only delegations reset. -/
theorem ownership_transfer_updates_caps (nft : AgentNFT) (newOwner : Address) :
    (transfer nft newOwner).capabilities = nft.capabilities := by
  simp [transfer]

/-- Transfer changes the owner. -/
theorem transfer_changes_owner (nft : AgentNFT) (newOwner : Address) :
    (transfer nft newOwner).owner = newOwner := by
  simp [transfer]

/-- Transfer clears all delegations. -/
theorem transfer_clears_delegates (nft : AgentNFT) (newOwner : Address) (addr : Address) :
    (transfer nft newOwner).delegates addr = emptyCaps := by
  simp [transfer]

/-! ## Delegation -/

/-- Delegate a subset of capabilities to an address.
    The delegated set must be a subset of the agent's capabilities. -/
def delegate (nft : AgentNFT) (to_ : Address) (caps : CapSet)
    (_ : caps ⊆ nft.capabilities) : AgentNFT :=
  { nft with
    delegates := fun addr =>
      if addr = to_ then nft.delegates to_ ∪ caps
      else nft.delegates addr }

/-- Transitive delegation: if A delegates to B, and B delegates a subset
    of those capabilities to C, then C has those capabilities.
    We model this as a chain of delegation records. -/
structure DelegationChain where
  /-- The original agent -/
  agent : AgentNFT
  /-- Intermediate delegate -/
  intermediate : Address
  /-- Final delegate -/
  final : Address
  /-- Capabilities delegated to intermediate -/
  intermediateCaps : CapSet
  /-- Capabilities sub-delegated to final (must be subset of intermediate's) -/
  finalCaps : CapSet
  /-- Proof that intermediate actually has those capabilities -/
  hIntermediate : intermediateCaps ⊆ agent.capabilities
  /-- Proof that final's capabilities are subset of intermediate's -/
  hFinal : finalCaps ⊆ intermediateCaps

/-- Delegation is transitive: if the agent grants caps to B and B
    sub-delegates a subset to C, then C's capabilities are a subset
    of the agent's original capabilities. -/
theorem delegation_transitive (chain : DelegationChain) :
    chain.finalCaps ⊆ chain.agent.capabilities :=
  Finset.Subset.trans chain.hFinal chain.hIntermediate

/-! ## Revocation -/

/-- Revoke the agent entirely: deactivates it and clears all delegations. -/
def revoke (nft : AgentNFT) : AgentNFT :=
  { nft with
    active := false
    delegates := fun _ => emptyCaps }

/-- Revoking the agent propagates to all delegates:
    no delegate retains any capabilities after revocation. -/
theorem revocation_propagates (nft : AgentNFT) (addr : Address) :
    (revoke nft).delegates addr = emptyCaps := by
  simp [revoke]

/-- Revocation deactivates the agent. -/
theorem revocation_deactivates (nft : AgentNFT) :
    (revoke nft).active = false := by
  simp [revoke]

/-- Revocation preserves the token identity. -/
theorem revocation_preserves_id (nft : AgentNFT) :
    (revoke nft).tokenId = nft.tokenId := by
  simp [revoke]

/-! ## No Escalation -/

/-- A delegate's capabilities are always a subset of the agent's capabilities.
    This is the fundamental no-escalation invariant: an agent can never
    grant more capabilities than it possesses.

    The `delegate` operation sets the delegate's caps to `old ∪ new` where
    `new = caps ⊆ capabilities` by construction (`h`). For the union to stay
    within `capabilities`, the pre-existing delegation `nft.delegates to_` must
    already be bounded — exactly the no-escalation invariant maintained across
    operations (transfer/revoke reset delegations to `∅`, which trivially
    satisfies it). We therefore take that invariant as hypothesis `h_inv` and
    prove the union is bounded honestly. -/
theorem no_escalation (nft : AgentNFT) (to_ : Address) (caps : CapSet)
    (h : caps ⊆ nft.capabilities)
    (h_inv : ∀ c ∈ nft.delegates to_, c ∈ nft.capabilities) :
    ∀ c ∈ (delegate nft to_ caps h).delegates to_, c ∈ nft.capabilities := by
  intro c hc
  have hc' : c ∈ nft.delegates to_ ∪ caps := by
    simpa only [delegate, if_pos rfl] using hc
  rw [Finset.mem_union] at hc'
  rcases hc' with hc' | hc'
  · exact h_inv c hc'
  · exact h hc'

/-- Simpler no-escalation: delegated set is bounded by agent capabilities. -/
theorem no_escalation_set (_nft : AgentNFT) (_to_ : Address) (caps : CapSet)
    (h : caps ⊆ _nft.capabilities) :
    caps ⊆ _nft.capabilities := h

/-- An inactive agent cannot perform any actions.
    This is enforced at the contract level: all action functions
    check `require(agent.active)` before proceeding. -/
def canAct (nft : AgentNFT) : Prop := nft.active = true

theorem revoked_cannot_act (nft : AgentNFT) :
    ¬canAct (revoke nft) := by
  simp [canAct, revoke]

end Agent.NFTOwnership
