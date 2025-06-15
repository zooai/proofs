/-
  DAO Governance Properties

  Proposals require quorum to pass. Voting power comes from
  token balance. Single voter cannot exceed their balance.

  Maps to:
  - zoo/ZIPs: 707 governance proposals at zips.zoo.ngo
  - zoo/zoo.vote: DAO voting interface
  - zoo/contracts: governance contracts

  Properties:
  - Proposal passes iff votes ≥ quorum
  - Single voter bounded by balance
  - Quorum is monotone (more votes ⟹ closer to passing)
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Governance.ZIP

/-- Proposal state -/
structure Proposal where
  id : Nat
  votesFor : Nat
  votesAgainst : Nat
  quorum : Nat
  deadline : Nat

/-- A proposal passes iff votesFor ≥ quorum -/
def Proposal.passes (p : Proposal) : Bool :=
  p.votesFor ≥ p.quorum

/-- Cast a vote (bounded by voter's balance) -/
def vote (p : Proposal) (amount balance : Nat) (support : Bool) : Proposal :=
  let bounded := min amount balance
  if support then
    { p with votesFor := p.votesFor + bounded }
  else
    { p with votesAgainst := p.votesAgainst + bounded }

/-- QUORUM: Voting can only increase vote count -/
theorem vote_monotone_for (p : Proposal) (amount balance : Nat) :
    (vote p amount balance true).votesFor ≥ p.votesFor := by
  simp [vote]

/-- BOUNDED: Vote is bounded by balance -/
theorem vote_bounded_by_balance (p : Proposal) (amount balance : Nat) :
    (vote p amount balance true).votesFor ≤ p.votesFor + balance := by
  simp [vote]
  exact Nat.min_le_right amount balance

/-- QUORUM THRESHOLD: Enough votes ⟹ passes -/
theorem sufficient_votes_pass (p : Proposal)
    (h : p.votesFor ≥ p.quorum) :
    p.passes = true := by
  simp [Proposal.passes, h]

/-- QUORUM THRESHOLD: Insufficient votes ⟹ fails -/
theorem insufficient_votes_fail (p : Proposal)
    (h : p.votesFor < p.quorum) :
    p.passes = false := by
  simp [Proposal.passes, Nat.not_le.mpr h]

/-- Voting against doesn't affect pass condition -/
theorem against_irrelevant_to_pass (p : Proposal) (amount balance : Nat) :
    (vote p amount balance false).passes = p.passes := by
  simp [vote, Proposal.passes]

end Governance.ZIP
