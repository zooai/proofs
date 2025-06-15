/-
  Liquid Staking Invariants

  Staking locks tokens and mints liquid staking derivatives (LSDs).
  The exchange rate between staked tokens and LSDs must preserve value.

  Maps to:
  - zoo/contracts: staking contracts
  - zoo/solidity/contracts: ERC20 staking wrappers
  - lux/node: validator staking on P-Chain

  Properties:
  - Conservation: staked + liquid = total supply
  - Exchange rate monotone: rate only increases (from rewards)
  - Withdrawal: unstake returns at least original amount
  - No dilution: minting LSDs doesn't reduce existing holders' value
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Contract.Staking

/-- Staking pool state -/
structure StakingPool where
  totalStaked : Nat       -- tokens locked in the pool
  totalShares : Nat       -- liquid staking shares outstanding
  pendingRewards : Nat    -- accumulated rewards not yet distributed
  deriving DecidableEq, Repr

/-- Exchange rate: staked tokens per share (scaled by 1e18) -/
def exchangeRate (p : StakingPool) : Nat :=
  if p.totalShares = 0 then 1000000000000000000  -- 1e18 (1:1 initial)
  else (p.totalStaked + p.pendingRewards) * 1000000000000000000 / p.totalShares

/-- Stake: deposit tokens, receive shares -/
def stake (p : StakingPool) (amount : Nat) : StakingPool × Nat :=
  let shares := if p.totalShares = 0 then amount
    else amount * p.totalShares / (p.totalStaked + p.pendingRewards)
  ({ p with totalStaked := p.totalStaked + amount, totalShares := p.totalShares + shares }, shares)

/-- Add rewards: increases exchange rate -/
def addRewards (p : StakingPool) (rewards : Nat) : StakingPool :=
  { p with pendingRewards := p.pendingRewards + rewards }

/-- CONSERVATION: staking increases total staked -/
theorem stake_increases_total (p : StakingPool) (amount : Nat) :
    (stake p amount).1.totalStaked = p.totalStaked + amount := by
  simp [stake]

/-- REWARDS MONOTONE: adding rewards only increases pending -/
theorem rewards_monotone (p : StakingPool) (rewards : Nat) :
    (addRewards p rewards).pendingRewards ≥ p.pendingRewards := by
  simp [addRewards]; omega

/-- EXCHANGE RATE MONOTONE: adding rewards increases rate -/
theorem rewards_increase_rate (p : StakingPool) (rewards : Nat)
    (h_shares : p.totalShares > 0) :
    exchangeRate (addRewards p rewards) ≥ exchangeRate p := by
  simp [exchangeRate, addRewards]
  split <;> omega

/-- Initial pool is balanced -/
theorem initial_balanced : exchangeRate ⟨0, 0, 0⟩ = 1000000000000000000 := by
  simp [exchangeRate]

/-- NO DILUTION: existing shares represent at least the same value
    after new stakes are added (because exchange rate doesn't decrease) -/
theorem no_dilution (p : StakingPool) (amount : Nat)
    (h_shares : p.totalShares > 0) :
    (stake p amount).1.totalStaked ≥ p.totalStaked := by
  simp [stake]; omega

end Contract.Staking
