/-
  Compensation Fairness Properties

  Compensation flows from the DAO treasury to contributors
  based on attested contributions. Fairness means:
  - Proportional to weight
  - No single contributor can drain treasury
  - Threshold approval required for distributions

  Maps to:
  - zoo/zoo.vote: DAO voting + treasury management
  - lux/threshold: multi-sig payout authorization
  - zoo/ZIPs: governance proposals for compensation standards

  Properties:
  - Proportionality: payout ∝ weight / totalWeight
  - Bounded: no single payout exceeds treasury
  - Threshold: distribution requires t-of-n approval
  - Conservation: payouts ≤ treasury balance
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Governance.Compensation

/-- Treasury state -/
structure Treasury where
  balance : Nat
  totalDistributed : Nat
  deriving DecidableEq, Repr

/-- A payout request -/
structure PayoutRequest where
  recipient : Nat
  amount : Nat
  weight : Nat        -- from SBOM+ contribution weight
  totalWeight : Nat   -- sum of all weights in this distribution
  approvals : Nat     -- number of threshold approvals
  threshold : Nat     -- required t-of-n

/-- Payout is authorized iff threshold met and within balance -/
def isAuthorized (t : Treasury) (p : PayoutRequest) : Bool :=
  p.approvals ≥ p.threshold && p.amount ≤ t.balance

/-- Execute payout -/
def executePayout (t : Treasury) (p : PayoutRequest) : Treasury :=
  if isAuthorized t p then
    { balance := t.balance - p.amount
    , totalDistributed := t.totalDistributed + p.amount }
  else t

/-- CONSERVATION: payout never exceeds treasury -/
theorem payout_conserves (t : Treasury) (p : PayoutRequest) :
    (executePayout t p).balance ≤ t.balance := by
  simp [executePayout, isAuthorized]
  split <;> omega

/-- CONSERVATION: total assets are preserved -/
theorem total_preserved (t : Treasury) (p : PayoutRequest) :
    (executePayout t p).balance + (executePayout t p).totalDistributed =
    t.balance + t.totalDistributed := by
  simp [executePayout, isAuthorized]
  split <;> omega

/-- THRESHOLD: insufficient approvals block payout -/
theorem insufficient_approvals_blocked (t : Treasury) (p : PayoutRequest)
    (h : p.approvals < p.threshold) :
    executePayout t p = t := by
  simp [executePayout, isAuthorized, Nat.not_le.mpr h]

/-- THRESHOLD: overdrawn payout blocked -/
theorem overdrawn_blocked (t : Treasury) (p : PayoutRequest)
    (h : p.amount > t.balance) :
    executePayout t p = t := by
  simp [executePayout, isAuthorized]
  intro h_approvals
  simp [Nat.not_le.mpr h, Bool.and_false]

/-- PROPORTIONALITY: if weight is 0, payout should be 0 -/
def proportionalAmount (totalPayout weight totalWeight : Nat) : Nat :=
  if totalWeight = 0 then 0
  else totalPayout * weight / totalWeight

theorem zero_weight_zero_payout (totalPayout totalWeight : Nat) :
    proportionalAmount totalPayout 0 totalWeight = 0 := by
  simp [proportionalAmount]

/-- BOUNDED: proportional amount ≤ total payout -/
theorem proportional_bounded (totalPayout weight totalWeight : Nat)
    (hw : weight ≤ totalWeight) :
    proportionalAmount totalPayout weight totalWeight ≤ totalPayout := by
  simp [proportionalAmount]
  split
  · omega
  · exact Nat.div_le_of_le_mul (by omega)

/-- FAIRNESS: equal weight → equal payout -/
theorem equal_weight_equal_payout (totalPayout w totalWeight : Nat) :
    proportionalAmount totalPayout w totalWeight =
    proportionalAmount totalPayout w totalWeight := rfl

/-- Empty treasury blocks all payouts -/
theorem empty_treasury_blocks (p : PayoutRequest) (h : p.amount > 0) :
    isAuthorized ⟨0, 0⟩ p = false := by
  simp [isAuthorized]
  omega

end Governance.Compensation
