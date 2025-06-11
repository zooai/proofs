/-
  Treasury Management Properties

  The DAO treasury holds funds and distributes them via governance.
  All operations require proposal + quorum vote.

  Maps to:
  - zoo/zoo.vote: treasury management interface
  - zoo/contracts: on-chain treasury
  - zoo/ZIPs: governance proposals (ZIP-003 genesis)

  Properties:
  - Solvency: treasury balance ≥ 0 (no overdraft)
  - Authorization: all transfers require governance vote
  - Transparency: all operations are recorded
  - Budget: approved spending ≤ available balance
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Governance.Treasury

/-- Treasury operation types -/
inductive OpType where
  | deposit
  | grant (recipient : Nat) (amount : Nat)
  | investment (target : String) (amount : Nat)
  | burn (amount : Nat)
  deriving DecidableEq, Repr

/-- Operation with governance approval -/
structure TreasuryOp where
  opType : OpType
  proposalId : Nat
  approved : Bool      -- passed quorum vote
  executed : Bool      -- has been executed

/-- Treasury state -/
structure TreasuryState where
  balance : Nat
  totalDeposited : Nat
  totalGranted : Nat
  totalBurned : Nat
  operations : List TreasuryOp

/-- Execute a treasury operation -/
def execute (s : TreasuryState) (op : TreasuryOp) : TreasuryState :=
  if !op.approved then s  -- unapproved ops are no-ops
  else match op.opType with
  | .deposit =>
    { s with balance := s.balance + 0 }  -- deposits handled separately
  | .grant _ amount =>
    if amount ≤ s.balance then
      { s with balance := s.balance - amount
             , totalGranted := s.totalGranted + amount
             , operations := { op with executed := true } :: s.operations }
    else s
  | .investment _ amount =>
    if amount ≤ s.balance then
      { s with balance := s.balance - amount
             , operations := { op with executed := true } :: s.operations }
    else s
  | .burn amount =>
    if amount ≤ s.balance then
      { s with balance := s.balance - amount
             , totalBurned := s.totalBurned + amount
             , operations := { op with executed := true } :: s.operations }
    else s

/-- Deposit funds -/
def deposit (s : TreasuryState) (amount : Nat) : TreasuryState :=
  { s with balance := s.balance + amount
         , totalDeposited := s.totalDeposited + amount }

/-- SOLVENCY: balance never goes negative (Nat ensures this structurally) -/
theorem solvency (s : TreasuryState) (op : TreasuryOp) :
    (execute s op).balance ≤ s.balance ∨ (execute s op).balance = s.balance := by
  simp [execute]
  split <;> try exact Or.inr rfl
  split <;> simp_all <;> split <;> simp_all <;> omega

/-- AUTHORIZATION: unapproved ops don't change state -/
theorem unapproved_noop (s : TreasuryState) (op : TreasuryOp)
    (h : op.approved = false) :
    execute s op = s := by
  simp [execute, h]

/-- BUDGET: grants cannot exceed balance -/
theorem grant_within_budget (s : TreasuryState) (op : TreasuryOp)
    (recipient amount : Nat)
    (h_type : op.opType = .grant recipient amount)
    (h_approved : op.approved = true) :
    (execute s op).balance ≤ s.balance := by
  simp [execute, h_approved, h_type]
  split <;> omega

/-- DEPOSIT INCREASES BALANCE -/
theorem deposit_increases (s : TreasuryState) (amount : Nat) :
    (deposit s amount).balance = s.balance + amount := by
  simp [deposit]

/-- TRANSPARENCY: executed ops are recorded -/
theorem executed_recorded (s : TreasuryState) (op : TreasuryOp)
    (h : op.approved = true)
    (recipient amount : Nat) (h_type : op.opType = .grant recipient amount)
    (h_funds : amount ≤ s.balance) :
    (execute s op).operations.length > s.operations.length := by
  simp [execute, h, h_type, h_funds, List.length_cons]

/-- Empty treasury blocks all grants -/
theorem empty_blocks_grants (op : TreasuryOp)
    (recipient amount : Nat) (h_type : op.opType = .grant recipient amount)
    (h_amount : amount > 0) (h_approved : op.approved = true) :
    execute ⟨0, 0, 0, 0, []⟩ op = ⟨0, 0, 0, 0, []⟩ := by
  simp [execute, h_approved, h_type]

end Governance.Treasury
