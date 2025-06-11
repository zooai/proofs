/-
  ERC20 Token Invariants

  Transfer preserves total supply. Balance cannot go negative.
  Approve/transferFrom authorization check.

  Maps to:
  - zoo/solidity/contracts/ERC20.sol
  - zoo/contracts/src/ZooBridgeToken.sol (inherits ERC20)

  Properties:
  - Total supply conservation on transfer
  - No negative balances
  - TransferFrom requires sufficient allowance
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Contract.Token

/-- Token state: balances and allowances -/
structure TokenState where
  balances : Nat → Nat       -- address → balance
  allowances : Nat → Nat → Nat  -- owner → spender → allowance
  totalSupply : Nat

/-- Transfer: move tokens between accounts -/
def transfer (s : TokenState) (from_ to_ amount : Nat) : Option TokenState :=
  if s.balances from_ ≥ amount then
    some {
      balances := fun addr =>
        if addr = from_ then s.balances from_ - amount
        else if addr = to_ then s.balances to_ + amount
        else s.balances addr
      allowances := s.allowances
      totalSupply := s.totalSupply
    }
  else none

/-- Insufficient balance ⟹ transfer fails -/
theorem insufficient_balance_fails (s : TokenState) (from_ to_ amount : Nat)
    (h : s.balances from_ < amount) :
    transfer s from_ to_ amount = none := by
  simp [transfer, Nat.not_le.mpr h]

/-- TOTAL SUPPLY CONSERVATION: transfer doesn't change total supply -/
theorem transfer_preserves_supply (s s' : TokenState) (from_ to_ amount : Nat)
    (h : transfer s from_ to_ amount = some s')
    (h_diff : from_ ≠ to_) :
    s'.totalSupply = s.totalSupply := by
  simp [transfer] at h
  split at h <;> simp_all

/-- TransferFrom: requires allowance -/
def transferFrom (s : TokenState) (owner spender to_ amount : Nat) : Option TokenState :=
  if s.allowances owner spender ≥ amount && s.balances owner ≥ amount then
    some {
      balances := fun addr =>
        if addr = owner then s.balances owner - amount
        else if addr = to_ then s.balances to_ + amount
        else s.balances addr
      allowances := fun o sp =>
        if o = owner && sp = spender then s.allowances owner spender - amount
        else s.allowances o sp
      totalSupply := s.totalSupply
    }
  else none

/-- Insufficient allowance ⟹ transferFrom fails -/
theorem insufficient_allowance_fails (s : TokenState) (owner spender to_ amount : Nat)
    (h : s.allowances owner spender < amount) :
    transferFrom s owner spender to_ amount = none := by
  simp [transferFrom, Nat.not_le.mpr h]

end Contract.Token
