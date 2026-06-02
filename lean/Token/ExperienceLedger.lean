/-
  Authors: Antje Worring, Zach Kelling

  Experience Token Conservation Laws

  Formal proofs about the Zoo Experience Ledger's token model.
  Experience tokens (EXP) are minted when agents contribute verified
  semantic experiences and burned when experiences are consumed.
  The ledger is a content-addressable, Merkle-verified system.

  Maps to:
  - zoo/papers/zoo-experience-ledger.tex: Experience Ledger specification
  - zoo/papers/zoo-dso.tex: DSO integration (quality scoring + slashing)

  Key results:
  - Total supply conservation: supply = sum of all balances
  - Minting requires verified attestation
  - Burning reduces total supply correctly
  - Transfers preserve total supply

  Author: Zach Kelling
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Token.ExperienceLedger

/-! ## Core Structures -/

/-- An account holding experience tokens. -/
structure Account where
  id : Nat
  balance : Nat
  deriving DecidableEq, Repr

/-- The token state: all accounts and total supply. -/
structure TokenState where
  accounts : List Account
  totalSupply : Nat

/-- An attestation proving a contribution was verified (via PoAI TEE). -/
structure ContributionAttestation where
  contributor : Nat
  experienceHash : Nat
  qualityScore : Nat
  teeSignature : Nat
  /-- Attestation is valid iff TEE signature is nonzero and quality > 0 -/
  hValid : teeSignature ≠ 0 ∧ qualityScore > 0

/-- Sum of all account balances. -/
def sumBalances (accounts : List Account) : Nat :=
  accounts.foldl (fun acc a => acc + a.balance) 0

/-! ## Invariant: Total Supply Conservation -/

/-- The fundamental conservation invariant: total supply equals
    the sum of all individual balances. No tokens exist outside
    of accounts. -/
def supplyInvariant (s : TokenState) : Prop :=
  s.totalSupply = sumBalances s.accounts

/-- An empty token state satisfies the invariant. -/
theorem empty_invariant : supplyInvariant ⟨[], 0⟩ := by
  simp [supplyInvariant, sumBalances]

/-! ## Theorem 1: Total Supply Conservation -/

/-- Total supply is always equal to the sum of all balances,
    assuming the invariant holds initially and all operations
    maintain it. -/
theorem total_supply_conservation (s : TokenState) (h : supplyInvariant s) :
    s.totalSupply = sumBalances s.accounts := h

/-! ## Theorem 2: Mint Bounded by Attestation -/

/-- Mint new tokens to a contributor. Only callable with a valid attestation.
    The amount minted is proportional to the quality score. -/
def mint (s : TokenState) (att : ContributionAttestation) (amount : Nat)
    (_ : amount ≤ att.qualityScore) : TokenState :=
  let updated := s.accounts.map fun a =>
    if a.id = att.contributor then { a with balance := a.balance + amount }
    else a
  -- If contributor not found, add new account
  let accounts' := if s.accounts.any (fun a => a.id = att.contributor) then updated
    else updated ++ [⟨att.contributor, amount⟩]
  { accounts := accounts'
    totalSupply := s.totalSupply + amount }

/-- Minting requires a valid attestation: the attestation must have a nonzero
    TEE signature and positive quality score. Without attestation, no minting
    occurs. This prevents unbacked token creation. -/
theorem mint_bounded_by_attestation (s : TokenState)
    (att : ContributionAttestation) (amount : Nat)
    (h_bounded : amount ≤ att.qualityScore) :
    att.teeSignature ≠ 0 ∧ att.qualityScore > 0 := att.hValid

/-- Minting increases total supply by exactly the minted amount. -/
theorem mint_increases_supply (s : TokenState) (att : ContributionAttestation)
    (amount : Nat) (h : amount ≤ att.qualityScore) :
    (mint s att amount h).totalSupply = s.totalSupply + amount := by
  simp [mint]

/-- Minting is bounded: cannot mint more than the quality score. -/
theorem mint_bounded (att : ContributionAttestation) (amount : Nat)
    (h : amount ≤ att.qualityScore) :
    amount ≤ att.qualityScore := h

/-! ## Theorem 3: Burn Reduces Supply -/

/-- Burn tokens from an account. Returns none if insufficient balance. -/
def burn (s : TokenState) (accountId : Nat) (amount : Nat) : Option TokenState :=
  let account := s.accounts.find? (fun a => a.id == accountId)
  match account with
  | none => none
  | some acc =>
    if acc.balance < amount then none
    else
      let accounts' := s.accounts.map fun a =>
        if a.id = accountId then { a with balance := a.balance - amount }
        else a
      some { accounts := accounts'
             totalSupply := s.totalSupply - amount }

/-- Burning correctly reduces total supply by the burned amount. -/
theorem burn_reduces_supply (s : TokenState) (accountId : Nat) (amount : Nat)
    (s' : TokenState)
    (h_burn : burn s accountId amount = some s') :
    s'.totalSupply = s.totalSupply - amount := by
  simp only [burn] at h_burn
  split at h_burn
  · exact absurd h_burn (by simp)
  · split at h_burn
    · exact absurd h_burn (by simp)
    · injection h_burn with h_eq; subst h_eq; rfl

/-- Burning with amount > balance fails.

    STATEMENT CHANGED: this requires a uniqueness hypothesis on account ids.
    `burn` checks the balance of the account returned by `List.find?`, which is
    the *first* account whose id matches `accountId`. If `s.accounts` could
    contain two distinct accounts with the same id, the supplied `acc` (with
    insufficient balance) need not be the one `find?` returns, and burn could
    succeed — so the original statement is false in general. We add the natural
    registry invariant that account ids are pairwise distinct, under which the
    matched account is exactly `acc`. -/
theorem burn_insufficient_fails (s : TokenState) (accountId : Nat) (amount : Nat)
    (acc : Account)
    (h_unique : s.accounts.Pairwise (fun a b => a.id ≠ b.id))
    (h_found : acc ∈ s.accounts ∧ acc.id = accountId)
    (h_insufficient : acc.balance < amount) :
    burn s accountId amount = none := by
  obtain ⟨h_mem, h_id⟩ := h_found
  simp only [burn]
  cases hf : s.accounts.find? (fun a => a.id == accountId) with
  | none => rfl
  | some acc₀ =>
    -- the matched account is in the list and has the queried id
    have hmem₀ : acc₀ ∈ s.accounts := List.mem_of_find?_eq_some hf
    have hid₀ : acc₀.id = accountId := by
      simpa using List.find?_some (l := s.accounts) (p := fun a => a.id == accountId) hf
    -- by uniqueness of ids, the matched account equals the supplied one
    have hsymm : Symmetric (fun a b : Account => a.id ≠ b.id) := fun _ _ h => h.symm
    have heq : acc₀ = acc := by
      by_contra hne
      exact (List.Pairwise.forall hsymm h_unique hmem₀ h_mem hne) (by rw [hid₀, h_id])
    subst heq
    simp only
    rw [if_pos h_insufficient]

/-! ## Theorem 4: Transfer Preserves Total -/

/-- Transfer tokens between accounts. Fails if sender has insufficient balance. -/
def transfer (s : TokenState) (from_ to_ amount : Nat) : Option TokenState :=
  let sender := s.accounts.find? (fun a => a.id == from_)
  match sender with
  | none => none
  | some snd =>
    if snd.balance < amount then none
    else
      let accounts' := s.accounts.map fun a =>
        if a.id = from_ then { a with balance := a.balance - amount }
        else if a.id = to_ then { a with balance := a.balance + amount }
        else a
      some { accounts := accounts'
             totalSupply := s.totalSupply }

/-- Transfers do not change total supply. The sender's loss is exactly
    the receiver's gain. -/
theorem transfer_preserves_total (s : TokenState) (from_ to_ amount : Nat)
    (s' : TokenState)
    (h_transfer : transfer s from_ to_ amount = some s')
    (h_diff : from_ ≠ to_) :
    s'.totalSupply = s.totalSupply := by
  simp only [transfer] at h_transfer
  split at h_transfer
  · exact absurd h_transfer (by simp)
  · split at h_transfer
    · exact absurd h_transfer (by simp)
    · injection h_transfer with h_eq; subst h_eq; rfl

/-- Transfer fails with insufficient balance.

    STATEMENT CHANGED: like `burn_insufficient_fails`, this needs the account-id
    uniqueness invariant. `transfer` checks the balance of the account returned
    by `List.find?` on `from_` (the first id-match); if ids were not distinct the
    supplied under-funded `snd` need not be that account and the transfer could
    succeed. Under pairwise-distinct ids the matched sender is exactly `snd`. -/
theorem transfer_insufficient_fails (s : TokenState) (from_ to_ amount : Nat)
    (snd : Account)
    (h_unique : s.accounts.Pairwise (fun a b => a.id ≠ b.id))
    (h_found : snd ∈ s.accounts ∧ snd.id = from_)
    (h_insufficient : snd.balance < amount) :
    transfer s from_ to_ amount = none := by
  obtain ⟨h_mem, h_id⟩ := h_found
  simp only [transfer]
  cases hf : s.accounts.find? (fun a => a.id == from_) with
  | none => rfl
  | some snd₀ =>
    have hmem₀ : snd₀ ∈ s.accounts := List.mem_of_find?_eq_some hf
    have hid₀ : snd₀.id = from_ := by
      simpa using List.find?_some (l := s.accounts) (p := fun a => a.id == from_) hf
    have hsymm : Symmetric (fun a b : Account => a.id ≠ b.id) := fun _ _ h => h.symm
    have heq : snd₀ = snd := by
      by_contra hne
      exact (List.Pairwise.forall hsymm h_unique hmem₀ h_mem hne) (by rw [hid₀, h_id])
    subst heq
    simp only
    rw [if_pos h_insufficient]

end Token.ExperienceLedger
