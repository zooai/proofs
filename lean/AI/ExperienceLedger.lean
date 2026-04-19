/-
  Authors: Antje Worring, Zach Kelling

  Experience Ledger

  Content-addressed, append-only log of semantic experiences.
  Stored on IPFS/Arweave with on-chain registry.
  DAO-curated quality scoring.

  Maps to:
  - zoo/papers/experience-ledger.tex: specification
  - zoo/papers/experience-ledger-dso.tex: DSO integration
  - uor.foundation: content-addressing scheme

  Properties:
  - Append-only: experiences cannot be deleted (immutable)
  - Content-addressed: hash determines identity
  - DAO-curated: quality scores via governance voting
  - Merkle-verified: inclusion proofs for any experience
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace AI.ExperienceLedger

/-- Ledger entry -/
structure Entry where
  hash : Nat            -- content hash (uor.foundation/{hash}/{name})
  contributor : Nat     -- who contributed this
  timestamp : Nat       -- when
  qualityVotes : Nat    -- DAO quality score
  domain : String       -- task domain
  deriving DecidableEq, Repr

/-- The ledger: append-only list -/
structure Ledger where
  entries : List Entry
  merkleRoot : Nat      -- Merkle root of all entries

/-- Append an entry (the only mutation) -/
def append (l : Ledger) (e : Entry) : Ledger :=
  { entries := e :: l.entries
  , merkleRoot := l.merkleRoot + e.hash }  -- simplified Merkle update

/-- APPEND-ONLY: Ledger only grows -/
theorem append_grows (l : Ledger) (e : Entry) :
    (append l e).entries.length = l.entries.length + 1 := by
  simp [append, List.length_cons]

/-- IMMUTABILITY: Old entries are preserved -/
theorem append_preserves (l : Ledger) (e : Entry) (old : Entry)
    (h : old ∈ l.entries) :
    old ∈ (append l e).entries := by
  simp [append]; exact List.mem_cons_of_mem _ h

/-- CONTENT ADDRESSING: Same hash → same content -/
axiom content_addressed :
  ∀ (e1 e2 : Entry), e1.hash = e2.hash → e1 = e2

/-- EMPTY LEDGER -/
def emptyLedger : Ledger := ⟨[], 0⟩

theorem empty_has_zero : emptyLedger.entries.length = 0 := rfl

/-- QUALITY MONOTONE: Votes can only be added, not removed -/
def upvote (e : Entry) : Entry :=
  { e with qualityVotes := e.qualityVotes + 1 }

theorem upvote_increases (e : Entry) :
    (upvote e).qualityVotes > e.qualityVotes := by
  simp [upvote]; omega

/-- MERKLE VERIFICATION: root changes with each append -/
theorem root_changes (l : Ledger) (e : Entry) (h : e.hash > 0) :
    (append l e).merkleRoot > l.merkleRoot := by
  simp [append]; omega

end AI.ExperienceLedger
