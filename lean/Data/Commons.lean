/-
  Authors: Antje Worring, Zach Kelling

  Data Commons Access Control

  Formal proofs about the Zoo Data Commons access control model.
  The Data Commons enables cross-institutional data sharing for
  conservation and AI research with a formal permission lattice.

  Maps to:
  - zoo/papers/zoo-federated-wildlife.tex: cross-site data sharing
  - zoo/papers/zoo-experience-ledger.tex: content-addressed data

  Key results:
  - Permissions form a valid partial order (reflexive, antisymmetric, transitive)
  - Adding permissions never reduces access (monotonicity)
  - Revocation removes exactly the specified grants

  Author: Zach Kelling
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Data.Commons

/-! ## Core Structures -/

/-- Permission level. Higher numbers grant more access. -/
inductive PermLevel where
  | none    : PermLevel  -- no access
  | read    : PermLevel  -- read-only
  | comment : PermLevel  -- read + annotate
  | write   : PermLevel  -- read + write
  | admin   : PermLevel  -- full control
  deriving DecidableEq, Repr

/-- Numeric encoding for ordering. -/
def PermLevel.toNat : PermLevel → Nat
  | .none => 0
  | .read => 1
  | .comment => 2
  | .write => 3
  | .admin => 4

instance : LE PermLevel where
  le a b := a.toNat ≤ b.toNat

instance : LT PermLevel where
  lt a b := a.toNat < b.toNat

instance (a b : PermLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

/-- An access grant: subject has a permission level on a resource. -/
structure Grant where
  subject : Nat      -- user/institution ID
  resource : Nat     -- data resource ID
  level : PermLevel
  deriving DecidableEq, Repr

/-- Access control state: a set of active grants. -/
structure AccessState where
  grants : List Grant
  deriving Repr

/-- Look up the permission level for a (subject, resource) pair.
    Returns the highest permission level among matching grants,
    or PermLevel.none if no grant exists. -/
def getPermission (s : AccessState) (subject resource : Nat) : PermLevel :=
  let matching := s.grants.filter (fun g => g.subject == subject && g.resource == resource)
  matching.foldl (fun acc g => if g.level.toNat > acc.toNat then g.level else acc) .none

/-! ## Theorem 1: Permission Lattice Valid -/

/-- Reflexivity: every permission level is less than or equal to itself. -/
theorem perm_le_refl (p : PermLevel) : p ≤ p := by
  cases p <;> decide

/-- Antisymmetry: if a <= b and b <= a, then a = b. -/
theorem perm_le_antisymm (a b : PermLevel) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert h1 h2; decide)

/-- Transitivity: if a <= b and b <= c, then a <= c. -/
theorem perm_le_trans (a b c : PermLevel) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;> revert h1 h2 <;> decide

/-- The permission levels form a valid partial order (lattice). -/
theorem permission_lattice_valid :
    (∀ p : PermLevel, p ≤ p) ∧
    (∀ a b : PermLevel, a ≤ b → b ≤ a → a = b) ∧
    (∀ a b c : PermLevel, a ≤ b → b ≤ c → a ≤ c) :=
  ⟨perm_le_refl, perm_le_antisymm, perm_le_trans⟩

/-- None is the bottom element. -/
theorem none_is_bottom (p : PermLevel) : PermLevel.none ≤ p := by
  cases p <;> decide

/-- Admin is the top element. -/
theorem admin_is_top (p : PermLevel) : p ≤ PermLevel.admin := by
  cases p <;> decide

/-! ## Theorem 2: Access Monotone -/

/-- Add a grant to the access state. -/
def addGrant (s : AccessState) (g : Grant) : AccessState :=
  { grants := g :: s.grants }

/-- Helper: the permission-maximizing foldl never decreases the accumulator.
    Stated with the exact lambda used in `getPermission` so it unifies after
    unfolding. -/
private theorem foldl_ge_acc (l : List Grant) (acc : PermLevel) :
    acc.toNat ≤
    (l.foldl (fun acc g => if g.level.toNat > acc.toNat then g.level else acc) acc).toNat := by
  induction l generalizing acc with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons]
    split
    · rename_i hgt; exact le_trans (le_of_lt hgt) (ih h.level)
    · exact ih acc

/-- Helper: the permission-maximizing foldl is monotone in its starting accumulator. -/
private theorem foldl_mono (l : List Grant) (a1 a2 : PermLevel) (h : a1.toNat ≤ a2.toNat) :
    (l.foldl (fun acc g => if g.level.toNat > acc.toNat then g.level else acc) a1).toNat ≤
    (l.foldl (fun acc g => if g.level.toNat > acc.toNat then g.level else acc) a2).toNat := by
  induction l generalizing a1 a2 with
  | nil => simpa using h
  | cons hd t ih =>
    simp only [List.foldl_cons]
    by_cases c1 : hd.level.toNat > a1.toNat <;> by_cases c2 : hd.level.toNat > a2.toNat <;>
      simp only [c1, c2, if_true, if_false] <;> apply ih <;> omega

/-- Adding a permission never reduces access: if a subject had access
    before adding a grant, they still have it after.
    More precisely: the permission level for any (subject, resource) pair
    is non-decreasing when grants are added. -/
theorem access_monotone (s : AccessState) (g : Grant) (subject resource : Nat) :
    (getPermission s subject resource).toNat ≤
    (getPermission (addGrant s g) subject resource).toNat := by
  simp only [getPermission, addGrant, List.filter_cons]
  by_cases hp : (g.subject == subject && g.resource == resource) = true
  · -- the new grant matches the queried pair: it only raises the starting accumulator
    simp only [hp, if_true, List.foldl_cons]
    apply foldl_mono
    apply (foldl_ge_acc [g] PermLevel.none).trans_eq
    simp [List.foldl_cons]
  · -- the new grant is filtered out: the matching list is unchanged
    simp only [Bool.not_eq_true] at hp
    rw [hp]
    simp

/-- Adding a grant for a specific (subject, resource) pair increases access
    for that pair (assuming the new grant's level is higher). -/
theorem add_grant_increases (s : AccessState) (g : Grant)
    (h_higher : g.level.toNat > (getPermission s g.subject g.resource).toNat) :
    (getPermission (addGrant s g) g.subject g.resource).toNat ≥ g.level.toNat := by
  simp only [getPermission, addGrant, List.filter_cons]
  have hpg : (g.subject == g.subject && g.resource == g.resource) = true := by simp
  simp only [hpg, if_true, List.foldl_cons]
  -- the new grant has positive level, so it sets the starting accumulator to g.level
  have hg0 : g.level.toNat > (PermLevel.none).toNat := by
    have := foldl_ge_acc
      (s.grants.filter (fun gg => gg.subject == g.subject && gg.resource == g.resource))
      PermLevel.none
    simp only [getPermission] at h_higher
    omega
  rw [if_pos hg0]
  exact foldl_ge_acc _ g.level

/-- Adding a grant for one resource doesn't affect other resources. -/
theorem add_grant_other_unchanged (s : AccessState) (g : Grant)
    (subject resource : Nat) (h_diff : resource ≠ g.resource) :
    getPermission (addGrant s g) subject resource =
    getPermission s subject resource := by
  simp only [getPermission, addGrant, List.filter_cons]
  -- the new grant fails the (subject, resource) filter, so the matching list is unchanged
  have : (g.subject == subject && g.resource == resource) = false := by
    simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    right; exact fun h => h_diff h.symm
  rw [this]; simp

/-! ## Theorem 3: Revocation Correct -/

/-- Revoke all grants for a (subject, resource) pair. -/
def revokeAccess (s : AccessState) (subject resource : Nat) : AccessState :=
  { grants := s.grants.filter (fun g =>
      ¬(g.subject == subject && g.resource == resource)) }

/-- After revocation, the subject has no access to the resource. -/
theorem revocation_correct (s : AccessState) (subject resource : Nat) :
    getPermission (revokeAccess s subject resource) subject resource = PermLevel.none := by
  simp only [getPermission, revokeAccess, List.filter_filter]
  -- composing the two filters keeps grants that both match and don't match (subject, resource):
  -- impossible, so the matching list is empty
  have hnil : (List.filter
        (fun a => a.subject == subject && a.resource == resource &&
          decide ¬(a.subject == subject && a.resource == resource) = true) s.grants) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a _ha hcontra
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcontra
    exact hcontra.2 hcontra.1
  rw [hnil]
  rfl

/-- Revocation of one pair doesn't affect other pairs. -/
theorem revocation_targeted (s : AccessState) (subject resource : Nat)
    (otherSubject otherResource : Nat)
    (h_diff : subject ≠ otherSubject ∨ resource ≠ otherResource) :
    getPermission (revokeAccess s subject resource) otherSubject otherResource =
    getPermission s otherSubject otherResource := by
  simp only [getPermission, revokeAccess, List.filter_filter]
  -- the revocation filter is redundant on grants matching (otherSubject, otherResource),
  -- since such grants cannot match the distinct (subject, resource) pair
  have hfilt : (List.filter
        (fun a => a.subject == otherSubject && a.resource == otherResource &&
          decide ¬(a.subject == subject && a.resource == resource) = true) s.grants) =
      (List.filter (fun g => g.subject == otherSubject && g.resource == otherResource) s.grants) := by
    apply List.filter_congr
    intro a _ha
    by_cases hmatch : (a.subject == otherSubject && a.resource == otherResource) = true
    · have hrev : decide ¬(a.subject == subject && a.resource == resource) = true := by
        simp only [decide_eq_true_eq]
        simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
        obtain ⟨hs, hr⟩ := hmatch
        subst hs; subst hr
        simp only [Bool.and_eq_true, beq_iff_eq, not_and]
        intro h1 h2
        rcases h_diff with h | h
        · exact h h1.symm
        · exact h h2.symm
      rw [hmatch, hrev, Bool.and_true]
    · simp only [Bool.not_eq_true] at hmatch
      rw [hmatch, Bool.false_and]
  rw [hfilt]

/-- Revoking from an empty state is a no-op. -/
theorem revoke_empty (subject resource : Nat) :
    revokeAccess ⟨[]⟩ subject resource = ⟨[]⟩ := by
  simp [revokeAccess, List.filter_nil]

end Data.Commons
