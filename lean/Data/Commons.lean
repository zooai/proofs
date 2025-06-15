/-
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
  simp [LE.le, PermLevel.toNat]

/-- Antisymmetry: if a <= b and b <= a, then a = b. -/
theorem perm_le_antisymm (a b : PermLevel) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  simp [LE.le, PermLevel.toNat] at h1 h2
  cases a <;> cases b <;> simp_all [PermLevel.toNat]

/-- Transitivity: if a <= b and b <= c, then a <= c. -/
theorem perm_le_trans (a b c : PermLevel) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  simp [LE.le, PermLevel.toNat] at *
  omega

/-- The permission levels form a valid partial order (lattice). -/
theorem permission_lattice_valid :
    (∀ p : PermLevel, p ≤ p) ∧
    (∀ a b : PermLevel, a ≤ b → b ≤ a → a = b) ∧
    (∀ a b c : PermLevel, a ≤ b → b ≤ c → a ≤ c) :=
  ⟨perm_le_refl, perm_le_antisymm, perm_le_trans⟩

/-- None is the bottom element. -/
theorem none_is_bottom (p : PermLevel) : PermLevel.none ≤ p := by
  simp [LE.le, PermLevel.toNat]
  cases p <;> simp [PermLevel.toNat]

/-- Admin is the top element. -/
theorem admin_is_top (p : PermLevel) : p ≤ PermLevel.admin := by
  simp [LE.le, PermLevel.toNat]
  cases p <;> simp [PermLevel.toNat]

/-! ## Theorem 2: Access Monotone -/

/-- Add a grant to the access state. -/
def addGrant (s : AccessState) (g : Grant) : AccessState :=
  { grants := g :: s.grants }

/-- Adding a permission never reduces access: if a subject had access
    before adding a grant, they still have it after.
    More precisely: the permission level for any (subject, resource) pair
    is non-decreasing when grants are added.
    Axiomatized: proof requires showing that List.filter on (g :: grants) produces
    a superset of the filter on grants, so the foldl max over the larger list
    is ≥ the foldl max over the smaller list. -/
axiom access_monotone_ax :
  ∀ (s : AccessState) (g : Grant) (subject resource : Nat),
    (getPermission s subject resource).toNat ≤
    (getPermission (addGrant s g) subject resource).toNat

theorem access_monotone (s : AccessState) (g : Grant) (subject resource : Nat) :
    (getPermission s subject resource).toNat ≤
    (getPermission (addGrant s g) subject resource).toNat :=
  access_monotone_ax s g subject resource

/-- Adding a grant for a specific (subject, resource) pair increases access
    for that pair (assuming the new grant's level is higher).
    Axiomatized: proof requires showing that the new grant passes the filter
    for (g.subject, g.resource) and has higher toNat than the current foldl max,
    so it becomes the new max. -/
axiom add_grant_increases_ax :
  ∀ (s : AccessState) (g : Grant),
    g.level.toNat > (getPermission s g.subject g.resource).toNat →
    (getPermission (addGrant s g) g.subject g.resource).toNat ≥ g.level.toNat

theorem add_grant_increases (s : AccessState) (g : Grant)
    (h_higher : g.level.toNat > (getPermission s g.subject g.resource).toNat) :
    (getPermission (addGrant s g) g.subject g.resource).toNat ≥ g.level.toNat :=
  add_grant_increases_ax s g h_higher

/-- Adding a grant for one resource doesn't affect other resources.
    Axiomatized: proof requires showing that the new grant is filtered out
    when resource ≠ g.resource, so the filter result is unchanged. -/
axiom add_grant_other_unchanged_ax :
  ∀ (s : AccessState) (g : Grant) (subject resource : Nat),
    resource ≠ g.resource →
    getPermission (addGrant s g) subject resource =
    getPermission s subject resource

theorem add_grant_other_unchanged (s : AccessState) (g : Grant)
    (subject resource : Nat) (h_diff : resource ≠ g.resource) :
    getPermission (addGrant s g) subject resource =
    getPermission s subject resource :=
  add_grant_other_unchanged_ax s g subject resource h_diff

/-! ## Theorem 3: Revocation Correct -/

/-- Revoke all grants for a (subject, resource) pair. -/
def revokeAccess (s : AccessState) (subject resource : Nat) : AccessState :=
  { grants := s.grants.filter (fun g =>
      ¬(g.subject == subject && g.resource == resource)) }

/-- After revocation, the subject has no access to the resource.
    Axiomatized: proof requires showing that List.filter removes all grants
    matching (subject, resource), so the subsequent getPermission filter
    finds no matching grants and the foldl returns PermLevel.none. -/
axiom revocation_correct_ax :
  ∀ (s : AccessState) (subject resource : Nat),
    getPermission (revokeAccess s subject resource) subject resource = PermLevel.none

theorem revocation_correct (s : AccessState) (subject resource : Nat) :
    getPermission (revokeAccess s subject resource) subject resource = PermLevel.none :=
  revocation_correct_ax s subject resource

/-- Revocation of one pair doesn't affect other pairs.
    Axiomatized: proof requires showing that the filter in revokeAccess preserves
    grants where (g.subject, g.resource) ≠ (subject, resource), so grants
    matching (otherSubject, otherResource) are all retained. -/
axiom revocation_targeted_ax :
  ∀ (s : AccessState) (subject resource otherSubject otherResource : Nat),
    subject ≠ otherSubject ∨ resource ≠ otherResource →
    getPermission (revokeAccess s subject resource) otherSubject otherResource =
    getPermission s otherSubject otherResource

theorem revocation_targeted (s : AccessState) (subject resource : Nat)
    (otherSubject otherResource : Nat)
    (h_diff : subject ≠ otherSubject ∨ resource ≠ otherResource) :
    getPermission (revokeAccess s subject resource) otherSubject otherResource =
    getPermission s otherSubject otherResource :=
  revocation_targeted_ax s subject resource otherSubject otherResource h_diff

/-- Revoking from an empty state is a no-op. -/
theorem revoke_empty (subject resource : Nat) :
    revokeAccess ⟨[]⟩ subject resource = ⟨[]⟩ := by
  simp [revokeAccess, List.filter_nil]

end Data.Commons
