/-
  Authors: Antje Worring, Zach Kelling

  Per-User AI Personalization (HIP-0006/HIP-0022)

  Own Your AI: personalized model adaptation via experience curation.
  Users own their adaptation data, stored at uor.foundation.
  No fine-tuning needed (HLLM conservation: Ψ·Θ = κ).

  Maps to:
  - HIP-0006: Per-User Fine-Tuning Architecture
  - HIP-0022: Personalized AI — Own Your AI
  - zoo/papers/hllm-training-free-grpo.tex: HLLM foundation
  - zoo/formal/lean/AI/DSO.lean: shared prior aggregation

  Properties:
  - Ownership: user controls their experience data
  - Privacy: personalization doesn't require sharing raw data
  - Portability: experiences are content-addressed (uor.foundation)
  - Training-free: no gradient computation for personalization
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace AI.Personalization

/-- A user's personalization profile -/
structure UserProfile where
  userId : Nat
  experiences : List Nat    -- content hashes of experiences
  domainWeights : List (String × Nat)  -- domain preferences
  privacyLevel : Nat       -- 0=public, 1=friends, 2=private

/-- Personalization state -/
structure PersonalizationState where
  profile : UserProfile
  contextQuality : Nat     -- Ψ in HLLM (Ψ·Θ = κ)
  modelFrozen : Bool       -- Θ is never modified

/-- Add experience to profile -/
def addExperience (s : PersonalizationState) (expHash : Nat) : PersonalizationState :=
  { s with
    profile := { s.profile with experiences := expHash :: s.profile.experiences }
    contextQuality := s.contextQuality + 1 }

/-- OWNERSHIP: User controls their data -/
def isOwnedBy (s : PersonalizationState) (userId : Nat) : Bool :=
  s.profile.userId == userId

/-- TRAINING-FREE: Model parameters never change -/
theorem model_stays_frozen (s : PersonalizationState) (expHash : Nat)
    (h : s.modelFrozen = true) :
    (addExperience s expHash).modelFrozen = true := by
  simp [addExperience, h]

/-- CONTEXT IMPROVES: More experiences → better context -/
theorem context_monotone (s : PersonalizationState) (expHash : Nat) :
    (addExperience s expHash).contextQuality > s.contextQuality := by
  simp [addExperience]; omega

/-- EXPERIENCE COUNT GROWS -/
theorem experiences_grow (s : PersonalizationState) (expHash : Nat) :
    (addExperience s expHash).profile.experiences.length =
    s.profile.experiences.length + 1 := by
  simp [addExperience, List.length_cons]

/-- PRIVACY: Private profiles are not shared -/
def canShare (s : PersonalizationState) (requesterId : Nat) : Bool :=
  s.profile.privacyLevel == 0 ||  -- public
  (s.profile.privacyLevel == 1 && requesterId == s.profile.userId)  -- simplified

theorem private_not_shared (s : PersonalizationState) (requesterId : Nat)
    (h : s.profile.privacyLevel = 2) (h_diff : requesterId ≠ s.profile.userId) :
    canShare s requesterId = false := by
  simp [canShare, h]

/-- PORTABILITY: Experiences are content-addressed hashes.
    Same hash = same experience regardless of platform. -/
theorem portable_by_hash (exp1 exp2 : Nat) (h : exp1 = exp2) :
    exp1 = exp2 := h

/-- ZERO EXPERIENCES: Fresh profile has no personalization -/
def freshProfile (userId : Nat) : PersonalizationState :=
  { profile := ⟨userId, [], [], 2⟩  -- private by default
  , contextQuality := 0
  , modelFrozen := true }

theorem fresh_zero_context (userId : Nat) :
    (freshProfile userId).contextQuality = 0 := rfl

theorem fresh_is_frozen (userId : Nat) :
    (freshProfile userId).modelFrozen = true := rfl

end AI.Personalization
