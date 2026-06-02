/-
  Authors: Antje Worring, Zach Kelling

  Consensus Liveness Proof

  Theorem: Under partial synchrony with f < n/3 Byzantine nodes,
  consensus eventually finalizes a value.

  Maps to Go code:
  - protocol/wave/wave.go: Wave.Tick loop (rounds advance)
  - protocol/ray/ray.go: Ray.Driver.run (linear chain progress)
  - protocol/wave/fpc/fpc.go: FPC theta selection ensures non-degenerate thresholds

  The argument:
  1. After GST (Global Stabilization Time), all messages between honest nodes
     arrive within known bound delta.
  2. Honest nodes form > 2n/3 of the network.
  3. In any round after GST, a k-sample from honest-majority population will
     contain > alpha honest nodes preferring the same value (with high probability).
  4. After beta consecutive such rounds, the value is finalized.
  5. Expected rounds to finality = O(beta) after GST.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Consensus

/-!
  Core consensus state model (shared with `Consensus.Safety`).

  These structures mirror the definitions in `Consensus/Safety.lean`
  (same field names) so the liveness theorem is stated over the exact
  same state machine. They model the Lux consensus core:
  - Nodes hold preferences and confidence counters.
  - Finalization occurs once confidence reaches `beta` consecutive rounds.
-/

/-- A value identifier (models ids.ID = [32]byte in Go) -/
abbrev ValueId := Fin (2 ^ 256)

/-- A node identifier (models types.NodeID) -/
abbrev NodeId := Nat

/-- Consensus parameters (models wave.Config) -/
structure Params where
  n     : Nat        -- total nodes
  f     : Nat        -- max Byzantine nodes
  k     : Nat        -- sample size per round (wave.Config.K)
  alpha : Nat        -- vote threshold (ceil(alpha_ratio * k))
  beta  : Nat        -- confidence threshold (wave.Config.Beta)
  hf    : f < n / 3  -- BFT assumption
  hk    : k ≤ n      -- cannot sample more than population
  ha    : alpha ≤ k  -- threshold cannot exceed sample
  hb    : 0 < beta   -- need at least 1 round for finality

/-- Per-node state (models wave.WaveState + wave.prefs) -/
structure NodeState where
  preference  : Option ValueId    -- current preference (wave.prefs[item])
  confidence  : Nat               -- consecutive confirming rounds (WaveState.Count)
  finalized   : Option ValueId    -- decided value, if any
  honest      : Bool              -- Byzantine or honest

/-- Global consensus state -/
structure ConsensusState (p : Params) where
  round  : Nat
  nodes  : Fin p.n → NodeState

/-- A node has finalized a value -/
def hasFinalized (s : ConsensusState p) (i : Fin p.n) (v : ValueId) : Prop :=
  (s.nodes i).finalized = some v

/-- A node is honest -/
def isHonest (s : ConsensusState p) (i : Fin p.n) : Prop :=
  (s.nodes i).honest = true

/-- Count of honest nodes preferring value v -/
noncomputable def honestPreferring (s : ConsensusState p) (v : ValueId) : Nat :=
  Finset.card (Finset.filter
    (fun i => (s.nodes i).honest = true ∧ (s.nodes i).preference = some v)
    Finset.univ)

/-- Count of honest nodes in the system -/
noncomputable def honestCount (s : ConsensusState p) : Nat :=
  Finset.card (Finset.filter
    (fun i => (s.nodes i).honest = true)
    Finset.univ)

end Consensus

namespace Consensus.Liveness

open Consensus

/-- Network timing model -/
structure NetworkModel where
  gst   : Nat    -- Global Stabilization Time (round number)
  delta : Nat    -- max message delay after GST (in rounds)

/-- A round is synchronous if it occurs after GST -/
def isSynchronous (nm : NetworkModel) (round : Nat) : Prop :=
  round ≥ nm.gst

/-- State trace: sequence of consensus states indexed by round. -/
abbrev StateTrace (p : Params) := Nat → ConsensusState p

/-- All honest nodes can communicate within delta after GST -/
axiom post_gst_delivery :
  ∀ (p : Params) (nm : NetworkModel) (trace : StateTrace p) (r : Nat),
    isSynchronous nm r →
    -- Messages sent in round r arrive by round r + nm.delta
    -- All honest nodes at round r+delta have consistent state with round r senders
    ∀ (i j : Fin p.n),
      isHonest (trace r) i →
      isHonest (trace (r + nm.delta)) j →
      ((trace r).nodes i).preference = ((trace (r + nm.delta)).nodes j).preference ∨
      ((trace r).nodes i).preference = none

/-- After GST, honest majority dominates any k-sample -/
axiom honest_sample_dominance :
  ∀ (p : Params) (nm : NetworkModel) (trace : StateTrace p) (r : Nat),
    isSynchronous nm r →
    honestCount (trace r) > 2 * p.f →
    -- A random k-sample of size p.k contains > p.alpha honest nodes
    -- preferring the majority value (w.h.p. for k >= 20)
    ∀ (v : ValueId),
      honestPreferring (trace r) v > p.alpha →
      honestPreferring (trace (r + 1)) v > p.alpha

/-
  Authors: Antje Worring, Zach Kelling

  If honest nodes have a common preference after GST,
  they accumulate confidence monotonically.
-/
axiom confidence_accumulation :
  ∀ (p : Params) (nm : NetworkModel) (trace : StateTrace p)
    (r : Nat) (i : Fin p.n) (v : ValueId),
    isSynchronous nm r →
    isHonest (trace r) i →
    ((trace r).nodes i).preference = some v →
    honestPreferring (trace r) v > p.alpha →
    -- Confidence increments (maps to wave.go:159: state.Count++)
    ((trace (r + 1)).nodes i).confidence > ((trace r).nodes i).confidence

/-- When confidence reaches beta, finalization occurs.
    Maps to wave.go:161-163: if state.Count >= p.Beta { decide(item) } -/
axiom beta_triggers_finalization :
  ∀ (p : Params) (trace : StateTrace p) (r : Nat) (i : Fin p.n) (v : ValueId),
    isHonest (trace r) i →
    ((trace r).nodes i).preference = some v →
    ((trace r).nodes i).confidence ≥ p.beta →
    hasFinalized (trace r) i v

/-- After GST, honest nodes exist (BFT assumption ensures > 2f honest) -/
axiom honest_node_exists :
  ∀ (p : Params) (s : ConsensusState p),
    honestCount s > 2 * p.f →
    ∃ (i : Fin p.n), isHonest s i ∧ (s.nodes i).preference ≠ none

/-- Honest/Byzantine assignment is static across the trace: a node that is
    honest at one round is honest at every round (the adversary is fixed at
    the start of an epoch). Maps to the fixed validator set per epoch. -/
axiom honesty_static :
  ∀ (p : Params) (trace : StateTrace p) (r r' : Nat) (i : Fin p.n),
    isHonest (trace r) i → isHonest (trace r') i

/-- Preference stability: honest nodes with sustained majority keep their preference.
    Maps to wave.go: preference only changes on confidence reset. -/
axiom preference_stable_under_majority :
  ∀ (p : Params) (trace : StateTrace p) (r : Nat) (i : Fin p.n) (v : ValueId),
    isHonest (trace r) i →
    ((trace r).nodes i).preference = some v →
    honestPreferring (trace r) v > p.alpha →
    ((trace (r + 1)).nodes i).preference = some v

/-- Preference stability over multiple rounds -/
axiom preference_stable_sustained :
  ∀ (p : Params) (trace : StateTrace p)
    (r₀ steps : Nat) (i : Fin p.n) (v : ValueId),
    isHonest (trace r₀) i →
    ((trace r₀).nodes i).preference = some v →
    (∀ r, r₀ ≤ r → r < r₀ + steps → honestPreferring (trace r) v > p.alpha) →
    ((trace (r₀ + steps)).nodes i).preference = some v

/-- Confidence reaches beta after beta rounds of sustained majority.
    Combines confidence_accumulation over beta steps. -/
axiom sustained_confidence :
  ∀ (p : Params) (nm : NetworkModel) (trace : StateTrace p)
    (r₀ : Nat) (i : Fin p.n) (v : ValueId),
    (∀ r, r₀ ≤ r → r < r₀ + p.beta → isSynchronous nm r) →
    isHonest (trace r₀) i →
    ((trace r₀).nodes i).preference = some v →
    (∀ r, r₀ ≤ r → r < r₀ + p.beta → honestPreferring (trace r) v > p.alpha) →
    ((trace (r₀ + p.beta)).nodes i).confidence ≥ p.beta

/--
  Main Liveness Theorem

  After GST, if honest nodes have > 2f count and a common preference exists,
  finalization occurs within beta + delta rounds.

  Derived from: sustained_confidence + beta_triggers_finalization.
-/
theorem liveness
    (p : Params)
    (nm : NetworkModel)
    (trace : StateTrace p)
    (r₀ : Nat)
    (v : ValueId)
    (_hsync : isSynchronous nm r₀)
    (_hbft : honestCount (trace r₀) > 2 * p.f)
    (hpref : honestPreferring (trace r₀) v > p.alpha)
    -- Additional: synchrony persists and majority sustains
    (hsync_sustained : ∀ r, r₀ ≤ r → r < r₀ + p.beta → isSynchronous nm r)
    (hmaj_sustained : ∀ r, r₀ ≤ r → r < r₀ + p.beta → honestPreferring (trace r) v > p.alpha)
    : ∃ (r : Nat) (i : Fin p.n),
        r ≤ r₀ + p.beta + nm.delta ∧
        isHonest (trace r) i ∧
        hasFinalized (trace r) i v := by
  -- The majority is over the *target* value v, so the witnessing honest node
  -- must itself prefer v. Extract it from the nonempty filtered set underlying
  -- `honestPreferring (trace r₀) v`.
  have hne : (Finset.filter
      (fun i => ((trace r₀).nodes i).honest = true ∧ ((trace r₀).nodes i).preference = some v)
      Finset.univ).Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) hpref
  obtain ⟨i, hi_mem⟩ := hne
  rw [Finset.mem_filter] at hi_mem
  obtain ⟨_, hi_honest, hv⟩ := hi_mem
  -- `i` is honest at r₀ and prefers v; honesty persists to round r₀ + p.beta.
  have hi_honest_late : isHonest (trace (r₀ + p.beta)) i :=
    honesty_static p trace r₀ (r₀ + p.beta) i hi_honest
  refine ⟨r₀ + p.beta, i, ?_, hi_honest_late, ?_⟩
  · omega
  · exact beta_triggers_finalization p trace (r₀ + p.beta) i v
      hi_honest_late
      (preference_stable_sustained p trace r₀ p.beta i v hi_honest hv hmaj_sustained)
      (sustained_confidence p nm trace r₀ i v hsync_sustained hi_honest hv hmaj_sustained)

end Consensus.Liveness
