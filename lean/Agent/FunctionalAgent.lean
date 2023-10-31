/-
  Functional/Compositional Agent Proofs

  Compositional agent architectures using functional programming
  principles. Agents are modeled as functions from observations to
  actions, composed via standard combinators (sequence, parallel, map).

  Maps to:
  - zoo/papers/zoo-agent-nft.tex: Agent NFT composability
  - zoo/papers/zoo-dso.tex: DSO agent composition for governance
  - hanzo/agents: agent framework composition primitives

  Key results:
  - Composing agents is associative
  - Identity agent is neutral element (monoid laws)
  - Mapping over agent outputs preserves protocol structure
  - Monadic bind correctly sequences agent actions
  - Independent parallel agents commute

  Author: Zach Kelling
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Agent.FunctionalAgent

/-! ## Core Structures -/

/-- An agent is a function from observation to action.
    We model agents abstractly by their input/output behavior. -/
structure Agent (α β : Type) where
  /-- The agent's policy function -/
  run : α → β

/-- The identity agent: passes input through unchanged. -/
def idAgent : Agent α α :=
  ⟨fun x => x⟩

/-- Compose two agents sequentially: output of first feeds input of second. -/
def compose (f : Agent α β) (g : Agent β γ) : Agent α γ :=
  ⟨fun x => g.run (f.run x)⟩

/-- Map a function over an agent's output. -/
def mapOutput (f : Agent α β) (g : β → γ) : Agent α γ :=
  ⟨fun x => g (f.run x)⟩

/-- Parallel composition: run two agents on the same input. -/
def parallel (f : Agent α β) (g : Agent α γ) : Agent α (β × γ) :=
  ⟨fun x => (f.run x, g.run x)⟩

/-- Monadic bind: sequence agent actions where second depends on first. -/
def bind (f : Agent α β) (g : β → Agent α γ) : Agent α γ :=
  ⟨fun x => (g (f.run x)).run x⟩

/-- A protocol structure: a set of constraints on agent outputs. -/
structure Protocol (β : Type) where
  /-- Predicate that outputs must satisfy -/
  valid : β → Prop

/-! ## Theorem 1: Agent Composition Associative -/

/-- Composing agents is associative: (f ; g) ; h = f ; (g ; h).
    This ensures that multi-agent pipelines can be restructured
    without changing behavior, enabling modular agent design. -/
theorem agent_composition_associative (f : Agent α β) (g : Agent β γ) (h : Agent γ δ) :
    (compose (compose f g) h).run = (compose f (compose g h)).run := by
  ext x
  simp [compose]

/-- Composition preserves equality of agent functions. -/
theorem compose_congr {f₁ f₂ : Agent α β} {g₁ g₂ : Agent β γ}
    (hf : f₁.run = f₂.run) (hg : g₁.run = g₂.run) :
    (compose f₁ g₁).run = (compose f₂ g₂).run := by
  ext x
  simp [compose, hf, hg]

/-! ## Theorem 2: Identity Agent Neutral -/

/-- The identity agent is the left neutral element for composition:
    id ; f = f. Together with right neutrality and associativity,
    this makes agents a monoid under composition. -/
theorem agent_identity_neutral_left (f : Agent α β) :
    (compose idAgent f).run = f.run := by
  ext x
  simp [compose, idAgent]

/-- The identity agent is the right neutral element: f ; id = f. -/
theorem agent_identity_neutral_right (f : Agent α β) :
    (compose f idAgent).run = f.run := by
  ext x
  simp [compose, idAgent]

/-- Agents form a monoid: associativity + identity. -/
theorem agent_monoid (f : Agent α β) (g : Agent β γ) (h : Agent γ δ) :
    (compose (compose f g) h).run = (compose f (compose g h)).run ∧
    (compose idAgent f).run = f.run ∧
    (compose f (idAgent : Agent β β)).run = f.run :=
  ⟨agent_composition_associative f g h,
   agent_identity_neutral_left f,
   agent_identity_neutral_right f⟩

/-! ## Theorem 3: Map Preserves Structure -/

/-- Mapping over agent outputs preserves protocol structure: if the
    original agent's output satisfies a protocol, and the mapping
    function preserves the protocol predicate, then the mapped
    agent also satisfies the protocol. -/
theorem map_preserves_structure (agent : Agent α β) (g : β → γ)
    (protocolB : Protocol β) (protocolC : Protocol γ)
    (h_preserves : ∀ b, protocolB.valid b → protocolC.valid (g b))
    (x : α)
    (h_valid : protocolB.valid (agent.run x)) :
    protocolC.valid ((mapOutput agent g).run x) := by
  simp [mapOutput]
  exact h_preserves _ h_valid

/-- Map with identity function is the original agent. -/
theorem map_id (agent : Agent α β) :
    (mapOutput agent id).run = agent.run := by
  ext x
  simp [mapOutput]

/-- Map distributes over function composition. -/
theorem map_compose (agent : Agent α β) (g : β → γ) (h : γ → δ) :
    (mapOutput (mapOutput agent g) h).run = (mapOutput agent (h ∘ g)).run := by
  ext x
  simp [mapOutput, Function.comp]

/-! ## Theorem 4: Bind Sequential Correct -/

/-- Monadic bind correctly sequences agent actions: the second agent
    receives the output of the first and produces the final result.
    This is the foundation of agent chaining where later decisions
    depend on earlier observations. -/
theorem bind_sequential_correct (f : Agent α β) (g : β → Agent α γ)
    (x : α) :
    (bind f g).run x = (g (f.run x)).run x := by
  simp [bind]

/-- Bind with a constant second agent is just composition. -/
theorem bind_const (f : Agent α β) (g : Agent α γ) :
    (bind f (fun _ => g)).run = g.run := by
  ext x
  simp [bind]

/-- Left identity: bind with return is the original function. -/
theorem bind_left_identity (a : β) (g : β → Agent α γ) :
    (bind (⟨fun _ => a⟩ : Agent α β) g).run = (g a).run := by
  ext x
  simp [bind]

/-- Right identity: bind with id agent returns the same result. -/
theorem bind_right_identity (f : Agent α β) :
    (bind f (fun b => (⟨fun _ => b⟩ : Agent α β))).run = f.run := by
  ext x
  simp [bind]

/-! ## Theorem 5: Parallel Composition Commutative -/

/-- Independent parallel agents commute: running (f, g) in parallel
    produces the same results as (g, f), just with swapped tuple order.
    This ensures that the order of independent agent evaluation doesn't
    matter, enabling safe parallelization. -/
theorem parallel_composition_commutative (f : Agent α β) (g : Agent α γ) (x : α) :
    let (a, b) := (parallel f g).run x
    let (c, d) := (parallel g f).run x
    a = d ∧ b = c := by
  simp [parallel]

/-- Parallel composition preserves individual agent behavior. -/
theorem parallel_preserves_left (f : Agent α β) (g : Agent α γ) (x : α) :
    (parallel f g).run x |>.1 = f.run x := by
  simp [parallel]

theorem parallel_preserves_right (f : Agent α β) (g : Agent α γ) (x : α) :
    (parallel f g).run x |>.2 = g.run x := by
  simp [parallel]

/-- Parallel with identity extracts the agent result. -/
theorem parallel_with_id (f : Agent α β) (x : α) :
    (parallel f (idAgent : Agent α α)).run x = (f.run x, x) := by
  simp [parallel, idAgent]

end Agent.FunctionalAgent
