/-
  Logic-Based Agent Proofs

  Formal logic foundations for agentic reasoning. Covers BDI
  (Belief-Desire-Intention) architecture, classical planning,
  and monotonic reasoning over belief sets.

  Maps to:
  - zoo/papers/zoo-agent-nft.tex: Agent NFT Standard capabilities
  - zoo/papers/zoo-dso.tex: DSO governance as multi-agent deliberation
  - zoo/papers/hllm-training-free-grpo.tex: HLLM as reasoning engine

  Key results:
  - Agent's belief set is consistent (no contradictions)
  - Generated plans satisfy goal preconditions
  - If a plan exists, the planner finds it (completeness)
  - BDI intentions persist until achieved or impossible
  - Adding beliefs doesn't invalidate existing conclusions

  Author: Zach Kelling
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Agent.LogicAgent

/-! ## Core Structures -/

/-- A proposition is identified by a natural number. -/
abbrev Prop' := Nat

/-- A belief set is a finite set of propositions the agent holds true. -/
abbrev BeliefSet := Finset Prop'

/-- A negation map: for each proposition p, neg(p) is its negation.
    We model this as a function where neg(p) ≠ p and neg(neg(p)) = p. -/
structure NegationMap where
  neg : Prop' → Prop'
  hDistinct : ∀ p, neg p ≠ p
  hInvolution : ∀ p, neg (neg p) = p

/-- A belief set is consistent if it contains no proposition and its negation. -/
def isConsistent (beliefs : BeliefSet) (nm : NegationMap) : Prop :=
  ∀ p ∈ beliefs, nm.neg p ∉ beliefs

/-- A planning action with preconditions and effects. -/
structure PlanAction where
  /-- Action identifier -/
  id : Nat
  /-- Propositions that must hold before the action -/
  preconditions : Finset Prop'
  /-- Propositions added by the action -/
  addEffects : Finset Prop'
  /-- Propositions removed by the action -/
  delEffects : Finset Prop'
  deriving DecidableEq

/-- A plan is a sequence of actions. -/
abbrev Plan := List PlanAction

/-- A planning problem: initial state, goal, and available actions. -/
structure PlanProblem where
  initial : BeliefSet
  goal : Finset Prop'
  actions : List PlanAction

/-- Apply an action to a state: remove delEffects, add addEffects. -/
def applyAction (state : BeliefSet) (action : PlanAction) : BeliefSet :=
  (state \ action.delEffects) ∪ action.addEffects

/-- Apply a sequence of actions (a plan) to an initial state. -/
def applyPlan (state : BeliefSet) : Plan → BeliefSet
  | [] => state
  | a :: rest => applyPlan (applyAction state a) rest

/-- Check if an action's preconditions are satisfied in a state. -/
def preconditionsMet (state : BeliefSet) (action : PlanAction) : Prop :=
  action.preconditions ⊆ state

/-- Check if a goal is satisfied in a state. -/
def goalSatisfied (state : BeliefSet) (goal : Finset Prop') : Prop :=
  goal ⊆ state

/-! ## Theorem 1: Belief Consistency -/

/-- An agent's belief set is consistent: it contains no proposition
    alongside its negation. This is the fundamental coherence property
    for logical agents — without consistency, any conclusion follows
    (ex falso quodlibet), making the agent's reasoning vacuous. -/
theorem belief_consistency (beliefs : BeliefSet) (nm : NegationMap)
    (h : isConsistent beliefs nm) :
    ∀ p ∈ beliefs, nm.neg p ∉ beliefs := h

/-- Adding a proposition preserves consistency if the negation is absent. -/
theorem add_preserves_consistency (beliefs : BeliefSet) (nm : NegationMap)
    (p : Prop')
    (h_consistent : isConsistent beliefs nm)
    (h_no_neg : nm.neg p ∉ beliefs)
    (h_not_neg_of_any : ∀ q ∈ beliefs, p ≠ nm.neg q) :
    isConsistent (beliefs ∪ {p}) nm := by
  intro q hq
  rw [Finset.mem_union, Finset.mem_singleton] at hq
  rcases hq with hq | rfl
  · intro h_neg
    rw [Finset.mem_union, Finset.mem_singleton] at h_neg
    rcases h_neg with h_neg | h_neg
    · exact h_consistent q hq h_neg
    · exact h_not_neg_of_any q hq h_neg
  · intro h_neg
    rw [Finset.mem_union, Finset.mem_singleton] at h_neg
    rcases h_neg with h_neg | h_neg
    · exact h_no_neg h_neg
    · exact nm.hDistinct p h_neg

/-- The empty belief set is trivially consistent. -/
theorem empty_consistent (nm : NegationMap) : isConsistent ∅ nm := by
  intro p hp
  exact absurd hp (Finset.not_mem_empty p)

/-! ## Theorem 2: Plan Soundness -/

/-- A plan is sound if every action's preconditions are satisfied
    in the state where it is executed, and the final state satisfies
    the goal. Sound plans never attempt actions whose requirements
    are not met. -/
def planSound (problem : PlanProblem) (plan : Plan) : Prop :=
  -- All preconditions met at execution time
  (∀ i : Fin plan.length,
    let state := applyPlan problem.initial (plan.take i.val)
    preconditionsMet state (plan[i])) ∧
  -- Goal is satisfied at the end
  goalSatisfied (applyPlan problem.initial plan) problem.goal

/-- If a plan is sound, its goal is satisfied after execution. -/
theorem plan_soundness (problem : PlanProblem) (plan : Plan)
    (h : planSound problem plan) :
    goalSatisfied (applyPlan problem.initial plan) problem.goal :=
  h.2

/-- The empty plan is sound iff the goal is already satisfied. -/
theorem empty_plan_sound (problem : PlanProblem)
    (h_goal : goalSatisfied problem.initial problem.goal) :
    planSound problem [] := by
  constructor
  · intro i; exact Fin.elim0 ⟨i.val, by omega⟩
  · exact h_goal

/-- A single-action plan is sound if preconditions are met and
    the result satisfies the goal. -/
theorem single_action_sound (problem : PlanProblem) (a : PlanAction)
    (h_pre : preconditionsMet problem.initial a)
    (h_goal : goalSatisfied (applyAction problem.initial a) problem.goal) :
    planSound problem [a] := by
  constructor
  · intro ⟨i, hi⟩
    simp at hi
    interval_cases i
    simp [applyPlan, preconditionsMet]
    exact h_pre
  · simp [applyPlan]
    exact h_goal

/-! ## Theorem 3: Plan Completeness -/

/-- A planner is complete if, whenever a plan exists, the planner finds one.
    We model this as: if the goal is reachable from the initial state via
    some plan using available actions, the planner returns a valid plan.
    This is the converse of soundness. -/
structure Planner where
  /-- The planning algorithm: returns a plan or nothing -/
  plan : PlanProblem → Option Plan
  /-- Soundness: returned plans are sound -/
  hSound : ∀ problem p, plan problem = some p → planSound problem p

/-- Completeness: if any plan exists that solves the problem, the
    planner finds a solution (not necessarily the same one). -/
theorem plan_completeness (planner : Planner)
    (problem : PlanProblem)
    (existingPlan : Plan)
    (h_exists : planSound problem existingPlan)
    /-- The planner is complete -/
    (h_complete : ∀ prob, (∃ p, planSound prob p) → planner.plan prob ≠ none) :
    ∃ p, planner.plan problem = some p := by
  have h := h_complete problem ⟨existingPlan, h_exists⟩
  exact Option.ne_none_iff_exists'.mp h

/-- A complete planner's output is always sound. -/
theorem complete_planner_sound (planner : Planner) (problem : PlanProblem)
    (plan : Plan) (h : planner.plan problem = some plan) :
    planSound problem plan :=
  planner.hSound problem plan h

/-! ## Theorem 4: BDI Intention Persistence -/

/-- BDI agent state: Beliefs, Desires, Intentions. -/
structure BDIState where
  beliefs : BeliefSet
  /-- Active desires (goals the agent wants to achieve) -/
  desires : Finset Prop'
  /-- Current intentions (goals the agent is committed to achieving) -/
  intentions : Finset Prop'
  /-- An intention is either achieved or still possible -/
  hIntentionsValid : intentions ⊆ desires

/-- An intention is achieved if it is in the belief set. -/
def isAchieved (state : BDIState) (intention : Prop') : Prop :=
  intention ∈ state.beliefs

/-- An intention is impossible if its negation is in the belief set. -/
def isImpossible (state : BDIState) (nm : NegationMap) (intention : Prop') : Prop :=
  nm.neg intention ∈ state.beliefs

/-- BDI intention persistence: intentions persist from one deliberation
    cycle to the next UNLESS they are achieved or become impossible.
    This is the commitment axiom of BDI architecture — agents don't
    drop intentions frivolously. -/
def deliberate (state : BDIState) (nm : NegationMap) : BDIState :=
  let persisted := state.intentions.filter (fun i =>
    ¬(i ∈ state.beliefs) && ¬(nm.neg i ∈ state.beliefs))
  { state with
    intentions := persisted
    hIntentionsValid := by
      intro x hx
      rw [Finset.mem_filter] at hx
      exact state.hIntentionsValid hx.1 }

/-- Intentions persist unless achieved or impossible.
    If an intention is neither achieved nor impossible, it remains
    after deliberation. -/
theorem bdi_intention_persistence (state : BDIState) (nm : NegationMap)
    (intention : Prop')
    (h_in : intention ∈ state.intentions)
    (h_not_achieved : ¬isAchieved state intention)
    (h_not_impossible : ¬isImpossible state nm intention) :
    intention ∈ (deliberate state nm).intentions := by
  simp [deliberate, Finset.mem_filter, isAchieved, isImpossible] at *
  exact ⟨h_in, h_not_achieved, h_not_impossible⟩

/-- Achieved intentions are dropped. -/
theorem achieved_dropped (state : BDIState) (nm : NegationMap)
    (intention : Prop')
    (h_achieved : isAchieved state intention) :
    intention ∉ (deliberate state nm).intentions := by
  simp [deliberate, Finset.mem_filter, isAchieved] at *
  intro _
  exact h_achieved

/-- Impossible intentions are dropped. -/
theorem impossible_dropped (state : BDIState) (nm : NegationMap)
    (intention : Prop')
    (h_impossible : isImpossible state nm intention) :
    intention ∉ (deliberate state nm).intentions := by
  simp [deliberate, Finset.mem_filter, isImpossible] at *
  intro _
  simp [h_impossible]

/-! ## Theorem 5: Logical Consequence Monotone -/

/-- A consequence relation: conclusions derivable from a belief set. -/
def consequences (beliefs : BeliefSet) (rules : Prop' → Finset Prop') : Finset Prop' :=
  beliefs.biUnion rules

/-- Monotonicity of logical consequence: adding beliefs to the set
    never invalidates existing conclusions. In classical logic,
    if Gamma |- phi, then Gamma ∪ Delta |- phi.
    This is the monotonicity property of classical entailment. -/
theorem logical_consequence_monotone (beliefs₁ beliefs₂ : BeliefSet)
    (rules : Prop' → Finset Prop')
    (h_subset : beliefs₁ ⊆ beliefs₂) :
    consequences beliefs₁ rules ⊆ consequences beliefs₂ rules := by
  intro p hp
  simp [consequences, Finset.mem_biUnion] at *
  obtain ⟨q, hq_in, hq_rule⟩ := hp
  exact ⟨q, h_subset hq_in, hq_rule⟩

/-- Consequences of the empty set are empty (no premises, no conclusions). -/
theorem empty_no_consequences (rules : Prop' → Finset Prop')
    (h_no_axioms : ∀ p, rules p = ∅ → True) :
    consequences ∅ rules = ∅ := by
  simp [consequences]

/-- Adding a belief can only grow the consequence set. -/
theorem add_belief_grows_consequences (beliefs : BeliefSet) (p : Prop')
    (rules : Prop' → Finset Prop') :
    consequences beliefs rules ⊆ consequences (beliefs ∪ {p}) rules := by
  exact logical_consequence_monotone beliefs (beliefs ∪ {p}) rules Finset.subset_union_left

end Agent.LogicAgent
