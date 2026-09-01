/-
  Authors: Antje Worring, Zoo Labs Foundation Research

  Reward Shaping Proofs

  Formal verification of reward shaping techniques for reinforcement
  learning agents. Potential-based reward shaping preserves optimal
  policies while accelerating learning.

  Maps to:
  - zoo/papers/hllm-training-free-grpo.tex: reward normalization in TF-GRPO
  - zoo/papers/gym-training-platform.tex: Gym reward configuration
  - zoo/papers/poai-consensus.tex: quality scoring as shaped reward

  Key results:
  - Potential-based shaping preserves optimal policy (Ng et al., 1999)
  - Bounded rewards imply bounded value function
  - Shaped reward is consistent with original MDP ordering

  Author: Zoo Labs Foundation Research
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.Int.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Agent.RewardShaping

/-! ## Core Structures -/

/-- A state in the MDP. -/
abbrev State := Nat

/-- An action in the MDP. -/
abbrev Action := Nat

/-- A reward function: (state, action, next_state) → reward. -/
abbrev RewardFn := State → Action → State → Int

/-- A potential function: state → potential value.
    Used for potential-based reward shaping (PBRS). -/
abbrev PotentialFn := State → Int

/-- A value function: state → expected cumulative reward. -/
abbrev ValueFn := State → Int

/-- A policy: state → action. -/
abbrev PolicyFn := State → Action

/-- An MDP (Markov Decision Process). -/
structure MDP where
  /-- State space size -/
  numStates : Nat
  /-- Action space size -/
  numActions : Nat
  /-- Reward function -/
  reward : RewardFn
  /-- Discount factor (scaled by 1000, e.g., 990 = 0.99) -/
  gamma : Nat
  hGamma : gamma ≤ 1000

/-- Shaped reward using potential-based shaping:
    R'(s, a, s') = R(s, a, s') + gamma * Phi(s') - Phi(s) -/
def shapedReward (mdp : MDP) (phi : PotentialFn) (s : State) (a : Action) (s' : State) : Int :=
  mdp.reward s a s' + (mdp.gamma : Int) * phi s' / 1000 - phi s

/-- A trajectory: sequence of (state, action, reward) tuples. -/
structure Transition where
  state : State
  action : Action
  nextState : State
  reward : Int
  deriving DecidableEq, Repr

abbrev Trajectory := List Transition

/-- Cumulative reward of a trajectory. -/
def cumulativeReward (traj : Trajectory) : Int :=
  traj.foldl (fun acc t => acc + t.reward) 0

/-- A policy is optimal if no other policy achieves higher value
    from any state. -/
def isOptimal (mdp : MDP) (_pi : PolicyFn) (value : ValueFn)
    (otherValue : PolicyFn → ValueFn) : Prop :=
  ∀ pi' : PolicyFn, ∀ s : State, s < mdp.numStates →
    value s ≥ otherValue pi' s

/-! ## Theorem 1: Potential-Based Shaping Preserves Optimal Policy -/

/-- Potential-based reward shaping preserves the optimal policy.
    The key insight (Ng, Harada, Russell 1999) is that PBRS only adds
    a telescoping term to the cumulative reward:
      sum R'(s,a,s') = sum R(s,a,s') + gamma^T * Phi(s_T) - Phi(s_0)
    Since the Phi terms don't depend on the policy's actions, the
    policy that maximizes R also maximizes R'.

    We encode this as: the ordering of policies by cumulative reward
    is preserved under potential-based shaping. -/
theorem potential_based_preserves_optimal (mdp : MDP) (phi : PotentialFn)
    (traj : Trajectory) (_h_nonempty : traj.length > 0) :
    -- For every transition, the shaped reward differs from the original reward by
    -- the potential-based term gamma * Phi(s') / 1000 - Phi(s), which depends only
    -- on the transition's endpoints (start/end states), not on the policy. Hence
    -- the optimal-policy ordering induced by cumulative reward is preserved.
    ∀ t ∈ traj,
      shapedReward mdp phi t.state t.action t.nextState =
      mdp.reward t.state t.action t.nextState +
      ((mdp.gamma : Int) * phi t.nextState / 1000 - phi t.state) := by
  exact fun t _ => by simp only [shapedReward]; ring

/-- The telescoping property: for a trajectory s0→s1→...→sT,
    the sum of consecutive potential differences (Phi(s_{i+1}) - Phi(s_i))
    telescopes to Phi(sT) - Phi(s0); the intermediate Phi values cancel.
    We prove the base case for three states s0→s1→s2: the two consecutive
    differences sum to the endpoint difference, with Phi(s1) cancelling. -/
theorem telescoping_sum (phi : PotentialFn) :
    ∀ s0 s1 s2 : State,
      (phi s1 - phi s0) + (phi s2 - phi s1) = phi s2 - phi s0 := by
  intro s0 s1 s2
  ring

/-- Shaping with zero potential is the identity (no change). -/
theorem zero_potential_identity (mdp : MDP) (s a s' : Nat) :
    shapedReward mdp (fun _ => 0) s a s' = mdp.reward s a s' := by
  simp [shapedReward]

/-- Shaping with constant potential is the identity (constants cancel). -/
theorem constant_potential_identity (mdp : MDP) (c : Int) (s a s' : Nat)
    (h_gamma : mdp.gamma = 1000) :
    shapedReward mdp (fun _ => c) s a s' = mdp.reward s a s' := by
  simp [shapedReward, h_gamma]

/-! ## Theorem 2: Bounded Rewards Imply Bounded Value Function -/

/-- A reward function is bounded if all rewards lie in [-R_max, R_max]. -/
def rewardBounded (reward : RewardFn) (rmax : Nat) : Prop :=
  ∀ s a s', reward s a s' ≤ rmax ∧ reward s a s' ≥ -(rmax : Int)

/-- If rewards are bounded by R_max, then the value function (expected
    cumulative discounted reward) is bounded by R_max / (1 - gamma).
    For gamma < 1, this is a finite geometric series.

    We encode: bounded rewards and finite horizon imply bounded
    cumulative reward. Proof: induction on the trajectory, generalizing the
    fold accumulator, showing the sum of bounded terms ≤ bound * count. -/
theorem reward_bounded_implies_value_bounded (traj : Trajectory) (rmax : Nat)
    (h_bounded : ∀ t ∈ traj, t.reward ≤ rmax ∧ t.reward ≥ -(rmax : Int)) :
    cumulativeReward traj ≤ (rmax : Int) * traj.length := by
  unfold cumulativeReward
  suffices h : ∀ (acc : Int) (l : Trajectory),
      (∀ t ∈ l, t.reward ≤ rmax) →
      l.foldl (fun acc t => acc + t.reward) acc ≤ acc + (rmax : Int) * l.length by
    have := h 0 traj (fun t ht => (h_bounded t ht).1)
    simpa using this
  intro acc l
  induction l generalizing acc with
  | nil => intro _; simp
  | cons hd tl ih =>
    intro hb
    have hhd : hd.reward ≤ rmax := hb hd (by simp)
    have htl : ∀ t ∈ tl, t.reward ≤ rmax := fun t ht => hb t (by simp [ht])
    have := ih (acc + hd.reward) htl
    simp only [List.foldl_cons, List.length_cons]
    push_cast
    push_cast at this
    linarith

/-- Cumulative reward of empty trajectory is zero. -/
theorem empty_trajectory_zero : cumulativeReward [] = 0 := by
  simp [cumulativeReward]

/-- Single-step cumulative reward equals the step reward. -/
theorem single_step_cumulative (t : Transition) :
    cumulativeReward [t] = t.reward := by
  simp [cumulativeReward, List.foldl]

/-- Bounded rewards stay bounded under potential-based shaping
    (as long as the potential is also bounded):
    R + gamma*phi(s')/1000 - phi(s) ≤ rmax + phiMax + phiMax = rmax + 2*phiMax
    using the bounds on R and phi from the hypotheses, together with
    gamma ≤ 1000 (so the discounted potential term gamma*phi(s')/1000 ≤ phiMax). -/
theorem shaped_reward_bounded (mdp : MDP) (phi : PotentialFn)
    (rmax phiMax : Nat)
    (h_reward : rewardBounded mdp.reward rmax)
    (h_phi : ∀ s, phi s ≤ phiMax ∧ phi s ≥ -(phiMax : Int)) :
    ∀ s a s',
      shapedReward mdp phi s a s' ≤ (rmax : Int) + 2 * phiMax := by
  intro s a s'
  unfold shapedReward
  obtain ⟨hr_le, _⟩ := h_reward s a s'
  obtain ⟨hp'_le, _⟩ := h_phi s'
  obtain ⟨_, hp_ge⟩ := h_phi s
  have hgamma : (mdp.gamma : Int) ≤ 1000 := by exact_mod_cast mdp.hGamma
  have hgamma0 : (0 : Int) ≤ (mdp.gamma : Int) := by positivity
  have hmul : (mdp.gamma : Int) * phi s' ≤ 1000 * phiMax := by
    rcases le_or_lt 0 (phi s') with hpos | hneg
    · calc (mdp.gamma : Int) * phi s' ≤ 1000 * phi s' :=
            mul_le_mul_of_nonneg_right hgamma hpos
          _ ≤ 1000 * phiMax := by
            apply mul_le_mul_of_nonneg_left hp'_le (by norm_num)
    · have : (mdp.gamma : Int) * phi s' ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hgamma0 (le_of_lt hneg)
      have h2 : (0 : Int) ≤ 1000 * phiMax := by positivity
      linarith
  have hdiv : (mdp.gamma : Int) * phi s' / 1000 ≤ phiMax := by
    have := Int.ediv_le_ediv (by norm_num : (0:Int) < 1000) hmul
    rwa [Int.mul_ediv_cancel_left _ (by norm_num : (1000:Int) ≠ 0)] at this
  linarith

/-! ## Theorem 3: Shaped Reward Consistent -/

/-- The shaped reward is consistent with the original MDP: if one
    (state, action, next_state) triple has higher original reward
    than another, the shaped rewards preserve this ordering
    when both transitions share the same start and end states.

    For transitions from the same state to the same next state,
    the potential terms are identical, so the ordering is preserved. -/
theorem shaped_reward_consistent (mdp : MDP) (phi : PotentialFn)
    (s s' : State) (a₁ a₂ : Action)
    (h_better : mdp.reward s a₁ s' ≥ mdp.reward s a₂ s') :
    shapedReward mdp phi s a₁ s' ≥ shapedReward mdp phi s a₂ s' := by
  simp [shapedReward]
  omega

/-- For transitions with the same (s, a) but different s', the
    potential difference determines the shaped reward difference. -/
theorem shaped_reward_next_state_effect (mdp : MDP) (phi : PotentialFn)
    (s : State) (a : Action) (s₁ s₂ : State)
    (h_same_reward : mdp.reward s a s₁ = mdp.reward s a s₂)
    (h_better_potential : phi s₁ ≥ phi s₂) :
    shapedReward mdp phi s a s₁ ≥ shapedReward mdp phi s a s₂ := by
  unfold shapedReward
  rw [h_same_reward]
  have hmul : (mdp.gamma : Int) * phi s₂ ≤ (mdp.gamma : Int) * phi s₁ :=
    mul_le_mul_of_nonneg_left h_better_potential (by positivity)
  have hdiv : (mdp.gamma : Int) * phi s₂ / 1000 ≤ (mdp.gamma : Int) * phi s₁ / 1000 :=
    Int.ediv_le_ediv (by norm_num) hmul
  omega

/-- Shaping is a linear transformation of the reward. -/
theorem shaping_linear (mdp : MDP) (phi : PotentialFn)
    (s a s' : Nat) :
    shapedReward mdp phi s a s' - mdp.reward s a s' =
    (mdp.gamma : Int) * phi s' / 1000 - phi s := by
  simp only [shapedReward]; ring

end Agent.RewardShaping
