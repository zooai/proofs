/-
  Zoo formal verification — entry point.

  `zoo_correctness` conjoins results proved elsewhere in this corpus. It holds
  what it imports and nothing more, which is the only thing a top-level theorem
  can honestly do: `lake build` succeeding here means Lean checked each
  conjunct's proof, in its own module, from its own hypotheses.

  Every conjunct below rests on Lean's ambient logic alone — no axiom of ours —
  which `lean/axioms.py` reports per theorem. Deliberately absent:

  - Safety and liveness. `Consensus.safety` composes two axioms;
    `Consensus.Liveness.liveness` applies the axioms that are its argument.
  - Threshold unforgeability, post-quantum hardness and FHE correctness. These
    reduce to hardness axioms: the reductions are checked, the assumptions are
    assumed.
  - Anything about GPU throughput. A speedup is a measurement, not a theorem,
    and belongs in a benchmark.

  Zoo inherits Lux's consensus and cryptography models; `luxfi/proofs` is where
  those are maintained.

  Maps to: the modules imported below.
-/

import Consensus.BFT
import Governance.ZIP

namespace Zoo.Main

/-- Results this corpus proves outright, conjoined.

    An earlier version stated eight conjuncts, of which six were arithmetic
    facts about `Nat` presented as systems claims — `p * rate ≥ rate` as "GPU
    EVM linear scaling", `cpu_time / speedup ≤ cpu_time` as "GPU FHE bootstrap
    speedup", `pairs / cores ≤ pairs` as "GPU DEX pair parallelism",
    `max a b ≤ a + b` as "hybrid finality", `t - 1 < t` as threshold secrecy —
    and the eighth was `True`. Its header claimed a 40x FHE bootstrap speedup,
    which no theorem here establishes. Each conjunct now names a theorem proved
    in the module it comes from, applied rather than restated. -/
theorem zoo_correctness :
    -- Quorum intersection: two quorums each above 2n/3, with f < n/3 faulty,
    -- overlap in more than f nodes — so they share an honest one.
    (∀ n f : Nat, f < n / 3 → ∀ q1 q2 : Nat,
      q1 > 2 * n / 3 → q2 > 2 * n / 3 → q1 + q2 > n + f) ∧
    -- An honest majority of 2f+1 in 3f+1 nodes clears that threshold.
    (∀ f : Nat, 0 < f → 2 * f + 1 > 2 * (3 * f + 1) / 3) ∧
    -- Governance: a proposal at or above quorum passes.
    (∀ p : Governance.ZIP.Proposal, p.votesFor ≥ p.quorum → p.passes = true) :=
  ⟨fun n f hf q1 q2 hq1 hq2 =>
     Consensus.BFT.quorum_intersection n f hf q1 q2 hq1 hq2,
   fun f hf => Consensus.BFT.honest_majority_sufficient f hf,
   fun p h => Governance.ZIP.sufficient_votes_pass p h⟩

end Zoo.Main
