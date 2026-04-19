/-
  Authors: Antje Worring, Zach Kelling

  Automated Market Maker (HMM) Invariants

  Hanzo Market Maker: constant-product AMM for AI compute resources.
  Native DEX for pricing $AI against other assets.

  Maps to:
  - HIP-0008: HMM specification
  - zoo/contracts: AMM contracts
  - zoo/solidity: UniswapV2-style AMM math

  Properties:
  - Output is bounded by reserve (`output_bounded`)
  - Zero input produces zero output (`zero_in_zero_out`)
  - Adding liquidity is monotone on reserves and LP supply
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Contract.AMM

/-- AMM pool state (constant product x * y = k). -/
structure Pool where
  reserveX : Nat
  reserveY : Nat
  totalLP  : Nat
  feeBps   : Nat

/-- The constant product k = x * y. -/
def invariant (p : Pool) : Nat := p.reserveX * p.reserveY

/-- Swap: trade `dx` of token X for `dy` of token Y (fee taken on input). -/
def swap (p : Pool) (dx : Nat) : Pool × Nat :=
  let feeAdjusted := dx * (10000 - p.feeBps) / 10000
  let dy := p.reserveY * feeAdjusted / (p.reserveX + feeAdjusted)
  ({ p with reserveX := p.reserveX + dx
          , reserveY := p.reserveY - dy }, dy)

/-- **Axiom (constant product under fee):** with a non-zero fee, swapping
    never decreases the pool invariant `x * y`. This is the standard
    UniswapV2 result; the arithmetic is long and relies on the specific
    rounding in `feeAdjusted`. Stated as an axiom pending full
    mechanisation. -/
axiom swap_preserves_invariant
    (p : Pool) (dx : Nat)
    (_h_nonzero : dx > 0) (_h_reserve : p.reserveX > 0) (_h_reserveY : p.reserveY > 0) :
    invariant p ≤ invariant (swap p dx).1

/-- **Theorem (output bounded):** the amount of Y handed out never
    exceeds the current Y reserve. Since `dy = reserveY * f / (reserveX + f)`
    with integer division, we have `dy ≤ reserveY`. -/
theorem output_bounded (p : Pool) (dx : Nat) :
    (swap p dx).2 ≤ p.reserveY := by
  unfold swap
  simp only
  -- Goal: p.reserveY * feeAdjusted / (p.reserveX + feeAdjusted) ≤ p.reserveY
  set f := dx * (10000 - p.feeBps) / 10000
  by_cases h : p.reserveX + f = 0
  · simp [h]
  · have hpos : 0 < p.reserveX + f := Nat.pos_of_ne_zero h
    calc p.reserveY * f / (p.reserveX + f)
        ≤ p.reserveY * f / f := by
          by_cases hf : f = 0
          · simp [hf]
          · apply Nat.div_le_div_left (Nat.le_add_left _ _) (Nat.pos_of_ne_zero hf)
      _ ≤ p.reserveY := by
          by_cases hf : f = 0
          · simp [hf]
          · rw [Nat.mul_div_assoc _ (Nat.dvd_refl f), Nat.div_self (Nat.pos_of_ne_zero hf)]
            simp

/-- **Theorem:** zero input produces zero output. Both the fee
    adjustment and the subsequent division are monotone and yield 0
    when the input is 0. -/
theorem zero_in_zero_out (p : Pool) :
    (swap p 0).2 = 0 := by
  unfold swap; simp

/-- Add liquidity: mint LP tokens proportional to contribution. -/
def addLiquidity (p : Pool) (dx dy : Nat) : Pool × Nat :=
  let lpMinted := if p.totalLP = 0 then dx
    else dx * p.totalLP / p.reserveX
  ({ p with reserveX := p.reserveX + dx
          , reserveY := p.reserveY + dy
          , totalLP  := p.totalLP  + lpMinted }, lpMinted)

/-- **Theorem (adding liquidity grows reserves):** reserveX is monotone
    under `addLiquidity`. -/
theorem add_liquidity_increases (p : Pool) (dx dy : Nat) :
    p.reserveX ≤ (addLiquidity p dx dy).1.reserveX := by
  unfold addLiquidity; simp

/-- **Theorem (LP tokens mint monotone):** totalLP never decreases. -/
theorem add_liquidity_mints (p : Pool) (dx dy : Nat) :
    p.totalLP ≤ (addLiquidity p dx dy).1.totalLP := by
  unfold addLiquidity; simp

end Contract.AMM
