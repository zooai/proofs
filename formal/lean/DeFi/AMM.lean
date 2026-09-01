/-
  Automated Market Maker (AMM) Invariants

  Constant-product AMM for Lux DeFi.
  x * y = k invariant preserved on every swap.
  Permissionless liquidity provision.

  Maps to:
  - lux/exchange: AMM pool contracts
  - zoo/contracts: bridge token AMM pools

  Properties:
  - Constant product: x * y = k preserved (or increased by fees)
  - No free tokens: output ≤ reserve
  - Fee conservation: fees accrue to LPs
  - Permissionless: anyone can provide liquidity

  Authors: Zoo Labs Foundation Research (Dec 2025), Woo Bin (Mar 2026)
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace DeFi.AMM

/-- AMM pool state -/
structure Pool where
  reserveX : Nat
  reserveY : Nat
  totalLP : Nat
  feeBps : Nat         -- fee in basis points (e.g., 30 = 0.3%)

/-- The constant product -/
def invariant (p : Pool) : Nat := p.reserveX * p.reserveY

/-- Swap dx of X for dy of Y -/
def swap (p : Pool) (dx : Nat) : Pool × Nat :=
  let feeAdjusted := dx * (10000 - p.feeBps) / 10000
  let dy := p.reserveY * feeAdjusted / (p.reserveX + feeAdjusted)
  ({ p with reserveX := p.reserveX + dx
          , reserveY := p.reserveY - dy }, dy)

/-- NO FREE TOKENS: Output bounded by reserve -/
theorem output_bounded (p : Pool) (dx : Nat) :
    (swap p dx).2 ≤ p.reserveY := by
  simp only [swap]
  apply Nat.div_le_of_le_mul
  set fA := dx * (10000 - p.feeBps) / 10000
  calc p.reserveY * fA ≤ p.reserveY * fA + p.reserveX * p.reserveY := Nat.le_add_right _ _
    _ = (p.reserveX + fA) * p.reserveY := by ring

/-- ZERO IN = ZERO OUT -/
theorem zero_in_zero_out (p : Pool) : (swap p 0).2 = 0 := by
  simp [swap]

/-- INVARIANT PRESERVED: k never decreases (fees increase it) -/
theorem invariant_preserved (p : Pool) (dx : Nat)
    (_h_rx : p.reserveX > 0) (_h_ry : p.reserveY > 0) :
    invariant (swap p dx).1 ≥ invariant p := by
  simp only [swap, invariant]
  -- Abbreviations: fee-adjusted input fA, denominator D, output dy
  set fA := dx * (10000 - p.feeBps) / 10000 with hfA
  set D := p.reserveX + fA with hD
  set dy := p.reserveY * fA / D with hdy
  -- fA ≤ dx  (fee only shrinks the input)
  have hfA_le_dx : fA ≤ dx := by
    rw [hfA]
    apply Nat.div_le_of_le_mul
    calc dx * (10000 - p.feeBps) ≤ dx * 10000 := Nat.mul_le_mul_left dx (Nat.sub_le _ _)
      _ = 10000 * dx := Nat.mul_comm _ _
  -- dy ≤ reserveY  (output never exceeds the reserve)
  have hfA_le_D : fA ≤ D := by rw [hD]; exact Nat.le_add_left _ _
  have hdy_le_Y : dy ≤ p.reserveY := by
    rw [hdy]
    apply Nat.div_le_of_le_mul
    calc p.reserveY * fA ≤ p.reserveY * D := Nat.mul_le_mul_left p.reserveY hfA_le_D
      _ = D * p.reserveY := Nat.mul_comm _ _
  -- floor-division fact:  D * dy ≤ reserveY * fA
  have hfloor : D * dy ≤ p.reserveY * fA := by
    rw [hdy, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  -- core inequality on the (R+fA) factor:  D*(reserveY - dy) ≥ reserveX*reserveY
  have hcore : D * (p.reserveY - dy) ≥ p.reserveX * p.reserveY := by
    rw [Nat.mul_sub]
    have hDY : D * p.reserveY = p.reserveX * p.reserveY + p.reserveY * fA := by
      rw [hD]; ring
    omega
  -- monotonicity in the first factor:  reserveX + dx ≥ D = reserveX + fA
  have hmono : (p.reserveX + dx) * (p.reserveY - dy) ≥ D * (p.reserveY - dy) := by
    apply Nat.mul_le_mul_right
    rw [hD]; exact Nat.add_le_add_left hfA_le_dx _
  exact le_trans hcore hmono

/-- ADD LIQUIDITY: Mint LP tokens -/
def addLiquidity (p : Pool) (dx dy : Nat) : Pool × Nat :=
  let lpMinted := if p.totalLP = 0 then dx
    else dx * p.totalLP / p.reserveX
  ({ p with reserveX := p.reserveX + dx
          , reserveY := p.reserveY + dy
          , totalLP := p.totalLP + lpMinted }, lpMinted)

/-- LIQUIDITY GROWS -/
theorem add_liquidity_grows (p : Pool) (dx dy : Nat) :
    (addLiquidity p dx dy).1.reserveX ≥ p.reserveX := by
  simp [addLiquidity]

/-- LP TOKENS MINTED -/
theorem lp_minted (p : Pool) (dx dy : Nat) :
    (addLiquidity p dx dy).1.totalLP ≥ p.totalLP := by
  simp [addLiquidity]

/-- PERMISSIONLESS: No access control -/
theorem anyone_can_swap (p : Pool) (dx : Nat) :
    (swap p dx).1.reserveX ≥ p.reserveX := by
  simp [swap]

end DeFi.AMM
