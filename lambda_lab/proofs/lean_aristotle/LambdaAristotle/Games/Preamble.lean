/-
  LambdaAristotle.Games.Preamble
  ------------------------------
  Used by the games session prewarm. We import the heavy tactic surface
  ONCE here, build the olean, and then exercise each tactic in a trivial
  example. Lean caches typeclass instance derivations (CommRing for Nat
  via `ring`, the simp set, omega's Presburger preprocessor, etc.) at
  elaboration time — so games using these tactics for real later don't
  pay the warm-up cost.

  Sources here are intentionally minimal; only the `import` and the
  per-tactic single-line `example` are required to seed the caches.
-/
import Mathlib.Tactic

namespace LambdaAristotle.Games.Preamble

example : (1 : Nat) = 1 := by rfl
example : (1 : Nat) = 1 := by simp
example : (2 + 3 : Nat) = 5 := by norm_num
example : (2 + 3 : Nat) = 5 := by decide
example : (2 + 3 : Nat) = 5 := by omega
example : ((1 : Int) + 2) * 3 = 9 := by ring
example (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by linarith
example (a b : Nat) : a + b = b + a := by omega
example : True := by trivial

end LambdaAristotle.Games.Preamble
