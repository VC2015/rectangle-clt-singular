import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp

/-! Finite Boolean cubes and the uniform average sensitivity used in Kane (2015). -/

open scoped BigOperators

namespace Kane

abbrev Cube (n : ℕ) := Fin n → Bool

def flip {n : ℕ} (x : Cube n) (i : Fin n) : Cube n :=
  Function.update x i (!x i)

noncomputable def avg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

def boolVal (b : Bool) : ℝ := if b then 1 else 0

noncomputable def averageSensitivity {n : ℕ} (f : Cube n → Bool) : ℝ :=
  avg fun x => ∑ i : Fin n, if f x = f (flip x i) then (0 : ℝ) else 1

def signedCoord {n : ℕ} (s x : Cube n) (i : Fin n) : ℝ :=
  if x i = s i then 1 else -1

def signedSum {n : ℕ} (s x : Cube n) : ℝ := ∑ i, signedCoord s x i

structure UnateFunction (n : ℕ) where
  fn : Cube n → Bool
  direction : Cube n
  increasing : ∀ x i, x i = direction i → fn (flip x i) ≤ fn x

def union {n : ℕ} : List (UnateFunction n) → Cube n → Bool
  | [], _ => false
  | f :: fs, x => f.fn x || union fs x

end Kane
