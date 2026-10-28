import Decoupling.HighDim.StableFreeEffectiveDimensions
import Decoupling.HighDim.LaurentSolverGrowth

/-!
# HD012 one uniform polynomial envelope for an actual Schanuel stage

All numerical functions being bounded are the cost and box functions of
the executed compiler, two lifting solves and explicit matrix updates.
These estimates will be iterated along the proved finite recursion.
-/
namespace Decoupling.HighDim.StableFree.Resource
open Effective LaurentArithmetic

def solverSize (s : ℕ) : ℕ := 12*(s+1)^2
def solveCap (D s : ℕ) : ℕ := LaurentSolverGrowth.bound D (solverSize s)
def liftCap (D s : ℕ) : ℕ := 12*s*s*boxSize D (2*s)+solveCap D s
def prepareCap (D s : ℕ) : ℕ := (2*s)*(2*s)*(2*s)*boxSize D (2*s)*(2*boxSize D s+1)
def stepBound (D s : ℕ) : ℕ :=
  s+1+2*solveCap D s+prepareCap D s+2*liftCap D s+
    DenseTower.updateCost D s s s s (solveCap D s)

theorem input_le_solverSize (s : ℕ) : s ≤ solverSize s := by unfold solverSize; nlinarith
theorem twice_le_solverSize (s : ℕ) : 2*s ≤ solverSize s := by unfold solverSize; nlinarith
theorem input_le_solveCap (D s : ℕ) : s ≤ solveCap D s :=
  (input_le_solverSize s).trans (LaurentSolverGrowth.input_le_bound D (solverSize s))
theorem input_le_stepBound (D s : ℕ) : s ≤ stepBound D s := by unfold stepBound; omega
theorem next_le_stepBound (D s : ℕ) : s+2*solveCap D s ≤ stepBound D s := by
  unfold stepBound
  omega

theorem solveCap_monotone (D : ℕ) : Monotone (solveCap D) := by
  intro s t h
  apply LaurentSolverGrowth.bound_monotone D
  unfold solverSize
  gcongr

theorem scalar_rows_le {v k l s : ℕ} (hv : v ≤ 2*s) (hk : k ≤ 2*s) (hl : l ≤ 2*s) :
    (v+(k+k))*l ≤ solverSize s := by
  have hm := Nat.mul_le_mul (show v+(k+k) ≤ 6*s by omega) hl
  unfold solverSize
  nlinarith

theorem scalar_columns_le {k l r s : ℕ} (hk : k ≤ 2*s) (hl : l ≤ 2*s) (hr : r ≤ 2*s) :
    (k+r)*l ≤ solverSize s := by
  have hm := Nat.mul_le_mul (Nat.add_le_add hk hr) hl
  unfold solverSize
  nlinarith

theorem stageLiftBox_le {D v k l h s : ℕ}
    (hv : v ≤ 2*s) (hk : k ≤ 2*s) (hl : l ≤ 2*s) (hh : h ≤ 2*s) :
    stageLiftBox D v k l h ≤ solveCap D s := by
  unfold stageLiftBox
  apply max_le
  · exact (LaurentSolverGrowth.outputBox_le (scalar_rows_le hv hk hl)
      (hh.trans (twice_le_solverSize s))).trans
        (LaurentSolverGrowth.radiusCap_le_bound D (solverSize s))
  · exact (LaurentSolverGrowth.outputBox_le (scalar_rows_le hv hl hk)
      (hh.trans (twice_le_solverSize s))).trans
        (LaurentSolverGrowth.radiusCap_le_bound D (solverSize s))

theorem liftSolveCost_le {D v r k l h s : ℕ}
    (hv : v ≤ 2*s) (hr : r ≤ 2*s) (hk : k ≤ 2*s) (hl : l ≤ 2*s) (hh : h ≤ 2*s) :
    liftSolveCost D v r k l h ≤ liftCap D s := by
  have hcoeff : v*r+k*k+l*l ≤ 12*s*s := by
    have hvr := Nat.mul_le_mul hv hr
    have hkk := Nat.mul_le_mul hk hk
    have hll := Nat.mul_le_mul hl hl
    nlinarith
  have hcomp := Nat.mul_le_mul hcoeff (boxSize_mono (D := D) hh)
  have hs := LaurentSolverGrowth.solveCost_le (D := D)
    (scalar_rows_le hv hk hl) (scalar_columns_le hk hl hr) (hh.trans (twice_le_solverSize s))
  exact Nat.add_le_add hcomp hs

theorem updateCost_mono {D a b p q h a' b' p' q' h' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') (hp : p ≤ p') (hq : q ≤ q') (hh : h ≤ h') :
    DenseTower.updateCost D a b p q h ≤ DenseTower.updateCost D a' b' p' q' h' := by
  unfold DenseTower.updateCost boxSize
  gcongr

theorem stepBound_monotone (D : ℕ) : Monotone (stepBound D) := by
  intro s t h
  have hq := solveCap_monotone D h
  have hu := updateCost_mono (D := D) h h h h hq
  unfold stepBound prepareCap liftCap
  gcongr
  · exact boxSize_mono (by omega)
  · exact boxSize_mono h
  · exact boxSize_mono (by omega)

/-- All terms of the actual nonterminal cost recurrence fit one envelope. -/
theorem stage_cost_le {D s₀ t a b p q h S : ℕ}
    (hs : s₀ ≤ S) (ht : t ≤ S) (ha : a ≤ S) (hb : b ≤ S)
    (hp : p ≤ S) (hq : q ≤ S) (hh : h ≤ S) :
    (s₀+p)*(b+q)*(t+q)*boxSize D (h+h)*(2*boxSize D h+1) +
      (liftSolveCost D (s₀+p) 0 (a+p) (b+q) (h+h) +
        liftSolveCost D (s₀+p) 0 (b+q) (a+p) (h+h)) +
      DenseTower.updateCost D a b p q (stageLiftBox D (s₀+p) (a+p) (b+q) (h+h))
        ≤ stepBound D S := by
  have hprep : (s₀+p)*(b+q)*(t+q)*boxSize D (h+h)*(2*boxSize D h+1) ≤ prepareCap D S := by
    unfold prepareCap boxSize
    gcongr <;> omega
  have h₁ := liftSolveCost_le (D := D) (by omega : s₀+p ≤ 2*S) (by omega : 0 ≤ 2*S)
    (by omega : a+p ≤ 2*S) (by omega : b+q ≤ 2*S) (by omega : h+h ≤ 2*S)
  have h₂ := liftSolveCost_le (D := D) (by omega : s₀+p ≤ 2*S) (by omega : 0 ≤ 2*S)
    (by omega : b+q ≤ 2*S) (by omega : a+p ≤ 2*S) (by omega : h+h ≤ 2*S)
  have hbox := stageLiftBox_le (D := D) (by omega : s₀+p ≤ 2*S)
    (by omega : a+p ≤ 2*S) (by omega : b+q ≤ 2*S) (by omega : h+h ≤ 2*S)
  have hu := updateCost_mono (D := D) ha hb hp hq hbox
  unfold stepBound
  omega

theorem nextStageBox_le {D s₀ a b p q h S : ℕ}
    (hs : s₀ ≤ S) (ha : a ≤ S) (hb : b ≤ S) (hp : p ≤ S) (hq : q ≤ S) (hh : h ≤ S) :
    nextStageBox D s₀ a b p q h ≤ stepBound D S := by
  have hbox := stageLiftBox_le (D := D) (by omega : s₀+p ≤ 2*S)
    (by omega : a+p ≤ 2*S) (by omega : b+q ≤ 2*S) (by omega : h+h ≤ 2*S)
  unfold nextStageBox
  apply max_le
  · exact hh.trans (input_le_stepBound D S)
  · exact (show stageLiftBox D (s₀+p) (a+p) (b+q) (h+h) +
        stageLiftBox D (s₀+p) (a+p) (b+q) (h+h) ≤ S+2*solveCap D S by omega).trans
      (next_le_stepBound D S)

end Decoupling.HighDim.StableFree.Resource
