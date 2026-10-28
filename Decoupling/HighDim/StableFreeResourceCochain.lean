import Decoupling.HighDim.StableFreeResourceRecursion
import Decoupling.HighDim.StableFreeEffectiveCochainCost

/-!
# Global numeric growth of native C4, including the initial quotient stage

The budget contains the actual original free ranks, relation rank and input
radius. The factor five is the proved radius of the concrete initial
formulas. It is not an assumed bound on a selected projective basis.
-/
namespace Decoupling.HighDim.StableFree.Resource
open Effective Effective.CochainProgram LaurentArithmetic
variable {K : Type*} {D h₀ length n c : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def nativeBudget (F : DenseTower K D h₀ length n) (G : DenseTower K D h₀ length c)
    (p e rel h : ℕ) : ℕ := F.rankBudget G (c+(e+p)) (n+p)+rel+h

def firstCost (D c n p e rel h : ℕ) : ℕ :=
  (liftSolveCost D (n+p) rel (n+p) (c+(e+p)) (Initial.radius5 h) +
    liftSolveCost D (n+p) rel (c+(e+p)) (n+p) (Initial.radius5 h)) +
  DenseTower.updateCost D n c p (e+p)
    (stageLiftBox D (n+p) (n+p) (c+(e+p)) (Initial.radius5 h))

/-- Initial quotient solve and every actual recursive level fit the same
iterated polynomial envelope. -/
theorem stabilization_bounds (F : DenseTower K D h₀ length n) (G : DenseTower K D h₀ length c)
    (p e rel h S : ℕ) (hb : nativeBudget F G p e rel h ≤ S) :
    F.outputBox G (c+(e+p)) (n+p) (firstBox D c n p e h) ≤
        iteratedBound D (length+1) (5*S) ∧
    firstCost D c n p e rel h + F.costBound G (c+(e+p)) (n+p) (firstBox D c n p e h) ≤
        (length+1)*iteratedBound D (length+1) (5*S) := by
  have hc : c ≤ 5*S := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have hn : n ≤ 5*S := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have hp : p ≤ 5*S := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have hq : e+p ≤ 5*S := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have hr : rel ≤ 2*(5*S) := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have hh : Initial.radius5 h ≤ 5*S := by
    rw [Initial.radius5_eq]
    dsimp [nativeBudget] at hb
    omega
  have hnp : n+p ≤ 2*(5*S) := by omega
  have hcq : c+(e+p) ≤ 2*(5*S) := by omega
  have hlift := stageLiftBox_le (D := D) hnp hnp hcq (show Initial.radius5 h ≤ 2*(5*S) by omega)
  have hfirst : firstBox D c n p e h ≤ stepBound D (5*S) := by
    unfold firstBox
    apply max_le
    · exact hh.trans (input_le_stepBound D (5*S))
    · exact (show stageLiftBox D (n+p) (n+p) (c+(e+p)) (Initial.radius5 h) +
          stageLiftBox D (n+p) (n+p) (c+(e+p)) (Initial.radius5 h) ≤
          5*S+2*solveCap D (5*S) by omega).trans (next_le_stepBound D (5*S))
  have hcost : firstCost D c n p e rel h ≤ stepBound D (5*S) := by
    have h₁ := liftSolveCost_le (D := D) hnp hr hnp hcq (show Initial.radius5 h ≤ 2*(5*S) by omega)
    have h₂ := liftSolveCost_le (D := D) hnp hr hcq hnp (show Initial.radius5 h ≤ 2*(5*S) by omega)
    have hu := updateCost_mono (D := D) hn hc hp hq hlift
    unfold firstCost stepBound
    omega
  have hbudget : F.rankBudget G (c+(e+p)) (n+p) ≤ stepBound D (5*S) := by
    have hB : F.rankBudget G (c+(e+p)) (n+p) ≤ 5*S := by dsimp [nativeBudget] at hb; omega
    exact hB.trans (input_le_stepBound D (5*S))
  have hi := recursion_bounds F G (c+(e+p)) (n+p) (firstBox D c n p e h) (stepBound D (5*S))
    hbudget (hn.trans (input_le_stepBound D (5*S))) (hc.trans (input_le_stepBound D (5*S))) hfirst
  refine ⟨hi.1,?_⟩
  have hI : stepBound D (5*S) ≤ iteratedBound D length (stepBound D (5*S)) :=
    input_le_iteratedBound D length (stepBound D (5*S))
  change _ ≤ (length+1)*iteratedBound D length (stepBound D (5*S))
  nlinarith [hi.2]

/-- A polynomial envelope for the three actual absorption products. -/
def absorbEnvelope (D S : ℕ) : ℕ :=
  3*((3*S)*(3*S)*(3*S)*boxSize D (3*S)*(2*boxSize D S+1))

theorem absorbCost_le {D n c p q A B hL hS hE S : ℕ}
    (hn : n ≤ S) (hc : c ≤ S) (hp : p ≤ S) (hq : q ≤ S)
    (hA : A ≤ S) (hB : B ≤ S) (hhL : hL ≤ S) (hhS : hS ≤ S) (hhE : hE ≤ S) :
    absorbCost D n c p q A B hL hS hE ≤ absorbEnvelope D S := by
  have hprod (a b c r t : ℕ) (ha : a ≤ 3*S) (hb : b ≤ 3*S) (hc : c ≤ 3*S)
      (hr : r ≤ 3*S) (ht : t ≤ S) :
      a*b*c*boxSize D r*(2*boxSize D t+1) ≤
        (3*S)*(3*S)*(3*S)*boxSize D (3*S)*(2*boxSize D S+1) := by
    unfold boxSize
    gcongr
  have h₁ := hprod (c+(q+B)) (n+(p+B)) (c+(q+B)) (hE+hL) hE
    (by omega) (by omega) (by omega) (by omega) hhE
  have h₂ := hprod (c+(p+A)) (n+(p+B)) (c+(q+B)) (hS+(hE+hL)) hS
    (by omega) (by omega) (by omega) (by omega) hhS
  have h₃ := hprod (n+(p+B)) (c+(p+A)) (c+(q+B)) (hL+hS) hL
    (by omega) (by omega) (by omega) (by omega) hhL
  unfold absorbCost absorbEnvelope
  omega

/-- Actual full native output box and remaining C4 trace after Initial.run. -/
theorem native_bounds (F : DenseTower K D h₀ length n) (G : DenseTower K D h₀ length c)
    (p e rel h S : ℕ) (hb : nativeBudget F G p e rel h ≤ S) :
    runBox F G p e h ≤ 3*iteratedBound D (length+1) (5*S) ∧
    remainingCost F G p e rel h ≤
      (length+1)*iteratedBound D (length+1) (5*S) + absorbEnvelope D (iteratedBound D (length+1) (5*S)) := by
  have hs := stabilization_bounds F G p e rel h S hb
  let I := iteratedBound D (length+1) (5*S)
  have hSI : S ≤ I := by have hh := input_le_iteratedBound D (length+1) (5*S); dsimp [I]; omega
  have h₅ : Initial.radius5 h ≤ I := by
    have hh : h ≤ S := by dsimp [nativeBudget] at hb; omega
    rw [Initial.radius5_eq]
    exact (Nat.mul_le_mul_left 5 hh).trans (input_le_iteratedBound D (length+1) (5*S))
  have hranks := DenseTower.ranks_sum F G
  have hn : n ≤ I := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have hc : c ≤ I := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have hp : p ≤ I := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have hq : e+p ≤ I := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have hA : n+(F.ranks G).2 ≤ I := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have hB : c+(F.ranks G).1 ≤ I := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have ha := absorbCost_le (D := D) hn hc hp hq hA hB h₅ hs.1 h₅
  constructor
  · unfold runBox
    dsimp [I] at h₅
    omega
  · change firstCost D c n p e rel h + F.costBound G (c+(e+p)) (n+p) (firstBox D c n p e h) + _ ≤ _
    exact Nat.add_le_add hs.2 ha

end Decoupling.HighDim.StableFree.Resource
