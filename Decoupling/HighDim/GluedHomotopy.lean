import Decoupling.HighDim.GluedCoupling
import Decoupling.HighDim.LaurentDerivative

/-!
# An explicit derivative nullhomotopy of the example's coupling

These are actual coefficient-linear operators on Laurent modules. The
next directional-lattice module proves they are linear over the retained
subring in characteristic p; this module does not claim R-linearity.
The two homotopy equations are proved for arbitrary coefficients, not
merely for individual basis vectors.
-/

namespace Decoupling.HighDim.Glued

open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

def homotopyMinus : (Fin 1 → Laurent K 3) →ₗ[K] (Fin 3 → Laurent K 3) where
  toFun v := ![0, 0, -laurentDerivative K 1 (v 0)]
  map_add' v w := by funext i; fin_cases i <;> simp [add_comm]
  map_smul' a v := by funext i; fin_cases i <;> simp

def homotopyZero : (Fin 3 → Laurent K 3) →ₗ[K] (Fin 3 → Laurent K 3) where
  toFun v := ![0, laurentDerivative K 1 (v 0), laurentDerivative K 1 (v 1)]
  map_add' v w := by funext i; fin_cases i <;> simp
  map_smul' a v := by funext i; fin_cases i <;> simp

def homotopyOne : (Fin 3 → Laurent K 3) →ₗ[K] (Fin 1 → Laurent K 3) where
  toFun v := ![-laurentDerivative K 1 (v 0)]
  map_add' v w := by funext i; fin_cases i; simp [add_comm]
  map_smul' a v := by funext i; fin_cases i; simp

/-- The Z coupling is the actual boundary of the displayed homotopy. -/
theorem homotopy_Z (v : Fin 1 → Laurent K 3) :
    couplingZ K *ᵥ v =
      secondBoundary (Laurent K 3) (difference K) *ᵥ homotopyMinus K v -
        homotopyZero K (thirdBoundary (Laurent K 3) (difference K) *ᵥ v) := by
  funext i
  fin_cases i <;>
    simp [couplingZ, secondBoundary, thirdBoundary, homotopyMinus, homotopyZero,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, laurentDerivative_difference_mul]

/-- The X coupling has the signed nullhomotopy required in odd characteristic too. -/
theorem homotopy_X (v : Fin 3 → Laurent K 3) :
    couplingX K *ᵥ v =
      firstBoundary (Laurent K 3) (difference K) *ᵥ homotopyZero K v -
        homotopyOne K (secondBoundary (Laurent K 3) (difference K) *ᵥ v) := by
  funext i
  fin_cases i
  simp [couplingX, firstBoundary, secondBoundary, homotopyZero, homotopyOne,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, laurentDerivative_difference_mul]
  ring

end
end Decoupling.HighDim.Glued
