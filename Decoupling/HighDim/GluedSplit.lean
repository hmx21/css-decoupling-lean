import Decoupling.HighDim.GluedDirectionalMatrices

/-!
# The literal diagonal toric target and the example's coarse-linear shear

The target removes exactly the two displayed coupling entries. Its two
blocks are the actual first and second Koszul CSS windows, in the same
six physical species, without adjoining ancillary qudits.
-/

namespace Decoupling.HighDim.Glued

open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [CommRing K]

def splitX : Matrix (Fin 4) (Fin 6) (Laurent K 3) :=
  let w := difference K
  ![![w 0, w 1, w 2, 0, 0, 0],
    ![0, 0, 0, -w 1, -w 2, 0],
    ![0, 0, 0, w 0, 0, -w 2],
    ![0, 0, 0, 0, w 0, w 1]]

def splitZ : Matrix (Fin 6) (Fin 4) (Laurent K 3) :=
  let w := difference K
  ![![-w 1, -w 2, 0, 0],
    ![w 0, 0, -w 2, 0],
    ![0, w 0, w 1, 0],
    ![0, 0, 0, w 2],
    ![0, 0, 0, -w 1],
    ![0, 0, 0, w 0]]

theorem split_commute : splitX K * splitZ K = 0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [splitX, splitZ, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

variable [IsDomain K]

theorem split_exact (v : Fin 6 → Laurent K 3) :
    splitX K *ᵥ v = 0 ↔ ∃ z, splitZ K *ᵥ z = v := by
  constructor
  · intro hv
    have he : firstBoundary (Laurent K 3) (difference K) *ᵥ ![v 0, v 1, v 2] = 0 := by
      have h := congrFun hv 0
      funext i
      fin_cases i
      simpa [splitX, firstBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
    have hp : secondBoundary (Laurent K 3) (difference K) *ᵥ ![v 3, v 4, v 5] = 0 := by
      funext i
      fin_cases i
      · simpa [splitX, secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hv 1
      · simpa [splitX, secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hv 2
      · simpa [splitX, secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hv 3
    obtain ⟨u, hu⟩ := (first_exact K _).mp he
    obtain ⟨t, ht⟩ := (second_exact K _).mp hp
    refine ⟨![u 0, u 1, u 2, t 0], ?_⟩
    funext i
    fin_cases i
    · simpa [splitZ, secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hu 0
    · simpa [splitZ, secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hu 1
    · simpa [splitZ, secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hu 2
    · simpa [splitZ, thirdBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using congrFun ht 0
    · simpa [splitZ, thirdBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using congrFun ht 1
    · simpa [splitZ, thirdBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using congrFun ht 2
  · rintro ⟨z, rfl⟩
    rw [Matrix.mulVec_mulVec, split_commute, Matrix.zero_mulVec]

end
end Decoupling.HighDim.Glued

namespace Decoupling.HighDim.GluedDirectional

open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime]

def quditN : restrictedFree p 6 →ₗ[Laurent (ZMod p) 3] restrictedFree p 6 where
  toFun v := ![0, laurentDerivative (ZMod p) 1 (v 3),
    laurentDerivative (ZMod p) 1 (v 4), 0, 0, 0]
  map_add' v w := by funext i; fin_cases i <;> simp
  map_smul' a v := by
    funext i
    fin_cases i
    · change (0 : Laurent (ZMod p) 3) = ringMap p a * 0; simp
    · exact derivative_ringMap_mul p a (v 3)
    · exact derivative_ringMap_mul p a (v 4)
    · change (0 : Laurent (ZMod p) 3) = ringMap p a * 0; simp
    · change (0 : Laurent (ZMod p) 3) = ringMap p a * 0; simp
    · change (0 : Laurent (ZMod p) 3) = ringMap p a * 0; simp

def syndromeN : restrictedFree p 4 →ₗ[Laurent (ZMod p) 3] restrictedFree p 4 where
  toFun v := ![-laurentDerivative (ZMod p) 1 (v 1), 0, 0, 0]
  map_add' v w := by funext i; fin_cases i <;> simp [add_comm]
  map_smul' a v := by
    funext i
    fin_cases i
    · change -laurentDerivative (ZMod p) 1 (ringMap p a * v 1) =
        ringMap p a * (-laurentDerivative (ZMod p) 1 (v 1))
      rw [derivative_ringMap_mul, mul_neg]
    · change (0 : Laurent (ZMod p) 3) = ringMap p a * 0; simp
    · change (0 : Laurent (ZMod p) 3) = ringMap p a * 0; simp
    · change (0 : Laurent (ZMod p) 3) = ringMap p a * 0; simp

theorem quditN_squared : (quditN p).comp (quditN p) = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> simp [quditN]

theorem syndromeN_squared : (syndromeN p).comp (syndromeN p) = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> simp [syndromeN]

/-- The retained-ring-linear shear satisfies the actual check square. -/
theorem split_square :
    (restrictMatrix p (Glued.splitX (ZMod p))).comp (LinearMap.id + quditN p) =
      (LinearMap.id + syndromeN p).comp (restrictMatrix p (Glued.xChecks (ZMod p))) := by
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;>
    simp [restrictMatrix, quditN, syndromeN, Glued.splitX, Glued.xChecks,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, laurentDerivative_difference_mul]
  ring

end
end Decoupling.HighDim.GluedDirectional
