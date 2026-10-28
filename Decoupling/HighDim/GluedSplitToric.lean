import Decoupling.HighDim.GluedSplit
import Decoupling.HighDim.GluedDualExact

/-!
# The ancilla-free target is literally the two toric codes

These identities connect the six displayed target species to the native
first-form and second-form toric check matrices by cell relabelings only.
Together with actual coarse-cell expansion they identify the circuit's
target as restriction of the original fine-lattice toric stack.
-/

namespace Decoupling.HighDim.Glued

open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [CommRing K]

theorem splitX_blocks : (splitX K).submatrix
    (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4)
    (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6) =
      Matrix.fromBlocks (firstBoundary (Laurent K 3) (difference K)) 0 0
        (secondBoundary (Laurent K 3) (difference K)) := by
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => fin_cases i; fin_cases j <;> rfl
    | inr j => fin_cases i; fin_cases j <;> rfl
  | inr i =>
    cases j with
    | inl j => fin_cases i <;> fin_cases j <;> rfl
    | inr j => fin_cases i <;> fin_cases j <;> rfl

theorem splitZ_blocks : (splitZ K).submatrix
    (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6)
    (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4) =
      Matrix.fromBlocks (secondBoundary (Laurent K 3) (difference K)) 0 0
        (thirdBoundary (Laurent K 3) (difference K)) := by
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => fin_cases i <;> fin_cases j <;> rfl
    | inr j => fin_cases i <;> fin_cases j <;> rfl
  | inr i =>
    cases j with
    | inl j => fin_cases i <;> fin_cases j <;> rfl
    | inr j => fin_cases i <;> fin_cases j <;> rfl

def toricQubitLabels : Fin 6 ≃
    (Fin (Toric.cellCount 3 1) ⊕ Fin (Toric.cellCount 3 2)) :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr (nativeCellRelabel edgeEquiv) (nativeCellRelabel plaquetteEquiv))

def toricXLabels : Fin 4 ≃
    (Fin (Toric.cellCount 3 0) ⊕ Fin (Toric.cellCount 3 1)) :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr (nativeCellRelabel vertexEquiv) (nativeCellRelabel edgeEquiv))

def toricZLabels : Fin 4 ≃
    (Fin (Toric.cellCount 3 2) ⊕ Fin (Toric.cellCount 3 3)) :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr (nativeCellRelabel plaquetteEquiv) (nativeCellRelabel cubeEquiv))

/-- Exact equality to the actual toric X checks, modulo the displayed
bijection of ordered cells. -/
theorem splitX_nativeToric : splitX K =
    (Matrix.fromBlocks (Toric.checks K 3 0).H_X 0 0 (Toric.checks K 3 1).H_X).submatrix
      toricXLabels toricQubitLabels := by
  have hb := splitX_blocks K
  rw [← firstBoundary_coordinates, ← secondBoundary_coordinates,
    coordinateBoundary_eq_native, coordinateBoundary_eq_native] at hb
  apply Matrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).surjective j
  have h := congrFun (congrFun hb i) j
  cases i <;> cases j <;>
    simpa [toricXLabels, toricQubitLabels, Toric.checks_H_X] using h

/-- Exact equality to the actual toric Z generators, in the same physical
qudit relabeling as the X-check identity. -/
theorem splitZ_nativeToric : splitZ K =
    (Matrix.fromBlocks (dagger (Toric.checks K 3 0).H_Z) 0 0
      (dagger (Toric.checks K 3 1).H_Z)).submatrix toricQubitLabels toricZLabels := by
  have hb := splitZ_blocks K
  rw [← secondBoundary_coordinates, ← thirdBoundary_coordinates,
    coordinateBoundary_eq_native, coordinateBoundary_eq_native] at hb
  apply Matrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4).surjective j
  have h := congrFun (congrFun hb i) j
  cases i <;> cases j <;>
    simpa [toricZLabels, toricQubitLabels, Toric.checks_dagger_H_Z] using h

end
end Decoupling.HighDim.Glued
