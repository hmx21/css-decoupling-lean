import Decoupling.HighDim.GluedDirectional

/-!
# The explicit nullhomotopy is linear over the genuine retained ring

All objects below are actual scalar restrictions along the directional
lattice embedding. The homotopy is constructed, rather than supplied as
a hypothesis, and its two required chain equations are equalities of
retained-ring-linear maps.
-/

namespace Decoupling.HighDim.GluedDirectional

open CategoryTheory Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime]

abbrev restrictedFree (n : ℕ) : ModuleCat (Laurent (ZMod p) 3) :=
  (ModuleCat.restrictScalars (ringMap p)).obj
    (ModuleCat.of (Laurent (ZMod p) 3) (Fin n → Laurent (ZMod p) 3))

@[simp] theorem restrictedFree_add_apply {n : ℕ} (v w : restrictedFree p n) (i : Fin n) :
    (v + w) i = v i + w i := rfl

@[simp] theorem restrictedFree_sub_apply {n : ℕ} (v w : restrictedFree p n) (i : Fin n) :
    (v - w) i = v i - w i := rfl

@[simp] theorem restrictedFree_zero_apply {n : ℕ} (i : Fin n) :
    (0 : restrictedFree p n) i = 0 := rfl

def restrictMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) (Laurent (ZMod p) 3)) :
    restrictedFree p n →ₗ[Laurent (ZMod p) 3] restrictedFree p m :=
  ((ModuleCat.restrictScalars (ringMap p)).map (ModuleCat.ofHom A.mulVecLin)).hom

def homotopyMinus : restrictedFree p 1 →ₗ[Laurent (ZMod p) 3] restrictedFree p 3 where
  toFun v := Glued.homotopyMinus (ZMod p) v
  map_add' := (Glued.homotopyMinus (ZMod p)).map_add
  map_smul' a v := by
    funext i
    fin_cases i
    · change (0 : Laurent (ZMod p) 3) = ringMap p a * 0; simp
    · change (0 : Laurent (ZMod p) 3) = ringMap p a * 0; simp
    · change -laurentDerivative (ZMod p) 1 (ringMap p a * v 0) =
        ringMap p a * (-laurentDerivative (ZMod p) 1 (v 0))
      rw [derivative_ringMap_mul, mul_neg]

def homotopyZero : restrictedFree p 3 →ₗ[Laurent (ZMod p) 3] restrictedFree p 3 where
  toFun v := Glued.homotopyZero (ZMod p) v
  map_add' := (Glued.homotopyZero (ZMod p)).map_add
  map_smul' a v := by
    funext i
    fin_cases i
    · change (0 : Laurent (ZMod p) 3) = ringMap p a * 0; simp
    · exact derivative_ringMap_mul p a (v 0)
    · exact derivative_ringMap_mul p a (v 1)

def homotopyOne : restrictedFree p 3 →ₗ[Laurent (ZMod p) 3] restrictedFree p 1 where
  toFun v := Glued.homotopyOne (ZMod p) v
  map_add' := (Glued.homotopyOne (ZMod p)).map_add
  map_smul' a v := by
    funext i
    fin_cases i
    change -laurentDerivative (ZMod p) 1 (ringMap p a * v 0) =
      ringMap p a * (-laurentDerivative (ZMod p) 1 (v 0))
    rw [derivative_ringMap_mul, mul_neg]

theorem homotopy_Z : restrictMatrix p (Glued.couplingZ (ZMod p)) =
    (restrictMatrix p (Glued.secondBoundary (Laurent (ZMod p) 3) (difference (ZMod p)))).comp
        (homotopyMinus p) -
      (homotopyZero p).comp
        (restrictMatrix p (Glued.thirdBoundary (Laurent (ZMod p) 3) (difference (ZMod p)))) := by
  apply LinearMap.ext
  exact Glued.homotopy_Z (ZMod p)

theorem homotopy_X : restrictMatrix p (Glued.couplingX (ZMod p)) =
    (restrictMatrix p (Glued.firstBoundary (Laurent (ZMod p) 3) (difference (ZMod p)))).comp
        (homotopyZero p) -
      (homotopyOne p).comp
        (restrictMatrix p (Glued.secondBoundary (Laurent (ZMod p) 3) (difference (ZMod p)))) := by
  apply LinearMap.ext
  exact Glued.homotopy_X (ZMod p)

end
end Decoupling.HighDim.GluedDirectional
