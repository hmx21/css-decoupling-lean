import Decoupling.HighDim.GluedDualModel
import Decoupling.HighDim.ToricModel

/-!
# The two explicit signed gluing components

The maps are on the actual ordered Koszul cells. Their anticommuting
square is proved over arbitrary characteristic, retaining the minus sign
on the 12 plaquette.
-/

namespace Decoupling.HighDim.Glued

open CategoryTheory CategoryTheory.Limits Koszul Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

def couplingZ : Matrix (Fin 3) (Fin 1) (Laurent K 3) := ![![0], ![0], ![1]]
def couplingX : Matrix (Fin 1) (Fin 3) (Laurent K 3) := ![![-1, 0, 0]]

def cellCouplingZ : ModuleCat.of (Laurent K 3) (Term (Laurent K 3) 3 3) ⟶
    ModuleCat.of (Laurent K 3) (Term (Laurent K 3) 3 1) :=
  (coordinates (Laurent K 3) cubeEquiv).toModuleIso.hom ≫
    ModuleCat.ofHom (couplingZ K).mulVecLin ≫
      (coordinates (Laurent K 3) edgeEquiv).toModuleIso.inv

def cellCouplingX : ModuleCat.of (Laurent K 3) (Term (Laurent K 3) 3 2) ⟶
    ModuleCat.of (Laurent K 3) (Term (Laurent K 3) 3 0) :=
  (coordinates (Laurent K 3) plaquetteEquiv).toModuleIso.hom ≫
    ModuleCat.ofHom (couplingX K).mulVecLin ≫
      (coordinates (Laurent K 3) vertexEquiv).toModuleIso.inv

theorem boundary_coordinates {k m n : ℕ}
    (e : Fin m ≃ Cell 3 k) (f : Fin n ≃ Cell 3 (k + 1))
    (v : Term (Laurent K 3) 3 (k + 1)) :
    coordinates (Laurent K 3) e (boundary (Laurent K 3) (difference K) k v) =
      coordinateBoundary (Laurent K 3) (difference K) e f *ᵥ
        coordinates (Laurent K 3) f v := by
  rw [coordinateBoundary_apply, LinearEquiv.symm_apply_apply]

theorem coupling_square :
    cellCouplingZ K ≫ boundary (Laurent K 3) (difference K) 0 =
      -(boundary (Laurent K 3) (difference K) 2 ≫ cellCouplingX K) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  apply (coordinates (Laurent K 3) vertexEquiv).injective
  change coordinates (Laurent K 3) vertexEquiv
    (boundary (Laurent K 3) (difference K) 0 (cellCouplingZ K v)) =
      coordinates (Laurent K 3) vertexEquiv
        (-(cellCouplingX K (boundary (Laurent K 3) (difference K) 2 v)))
  rw [boundary_coordinates K vertexEquiv edgeEquiv, firstBoundary_coordinates, map_neg]
  change firstBoundary (Laurent K 3) (difference K) *ᵥ
    coordinates (Laurent K 3) edgeEquiv
      ((coordinates (Laurent K 3) edgeEquiv).symm
        (couplingZ K *ᵥ coordinates (Laurent K 3) cubeEquiv v)) =
    -(coordinates (Laurent K 3) vertexEquiv
      ((coordinates (Laurent K 3) vertexEquiv).symm
        (couplingX K *ᵥ coordinates (Laurent K 3) plaquetteEquiv
          (boundary (Laurent K 3) (difference K) 2 v))))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    boundary_coordinates K plaquetteEquiv cubeEquiv, thirdBoundary_coordinates]
  funext i
  fin_cases i
  simp [firstBoundary, thirdBoundary, couplingX, couplingZ,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ]

end
end Decoupling.HighDim.Glued
