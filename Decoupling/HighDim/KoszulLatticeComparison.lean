import Decoupling.HighDim.KoszulLatticeExterior

/-!
# Non-diagonal Koszul comparison maps

Source: Appendix B.2. Exterior powers of a linear map give the signed
minors in every degree. Naturality of contraction proves compatibility
with the actual ordered-cell Koszul boundaries.
-/

namespace Decoupling.HighDim.KoszulLattice

open CategoryTheory Koszul ExtValues
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] {D : ℕ}

/-- The genuine exterior power, expressed in the existing ordered-cell
bases. -/
def exteriorTerm (f : (Fin D → R) →ₗ[R] (Fin D → R)) (n : ℕ) :
    Term R D n →ₗ[R] Term R D n :=
  (termExteriorEquiv R D n).symm.toLinearMap.comp
    ((exteriorPower.map n f).comp (termExteriorEquiv R D n).toLinearMap)

theorem exteriorMap_coe (f : (Fin D → R) →ₗ[R] (Fin D → R)) (n : ℕ)
    (x : ⋀[R]^n (Fin D → R)) :
    ((exteriorPower.map n f x : ⋀[R]^n (Fin D → R)) : ExteriorAlgebra R (Fin D → R)) =
      ExteriorAlgebra.map f (x : ExteriorAlgebra R (Fin D → R)) := by
  have h : (ExteriorAlgebra.exteriorPower R n (Fin D → R)).subtype.comp
      (exteriorPower.map n f) =
      (ExteriorAlgebra.map f).toLinearMap.comp
        (ExteriorAlgebra.exteriorPower R n (Fin D → R)).subtype := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change ((exteriorPower.map n f (exteriorPower.ιMulti R n v) :
      ⋀[R]^n (Fin D → R)) : ExteriorAlgebra R (Fin D → R)) =
        ExteriorAlgebra.map f (ExteriorAlgebra.ιMulti R n v)
    rw [exteriorPower.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti]
    rfl
  exact LinearMap.congr_fun h x

theorem termExterior_exteriorTerm (f : (Fin D → R) →ₗ[R] (Fin D → R))
    (n : ℕ) (x : Term R D n) :
    termExterior R D n (exteriorTerm f n x) =
      ExteriorAlgebra.map f (termExterior R D n x) := by
  change (((termExteriorEquiv R D n) ((termExteriorEquiv R D n).symm
    (exteriorPower.map n f (termExteriorEquiv R D n x)))) :
      ExteriorAlgebra R (Fin D → R)) = _
  rw [LinearEquiv.apply_symm_apply, exteriorMap_coe]
  rfl

/-- Every matrix coefficient is the corresponding signed minor. -/
theorem exteriorTerm_single (f : (Fin D → R) →ₗ[R] (Fin D → R))
    (n : ℕ) (J I : Cell D n) :
    exteriorTerm f n (Finsupp.single J 1) I =
      Matrix.det (fun a b => f (Pi.single (J a) 1) (I b)) := by
  change (exteriorCellBasis R D n).repr
    (exteriorPower.map n f ((exteriorCellBasis R D n).repr.symm (Finsupp.single J 1))) I = _
  rw [Module.Basis.repr_symm_single_one, exteriorCellBasis_apply,
    exteriorPower.map_apply_ιMulti, exteriorCellBasis_repr]
  rfl

theorem exteriorTerm_single_coeff (f : (Fin D → R) →ₗ[R] (Fin D → R))
    (n : ℕ) (J I : Cell D n) (r : R) :
    exteriorTerm f n (Finsupp.single J r) I =
      r * Matrix.det (fun a b => f (Pi.single (J a) 1) (I b)) := by
  rw [show Finsupp.single J r = r • Finsupp.single J 1 by simp,
    map_smul, Finsupp.smul_apply, smul_eq_mul, exteriorTerm_single]

@[simp] theorem exteriorTerm_zero (f : (Fin D → R) →ₗ[R] (Fin D → R)) :
    exteriorTerm f 0 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro J r
  ext I
  rw [exteriorTerm_single_coeff]
  simp [Subsingleton.elim I J]

/-- Compatibility of the real chain maps, proved by contraction
naturality. The displayed covector equation is exactly the degree-one
boundary condition and will be proved from lattice paths. -/
theorem exteriorTerm_boundary (f : (Fin D → R) →ₗ[R] (Fin D → R))
    (w s : Fin D → R) (h : (weightForm R D w).comp f = weightForm R D s)
    (n : ℕ) (x : Term R D (n + 1)) :
    boundary R w n (exteriorTerm f (n + 1) x) =
      exteriorTerm f n (boundary R s n x) := by
  apply termExterior_injective R D n
  rw [termExterior_boundary, termExterior_exteriorTerm, contract_map, h,
    termExterior_exteriorTerm, termExterior_boundary]

/-- The chain comparison for a general linear change of generators. -/
def exteriorComparison (f : (Fin D → R) →ₗ[R] (Fin D → R))
    (w s : Fin D → R) (h : (weightForm R D w).comp f = weightForm R D s) :
    complex R s ⟶ complex R w :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (exteriorTerm f n)) (by
    intro n
    ext x
    simpa [complex] using exteriorTerm_boundary f w s h n x)

end
end Decoupling.HighDim.KoszulLattice
