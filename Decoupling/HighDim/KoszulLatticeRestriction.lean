import Decoupling.HighDim.KoszulLatticeComparison

/-!
# The actual arbitrary-lattice Koszul restriction comparison

Source: Appendix B.2. An integer homomorphism of full translation lattices
induces the actual group-algebra map. The signed path and exterior maps
construct the chain comparison; no comparison is supplied as an assumption.
The construction works even without an injectivity or finite-index input.
-/

namespace Decoupling.HighDim.KoszulLattice

open CategoryTheory CategoryTheory.Limits Koszul ExtValues
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [CommRing K] {D : ℕ}

/-- The genuine group-algebra map induced by an integer lattice map. -/
def latticeMap (a : Translation D →+ Translation D) : Laurent K D →+* Laurent K D :=
  AddMonoidAlgebra.mapDomainRingHom K a

/-- The coefficient-field linear map given by the integer lattice matrix
reduced in the coefficient ring. -/
def reducedMap (a : Translation D →+ Translation D) : (Fin D → K) →ₗ[K] (Fin D → K) :=
  (Pi.basisFun K (Fin D)).constr K (fun i j => (a (translationBasis i) j : K))

@[simp] theorem reducedMap_single (a : Translation D →+ Translation D) (i : Fin D) :
    reducedMap K a (Pi.single i 1) = (fun j => (a (translationBasis i) j : K)) := by
  rw [← Pi.basisFun_apply]
  exact (Pi.basisFun K (Fin D)).constr_basis K _ i

@[simp] theorem latticeMap_monomial (a : Translation D →+ Translation D)
    (b : Translation D) : latticeMap K a (monomial K b) = monomial K (a b) := by
  simp [latticeMap, monomial]

@[simp] theorem latticeMap_constant (a : Translation D →+ Translation D) (c : K) :
    latticeMap K a (constant c) = constant c := by
  simp [latticeMap, constant]

@[simp] theorem augmentation_latticeMap (a : Translation D →+ Translation D)
    (r : Laurent K D) : augmentation (latticeMap K a r) = augmentation r := by
  refine AddMonoidAlgebra.induction_on
    (motive := fun r : Laurent K D => augmentation (latticeMap K a r) = augmentation r)
    r ?_ ?_ ?_
  · intro b
    change augmentation (latticeMap K a (monomial K b)) = augmentation (monomial K b)
    simp
  · intro f g hf hg; simp [hf, hg]
  · intro c f hf
    have hc : c • f = constant c * f := by
      change c • f = AddMonoidAlgebra.single 0 c * f
      ext b
      simp
    rw [hc, map_mul, latticeMap_constant, map_mul, map_mul, hf]

@[simp] theorem latticeMap_difference (a : Translation D →+ Translation D) (i : Fin D) :
    latticeMap K a (difference K i) = monomial K (a (translationBasis i)) - 1 := by
  simp [difference, coordinate]

/-- The degree-one map sends a coarse unit edge to a proved signed path. -/
def pathLinear (a : Translation D →+ Translation D) :
    (Fin D → Laurent K D) →ₗ[Laurent K D] (Fin D → Laurent K D) :=
  (Pi.basisFun (Laurent K D) (Fin D)).constr (Laurent K D)
    (fun i => pathCoefficients K (a (translationBasis i)))

@[simp] theorem pathLinear_single (a : Translation D →+ Translation D) (i : Fin D) :
    pathLinear K a (Pi.single i 1) = pathCoefficients K (a (translationBasis i)) := by
  rw [← Pi.basisFun_apply]
  exact (Pi.basisFun (Laurent K D) (Fin D)).constr_basis (Laurent K D) _ i

/-- The degree-one boundary condition is proved from actual path boundaries. -/
theorem pathLinear_weights (a : Translation D →+ Translation D) :
    (weightForm (Laurent K D) D (difference K)).comp (pathLinear K a) =
      weightForm (Laurent K D) D (fun i => latticeMap K a (difference K i)) := by
  apply (Pi.basisFun (Laurent K D) (Fin D)).ext
  intro i
  rw [Pi.basisFun_apply, LinearMap.comp_apply, pathLinear_single, weightForm_single]
  change ((Pi.basisFun (Laurent K D) (Fin D)).constr (Laurent K D) (difference K))
    (pathCoefficients K (a (translationBasis i))) = _
  rw [Module.Basis.constr_apply_fintype]
  simpa only [Module.Basis.equivFun_apply, Pi.basisFun_repr, smul_eq_mul,
    latticeMap_difference] using pathCoefficients_boundary K (a (translationBasis i))

/-- Actual semilinear comparison from the coarse Koszul resolution to the
restriction of the fine one, including every off-diagonal minor. -/
def latticeComparison (a : Translation D →+ Translation D) :
    laurentComplex K D ⟶
      ((ModuleCat.restrictScalars (latticeMap K a)).mapHomologicalComplex (.down ℕ)).obj
        (laurentComplex K D) :=
  scalarChange (Laurent K D) (latticeMap K a) (difference K) ≫
    ((ModuleCat.restrictScalars (latticeMap K a)).mapHomologicalComplex (.down ℕ)).map
      (exteriorComparison (pathLinear K a) (difference K)
        (fun i => latticeMap K a (difference K i)) (pathLinear_weights K a))

theorem latticeComparison_single (a : Translation D →+ Translation D)
    (n : ℕ) (J I : Cell D n) :
    (show Term (Laurent K D) D n from (latticeComparison K a).f n
      (Finsupp.single J 1)) I =
      Matrix.det (fun k l => pathCoefficients K (a (translationBasis (J k))) (I l)) := by
  change exteriorTerm (pathLinear K a) n
    (scalarChangeTerm (Laurent K D) (latticeMap K a) n (Finsupp.single J 1)) I = _
  rw [scalarChangeTerm_single, map_one, exteriorTerm_single]
  simp only [pathLinear_single]

/-- Augmentation of each comparison coefficient is precisely the integer
minor reduced in the coefficient ring. -/
theorem augmentation_latticeComparison_single (a : Translation D →+ Translation D)
    (n : ℕ) (J I : Cell D n) :
    augmentation ((show Term (Laurent K D) D n from (latticeComparison K a).f n
      (Finsupp.single J 1)) I) =
      Matrix.det (fun k l => (a (translationBasis (J k)) (I l) : K)) := by
  rw [latticeComparison_single, RingHom.map_det]
  congr 1
  ext k l
  exact augmentation_pathCoefficients K _ _

/-- Restricting a coefficient module along the lattice map preserves its
augmentation action, with the literal identity on elements. -/
def latticeCoefficientIso (a : Translation D →+ Translation D) :
    coefficientModule K D ≅
      (ModuleCat.restrictScalars (latticeMap K a)).obj (coefficientModule K D) :=
  LinearEquiv.toModuleIso (show coefficientModule K D ≃ₗ[Laurent K D]
    (ModuleCat.restrictScalars (latticeMap K a)).obj (coefficientModule K D) from {
      toFun x := x
      invFun x := x
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r x := by
        change augmentation r * (show K from x) =
          augmentation (latticeMap K a r) * (show K from x)
        rw [augmentation_latticeMap] })

theorem latticeComparison_zero_single (a : Translation D →+ Translation D)
    (J : Cell D 0) (r : Laurent K D) :
    (latticeComparison K a).f 0 (Finsupp.single J r) =
      (show (ModuleCat.restrictScalars (latticeMap K a)).obj
        ((laurentComplex K D).X 0) from Finsupp.single J (latticeMap K a r)) := by
  change exteriorTerm (pathLinear K a) 0
    (scalarChangeTerm (Laurent K D) (latticeMap K a) 0 (Finsupp.single J r)) = _
  rw [exteriorTerm_zero, LinearMap.id_apply, scalarChangeTerm_single]

theorem latticeComparison_augmentation_zero (a : Translation D →+ Translation D) :
    (latticeComparison K a).f 0 ≫
      (ModuleCat.restrictScalars (latticeMap K a)).map (augmentationMap K D) =
      augmentationMap K D ≫ (latticeCoefficientIso K a).hom := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro I r
  change augmentationMap K D ((latticeComparison K a).f 0 (Finsupp.single I r)) =
    augmentation (zeroTermEquiv (Laurent K D) (Finsupp.single I r))
  rw [latticeComparison_zero_single]
  simp

theorem latticeComparison_augmentation (a : Translation D →+ Translation D) :
    latticeComparison K a ≫
      ((ModuleCat.restrictScalars (latticeMap K a)).mapHomologicalComplex (.down ℕ)).map
        (resolutionAugmentation K D) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.restrictScalars (latticeMap K a)) (.down ℕ) 0).hom.app
          (coefficientModule K D) =
      resolutionAugmentation K D ≫
        (ChainComplex.single₀ (ModuleCat (Laurent K D))).map (latticeCoefficientIso K a).hom := by
  apply HomologicalComplex.to_single_hom_ext
  simpa using latticeComparison_augmentation_zero K a

variable [IsDomain K]

/-- The constructed non-diagonal comparison really is a quasi-isomorphism. -/
instance latticeComparison_quasiIso (a : Translation D →+ Translation D) :
    QuasiIso (latticeComparison K a) := by
  let f := ((ModuleCat.restrictScalars (latticeMap K a)).mapHomologicalComplex (.down ℕ)).map
    (resolutionAugmentation K D) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.restrictScalars (latticeMap K a)) (.down ℕ) 0).hom.app (coefficientModule K D)
  have : QuasiIso (latticeComparison K a ≫ f) := by
    dsimp [f]
    rw [latticeComparison_augmentation]
    infer_instance
  exact quasiIso_of_comp_right (latticeComparison K a) f

end
end Decoupling.HighDim.KoszulLattice
