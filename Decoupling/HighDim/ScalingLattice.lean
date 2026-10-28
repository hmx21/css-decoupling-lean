import Decoupling.HighDim.TrivialLayers
import Decoupling.HighDim.KoszulRestriction
import Decoupling.HighDim.LatticeProfile

/-!
# Standard Laurent coordinates and the exact scaled retained lattice

An integer basis is only a coordinate choice on a subgroup. The maps below
retain that distinction: scaling the standard Laurent coordinates n times
has image exactly n Lambda, and coherent scaled coordinates give a literal
commuting square with the actual subgroup-algebra inclusion. No additional
finite-index subgroup is introduced.
-/

namespace Decoupling.HighDim.ScalingLattice

open CategoryTheory LatticeRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable (K : Type) [CommRing K] {D : ℕ}
  (Λ : AddSubgroup (Translation D))

/-- Coordinates may be any actual integer-lattice isomorphism. -/
def ringCoordinates (e : Λ ≃+ Translation D) : S K Λ ≃+* Laurent K D :=
  (latticeEquiv K Λ).symm.trans (AddMonoidAlgebra.mapDomainRingEquiv K e)

/-- Inclusion of the retained lattice, expressed in its chosen coordinates. -/
def coordinateEmbedding (e : Λ ≃+ Translation D) : Laurent K D →+* Laurent K D :=
  (retained K Λ).subtype.comp (ringCoordinates K Λ e).symm.toRingHom

@[simp] theorem coordinateEmbedding_single (e : Λ ≃+ Translation D)
    (a : Translation D) (c : K) :
    coordinateEmbedding K Λ e (AddMonoidAlgebra.single a c) =
      AddMonoidAlgebra.single (e.symm a : Translation D) c := by
  simp [coordinateEmbedding, ringCoordinates, latticeEquiv, embed, RingHom.rangeRestrict]
  change AddMonoidAlgebra.mapDomainRingHom K Λ.subtype
    (AddMonoidAlgebra.single (e.symm a) c) = _
  simp

@[simp] theorem coordinateEmbedding_monomial (e : Λ ≃+ Translation D)
    (a : Translation D) :
    coordinateEmbedding K Λ e (monomial K a) = monomial K (e.symm a : Translation D) :=
  coordinateEmbedding_single K Λ e a 1

@[simp] theorem coordinateEmbedding_constant (e : Λ ≃+ Translation D) (c : K) :
    coordinateEmbedding K Λ e (constant c) = constant c := by
  simp [constant]

theorem coordinateEmbedding_injective (e : Λ ≃+ Translation D) :
    Function.Injective (coordinateEmbedding K Λ e) :=
  Subtype.val_injective.comp (ringCoordinates K Λ e).symm.injective

@[simp] theorem augmentation_coordinateEmbedding (e : Λ ≃+ Translation D)
    (a : Laurent K D) : augmentation (coordinateEmbedding K Λ e a) = augmentation a := by
  have h : augmentation.comp (coordinateEmbedding K Λ e) =
      (augmentation : Laurent K D →+* K) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro x <;> simp
  exact DFunLike.congr_fun h a

@[simp] theorem coordinateEmbedding_bar (e : Λ ≃+ Translation D) (a : Laurent K D) :
    coordinateEmbedding K Λ e (bar a) = bar (coordinateEmbedding K Λ e a) := by
  have h : (coordinateEmbedding K Λ e).comp bar.toRingHom =
      bar.toRingHom.comp (coordinateEmbedding K Λ e) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro c
      simp [bar, translationNeg]
    · intro a
      change coordinateEmbedding K Λ e (bar (monomial K a)) =
        bar (coordinateEmbedding K Λ e (monomial K a))
      simp
  exact DFunLike.congr_fun h a

/-- The retained subring dagger is preserved by the integer-basis renaming. -/
theorem ringCoordinates_bar (e : Λ ≃+ Translation D) (a : S K Λ) :
    ringCoordinates K Λ e (barS K Λ a) = bar (ringCoordinates K Λ e a) := by
  apply coordinateEmbedding_injective K Λ e
  rw [coordinateEmbedding_bar]
  change ((ringCoordinates K Λ e).symm (ringCoordinates K Λ e (barS K Λ a)) :
      Laurent K D) = bar ((ringCoordinates K Λ e).symm (ringCoordinates K Λ e a) : Laurent K D)
  simp

/-- In particular this is exactly LatticeBasis.renameRing on the subgroup
algebra, after the actual image-subring equivalence. -/
theorem ringCoordinates_basis [Λ.FiniteIndex] :
    ringCoordinates K Λ (LatticeBasis.coordinates Λ) =
      (latticeEquiv K Λ).symm.trans (LatticeBasis.renameRing Λ K) := rfl

/-- Multiplication by n gives an isomorphism onto the literal scaled subgroup. -/
def scaleEquiv (n : ℕ) (hn : n ≠ 0) : Λ ≃+ LatticeBasis.scaled Λ n :=
  AddEquiv.ofBijective
    ({ toFun a := ⟨n • (a : Translation D), ⟨a, a.property, rfl⟩⟩
       map_zero' := Subtype.ext (smul_zero n)
       map_add' a b := Subtype.ext (nsmul_add (a : Translation D) b n) } :
      Λ →+ LatticeBasis.scaled Λ n)
    ⟨fun a b h => Subtype.ext (nsmul_right_injective hn (congrArg Subtype.val h)),
      by
        rintro ⟨a, b, hb, hab⟩
        exact ⟨⟨b, hb⟩, Subtype.ext hab⟩⟩

@[simp] theorem scaleEquiv_coe (n : ℕ) (hn : n ≠ 0) (a : Λ) :
    (scaleEquiv Λ n hn a : Translation D) = n • (a : Translation D) := rfl

/-- Use the scaled original basis, not an unrelated basis chosen afterward. -/
def scaledCoordinates (e : Λ ≃+ Translation D) (n : ℕ) (hn : n ≠ 0) :
    LatticeBasis.scaled Λ n ≃+ Translation D := (scaleEquiv Λ n hn).symm.trans e

@[simp] theorem scaledCoordinates_symm_coe (e : Λ ≃+ Translation D)
    (n : ℕ) (hn : n ≠ 0) (a : Translation D) :
    ((scaledCoordinates Λ e n hn).symm a : Translation D) =
      n • (e.symm a : Translation D) := rfl

/-- Exact compatibility of the standard scaling homomorphism with the
actual inclusion of n Lambda into the original translation lattice. -/
theorem coordinateEmbedding_scaled (e : Λ ≃+ Translation D) (n : ℕ) (hn : n ≠ 0) :
    coordinateEmbedding K (LatticeBasis.scaled Λ n) (scaledCoordinates Λ e n hn) =
      (coordinateEmbedding K Λ e).comp (Koszul.scaling K D n) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro c
    change coordinateEmbedding K (LatticeBasis.scaled Λ n) _ (constant c) =
      coordinateEmbedding K Λ e (Koszul.scaling K D n (constant c))
    rw [Koszul.scaling_constant, coordinateEmbedding_constant, coordinateEmbedding_constant]
  · intro a
    change coordinateEmbedding K (LatticeBasis.scaled Λ n) _ (monomial K a) =
      coordinateEmbedding K Λ e (Koszul.scaling K D n (monomial K a))
    rw [coordinateEmbedding_monomial, scaledCoordinates_symm_coe,
      Koszul.scaling_monomial, coordinateEmbedding_monomial]
    congr 1
    exact (congrArg Subtype.val (map_nsmul e.symm n a)).symm

/-- Scaling composes multiplicatively, on the ring maps themselves. -/
theorem scaling_comp (m n : ℕ) :
    (Koszul.scaling K D m).comp (Koszul.scaling K D n) = Koszul.scaling K D (m * n) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro c
    change Koszul.scaling K D m (Koszul.scaling K D n (constant c)) =
      Koszul.scaling K D (m * n) (constant c)
    rw [Koszul.scaling_constant, Koszul.scaling_constant, Koszul.scaling_constant]
  · intro a
    change Koszul.scaling K D m (Koszul.scaling K D n (monomial K a)) =
      Koszul.scaling K D (m * n) (monomial K a)
    simp [mul_smul]

@[simp] theorem scaling_one : Koszul.scaling K D 1 = RingHom.id _ := by
  apply AddMonoidAlgebra.ringHom_ext <;> intro x <;>
    simp [Koszul.scaling, Koszul.scaleTranslation]

/-- Scalar restriction for n Lambda equals restriction first to Lambda
and then along the standard scaling map. The isomorphism is identity on elements. -/
def scaledRestrictionIso (e : Λ ≃+ Translation D) (n : ℕ) (hn : n ≠ 0) :
    ModuleCat.restrictScalars
      (coordinateEmbedding K (LatticeBasis.scaled Λ n) (scaledCoordinates Λ e n hn)) ≅
    ModuleCat.restrictScalars (coordinateEmbedding K Λ e) ⋙
      ModuleCat.restrictScalars (Koszul.scaling K D n) :=
  ModuleCat.restrictScalarsComp' _ _ _ (coordinateEmbedding_scaled K Λ e n hn)

/-- Basis renaming after physical restriction is the same actual functor
as restriction along the displayed lattice inclusion. -/
def coordinateRestrictionIso (e : Λ ≃+ Translation D) :
    ModuleCat.restrictScalars (coordinateEmbedding K Λ e) ≅
      LatticeExt.restriction K Λ ⋙
        ModuleCat.restrictScalars (ringCoordinates K Λ e).symm.toRingHom :=
  ModuleCat.restrictScalarsComp' _ _ _ rfl

end
end Decoupling.HighDim.ScalingLattice
