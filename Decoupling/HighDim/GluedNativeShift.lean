import Decoupling.HighDim.GluedNativeFormality

/-!
# Sign-correct shifted resolution of the actual example

The native shift by three negates the differential. The comparison
therefore multiplies Koszul degree n by (-1)^n, in every characteristic.
-/
namespace Decoupling.HighDim.Glued
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex Koszul
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

def shiftedResolutionTermIso (i : ℤ) :
    (projectiveResolution K 3).cochainComplex.X i ≅ ((Toric.model K 3 3)⟦(3 : ℤ)⟧).X i :=
  if hi : i ≤ 0 then
    i.negOnePow • ((projectiveResolution K 3).cochainComplexXIso i (-i).toNat (by omega) ≪≫
      ((laurentComplex K 3).extendXIso (ComplexShape.embeddingUpIntLE 3)
        (i := (-i).toNat) (i' := i+3) (by change 3 - ((-i).toNat : ℤ) = i+3; omega)).symm)
  else
    ((projectiveResolution K 3).cochainComplex.isZero_of_isStrictlyLE 0 i (by omega)).iso
      (by
        change IsZero ((Toric.model K 3 3).X (i+3))
        exact (Toric.model K 3 3).isZero_of_isStrictlyLE 3 (i+3) (by omega))

theorem shiftedResolutionTermIso_nat (n : ℕ) :
    shiftedResolutionTermIso K (-n) =
      (-(n : ℤ)).negOnePow •
        ((projectiveResolution K 3).cochainComplexXIso (-n) n rfl ≪≫
          ((laurentComplex K 3).extendXIso (ComplexShape.embeddingUpIntLE 3)
            (i := n) (i' := -(n : ℤ)+3) (by change 3-(n : ℤ) = -n+3; omega)).symm) := by
  simp only [shiftedResolutionTermIso, neg_nonpos.mpr (Int.natCast_nonneg n), ↓reduceDIte]
  congr 1
  simp [ProjectiveResolution.cochainComplexXIso, HomologicalComplex.extendXIso,
    HomologicalComplex.extend.XIso, ComplexShape.embeddingUpIntLE]
  ext
  simp [eqToIso, eqToHom_trans]

/-- The actual signed comparison from the original native projective
resolution to the shifted degree-three Koszul model. -/
def shiftedResolutionIso : (projectiveResolution K 3).cochainComplex ≅
    (Toric.model K 3 3)⟦(3 : ℤ)⟧ :=
  HomologicalComplex.Hom.isoOfComponents (shiftedResolutionTermIso K) (by
    intro i j hij
    change i + 1 = j at hij
    by_cases hj : j ≤ 0
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
      have hi : i = -((n+1 : ℕ) : ℤ) := by omega
      subst i
      subst j
      rw [shiftedResolutionTermIso_nat, shiftedResolutionTermIso_nat]
      simp only [smul_iso_hom, Iso.trans_hom, Iso.symm_hom]
      rw [(projectiveResolution K 3).cochainComplex_d _ _ (n+1) n rfl rfl]
      simp only [CochainComplex.shiftFunctor_obj_d', Category.assoc,
        Linear.units_smul_comp, Linear.comp_units_smul, Iso.inv_hom_id_assoc]
      rw [show (Toric.model K 3 3).d (-((n+1 : ℕ) : ℤ)+3) (-(n : ℤ)+3) =
        ((laurentComplex K 3).extendXIso (ComplexShape.embeddingUpIntLE 3)
          (i := n+1) (i' := -((n+1 : ℕ) : ℤ)+3) (by change 3-((n+1 : ℕ) : ℤ) = _; omega)).hom ≫
        (laurentComplex K 3).d (n+1) n ≫
        ((laurentComplex K 3).extendXIso (ComplexShape.embeddingUpIntLE 3)
          (i := n) (i' := -(n : ℤ)+3) (by change 3-(n : ℤ) = _; omega)).inv from
          (laurentComplex K 3).extend_d_eq (ComplexShape.embeddingUpIntLE 3)
            (i := n+1) (j := n) (i' := -((n+1 : ℕ) : ℤ)+3) (j' := -(n : ℤ)+3)
              (by change 3-((n+1 : ℕ) : ℤ) = _; omega) (by change 3-(n : ℤ) = _; omega)]
      simp only [Iso.inv_hom_id_assoc]
      change Int.negOnePow 3 • (-((n+1 : ℕ) : ℤ)).negOnePow • _ =
        (-(n : ℤ)).negOnePow • _
      have hs : Int.negOnePow 3 * (-((n+1 : ℕ) : ℤ)).negOnePow = (-(n : ℤ)).negOnePow := by
        rw [show Int.negOnePow 3 = -1 from rfl]
        simp [Int.negOnePow_add]
      rw [smul_smul, hs]
      rfl
    · exact ((Toric.model K 3 3).isZero_of_isStrictlyLE 3 (j+3) (by omega)).eq_of_tgt _ _)

end
end Decoupling.HighDim.Glued
