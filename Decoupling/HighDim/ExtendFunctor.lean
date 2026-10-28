import Decoupling.HighDim.Profile

/-! # Change of coefficients commutes with extending a cochain complex by zero -/

namespace Decoupling.HighDim.ExtendFunctor

open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] [HasZeroObject D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : CochainComplex C ℕ)

abbrev mapped : CochainComplex D ℕ := (F.mapHomologicalComplex (.up ℕ)).obj K

def termIso (i : ℤ) :
    F.obj ((K.extend ComplexShape.embeddingUpNat).X i) ≅
      ((mapped F K).extend ComplexShape.embeddingUpNat).X i :=
  if hi : 0 ≤ i then
    F.mapIso (K.extendXIso ComplexShape.embeddingUpNat (i := i.toNat) (by change (i.toNat : ℤ) = i; omega)) ≪≫
      ((mapped F K).extendXIso ComplexShape.embeddingUpNat (i := i.toNat)
        (by change (i.toNat : ℤ) = i; omega)).symm
  else
    (F.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i (by
      intro n hn
      apply hi
      change (n : ℤ) = i at hn
      omega))).iso
      ((mapped F K).isZero_extend_X ComplexShape.embeddingUpNat i (by
        intro n hn
        apply hi
        change (n : ℤ) = i at hn
        omega))

theorem termIso_nat (i : ℕ) :
    termIso F K i =
      F.mapIso (K.extendXIso ComplexShape.embeddingUpNat (i := i) (i' := (i : ℤ)) rfl) ≪≫
        ((mapped F K).extendXIso ComplexShape.embeddingUpNat (i := i) (i' := (i : ℤ)) rfl).symm := by
  simp [termIso]

/-- A genuine chain isomorphism; zero terms are compared using their universal property. -/
def iso : (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
    (mapped F K).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents (termIso F K) (by
    intro i j _
    by_cases hi : 0 ≤ i
    · by_cases hj : 0 ≤ j
      · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hi
        obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hj
        simp only [termIso_nat, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
        symm
        change F.map ((K.extend ComplexShape.embeddingUpNat).d i j) ≫ _ =
          _ ≫ ((mapped F K).extend ComplexShape.embeddingUpNat).d i j
        rw [K.extend_d_eq ComplexShape.embeddingUpNat (i := i) (j := j)
            (i' := (i : ℤ)) (j' := (j : ℤ)) rfl rfl,
          (mapped F K).extend_d_eq ComplexShape.embeddingUpNat (i := i) (j := j)
            (i' := (i : ℤ)) (j' := (j : ℤ)) rfl rfl]
        simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
        simp only [← Functor.mapIso_inv, ← Functor.mapIso_hom, Iso.inv_hom_id_assoc]
        rfl
      · exact ((mapped F K).isZero_extend_X ComplexShape.embeddingUpNat j (by
          intro n hn; apply hj; change (n : ℤ) = j at hn; omega)).eq_of_tgt _ _
    · exact (F.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i (by
        intro n hn; apply hi; change (n : ℤ) = i at hn; omega))).eq_of_src _ _)

end
end Decoupling.HighDim.ExtendFunctor
