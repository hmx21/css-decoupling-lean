import Decoupling.HighDim.KoszulExtFunctor

/-! # Change of coefficients commutes with extending a chain complex by zero -/

namespace Decoupling.HighDim.KoszulExtendFunctor

open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] [HasZeroObject D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : ChainComplex C ℕ)

abbrev mapped : ChainComplex D ℕ := (F.mapHomologicalComplex (.down ℕ)).obj K

def termIso (i : ℤ) :
    F.obj ((K.extend ComplexShape.embeddingDownNat).X i) ≅
      ((mapped F K).extend ComplexShape.embeddingDownNat).X i :=
  if hi : i ≤ 0 then
    F.mapIso (K.extendXIso ComplexShape.embeddingDownNat (i := (-i).toNat) (by change -(((-i).toNat : ℕ) : ℤ) = i; omega)) ≪≫
      ((mapped F K).extendXIso ComplexShape.embeddingDownNat (i := (-i).toNat)
        (by change -(((-i).toNat : ℕ) : ℤ) = i; omega)).symm
  else
    (F.map_isZero (K.isZero_extend_X ComplexShape.embeddingDownNat i (by
      intro n hn
      apply hi
      change -(n : ℤ) = i at hn
      omega))).iso
      ((mapped F K).isZero_extend_X ComplexShape.embeddingDownNat i (by
        intro n hn
        apply hi
        change -(n : ℤ) = i at hn
        omega))

theorem termIso_nat (i : ℕ) :
    termIso F K (-i) =
      F.mapIso (K.extendXIso ComplexShape.embeddingDownNat (i := i) (i' := -(i : ℤ)) rfl) ≪≫
        ((mapped F K).extendXIso ComplexShape.embeddingDownNat (i := i) (i' := -(i : ℤ)) rfl).symm := by
  simp [termIso, HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
    ComplexShape.embeddingDownNat]
  ext
  simp [Functor.mapIso, eqToIso, eqToHom_trans]
  rw [eqToHom_map, eqToHom_map, eqToHom_trans, eqToHom_trans]


/-- A genuine chain isomorphism; zero terms are compared using their universal property. -/
def iso : (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingDownNat) ≅
    (mapped F K).extend ComplexShape.embeddingDownNat :=
  HomologicalComplex.Hom.isoOfComponents (termIso F K) (by
    intro i j _
    by_cases hi : i ≤ 0
    · by_cases hj : j ≤ 0
      · obtain ⟨i, rfl⟩ := Int.exists_eq_neg_ofNat hi
        obtain ⟨j, rfl⟩ := Int.exists_eq_neg_ofNat hj
        simp only [termIso_nat, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
        symm
        change F.map ((K.extend ComplexShape.embeddingDownNat).d (-i) (-j)) ≫ _ =
          _ ≫ ((mapped F K).extend ComplexShape.embeddingDownNat).d (-i) (-j)
        rw [K.extend_d_eq ComplexShape.embeddingDownNat (i := i) (j := j)
            (i' := -(i : ℤ)) (j' := -(j : ℤ)) rfl rfl,
          (mapped F K).extend_d_eq ComplexShape.embeddingDownNat (i := i) (j := j)
            (i' := -(i : ℤ)) (j' := -(j : ℤ)) rfl rfl]
        simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
        simp only [← Functor.mapIso_inv, ← Functor.mapIso_hom, Iso.inv_hom_id_assoc]
        rfl
      · exact ((mapped F K).isZero_extend_X ComplexShape.embeddingDownNat j (by
          intro n hn; apply hj; change -(n : ℤ) = j at hn; omega)).eq_of_tgt _ _
    · exact (F.map_isZero (K.isZero_extend_X ComplexShape.embeddingDownNat i (by
        intro n hn; apply hi; change -(n : ℤ) = i at hn; omega))).eq_of_src _ _)

end
end Decoupling.HighDim.KoszulExtendFunctor
