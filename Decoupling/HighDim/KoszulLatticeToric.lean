import Decoupling.HighDim.KoszulLatticeExt
import Decoupling.HighDim.ToricModel

/-!
# Arbitrary-lattice comparison in a placed Koszul resolution

This is the same proved lattice chain comparison, extended in any integer
cohomological placement. It is used for the displayed native gluing cone.
-/

namespace Decoupling.HighDim.KoszulLattice
open CategoryTheory CategoryTheory.Limits HomologicalComplex Koszul
noncomputable section
set_option backward.isDefEq.respectTransparency false

section Extend
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] [HasZeroObject D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (P : ChainComplex C ℕ) (q : ℤ)

def placedExtensionTermIso (i : ℤ) :
    F.obj ((P.extend (ComplexShape.embeddingUpIntLE q)).X i) ≅
      (((F.mapHomologicalComplex (.down ℕ)).obj P).extend (ComplexShape.embeddingUpIntLE q)).X i :=
  if hi : i ≤ q then
    F.mapIso (P.extendXIso (ComplexShape.embeddingUpIntLE q) (i := (q-i).toNat)
      (by change q - ((q-i).toNat : ℤ) = i; omega)) ≪≫
      (((F.mapHomologicalComplex (.down ℕ)).obj P).extendXIso
        (ComplexShape.embeddingUpIntLE q) (i := (q-i).toNat)
          (by change q - ((q-i).toNat : ℤ) = i; omega)).symm
  else
    (F.map_isZero (P.isZero_extend_X (ComplexShape.embeddingUpIntLE q) i (by
      intro n hn; apply hi; change q - (n : ℤ) = i at hn; omega))).iso
      (((F.mapHomologicalComplex (.down ℕ)).obj P).isZero_extend_X
        (ComplexShape.embeddingUpIntLE q) i (by
          intro n hn; apply hi; change q - (n : ℤ) = i at hn; omega))

theorem placedExtensionTermIso_nat (n : ℕ) :
    placedExtensionTermIso F P q (q - n) =
      F.mapIso (P.extendXIso (ComplexShape.embeddingUpIntLE q) (i := n) (i' := q - n) rfl) ≪≫
        (((F.mapHomologicalComplex (.down ℕ)).obj P).extendXIso
          (ComplexShape.embeddingUpIntLE q) (i := n) (i' := q - n) rfl).symm := by
  simp [placedExtensionTermIso, HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
    ComplexShape.embeddingUpIntLE]
  ext
  simp [Functor.mapIso, eqToIso, eqToHom_trans]
  rw [eqToHom_map, eqToHom_map, eqToHom_trans, eqToHom_trans]

def placedExtensionIso :
    (F.mapHomologicalComplex (.up ℤ)).obj (P.extend (ComplexShape.embeddingUpIntLE q)) ≅
      ((F.mapHomologicalComplex (.down ℕ)).obj P).extend (ComplexShape.embeddingUpIntLE q) :=
  HomologicalComplex.Hom.isoOfComponents (placedExtensionTermIso F P q) (by
    intro i j _
    by_cases hi : i ≤ q
    · by_cases hj : j ≤ q
      · obtain ⟨i, rfl⟩ : ∃ n : ℕ, i = q - n := ⟨(q-i).toNat, by omega⟩
        obtain ⟨j, rfl⟩ : ∃ n : ℕ, j = q - n := ⟨(q-j).toNat, by omega⟩
        simp only [placedExtensionTermIso_nat, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
        symm
        change F.map ((P.extend (ComplexShape.embeddingUpIntLE q)).d (q-i) (q-j)) ≫ _ =
          _ ≫ (((F.mapHomologicalComplex (.down ℕ)).obj P).extend
            (ComplexShape.embeddingUpIntLE q)).d (q-i) (q-j)
        rw [P.extend_d_eq (ComplexShape.embeddingUpIntLE q) (i := i) (j := j)
            (i' := q-i) (j' := q-j) rfl rfl,
          ((F.mapHomologicalComplex (.down ℕ)).obj P).extend_d_eq
            (ComplexShape.embeddingUpIntLE q) (i := i) (j := j)
            (i' := q-i) (j' := q-j) rfl rfl]
        simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
        simp only [← Functor.mapIso_inv, ← Functor.mapIso_hom, Iso.inv_hom_id_assoc]
        rfl
      · exact (((F.mapHomologicalComplex (.down ℕ)).obj P).isZero_extend_X
          (ComplexShape.embeddingUpIntLE q) j (by
            intro n hn; apply hj; change q - (n : ℤ) = j at hn; omega)).eq_of_tgt _ _
    · exact (F.map_isZero (P.isZero_extend_X (ComplexShape.embeddingUpIntLE q) i (by
        intro n hn; apply hi; change q - (n : ℤ) = i at hn; omega))).eq_of_src _ _)
end Extend

variable (K : Type) [Field K] {D : ℕ}

def latticeToricComparison (a : Translation D →+ Translation D) (q : ℤ) :
    Toric.model K D q ⟶
      ((ModuleCat.restrictScalars (latticeMap K a)).mapHomologicalComplex (.up ℤ)).obj
        (Toric.model K D q) :=
  HomologicalComplex.extendMap (latticeComparison K a) (ComplexShape.embeddingUpIntLE q) ≫
    (placedExtensionIso (ModuleCat.restrictScalars (latticeMap K a)) (laurentComplex K D) q).inv

instance latticeToricComparison_quasiIso (a : Translation D →+ Translation D) (q : ℤ) :
    QuasiIso (latticeToricComparison K a q) := by
  dsimp [latticeToricComparison]
  infer_instance

theorem latticeToricComparison_f (a : Translation D →+ Translation D) (q : ℤ) (n : ℕ) :
    (latticeToricComparison K a q).f (q - n) =
      (Toric.termIso K D q n).hom ≫ (latticeComparison K a).f n ≫
        (ModuleCat.restrictScalars (latticeMap K a)).map (Toric.termIso K D q n).inv := by
  simp only [latticeToricComparison, HomologicalComplex.comp_f]
  rw [HomologicalComplex.extendMap_f _ _ (i := n) (i' := q - n) rfl]
  simp only [placedExtensionIso, HomologicalComplex.Hom.isoOfComponents_inv_f,
    placedExtensionTermIso_nat, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

end
end Decoupling.HighDim.KoszulLattice
