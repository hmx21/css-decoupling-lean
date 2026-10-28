import Decoupling.HighDim.Profile

/-!
# Exact functors commute with positive truncation in the derived category

The comparison uses an actual quasi-isomorphism of canonically truncated
complexes. Equality of cohomology objects alone is never used as a
criterion for two arbitrary derived objects to be isomorphic.
-/

namespace Decoupling.HighDim.ExactTruncation

open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  (K : CochainComplex C ℤ) (n : ℤ)

abbrev mapped : CochainComplex D ℤ := (F.mapHomologicalComplex (.up ℤ)).obj K

def mappedProjection : mapped F K ⟶ mapped F (K.truncGE n) :=
  (F.mapHomologicalComplex (.up ℤ)).map (K.πTruncGE n)

def comparison : (mapped F K).truncGE n ⟶ (mapped F (K.truncGE n)).truncGE n :=
  CochainComplex.truncGEMap (mappedProjection F K n) n

omit [HasDerivedCategory D] in
theorem comparison_quasiIso : QuasiIso (comparison F K n) := by
  apply (CochainComplex.quasiIso_truncGEMap_iff (mappedProjection F K n) n).mpr
  intro i hi
  let := K.quasiIsoAt_πTruncGE n i hi
  dsimp [mappedProjection]
  infer_instance

/-- Restriction and other exact additive functors preserve the full truncation
object, including its extension data. -/
def derivedIso : DerivedCategory.Q.obj (mapped F (K.truncGE n)) ≅
    DerivedCategory.Q.obj ((mapped F K).truncGE n) := by
  let T := mapped F (K.truncGE n)
  have hT : T.IsStrictlyGE n := by
    dsimp [T, mapped]
    infer_instance
  have hπ : IsIso (T.πTruncGE n) := by
    change IsIso (HomologicalComplex.πTruncGE T (ComplexShape.embeddingUpIntGE n))
    infer_instance
  let eπ := DerivedCategory.Q.mapIso (@asIso _ _ _ _ (T.πTruncGE n) hπ)
  have hcomp : IsIso (DerivedCategory.Q.map (comparison F K n)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso D _).mpr (comparison_quasiIso F K n)
  exact eπ ≪≫ (@asIso _ _ _ _ (DerivedCategory.Q.map (comparison F K n)) hcomp).symm

end
end Decoupling.HighDim.ExactTruncation
