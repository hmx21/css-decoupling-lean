import Decoupling.HighDim.AlgorithmTwoComparisonLift

/-!
# Solvability of the actual mapping-cone contraction equations

For the supplied bounded free complexes and an actual quasi-isomorphism,
the genuine mapping cone is K-projective and becomes zero in the
derived category. Faithfulness on homotopy classes therefore proves
the existence of its contraction. This proves solvability of the
linear contraction system, not a cost for a chosen contracting map.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparison
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable {R : Type} [CommRing R]
variable {T C : CochainComplex (ModuleCat.{0} R) ℤ}

def actualConeTermIso (f : T ⟶ C) (n : ℤ) :
    (CochainComplex.mappingCone f).X n ≅ ModuleCat.of R (T.X (n + 1) × C.X n) :=
  homotopyCofiber.XIsoBiprod f n (n + 1) rfl ≪≫ ModuleCat.biprodIsoProd _ _

theorem cone_derived_isZero (f : T ⟶ C) [QuasiIso f] :
    IsZero (DerivedCategory.Q.obj (CochainComplex.mappingCone f)) := by
  exact CategoryTheory.Pretriangulated.Triangle.isZero₃_of_isIso₁
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f))
    (DerivedCategory.mappingCone_triangle_distinguished f) (by
      change IsIso (DerivedCategory.Q.map f)
      infer_instance)

def contractionOfDerivedZero (G : CochainComplex (ModuleCat R) ℤ) [G.IsKProjective]
    (hz : IsZero (DerivedCategory.Q.obj G)) : Homotopy (𝟙 G) 0 := by
  apply HomotopyCategory.homotopyOfEq
  apply (Torus.homotopyDerivedEquiv G G).injective
  rw [Torus.homotopyDerivedEquiv_map, Torus.homotopyDerivedEquiv_map,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hz.eq_of_src _ _

def coneContraction (f : T ⟶ C) [QuasiIso f]
    (cT : StableFree.Coordinates T) (cC : StableFree.Coordinates C)
    (upperT upperC : ℤ) [T.IsStrictlyLE upperT] [C.IsStrictlyLE upperC] :
    Homotopy (𝟙 (CochainComplex.mappingCone f)) 0 := by
  letI (n : ℤ) : Module.Free R (T.X n) := Module.Free.of_equiv (cT.equiv n).symm
  letI (n : ℤ) : Module.Free R (C.X n) := Module.Free.of_equiv (cC.equiv n).symm
  letI (n : ℤ) : Module.Free R ((CochainComplex.mappingCone f).X n) :=
    Module.Free.of_equiv (actualConeTermIso f n).symm.toLinearEquiv
  letI (n : ℤ) : Projective ((CochainComplex.mappingCone f).X n) := inferInstance
  letI : (CochainComplex.mappingCone f).IsStrictlyLE (max (upperT - 1) upperC) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨T.isZero_of_isStrictlyLE upperT (n + 1) (by omega),
      C.isZero_of_isStrictlyLE upperC n (by omega)⟩
  letI : (CochainComplex.mappingCone f).IsKProjective :=
    CochainComplex.isKProjective_of_projective _ (max (upperT - 1) upperC)
  exact contractionOfDerivedZero _ (cone_derived_isZero f)

/-- Explicit equations of the actual contraction at every degree.
The adjacent component order is native cochain composition order. -/
theorem contraction_equations (G : CochainComplex (ModuleCat R) ℤ)
    (h : Homotopy (𝟙 G) 0) (n : ℤ) :
    G.d n (n + 1) ≫ h.hom (n + 1) n +
      h.hom n (n - 1) ≫ G.d (n - 1) n = 𝟙 (G.X n) := by
  have he := congrArg (fun f : G ⟶ G => f.f n) h.sub_eq_nullHomotopicMap
  rw [sub_zero, HomologicalComplex.id_f,
    Homotopy.nullHomotopicMap_f (c := ComplexShape.up ℤ) (k₂ := n - 1) (k₁ := n) (k₀ := n + 1)
      (by change n - 1 + 1 = n; omega) (by rfl) h.hom] at he
  exact he.symm

theorem exists_cone_contraction (f : T ⟶ C) [QuasiIso f]
    (cT : StableFree.Coordinates T) (cC : StableFree.Coordinates C)
    (upperT upperC : ℤ) [T.IsStrictlyLE upperT] [C.IsStrictlyLE upperC] :
    ∃ s : ∀ n, (CochainComplex.mappingCone f).X n ⟶
        (CochainComplex.mappingCone f).X (n - 1),
      ∀ n, (CochainComplex.mappingCone f).d n (n + 1) ≫ s (n + 1) ≫
          eqToHom (congrArg (CochainComplex.mappingCone f).X (by ring : n + 1 - 1 = n)) +
        s n ≫ (CochainComplex.mappingCone f).d (n - 1) n =
          𝟙 ((CochainComplex.mappingCone f).X n) := by
  let h := coneContraction f cT cC upperT upperC
  refine ⟨fun n => h.hom n (n - 1), ?_⟩
  intro n
  have he := contraction_equations (CochainComplex.mappingCone f) h n
  convert he using 1
  simp

end
end Decoupling.HighDim.AlgorithmTwoComparison
