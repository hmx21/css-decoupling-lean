import Decoupling.HighDim.TorusKoszulDual
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Ordinary duality of finite projective cochain complexes

The dual reverses degrees and transposes each actual differential. This
file supplies the chain-level and homotopy-level duality needed to compare
finite-period tensor homology with a genuine derived representable functor.
The reflexivity hypotheses below follow for finite free terms; they are
not assumptions on the final CSS code.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R]

/-- Ordinary module dual, as a contravariant functor. -/
def moduleDual : (ModuleCat R)ᵒᵖ ⥤ ModuleCat R where
  obj M := ModuleCat.of R (Module.Dual R M.unop)
  map f := ModuleCat.ofHom f.unop.hom.dualMap

instance : (moduleDual R).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro l
    apply LinearMap.ext
    intro x
    exact l.map_add _ _

/-- Degree-reversing ordinary dual of an integer cochain complex. -/
abbrev complexDual (C : CochainComplex (ModuleCat R) ℤ) :
    CochainComplex (ModuleCat R) ℤ where
  X n := ModuleCat.of R (Module.Dual R (C.X (-n)))
  d i j := ModuleCat.ofHom (C.d (-j) (-i)).hom.dualMap
  shape i j h := by
    have hd : C.d (-j) (-i) = 0 := C.shape _ _ (by dsimp at h ⊢; omega)
    rw [hd]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro l
    apply LinearMap.ext
    intro x
    exact l.map_zero
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro l
    apply LinearMap.ext
    intro x
    change l ((C.d (-k) (-j) ≫ C.d (-j) (-i)) x) = 0
    rw [C.d_comp_d]
    exact l.map_zero

/-- Transpose of a cochain map. -/
abbrev complexDualMap {C E : CochainComplex (ModuleCat R) ℤ} (f : C ⟶ E) :
    complexDual R E ⟶ complexDual R C where
  f n := ModuleCat.ofHom (f.f (-n)).hom.dualMap
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro l
    apply LinearMap.ext
    intro x
    change l ((C.d (-j) (-i) ≫ f.f (-i)) x) =
      l ((f.f (-j) ≫ E.d (-j) (-i)) x)
    rw [f.comm]

theorem complexDual_d (C : CochainComplex (ModuleCat R) ℤ) (i j : ℤ) :
    ((complexDual R C).d i j).hom = (C.d (-j) (-i)).hom.dualMap := rfl

theorem complexDualMap_f {C E : CochainComplex (ModuleCat R) ℤ} (f : C ⟶ E) (i : ℤ) :
    ((complexDualMap R f).f i).hom = (f.f (-i)).hom.dualMap := rfl

/-- Genuine homotopies transpose to genuine homotopies. -/
def complexDualHomotopy {C E : CochainComplex (ModuleCat R) ℤ} {f g : C ⟶ E}
    (h : Homotopy f g) : Homotopy (complexDualMap R f) (complexDualMap R g) :=
  (moduleDual R).mapHomotopy (CochainComplex.homotopyOp h)

variable {R}

/-- Evaluation into the double dual, including the degree identification. -/
def complexEvaluation (C : CochainComplex (ModuleCat R) ℤ) :
    C ⟶ complexDual R (complexDual R C) where
  f n := (C.XIsoOfEq (by simp : n = - -n)).hom ≫
    ModuleCat.ofHom (Module.Dual.eval R (C.X (- -n)))
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro l
    change l (((C.XIsoOfEq _).hom ≫ C.d (- -i) (- -j)) x) =
      l ((C.d i j ≫ (C.XIsoOfEq _).hom) x)
    rw [XIsoOfEq_hom_comp_d, d_comp_XIsoOfEq_hom]

instance complexEvaluation_component_isIso (C : CochainComplex (ModuleCat R) ℤ)
    [∀ n, Module.IsReflexive R (C.X n)] (n : ℤ) : IsIso ((complexEvaluation C).f n) := by
  change IsIso ((C.XIsoOfEq _).hom ≫ ModuleCat.ofHom (Module.evalEquiv R _).toLinearMap)
  exact inferInstanceAs (IsIso ((C.XIsoOfEq _).hom ≫ (Module.evalEquiv R _).toModuleIso.hom))

instance complexEvaluation_isIso (C : CochainComplex (ModuleCat R) ℤ)
    [∀ n, Module.IsReflexive R (C.X n)] : IsIso (complexEvaluation C) :=
  HomologicalComplex.Hom.isIso_of_components _

/-- Reflexive terms give an actual double-dual chain isomorphism. -/
def complexDoubleDualIso (C : CochainComplex (ModuleCat R) ℤ)
    [∀ n, Module.IsReflexive R (C.X n)] : C ≅ complexDual R (complexDual R C) :=
  asIso (complexEvaluation C)

theorem complexEvaluation_naturality {C E : CochainComplex (ModuleCat R) ℤ} (f : C ⟶ E) :
    complexEvaluation C ≫ complexDualMap R (complexDualMap R f) = f ≫ complexEvaluation E := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro l
  change l (((C.XIsoOfEq _).hom ≫ f.f (- -n)) x) =
    l ((f.f n ≫ (E.XIsoOfEq _).hom) x)
  rw [XIsoOfEq_hom_naturality]

@[simp] theorem complexDualMap_comp {A B C : CochainComplex (ModuleCat R) ℤ}
    (f : A ⟶ B) (g : B ⟶ C) :
    complexDualMap R (f ≫ g) = complexDualMap R g ≫ complexDualMap R f := rfl

@[simp] theorem complexDualMap_id (C : CochainComplex (ModuleCat R) ℤ) :
    complexDualMap R (𝟙 C) = 𝟙 (complexDual R C) := rfl

@[simp] theorem complexDualMap_add {C E : CochainComplex (ModuleCat R) ℤ} (f g : C ⟶ E) :
    complexDualMap R (f + g) = complexDualMap R f + complexDualMap R g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro l
  apply LinearMap.ext
  intro x
  exact l.map_add _ _

@[simp] theorem complexDualMap_smul {C E : CochainComplex (ModuleCat R) ℤ}
    (r : R) (f : C ⟶ E) : complexDualMap R (r • f) = r • complexDualMap R f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro l
  apply LinearMap.ext
  intro x
  exact l.map_smul r _

/-- Evaluation and transposition obey the duality triangle identity. -/
theorem complexEvaluation_triangle (C : CochainComplex (ModuleCat R) ℤ) :
    complexEvaluation (complexDual R C) ≫ complexDualMap R (complexEvaluation C) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro l
  apply LinearMap.ext
  intro x
  have eval_transport (n m : ℤ) (h : n = m)
      (l : (complexDual R C).X n) (x : C.X (-n)) :
      ((complexDual R C).XIsoOfEq h).hom l
        ((C.XIsoOfEq (congrArg Neg.neg h)).hom x) = l x := by
    subst m
    rfl
  exact eval_transport n (- -n) (by simp) l x

theorem complexDualMap_injective (C E : CochainComplex (ModuleCat R) ℤ)
    [∀ n, Module.IsReflexive R (E.X n)] : Function.Injective (@complexDualMap R _ C E) := by
  intro f g h
  apply (cancel_mono (complexEvaluation E)).mp
  rw [← complexEvaluation_naturality, ← complexEvaluation_naturality, h]

instance complexDualMap_isIso {C E : CochainComplex (ModuleCat R) ℤ}
    (f : C ⟶ E) [IsIso f] : IsIso (complexDualMap R f) := by
  change IsIso (((moduleDual R).mapHomologicalComplex (.up ℤ)).map
    ((CochainComplex.opEquivalence (ModuleCat R)).functor.map f.op))
  infer_instance

/-- Inverse transposition for complexes with reflexive terms. -/
def complexUndualMap {C E : CochainComplex (ModuleCat R) ℤ}
    [∀ n, Module.IsReflexive R (E.X n)]
    (g : complexDual R E ⟶ complexDual R C) : C ⟶ E :=
  complexEvaluation C ≫ complexDualMap R g ≫ (complexDoubleDualIso E).inv

@[simp] theorem complexUndualMap_dual {C E : CochainComplex (ModuleCat R) ℤ}
    [∀ n, Module.IsReflexive R (E.X n)] (f : C ⟶ E) :
    complexUndualMap (complexDualMap R f) = f := by
  rw [complexUndualMap, ← Category.assoc, complexEvaluation_naturality]
  simp [complexDoubleDualIso]

@[simp] theorem complexDualMap_undual {C E : CochainComplex (ModuleCat R) ℤ}
    [∀ n, Module.IsReflexive R (E.X n)]
    (g : complexDual R E ⟶ complexDual R C) :
    complexDualMap R (complexUndualMap g) = g := by
  have hE : complexDualMap R (complexDoubleDualIso E).inv =
      complexEvaluation (complexDual R E) := by
    apply (cancel_mono (complexDualMap R (complexEvaluation E))).mp
    rw [← complexDualMap_comp, complexEvaluation_triangle]
    change complexDualMap R ((complexDoubleDualIso E).hom ≫
      (complexDoubleDualIso E).inv) = _
    simp
  rw [complexUndualMap, complexDualMap_comp, complexDualMap_comp, hE,
    complexEvaluation_naturality, Category.assoc,
    complexEvaluation_triangle, Category.comp_id]

/-- Transposition is an actual linear equivalence on cochain maps. -/
def complexDualHomEquiv (C E : CochainComplex (ModuleCat R) ℤ)
    [∀ n, Module.IsReflexive R (E.X n)] :
    (C ⟶ E) ≃ₗ[R] (complexDual R E ⟶ complexDual R C) where
  toFun := complexDualMap R
  invFun := complexUndualMap
  left_inv := complexUndualMap_dual
  right_inv := complexDualMap_undual
  map_add' := complexDualMap_add
  map_smul' := complexDualMap_smul

/-- Ordinary duality interchanges upper and lower strict bounds. -/
instance complexDual_boundedAbove (C : CochainComplex (ModuleCat R) ℤ)
    (b : ℤ) [C.IsStrictlyGE b] : (complexDual R C).IsStrictlyLE (-b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  let : Subsingleton (C.X (-n)) := ModuleCat.subsingleton_of_isZero
    (C.isZero_of_isStrictlyGE b (-n) (by omega))
  exact ModuleCat.isZero_of_subsingleton _

instance complexDual_boundedBelow (C : CochainComplex (ModuleCat R) ℤ)
    (b : ℤ) [C.IsStrictlyLE b] : (complexDual R C).IsStrictlyGE (-b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  let : Subsingleton (C.X (-n)) := ModuleCat.subsingleton_of_isZero
    (C.isZero_of_isStrictlyLE b (-n) (by omega))
  exact ModuleCat.isZero_of_subsingleton _

instance complexDual_finite (C : CochainComplex (ModuleCat R) ℤ)
    [∀ n, Module.Finite R (C.X n)] [∀ n, Module.Free R (C.X n)] (n : ℤ) :
    Module.Finite R ((complexDual R C).X n) := inferInstanceAs
      (Module.Finite R (Module.Dual R (C.X (-n))))

instance complexDual_free (C : CochainComplex (ModuleCat R) ℤ)
    [∀ n, Module.Finite R (C.X n)] [∀ n, Module.Free R (C.X n)] (n : ℤ) :
    Module.Free R ((complexDual R C).X n) := inferInstanceAs
      (Module.Free R (Module.Dual R (C.X (-n))))

instance complexDual_projective (C : CochainComplex (ModuleCat R) ℤ)
    [∀ n, Module.Finite R (C.X n)] [∀ n, Module.Free R (C.X n)] (n : ℤ) :
    Projective ((complexDual R C).X n) := inferInstance

end
end Decoupling.HighDim.Torus
