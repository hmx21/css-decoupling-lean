import Decoupling.HighDim.AlgorithmTwoComputedLayersCoordinates

/-!
# Explicit unit coordinates for each computed toric layer

The map reads the actual biproduct component of copy `(j,k)`.
All other degree components are zero modules. Its inverse fills those
zero components with zero, so no basis is selected for the source.
-/
namespace Decoupling.HighDim.AlgorithmTwoComputedLayers
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgorithmTwoComparison TrivialLayers
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
variable (K : Type) [Field K] (D : ℕ) (t : Fin (D - 1) → ℕ)

local instance : HasFiniteBiproducts (CochainComplex (ModuleCat (Laurent K D)) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

def zeroTermPiIso (n : ℤ) :
    (stackZeroModel K D (Toric.copyForms D t)).X n ≅
      ModuleCat.of (Laurent K D) (∀ i : Toric.Copies D t,
        (stackSingleFamily K D (Toric.copyForms D t) i).X n) :=
  (eval (ModuleCat (Laurent K D)) (ComplexShape.up ℤ) n).mapBiproduct
    (stackSingleFamily K D (Toric.copyForms D t)) ≪≫ ModuleCat.biproductIsoPi _

theorem zeroTermPiIso_apply (n : ℤ)
    (x : (stackZeroModel K D (Toric.copyForms D t)).X n) (i : Toric.Copies D t) :
    (zeroTermPiIso K D t n).hom x i =
      (biproduct.π (stackSingleFamily K D (Toric.copyForms D t)) i).f n x := by
  let N := stackSingleFamily K D (Toric.copyForms D t)
  have hp : (ModuleCat.biproductIsoPi (fun i => (N i).X n)).hom ≫
      ModuleCat.ofHom (LinearMap.proj i) = biproduct.π (fun i => (N i).X n) i := by
    rw [← cancel_epi (ModuleCat.biproductIsoPi (fun i => (N i).X n)).inv]
    simp
  have he : (zeroTermPiIso K D t n).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      (biproduct.π N i).f n := by
    dsimp only [zeroTermPiIso, Iso.trans_hom]
    dsimp +instances only [Function.comp_def, eval_obj, N, stackZeroModel] at *
    rw [Category.assoc, hp, Functor.mapBiproduct_hom]
    exact biproduct.lift_π _ i
  exact congrArg (fun f => f x) he

def supportedPiEquiv (j : Fin (D - 1)) :
    (∀ i : Toric.Copies D t, (stackSingleFamily K D (Toric.copyForms D t) i).X (j.val + 1)) ≃ₗ[Laurent K D]
      coefficientVector K D (t j) where
  toFun v k := (singleObjXSelf (ComplexShape.up ℤ) (j.val + 1)
    (Koszul.coefficientModule K D)).hom (v ⟨j, k⟩)
  invFun v i := if h : i.1 = j then by
      rcases i with ⟨l, k⟩
      dsimp at h
      subst l
      exact (singleObjXSelf (ComplexShape.up ℤ) (j.val + 1)
        (Koszul.coefficientModule K D)).inv (v k)
    else 0
  left_inv v := by
    funext i
    rcases i with ⟨l, k⟩
    dsimp only
    by_cases hlj : l = j
    · subst l
      simp only
      change ((singleObjXSelf (ComplexShape.up ℤ) (j.val + 1) (Koszul.coefficientModule K D)).hom ≫
        (singleObjXSelf (ComplexShape.up ℤ) (j.val + 1) (Koszul.coefficientModule K D)).inv) (v ⟨j, k⟩) = _
      rw [Iso.hom_inv_id]
      rfl
    · rw [dite_eq_right hlj]
      have hz : IsZero ((stackSingleFamily K D (Toric.copyForms D t) ⟨l, k⟩).X (j.val + 1)) := by
        apply isZero_single_obj_X
        intro he
        apply hlj
        apply Fin.ext
        change (j.val : ℤ) + 1 = (l.val : ℤ) + 1 at he
        omega
      exact (ModuleCat.subsingleton_of_isZero hz).elim _ _
  right_inv v := by
    funext k
    simp only
    change ((singleObjXSelf (ComplexShape.up ℤ) (j.val + 1) (Koszul.coefficientModule K D)).inv ≫
      (singleObjXSelf (ComplexShape.up ℤ) (j.val + 1) (Koszul.coefficientModule K D)).hom) (v k) = _
    rw [Iso.inv_hom_id]
    rfl
  map_add' v w := by funext k; exact map_add _ _ _
  map_smul' a v := by funext k; exact map_smul _ _ _

/-- Read the individual unit coordinates in degree `j+1`. -/
def sourceCoordinates (j : Fin (D - 1)) :
    (stackZeroModel K D (Toric.copyForms D t)).X (j.val + 1) ≅ coefficientVector K D (t j) :=
  zeroTermPiIso K D t (j.val + 1) ≪≫ (supportedPiEquiv K D t j).toModuleIso

theorem sourceCoordinates_apply (j : Fin (D - 1))
    (x : (stackZeroModel K D (Toric.copyForms D t)).X (j.val + 1)) (k : Fin (t j)) :
    (sourceCoordinates K D t j).hom x k =
      (singleObjXSelf (ComplexShape.up ℤ) (j.val + 1) (Koszul.coefficientModule K D)).hom
        ((biproduct.π (stackSingleFamily K D (Toric.copyForms D t)) ⟨j, k⟩).f (j.val + 1) x) := by
  change (singleObjXSelf (ComplexShape.up ℤ) (j.val + 1) (Koszul.coefficientModule K D)).hom
    ((zeroTermPiIso K D t (j.val + 1)).hom x ⟨j, k⟩) = _
  rw [zeroTermPiIso_apply]

theorem sourceCoordinates_top (j : Fin (D - 1)) (k : Fin (t j)) :
    (sourceCoordinates K D t j).hom (stackTopImage K D (Toric.copyForms D t) ⟨j, k⟩) =
      Pi.single k (1 : K) := by
  classical
  funext l
  rw [sourceCoordinates_apply, stackTopImage_eq_inclusion]
  let N := stackSingleFamily K D (Toric.copyForms D t)
  change (singleObjXSelf (ComplexShape.up ℤ) (j.val + 1) (Koszul.coefficientModule K D)).hom
    (((biproduct.ι N ⟨j, k⟩).f (j.val + 1) ≫ (biproduct.π N ⟨j, l⟩).f (j.val + 1))
      ((singleObjXSelf (ComplexShape.up ℤ) (j.val + 1) (Koszul.coefficientModule K D)).inv (1 : K))) = _
  rw [← HomologicalComplex.comp_f]
  by_cases hkl : k = l
  · subst l
    rw [biproduct.ι_π_self, HomologicalComplex.id_f]
    change ((singleObjXSelf (ComplexShape.up ℤ) (j.val + 1) (Koszul.coefficientModule K D)).inv ≫
      (singleObjXSelf (ComplexShape.up ℤ) (j.val + 1) (Koszul.coefficientModule K D)).hom) (1 : K) = _
    rw [Iso.inv_hom_id]
    simp
  · rw [biproduct.ι_π_ne _ (by
      intro he
      exact hkl (Fin.ext (congrArg (fun i : Toric.Copies D t => i.2.val) he)))]
    simp [Ne.symm hkl]

end
end Decoupling.HighDim.AlgorithmTwoComputedLayers
