import Decoupling.HighDim.AlgorithmTwoComparisonCone

/-! # Literal block differential of the native mapping cone -/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgorithmTwoComparison CochainComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
variable {R : Type} [CommRing R] {T C : CochainComplex (ModuleCat.{0} R) ℤ}

theorem coneCoordinate_fst (f : T ⟶ C) (n : ℤ) (x : (mappingCone f).X n) :
    ((actualConeTermIso f n).hom x).1 = (mappingCone.fst f).1.v n (n + 1) rfl x := by
  have he : (ModuleCat.biprodIsoProd (T.X (n + 1)) (C.X n)).hom ≫
      ModuleCat.ofHom (LinearMap.fst R _ _) = biprod.fst := by
    rw [← cancel_epi (ModuleCat.biprodIsoProd (T.X (n + 1)) (C.X n)).inv]
    simp
  change ((actualConeTermIso f n).hom ≫ ModuleCat.ofHom (LinearMap.fst R _ _)) x = _
  rw [actualConeTermIso, Iso.trans_hom, Category.assoc, he]
  rfl

theorem coneCoordinate_snd (f : T ⟶ C) (n : ℤ) (x : (mappingCone f).X n) :
    ((actualConeTermIso f n).hom x).2 = (mappingCone.snd f).v n n (add_zero n) x := by
  have he : (ModuleCat.biprodIsoProd (T.X (n + 1)) (C.X n)).hom ≫
      ModuleCat.ofHom (LinearMap.snd R _ _) = biprod.snd := by
    rw [← cancel_epi (ModuleCat.biprodIsoProd (T.X (n + 1)) (C.X n)).inv]
    simp
  change ((actualConeTermIso f n).hom ≫ ModuleCat.ofHom (LinearMap.snd R _ _)) x = _
  rw [actualConeTermIso, Iso.trans_hom, Category.assoc, he]
  have hs : (homotopyCofiber.XIsoBiprod f n (n + 1) rfl).hom ≫ biprod.snd =
      homotopyCofiber.sndX f n := by
    apply homotopyCofiber.ext_from_X f (n + 1) n rfl <;> simp
  rw [hs]
  rfl

/-- The native cone uses the order `(T[n+1], C[n])` and the exact
differential `(-dT*x, Γ*x+dC*y)`, in every characteristic. -/
theorem coneCoordinate_d (f : T ⟶ C) (n : ℤ) (x : (mappingCone f).X n) :
    (actualConeTermIso f (n + 1)).hom ((mappingCone f).d n (n + 1) x) =
      (-(T.d (n + 1) (n + 1 + 1) (((actualConeTermIso f n).hom x).1)),
        f.f (n + 1) (((actualConeTermIso f n).hom x).1) +
          C.d n (n + 1) (((actualConeTermIso f n).hom x).2)) := by
  apply Prod.ext
  · rw [coneCoordinate_fst, coneCoordinate_fst]
    change ((mappingCone f).d n (n + 1) ≫ (mappingCone.fst f).1.v (n + 1) (n + 1 + 1) rfl) x = _
    rw [mappingCone.d_fst_v f n (n + 1) (n + 1 + 1) rfl rfl]
    rfl
  · rw [coneCoordinate_snd, coneCoordinate_fst, coneCoordinate_snd]
    change ((mappingCone f).d n (n + 1) ≫ (mappingCone.snd f).v (n + 1) (n + 1) (add_zero _)) x = _
    rw [mappingCone.d_snd_v f n (n + 1) rfl]
    rfl

theorem coneCoordinate_d_pair (f : T ⟶ C) (n : ℤ) (x : T.X (n + 1)) (y : C.X n) :
    (actualConeTermIso f (n + 1)).hom
        ((mappingCone f).d n (n + 1) ((actualConeTermIso f n).inv (x, y))) =
      (-(T.d (n + 1) (n + 1 + 1) x), f.f (n + 1) x + C.d n (n + 1) y) := by
  rw [coneCoordinate_d]
  have he : (actualConeTermIso f n).hom ((actualConeTermIso f n).inv (x, y)) = (x, y) :=
    (actualConeTermIso f n).toLinearEquiv.apply_symm_apply _
  rw [he]

end
end Decoupling.HighDim.AlgorithmTwoToricData
