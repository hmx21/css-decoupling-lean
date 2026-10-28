import Decoupling.HighDim.GluedNativeComparisonExact

/-!
# The native cone is the actual check-matrix profile

The comparison is a proved positive quasi-isomorphism, not a match of
cohomology dimensions. Consequently it retains the genuine connecting
class of the displayed matrices.
-/

namespace Decoupling.HighDim.Glued
open CategoryTheory CategoryTheory.Limits HomologicalComplex Koszul
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

theorem rightToCone_surjective (n : ℕ) (hn : Function.Surjective (rightConeComponent K n)) :
    Function.Surjective ((rightToCone K).f (n : ℤ)) := by
  rw [rightToCone_f]
  exact hn.comp ((rightComplex K).extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv.surjective

theorem rightToCone_injective (n : ℕ) (hn : Function.Injective (rightConeComponent K n)) :
    Function.Injective ((rightToCone K).f (n : ℤ)) := by
  rw [rightToCone_f]
  exact hn.comp ((rightComplex K).extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv.injective

theorem rightExtended_X_zero (n : ℤ) (hn : 3 ≤ n) :
    IsZero (((rightComplex K).extend ComplexShape.embeddingUpNat).X n) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = ((m + 3 : ℕ) : ℤ) := ⟨(n - 3).toNat, by omega⟩
  apply IsZero.of_iso _ ((rightComplex K).extendXIso ComplexShape.embeddingUpNat
    (i := m + 3) rfl)
  change IsZero (ModuleCat.of (Laurent K 3) (Fin 0 → Laurent K 3))
  exact ModuleCat.isZero_of_subsingleton _

theorem rightToCone_one_kernel (x : ((rightComplex K).extend ComplexShape.embeddingUpNat).X 1)
    (hx : (rightToCone K).f 1 x = 0) :
    ∃ w, ((rightComplex K).extend ComplexShape.embeddingUpNat).d 0 1 w = x := by
  let e₀ := (rightComplex K).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl
  let e₁ := (rightComplex K).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl
  have hv : rightConeComponent K 1 (e₁.hom x) = 0 := by
    have he := rightToCone_f K 1
    change (rightToCone K).f 1 = e₁.hom ≫ rightConeComponent K 1 at he
    rw [he] at hx
    exact hx
  obtain ⟨w, hw⟩ := rightConeComponent_one_kernel K (e₁.hom x) hv
  refine ⟨e₀.inv w, ?_⟩
  apply e₁.toLinearEquiv.injective
  change (e₀.inv ≫ ((rightComplex K).extend ComplexShape.embeddingUpNat).d 0 1 ≫ e₁.hom) w = e₁.hom x
  rw [(rightComplex K).extend_d_eq ComplexShape.embeddingUpNat
    (i := 0) (j := 1) (i' := 0) (j' := 1) rfl rfl]
  simp only [e₀, e₁, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact hw

theorem rightToCone_quasiIsoAt_one : QuasiIsoAt (rightToCone K) 1 := by
  rw [quasiIsoAt_iff' _ 0 1 2 (by simp) (by simp)]
  apply quasiIso_of_surjective_exact_kernel
  · exact rightToCone_surjective K 0 (rightConeComponent_zero_surjective K)
  · exact rightToCone_surjective K 1 (rightConeComponent_one_surjective K)
  · exact rightToCone_injective K 2 (rightConeComponent_two_bijective K).1
  · exact rightToCone_one_kernel K

theorem rightToCone_quasiIsoAt_two : QuasiIsoAt (rightToCone K) 2 := by
  rw [quasiIsoAt_iff' _ 1 2 3 (by simp) (by simp)]
  apply quasiIso_of_surjective_exact_kernel
  · exact rightToCone_surjective K 1 (rightConeComponent_one_surjective K)
  · exact rightToCone_surjective K 2 (rightConeComponent_two_bijective K).2
  · intro x y _
    exact (ModuleCat.subsingleton_of_isZero (rightExtended_X_zero K 3 (by omega))).elim x y
  · intro x hx
    have hz : x = 0 := rightToCone_injective K 2 (rightConeComponent_two_bijective K).1
      (hx.trans (map_zero _).symm)
    exact ⟨0, by rw [map_zero, hz]⟩

theorem rightToCone_quasiIsoAt (n : ℤ) (hn : 1 ≤ n) : QuasiIsoAt (rightToCone K) n := by
  by_cases h1 : n = 1
  · subst n; exact rightToCone_quasiIsoAt_one K
  by_cases h2 : n = 2
  · subst n; exact rightToCone_quasiIsoAt_two K
  have hn3 : 3 ≤ n := by omega
  rw [quasiIsoAt_iff_exactAt' _ n ((couplingCone K).exactAt_of_isLE 2 n (by omega))]
  rw [HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_isZero_X₂ _ (rightExtended_X_zero K n hn3)

instance rightToCone_truncGE_quasiIso :
    QuasiIso (CochainComplex.truncGEMap (rightToCone K) 1) :=
  (CochainComplex.quasiIso_truncGEMap_iff _ _).mpr (rightToCone_quasiIsoAt K)

/-- The concrete native CSS profile is isomorphic to the actual coupling
cone, with its full derived extension data preserved. -/
def actualProfileConeIso : Profile.S_X (checks K) ≅ DerivedCategory.Q.obj (couplingCone K) :=
  (nativeRightProfileIso K).symm ≪≫
    asIso (DerivedCategory.Q.map (CochainComplex.truncGEMap (rightToCone K) 1)) ≪≫
      (asIso (DerivedCategory.Q.map ((couplingCone K).πTruncGE 1))).symm

end
end Decoupling.HighDim.Glued
