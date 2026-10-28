import Decoupling.RetainedRing

/-! Exact augmented Koszul sequence over the actual doubled subring S. -/

namespace Decoupling.RetainedKoszul

open Matrix RetainedRing

noncomputable section

def evaluation : S →+* ZMod 2 := augmentation.comp renameEquiv.symm.toRingHom

theorem augmentation_embed (r : R) : augmentation (embed r) = augmentation r := by
  have he : (augmentation.comp embed).toAddMonoidHom = augmentation.toAddMonoidHom := by
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro a t
    simp [embed]
  exact DFunLike.congr_fun he r

theorem evaluation_inclusion (s : S) : evaluation s = augmentation (algebraMap S R s) := by
  obtain ⟨r, rfl⟩ := renameEquiv.surjective s
  change augmentation (renameEquiv.symm (renameEquiv r)) = augmentation (embed r)
  rw [renameEquiv.symm_apply_apply, augmentation_embed]

def d₁ : Matrix (Fin 1) (Fin 3) S := Koszul.d₁ (X - 1) (Y - 1) (Z - 1)
def d₂ : Matrix (Fin 3) (Fin 3) S := Koszul.d₂ (X - 1) (Y - 1) (Z - 1)
def d₃ : Matrix (Fin 3) (Fin 1) S := Koszul.d₃ (X - 1) (Y - 1) (Z - 1)

theorem rename_d₁ : PhysicalKoszul.partial₁.map renameEquiv = d₁ := by
  funext i j
  fin_cases i
  fin_cases j <;> simp [PhysicalKoszul.partial₁, Koszul.d₁, d₁]

theorem rename_mulVec {m n : Type*} [Fintype n] (D : Matrix m n R) (a : n → R) :
    D.map renameEquiv *ᵥ (renameEquiv ∘ a) = renameEquiv ∘ (D *ᵥ a) := by
  funext i
  exact (renameEquiv.toRingHom.map_mulVec D a i).symm

/-- Exactness at S, including the augmentation, with no regularity input. -/
theorem exact_augmentation (s : S) : evaluation s = 0 ↔
    ∃ a : Fin 3 → S, d₁ *ᵥ a = ![s] := by
  constructor
  · intro hs
    obtain ⟨a, ha⟩ := (PhysicalKoszul.exact_augmentation (renameEquiv.symm s)).mp hs
    refine ⟨renameEquiv ∘ a, ?_⟩
    rw [← rename_d₁, rename_mulVec, ha]
    funext i
    fin_cases i
    exact renameEquiv.apply_symm_apply s
  · rintro ⟨a, ha⟩
    apply (PhysicalKoszul.exact_augmentation (renameEquiv.symm s)).mpr
    refine ⟨renameEquiv.symm ∘ a, ?_⟩
    funext i
    apply renameEquiv.injective
    change (renameEquiv ∘ (PhysicalKoszul.partial₁ *ᵥ (renameEquiv.symm ∘ a))) i = _
    rw [← rename_mulVec, rename_d₁]
    have hv : renameEquiv ∘ (renameEquiv.symm ∘ a) = a := by
      funext j
      exact renameEquiv.apply_symm_apply (a j)
    rw [hv, ha]
    fin_cases i
    exact (renameEquiv.apply_symm_apply s).symm

theorem evaluation_surjective : Function.Surjective evaluation :=
  augmentation_surjective.comp renameEquiv.symm.surjective

theorem exact_d₁_d₂ (a : Fin 3 → S) : d₁ *ᵥ a = 0 ↔ ∃ b, d₂ *ᵥ b = a :=
  Koszul.exact_d₁_d₂ _ _ _ retained_regularTriple a

theorem exact_d₂_d₃ (a : Fin 3 → S) : d₂ *ᵥ a = 0 ↔ ∃ b, d₃ *ᵥ b = a :=
  Koszul.exact_d₂_d₃ _ _ _ retained_regularTriple.u_injective
    retained_regularTriple.v_mod_u a

theorem d₃_injective : Function.Injective (fun a : Fin 1 → S => d₃ *ᵥ a) :=
  Koszul.d₃_injective _ _ _ retained_regularTriple.u_injective

end
end Decoupling.RetainedKoszul
