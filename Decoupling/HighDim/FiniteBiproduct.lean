import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Finset.Erase

/-! # Adding one summand to a genuinely finite biproduct -/

namespace Decoupling.HighDim.FiniteBiproduct

open CategoryTheory CategoryTheory.Limits
noncomputable section

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  {α : Type} [DecidableEq α] (B : α → C) (s : Finset α)

abbrev sumObj := ⨁ (fun i : s => B i)

def fromErase (j : α) : sumObj B (s.erase j) ⟶ sumObj B s :=
  biproduct.desc (fun i => biproduct.ι (fun i : s => B i)
    ⟨i, Finset.mem_of_mem_erase i.property⟩)

def toErase (j : α) : sumObj B s ⟶ sumObj B (s.erase j) :=
  biproduct.lift (fun i => biproduct.π (fun i : s => B i)
    ⟨i, Finset.mem_of_mem_erase i.property⟩)

def eraseIso (j : α) (hj : j ∈ s) : sumObj B (s.erase j) ⊞ B j ≅ sumObj B s where
  hom := biprod.desc (fromErase B s j) (biproduct.ι (fun i : s => B i) ⟨j, hj⟩)
  inv := biprod.lift (toErase B s j) (biproduct.π (fun i : s => B i) ⟨j, hj⟩)
  hom_inv_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · apply biproduct.hom_ext'; intro i
        apply biproduct.hom_ext; intro k
        by_cases hik : i = k
        · subst k; simp [fromErase, toErase, Category.assoc]
        · have hval : (i : α) ≠ (k : α) := fun h => hik (Subtype.ext h)
          simp [fromErase, toErase, Category.assoc, Subtype.ext_iff, hval, hik]
      · apply biproduct.hom_ext'; intro i
        have hi : (i : α) ≠ j := (Finset.mem_erase.mp i.property).1
        simp [fromErase, Category.assoc, Subtype.ext_iff, hi]
    · apply biprod.hom_ext
      · apply biproduct.hom_ext; intro i
        have hi : j ≠ (i : α) := Ne.symm (Finset.mem_erase.mp i.property).1
        simp [toErase, Category.assoc, Subtype.ext_iff, hi]
      · simp
  inv_hom_id := by
    apply biproduct.hom_ext'; intro i
    simp only [biprod.lift_desc, Preadditive.comp_add, ← Category.assoc, Category.comp_id]
    by_cases hi : (i : α) = j
    · subst j
      have hto : biproduct.ι (fun i : s => B i) i ≫ toErase B s i = 0 := by
        apply biproduct.hom_ext; intro l
        have hl : (i : α) ≠ (l : α) := Ne.symm (Finset.mem_erase.mp l.property).1
        simp [toErase, Category.assoc, Subtype.ext_iff, hl]
      rw [hto]
      simp
    · have his : (i : α) ∈ s.erase j := Finset.mem_erase.mpr ⟨hi, i.property⟩
      have hto : biproduct.ι (fun i : s => B i) i ≫ toErase B s j =
          biproduct.ι (fun i : s.erase j => B i) ⟨i, his⟩ := by
        apply biproduct.hom_ext; intro l
        simp [toErase, Category.assoc, biproduct.ι_π, Subtype.ext_iff]
      rw [hto]
      simp [fromErase, Subtype.ext_iff, hi]

omit [HasBinaryBiproducts C] in
def singletonIso (j : α) : sumObj B {j} ≅ B j := by
  letI : Unique ({j} : Finset α) :=
    ⟨⟨j, Finset.mem_singleton_self j⟩, fun i => Subtype.ext (Finset.mem_singleton.mp i.property)⟩
  exact biproductUniqueIso (fun i : ({j} : Finset α) => B i)

end
end Decoupling.HighDim.FiniteBiproduct
