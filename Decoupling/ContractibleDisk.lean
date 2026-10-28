import Decoupling.Laurent
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Contractible disks and preservation of all-degree homology -/

namespace Decoupling.ContractibleDisk

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

set_option backward.isDefEq.respectTransparency false

instance : HasBinaryBiproducts (ChainComplex (ModuleCat R) ℤ) :=
  HasBinaryBiproducts.of_hasBinaryProducts

variable (P : ModuleCat R) (j : ℤ)

def disk : ChainComplex (ModuleCat R) ℤ :=
  HomologicalComplex.double (𝟙 P) (show (ComplexShape.down ℤ).Rel j (j - 1) by change _ + 1 = _; omega)

def upperIso : (disk P j).X j ≅ P := HomologicalComplex.doubleXIso₀ _ _
def lowerIso : (disk P j).X (j - 1) ≅ P := HomologicalComplex.doubleXIso₁ _ _ (by omega)

/-- Identity from degree j−1 to j, transported through the actual complex's
coordinate identifications, and zero everywhere else. -/
def contraction (i k : ℤ) : (disk P j).X i ⟶ (disk P j).X k :=
  if hi : i = j - 1 then if hk : k = j then
    eqToHom (congrArg (disk P j).X hi) ≫ (lowerIso P j).hom ≫ (upperIso P j).inv ≫
      eqToHom (congrArg (disk P j).X hk.symm)
  else 0 else 0

theorem contraction_zero (i k : ℤ) (h : ¬ (ComplexShape.down ℤ).Rel k i) :
    contraction P j i k = 0 := by
  dsimp [contraction]
  split_ifs with hi hk
  · subst i
    subst k
    exact (h (by change _ + 1 = _; omega)).elim
  · rfl
  · rfl

theorem dh_add_hd : Homotopy.nullHomotopicMap (contraction P j) = 𝟙 (disk P j) := by
  apply HomologicalComplex.from_double_hom_ext
  · change dNext j (contraction P j) + prevD j (contraction P j) = 𝟙 _
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel j (j - 1) by change _ + 1 = _; omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (j + 1) j by change _ + 1 = _; omega)]
    have hne : j ≠ j - 1 := by omega
    simp only [disk, HomologicalComplex.double_d _ _ hne]
    simp only [contraction, dite_eq_right hne, eqToHom_refl, Category.comp_id, Category.id_comp, lowerIso, upperIso]
    simp [Category.assoc]
  · change dNext (j - 1) (contraction P j) + prevD (j - 1) (contraction P j) = 𝟙 _
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (j - 1) (j - 2) by change _ + 1 = _; omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel j (j - 1) by change _ + 1 = _; omega)]
    have hne : j ≠ j - 1 := by omega
    have hne' : j - 2 ≠ j - 1 := by omega
    simp only [disk, HomologicalComplex.double_d _ _ hne]
    simp only [contraction, dite_eq_right hne', eqToHom_refl, Category.comp_id, Category.id_comp, lowerIso, upperIso]
    simp [Category.assoc]

def contractible : Homotopy (𝟙 (disk P j)) 0 :=
  (Homotopy.ofEq (dh_add_hd P j).symm).trans
    (Homotopy.nullHomotopy (contraction P j) (contraction_zero P j))

variable (K : ChainComplex (ModuleCat R) ℤ)

/-- Adding the actual disk is a chain homotopy equivalence. -/
def stabilization : HomotopyEquiv (K ⊞ disk P j) K where
  hom := biprod.fst
  inv := biprod.inl
  homotopyHomInvId := by
    have h : Homotopy
        ((biprod.snd : K ⊞ disk P j ⟶ disk P j) ≫ (biprod.inr : disk P j ⟶ K ⊞ disk P j)) 0 := by
      simpa using ((contractible P j).compLeft biprod.snd).compRight biprod.inr
    have hh := (Homotopy.refl (biprod.fst ≫ biprod.inl : K ⊞ disk P j ⟶ K ⊞ disk P j)).add h
    have htotal : Homotopy (𝟙 (K ⊞ disk P j)) (biprod.fst ≫ biprod.inl) := by
      simpa only [add_zero, biprod.total] using hh
    exact htotal.symm
  homotopyInvHomId := Homotopy.ofEq (by simp)

/-- Every degree's actual categorical homology is preserved. -/
def homologyIso (i : ℤ) : (K ⊞ disk P j).homology i ≅ K.homology i :=
  (stabilization P j K).toHomologyIso i

end
end Decoupling.ContractibleDisk
