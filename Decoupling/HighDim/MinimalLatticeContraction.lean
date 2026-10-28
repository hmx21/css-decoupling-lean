import Decoupling.HighDim.TorusCells
import Decoupling.HighDim.ExtValuesAlternating
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Detection by signed exterior multiplication

Source: Appendix B.3. Coefficients are taken from actual exterior-algebra
multiplication, including its permutation sign in every characteristic.
Disjoint cells isolate each nonzero Hom-valued coefficient. This is the
algebraic detection lemma; its native Yoneda comparison is separate.
-/

namespace Decoupling.HighDim.ExteriorDetection
open Koszul Toric.Hodge
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {D m n : ℕ}

abbrev asSubset {k : ℕ} (I : Cell D k) : Set.powersetCard (Fin D) k :=
  Set.powersetCard.ofCard (directions_card I)

def exteriorBasis : Module.Basis (Finset (Fin D)) K (ExteriorAlgebra K (Fin D → K)) :=
  (Pi.basisFun K (Fin D)).ExteriorAlgebra

def wedgeCoefficient (J : Cell D m) (I : Cell D n) (L : Cell D (m + n)) : K :=
  (exteriorBasis (K := K)).repr (exteriorBasis (directions J) * exteriorBasis (directions I))
    (directions L)

theorem wedgeCoefficient_of_not_disjoint (J : Cell D m) (I : Cell D n)
    (L : Cell D (m + n)) (h : ¬ Disjoint (directions J) (directions I)) :
    wedgeCoefficient (K := K) J I L = 0 := by
  unfold wedgeCoefficient exteriorBasis
  have hp := ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun K (Fin D)) (asSubset J) (asSubset I) h
  change (Pi.basisFun K (Fin D)).ExteriorAlgebra (directions J) *
    (Pi.basisFun K (Fin D)).ExteriorAlgebra (directions I) = 0 at hp
  rw [hp]
  simp

theorem wedgeCoefficient_of_disjoint (J : Cell D m) (I : Cell D n)
    (L : Cell D (m + n)) (h : Disjoint (directions J) (directions I)) :
    wedgeCoefficient (K := K) J I L =
      if directions J ∪ directions I = directions L then
        (Set.powersetCard.permOfDisjoint (s := asSubset J) (t := asSubset I) h).sign • (1 : K)
      else 0 := by
  unfold wedgeCoefficient exteriorBasis
  have hp := ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun K (Fin D)) (asSubset J) (asSubset I) h
  change (Pi.basisFun K (Fin D)).ExteriorAlgebra (directions J) *
    (Pi.basisFun K (Fin D)).ExteriorAlgebra (directions I) = _ at hp
  rw [hp]
  simp [Set.powersetCard.disjUnion, Finset.disjUnion_eq_union, asSubset, Finsupp.single_apply]

theorem exists_disjoint_cell (I : Cell D n) (hmn : m + n ≤ D) :
    ∃ J : Cell D m, Disjoint (directions J) (directions I) := by
  have hm : m ≤ (directions I)ᶜ.card := by simp only [Finset.card_compl, Fintype.card_fin, directions_card]; omega
  obtain ⟨s, hsub, hcard⟩ := Finset.exists_subset_card_eq hm
  let J : Cell D m := s.orderEmbOfFin hcard
  have hJ : directions J = s := Finset.map_orderEmbOfFin_univ _ _
  refine ⟨J, Finset.disjoint_left.mpr ?_⟩
  intro a ha hi
  rw [hJ] at ha
  exact (Finset.mem_compl.mp (hsub ha)) hi

def unionCell (J : Cell D m) (I : Cell D n) (h : Disjoint (directions J) (directions I)) :
    Cell D (m + n) := (directions J ∪ directions I).orderEmbOfFin (by
  rw [Finset.card_union_of_disjoint h, directions_card, directions_card])

@[simp] theorem directions_unionCell (J : Cell D m) (I : Cell D n)
    (h : Disjoint (directions J) (directions I)) :
    directions (unionCell J I h) = directions J ∪ directions I :=
  Finset.map_orderEmbOfFin_univ _ _

theorem union_injective_right (J : Cell D m) (I I' : Cell D n)
    (h : Disjoint (directions J) (directions I))
    (h' : Disjoint (directions J) (directions I'))
    (he : directions J ∪ directions I = directions J ∪ directions I') : I = I' := by
  apply directions_injective
  ext a
  have hh : a ∈ directions J ∪ directions I ↔ a ∈ directions J ∪ directions I' := by rw [he]
  have h₁ : ¬ (a ∈ directions J ∧ a ∈ directions I) := fun ha => (Finset.disjoint_left.mp h) ha.1 ha.2
  have h₂ : ¬ (a ∈ directions J ∧ a ∈ directions I') := fun ha => (Finset.disjoint_left.mp h') ha.1 ha.2
  simp only [Finset.mem_union] at hh
  tauto

theorem wedgeCoefficient_other (J : Cell D m) (I I' : Cell D n)
    (h : Disjoint (directions J) (directions I)) (hne : I' ≠ I) :
    wedgeCoefficient (K := K) J I' (unionCell J I h) = 0 := by
  by_cases h' : Disjoint (directions J) (directions I')
  · rw [wedgeCoefficient_of_disjoint _ _ _ h', directions_unionCell, ite_eq_right]
    exact fun he => hne (union_injective_right J I' I h' h he)
  · exact wedgeCoefficient_of_not_disjoint J I' _ h'

theorem wedgeCoefficient_self_ne_zero (J : Cell D m) (I : Cell D n)
    (h : Disjoint (directions J) (directions I)) :
    wedgeCoefficient (K := K) J I (unionCell J I h) ≠ 0 := by
  rw [wedgeCoefficient_of_disjoint _ _ _ h, directions_unionCell, ite_eq_left rfl]
  rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint
    (s := asSubset J) (t := asSubset I) h).sign with hh | hh <;> simp [hh]

variable {B A : Type*} [AddCommGroup B] [Module K B] [AddCommGroup A] [Module K A]

/-- Multiplication of a B-valued exterior form by a Hom(B,A)-valued form,
in the exact coefficients of the genuine exterior algebra product. -/
def wedgeTable (κ : Cell D n → (B →ₗ[K] A)) (α : Cell D m → B) : Cell D (m + n) → A :=
  fun L => ∑ J : Cell D m, ∑ I : Cell D n, wedgeCoefficient (K := K) J I L • κ I (α J)

theorem wedgeTable_single (κ : Cell D n → (B →ₗ[K] A)) (J : Cell D m)
    (I : Cell D n) (h : Disjoint (directions J) (directions I)) (b : B) :
    wedgeTable κ (Pi.single J b) (unionCell J I h) =
      wedgeCoefficient (K := K) J I (unionCell J I h) • κ I b := by
  unfold wedgeTable
  rw [Finset.sum_eq_single J]
  · simp only [Pi.single_eq_same]
    rw [Finset.sum_eq_single I]
    · intro I' _ hne
      rw [wedgeCoefficient_other J I I' h hne, zero_smul]
    · simp
  · intro J' _ hne
    simp [Pi.single_eq_of_ne hne]
  · simp

/-- A nonzero Hom-valued form is detected by multiplication with a
single disjoint cell and a single source vector. -/
theorem exists_wedgeTable_ne_zero (κ : Cell D n → (B →ₗ[K] A))
    (hκ : κ ≠ 0) (hmn : m + n ≤ D) : ∃ α : Cell D m → B, wedgeTable κ α ≠ 0 := by
  have hex : ∃ I b, κ I b ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hκ (funext (fun I => LinearMap.ext (hh I)))
  obtain ⟨I, b, hb⟩ := hex
  obtain ⟨J, hJI⟩ := exists_disjoint_cell I hmn
  refine ⟨Pi.single J b, ?_⟩
  intro hz
  have he := congrFun hz (unionCell J I hJI)
  rw [wedgeTable_single] at he
  exact (smul_ne_zero (wedgeCoefficient_self_ne_zero J I hJI) hb) he

def wedgeLinear (κ : Cell D n → (B →ₗ[K] A)) :
    (Cell D m → B) →ₗ[K] (Cell D (m + n) → A) where
  toFun := wedgeTable κ
  map_add' α β := by ext L; simp [wedgeTable, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' k α := by
    ext L
    simp [wedgeTable, map_smul, Finset.smul_sum, smul_smul, mul_comm]

theorem wedgeLinear_ne_zero (κ : Cell D n → (B →ₗ[K] A)) (hκ : κ ≠ 0) (hmn : m + n ≤ D) :
    wedgeLinear (m := m) κ ≠ 0 := by
  obtain ⟨α, hα⟩ := exists_wedgeTable_ne_zero κ hκ hmn
  intro hz
  exact hα (LinearMap.congr_fun hz α)

end
end Decoupling.HighDim.ExteriorDetection
