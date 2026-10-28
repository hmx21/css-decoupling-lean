import Decoupling.HighDim.KoszulComplex

/-!
# The diagonal comparison of actual signed Koszul complexes

Source: `drafts/appendix.tex`, proof of Lemma 1: the comparison multiplies
`e_I` by the product of the coordinate comparison factors indexed by `I`.
This file proves a native chain map over a common coefficient ring. The
coarse-ring semilinear identification and the passage to actual Ext still
require separate resolution and restriction arguments; they are not
claimed here.
-/

namespace Decoupling.HighDim.Koszul

open CategoryTheory CategoryTheory.Preadditive

noncomputable section

variable (A : Type*) [CommRing A] {D : ℕ}

/-- The product of one comparison factor for each ordered direction. -/
def comparisonFactor (c : Fin D → A) {k : ℕ} (I : Cell D k) : A :=
  ∏ j : Fin k, c (I j)

theorem comparisonFactor_face (c : Fin D → A) {k : ℕ}
    (I : Cell D (k + 1)) (i : Fin (k + 1)) :
    comparisonFactor A c I = c (I i) * comparisonFactor A c (face I i) :=
  Fin.prod_univ_succAbove (fun j => c (I j)) i

/-- Actual diagonal scaling on the free cell module. -/
def comparisonTerm (c : Fin D → A) (k : ℕ) :
    ModuleCat.of A (Term A D k) ⟶ ModuleCat.of A (Term A D k) :=
  ModuleCat.ofHom (Finsupp.linearCombination A
    (fun I : Cell D k => Finsupp.single I (comparisonFactor A c I)))

@[simp] theorem comparisonTerm_single (c : Fin D → A) {k : ℕ}
    (I : Cell D k) (a : A) :
    (comparisonTerm A c k).hom (Finsupp.single I a) =
      Finsupp.single I (a * comparisonFactor A c I) := by
  simp [comparisonTerm, Finsupp.smul_single, smul_eq_mul]

theorem comparisonTerm_weightedFace (w c : Fin D → A) (k : ℕ) (i : Fin (k + 1)) :
    comparisonTerm A c (k + 1) ≫ weightedFace A w k i =
      weightedFace A (fun j => w j * c j) k i ≫ comparisonTerm A c k := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro I a
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, comparisonTerm,
    weightedFace, ModuleCat.hom_ofHom, Finsupp.linearCombination_single,
    Finsupp.smul_single, smul_eq_mul]
  apply congrArg (Finsupp.single _)
  rw [comparisonFactor_face A c I i]
  ring

/-- Diagonal comparison commutes with the full alternating differential. -/
theorem comparisonTerm_boundary (w c : Fin D → A) (k : ℕ) :
    comparisonTerm A c (k + 1) ≫ boundary A w k =
      boundary A (fun j => w j * c j) k ≫ comparisonTerm A c k := by
  simp only [boundary, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [comparisonTerm_weightedFace]

/-- A native chain map `K(w_i c_i) → K(w_i)`, with the exact diagonal
formula on every degree. -/
def comparison (w c : Fin D → A) :
    complex A (fun i => w i * c i) ⟶ complex A w :=
  ChainComplex.ofHom (fun k => comparisonTerm A c k) (by
    intro k
    simpa [complex] using comparisonTerm_boundary A w c k)

@[simp] theorem comparison_f (w c : Fin D → A) (k : ℕ) :
    (comparison A w c).f k = comparisonTerm A c k := rfl

section AnnihilatedTarget

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- In positive degree, every comparison coefficient contains an
annihilating factor. This works in all characteristics and also when
there are no cells in that degree. -/
theorem comparisonFactor_smul_eq_zero (w : Fin D → A)
    (hM : ∀ i : Fin D, ∀ m : M, w i • m = 0)
    (e k : ℕ) (I : Cell D (k + 1)) (m : M) :
    comparisonFactor A (fun i => w i ^ (e + 1)) I • m = 0 := by
  rw [comparisonFactor_face A (fun i => w i ^ (e + 1)) I 0,
    pow_succ', mul_smul, mul_smul]
  exact hM _ _

/-- The actual composite into an annihilated module is zero. This is the
coefficient calculation needed later in the Ext comparison argument;
it does not identify arbitrary Ext classes with cochains by assumption. -/
theorem postcomp_comparisonTerm_eq_zero (w : Fin D → A)
    (hM : ∀ i : Fin D, ∀ m : M, w i • m = 0)
    (e k : ℕ) (f : Term A D (k + 1) →ₗ[A] M) :
    f.comp (comparisonTerm A (fun i => w i ^ (e + 1)) (k + 1)).hom = 0 := by
  apply Finsupp.lhom_ext
  intro I a
  simp only [LinearMap.comp_apply, comparisonTerm, ModuleCat.hom_ofHom,
    Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul, LinearMap.zero_apply]
  rw [mul_comm a, ← smul_eq_mul, ← Finsupp.smul_single, f.map_smul]
  exact comparisonFactor_smul_eq_zero A w hM e k I _

end AnnihilatedTarget

end

end Decoupling.HighDim.Koszul
