import Decoupling.HighDim.KoszulResolution
import Decoupling.HighDim.KoszulComparison
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra

/-!
# The actual semilinear Koszul comparison for lattice scaling

Source: `drafts/appendix.tex`, proof of Lemma 1. Scaling the lattice is the
ring endomorphism sending a monomial with exponent a to that with exponent
p a. Coefficients are fixed. All comparisons below are actual module and
chain maps for the associated scalar restriction functor.
-/

namespace Decoupling.HighDim.Koszul

open CategoryTheory CategoryTheory.Preadditive
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable (A : Type*) [CommRing A] {D : ℕ}

/-- Change the coefficients of a free cell vector using a ring endomorphism. -/
def scalarChangeTerm (φ : A →+* A) (k : ℕ) :
    ModuleCat.of A (Term A D k) ⟶
      (ModuleCat.restrictScalars φ).obj (ModuleCat.of A (Term A D k)) :=
  ModuleCat.ofHom (X := ModuleCat.of A (Term A D k))
    (Y := (ModuleCat.restrictScalars φ).obj (ModuleCat.of A (Term A D k)))
    (Finsupp.linearCombination A (fun I : Cell D k =>
      (show (ModuleCat.restrictScalars φ).obj (ModuleCat.of A (Term A D k)) from
        Finsupp.single I 1)))

@[simp] theorem scalarChangeTerm_single (φ : A →+* A) (k : ℕ)
    (I : Cell D k) (a : A) :
    scalarChangeTerm A φ k (Finsupp.single I a) = Finsupp.single I (φ a) := by
  simp only [scalarChangeTerm, ModuleCat.hom_ofHom, Finsupp.linearCombination_single]
  change φ a • Finsupp.single I 1 = _
  simp [Finsupp.smul_single, smul_eq_mul]

theorem scalarChangeTerm_weightedFace (φ : A →+* A) (w : Fin D → A)
    (k : ℕ) (i : Fin (k + 1)) :
    scalarChangeTerm A φ (k + 1) ≫
      (ModuleCat.restrictScalars φ).map (weightedFace A (fun j => φ (w j)) k i) =
    weightedFace A w k i ≫ scalarChangeTerm A φ k := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro I a
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  change (weightedFace A (fun j => φ (w j)) k i).hom
    (scalarChangeTerm A φ (k + 1) (Finsupp.single I a)) =
    scalarChangeTerm A φ k ((weightedFace A w k i).hom (Finsupp.single I a))
  rw [scalarChangeTerm_single A φ (k + 1) I a]
  rw [weightedFace_single A (fun j => φ (w j)) i I (φ a),
    weightedFace_single A w i I a, scalarChangeTerm_single]
  rw [map_mul]

theorem scalarChangeTerm_boundary (φ : A →+* A) (w : Fin D → A) (k : ℕ) :
    scalarChangeTerm A φ (k + 1) ≫
      (ModuleCat.restrictScalars φ).map (boundary A (fun j => φ (w j)) k) =
    boundary A w k ≫ scalarChangeTerm A φ k := by
  simp only [boundary, Functor.map_sum, Functor.map_zsmul, comp_sum, sum_comp,
    comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [scalarChangeTerm_weightedFace]

/-- A native semilinear comparison between the two signed complexes. -/
def scalarChange (φ : A →+* A) (w : Fin D → A) :
    complex A w ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
      (complex A (fun j => φ (w j))) where
  f k := scalarChangeTerm A φ k
  comm' i j h := by
    obtain rfl : j + 1 = i := h
    simpa only [Functor.mapHomologicalComplex_obj_d, complex_d] using
      scalarChangeTerm_boundary A φ w j

variable (K : Type*) [CommRing K] (D : ℕ)

/-- Multiply every translation coordinate by the scaling integer. -/
def scaleTranslation (e : ℕ) : Translation D →+ Translation D where
  toFun a := e • a
  map_zero' := smul_zero e
  map_add' a b := nsmul_add a b e

/-- The genuine lattice-scaling ring map, fixing the coefficient ring. -/
def scaling (e : ℕ) : Laurent K D →+* Laurent K D :=
  AddMonoidAlgebra.mapDomainRingHom K (scaleTranslation D e)

@[simp] theorem scaling_monomial (e : ℕ) (a : Translation D) :
    scaling K D e (monomial K a) = monomial K (e • a) := by
  simp [scaling, monomial, scaleTranslation]

@[simp] theorem scaling_constant (e : ℕ) (a : K) :
    scaling K D e (constant a) = constant a := by
  simp [scaling, constant]

theorem monomial_nsmul (a : Translation D) (e : ℕ) :
    monomial K (e • a) = monomial K a ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [show (e + 1) • a = e • a + a by exact add_nsmul a e 1 |>.trans (by simp),
      ← monomial_mul, ih, pow_succ]

@[simp] theorem augmentation_scaling (e : ℕ) (a : Laurent K D) :
    augmentation (scaling K D e a) = augmentation a := by
  refine AddMonoidAlgebra.induction_on
    (motive := fun a : Laurent K D => augmentation (scaling K D e a) = augmentation a)
    a ?_ ?_ ?_
  · intro a
    change augmentation (scaling K D e (monomial K a)) = augmentation (monomial K a)
    simp
  · intro a b ha hb; simp [ha, hb]
  · intro c a ha
    have hc : c • a = constant c * a := by
      change c • a = AddMonoidAlgebra.single 0 c * a
      ext x
      simp
    rw [hc, map_mul, scaling_constant, map_mul, map_mul, ha]

theorem scaling_difference (p : ℕ) [Fact p.Prime] [CharP K p] (i : Fin D) :
    scaling K D p (difference K i) = difference K i ^ p := by
  let : CharP (Laurent K D) p := charP_of_injective_ringHom
    (f := (constant : K →+* Laurent K D)) (by
      intro a b h
      simpa using congrArg augmentation h) p
  rw [difference, map_sub, map_one, coordinate, scaling_monomial,
    monomial_nsmul, sub_pow_char, one_pow]

end
end Decoupling.HighDim.Koszul
