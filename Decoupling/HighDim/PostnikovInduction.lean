import Decoupling.HighDim.PostnikovTruncation
import Decoupling.HighDim.PostnikovExtStep
import Decoupling.HighDim.ExactIteration
import Decoupling.HighDim.FiniteBiproduct
import Mathlib.Data.Finset.Max

/-!
# Splitting a finite Postnikov tower in exactly one fewer steps than layers

This is the categorical induction underlying Lemma 2. Its explicit
auxiliary criterion says that the exact functor preserves a class of
modules and kills positive native Ext between them. The application to
augmentation-trivial finite modules uses the separately proved Koszul
restriction theorem; that hypothesis is not assumed for a CSS code.
-/

namespace Decoupling.HighDim.PostnikovInduction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PostnikovTruncation ExactIteration FiniteBiproduct
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]

abbrev H (X : DerivedCategory (ModuleCat R)) (i : ℤ) :=
  (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X

def Supported (X : DerivedCategory (ModuleCat R)) (s : Finset ℤ) : Prop :=
  ∀ i : ℤ, i ∉ s → IsZero (H X i)

theorem supported_isLE {X : DerivedCategory (ModuleCat R)} {s : Finset ℤ}
    (hX : Supported X s) (j : ℤ) (hj : ∀ i ∈ s, i ≤ j) : X.IsLE j := by
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro i hi
  exact hX i (by intro hm; have := hj i hm; omega)

theorem supported_isGE {X : DerivedCategory (ModuleCat R)} {s : Finset ℤ}
    (hX : Supported X s) (j : ℤ) (hj : ∀ i ∈ s, j ≤ i) : X.IsGE j := by
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro i hi
  exact hX i (by intro hm; have := hj i hm; omega)

theorem lower_supported {X : DerivedCategory (ModuleCat R)} {s : Finset ℤ}
    (hX : Supported X s) (j : ℤ) : Supported (lower X j) (s.erase j) := by
  intro i hi
  by_cases hij : i < j
  · have his : i ∉ s := by
      intro his
      exact hi (Finset.mem_erase.mpr ⟨by omega, his⟩)
    exact (hX i his).of_iso (lowerHomologyIso X j i hij)
  · exact DerivedCategory.isZero_of_isLE (lower X j) (j - 1) i (by omega)

variable (F : ModuleCat R ⥤ ModuleCat R) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (P : ModuleCat R → Prop)

omit [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
theorem iterate_property (hMap : ∀ A, P A → P (F.obj A)) (n : ℕ) (A : ModuleCat R)
    (hA : P A) : P ((iterate F n).obj A) := by
  induction n with
  | zero => exact hA
  | succ n ih => exact hMap _ ih

def splitObject (X : DerivedCategory (ModuleCat R)) (s : Finset ℤ) (n : ℕ) :=
  sumObj (fun i => (DerivedCategory.singleFunctor (ModuleCat R) i).obj
    ((iterate F n).obj (H X i))) s

/-- Each additional nonzero layer requires at most one further application
of the functor. In particular the single-layer base case uses zero steps. -/
theorem exists_split
    (hIso : ∀ {A B : ModuleCat R}, (A ≅ B) → P A → P B)
    (hMap : ∀ A, P A → P (F.obj A))
    (hExt : ∀ A B, P A → P B → ∀ (n : ℕ), 0 < n →
      ∀ e : Ext A B n, e.mapExactFunctor F = 0) :
    ∀ (s : Finset ℤ), s.Nonempty → ∀ (X : DerivedCategory (ModuleCat R)),
      Supported X s → (∀ i ∈ s, P (H X i)) →
      Nonempty ((derived F (s.card - 1)).obj X ≅ splitObject F X s (s.card - 1)) := by
  intro s
  refine Finset.strongInductionOn s (fun s ih => ?_)
  intro hs X hX hP
  by_cases hcard : s.card = 1
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
    have : X.IsLE j := supported_isLE hX j (by intro i hi; have := Finset.mem_singleton.mp hi; omega)
    have : X.IsGE j := supported_isGE hX j (by intro i hi; have := Finset.mem_singleton.mp hi; omega)
    change Nonempty (X ≅ sumObj (fun i => (DerivedCategory.singleFunctor (ModuleCat R) i).obj
      (H X i)) {j})
    exact ⟨Profile.singleDegreeIso X j ≪≫ (singletonIso
      (fun i => (DerivedCategory.singleFunctor (ModuleCat R) i).obj (H X i)) j).symm⟩
  · let j := s.max' hs
    have hj : j ∈ s := Finset.max'_mem s hs
    have hle : ∀ i ∈ s, i ≤ j := fun i hi => Finset.le_max' s i hi
    have hlt : ∀ i : s.erase j, (i : ℤ) < j := by
      intro i
      have hi := Finset.mem_erase.mp i.property
      have := hle i hi.2
      omega
    have hne : (s.erase j).Nonempty := by
      apply Finset.card_pos.mp
      have hc := Finset.card_erase_add_one hj
      have hp := hs.card_pos
      omega
    let k := (s.erase j).card - 1
    have hk : s.card - 1 = k + 1 := by
      have hc := Finset.card_erase_add_one hj
      have hp := hne.card_pos
      dsimp [k]
      omega
    have hLE : X.IsLE j := supported_isLE hX j hle
    obtain ⟨eL⟩ := ih (s.erase j) (Finset.erase_ssubset hj) hne (lower X j)
      (lower_supported hX j) (by
        intro i hi
        exact hIso (lowerHomologyIso X j i (hlt ⟨i, hi⟩)).symm
          (hP i (Finset.mem_of_mem_erase hi)))
    let B : s.erase j → ModuleCat R := fun i => (iterate F k).obj (H X i)
    let A : ModuleCat R := (iterate F k).obj (H X j)
    let T := (derived F k).mapTriangle.obj (triangle X j)
    have hT : T ∈ distTriang _ :=
      (derived F k).map_distinguished _ (t.triangleLTGE_distinguished j X)
    let eLower : T.obj₁ ≅ ⨁ (fun i : s.erase j =>
        (DerivedCategory.singleFunctor (ModuleCat R) i).obj (B i)) :=
      eL ≪≫ biproduct.mapIso (fun i =>
        (DerivedCategory.singleFunctor (ModuleCat R) i).mapIso
          ((iterate F k).mapIso (lowerHomologyIso X j i (hlt i))))
    let eUpper : T.obj₃ ≅ (DerivedCategory.singleFunctor (ModuleCat R) j).obj A :=
      (derived F k).mapIso (upperSingleIso X j) ≪≫ singleIso F k j (H X j)
    obtain ⟨e, _, _⟩ := PostnikovExtStep.splits_of_native_ext F T hT
      (fun i : s.erase j => (i : ℤ)) B j A hlt eLower eUpper
      (fun i n hn => hExt A (B i) (iterate_property F P hMap k _ (hP j hj))
        (iterate_property F P hMap k _ (hP i (Finset.mem_of_mem_erase i.property))) n hn)
    rw [hk]
    refine ⟨e.symm ≪≫ biprod.mapIso ?_ ?_ ≪≫ eraseIso
      (fun i => (DerivedCategory.singleFunctor (ModuleCat R) i).obj
        ((iterate F (k + 1)).obj (H X i))) s j hj⟩
    · exact F.mapDerivedCategory.mapIso eLower ≪≫
        F.mapDerivedCategory.mapBiproduct _ ≪≫ biproduct.mapIso
          (fun i => (F.mapDerivedCategorySingleFunctor (i : ℤ)).app (B i))
    · exact F.mapDerivedCategory.mapIso eUpper ≪≫
        (F.mapDerivedCategorySingleFunctor j).app A
end
end Decoupling.HighDim.PostnikovInduction
