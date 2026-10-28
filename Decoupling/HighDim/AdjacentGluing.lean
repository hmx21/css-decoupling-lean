import Decoupling.HighDim.TwoLayerFormality
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# HD010 Lemma 6: all actual adjacent gluing maps

The j-th map comes from τ≤j−1 X → τ≤j X → Hʲ(X)[−j]. Its
relation to the cutoff triangle of τ≤j X is a proved triangle isomorphism.
Finite support, including empty support, is sufficient; no two-layer bound
or finite-dimensionality of any homology module is assumed.
-/
namespace Decoupling.HighDim.AdjacentGluing
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Preadditive
open PostnikovTruncation PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R]

abbrev cap (X : DerivedCategory (ModuleCat R)) (j : ℤ) := lower X (j + 1)

/-- This is literally the canonical τ≤j functor. -/
theorem cap_eq_truncLE (X : DerivedCategory (ModuleCat R)) (j : ℤ) :
    cap X j = (t.truncLE j).obj X := rfl

def rawTriangle (X : DerivedCategory (ModuleCat R)) (j : ℤ) :
    Triangle (DerivedCategory (ModuleCat R)) :=
  (t.triangleLTLTGELT j (j + 1) (by omega)).obj X

theorem rawTriangle_distinguished (X : DerivedCategory (ModuleCat R)) (j : ℤ) :
    rawTriangle X j ∈ distTriang _ := t.triangleLTLTGELT_distinguished j (j + 1) (by omega) X

@[simp] theorem rawTriangle_mor1 (X : DerivedCategory (ModuleCat R)) (j : ℤ) :
    (rawTriangle X j).mor₁ = (t.natTransTruncLTOfLE j (j + 1) (by omega)).app X := rfl

def lowerCapIso (X : DerivedCategory (ModuleCat R)) (j : ℤ) :
    lower (cap X j) j ≅ lower X j := by
  let := t.isIso_truncLT_map_truncLTι_app j (j + 1) (by omega) X
  exact asIso ((t.truncLT j).map ((t.truncLTι (j + 1)).app X))

/-- The actual canonical adjacent triangle is isomorphic to the cutoff
triangle of τ≤j X, with its lower term identified canonically. -/
def rawTriangleIso (X : DerivedCategory (ModuleCat R)) (j : ℤ) :
    rawTriangle X j ≅ triangle (cap X j) j := by
  refine Triangle.isoMk _ _ (lowerCapIso X j).symm (Iso.refl _) (Iso.refl _) ?_ (by simp [rawTriangle]) ?_
  · dsimp [rawTriangle, lowerCapIso]
    simp only [Category.comp_id, IsIso.eq_inv_comp]
    exact t.to_truncLT_obj_ext (by simp)
  · dsimp [rawTriangle, lowerCapIso]
    simp

def layerIso (X : DerivedCategory (ModuleCat R)) (j : ℤ) :
    (rawTriangle X j).obj₃ ≅ (DerivedCategory.singleFunctor (ModuleCat R) j).obj (H X j) :=
  upperSingleIso (cap X j) j ≪≫
    (DerivedCategory.singleFunctor (ModuleCat R) j).mapIso
      (lowerHomologyIso X (j + 1) j (by omega))

/-- The manuscript's adjacent attachment, with its actual homology source. -/
def delta (X : DerivedCategory (ModuleCat R)) (j : ℤ) :
    (DerivedCategory.singleFunctor (ModuleCat R) j).obj (H X j) ⟶ (lower X j)⟦(1 : ℤ)⟧ :=
  (layerIso X j).inv ≫ (rawTriangle X j).mor₃

theorem delta_zero_iff_raw (X : DerivedCategory (ModuleCat R)) (j : ℤ) :
    delta X j = 0 ↔ (rawTriangle X j).mor₃ = 0 := by
  simp only [delta, IsIso.comp_left_eq_zero]

theorem raw_zero_iff_cutoff (X : DerivedCategory (ModuleCat R)) (j : ℤ) :
    (rawTriangle X j).mor₃ = 0 ↔ TwoLayer.connecting (cap X j) j = 0 := by
  change TwoLayer.connecting (cap X j) j ≫
    ((t.truncLT j).map ((t.truncLTι (j + 1)).app X))⟦(1 : ℤ)⟧' = 0 ↔ _
  let := t.isIso_truncLT_map_truncLTι_app j (j + 1) (by omega) X
  exact IsIso.comp_right_eq_zero _ _

theorem delta_zero_iff_cutoff (X : DerivedCategory (ModuleCat R)) (j : ℤ) :
    delta X j = 0 ↔ TwoLayer.connecting (cap X j) j = 0 :=
  (delta_zero_iff_raw X j).trans (raw_zero_iff_cutoff X j)

theorem cutoff_cap_zero_of_cutoff_zero (X : DerivedCategory (ModuleCat R)) (j : ℤ)
    (h : TwoLayer.connecting X j = 0) : TwoLayer.connecting (cap X j) j = 0 := by
  let := t.isIso_truncLT_map_truncLTι_app j (j + 1) (by omega) X
  apply (cancel_mono (((t.truncLT j).map ((t.truncLTι (j + 1)).app X))⟦(1 : ℤ)⟧')).mp
  have he := (t.truncGEδLT j).naturality ((t.truncLTι (j + 1)).app X)
  change _ ≫ TwoLayer.connecting X j = TwoLayer.connecting (cap X j) j ≫ _ at he
  simpa only [h, comp_zero, zero_comp, Functor.comp_map] using he.symm

theorem delta_zero_of_formal (X : DerivedCategory (ModuleCat R)) (s : Finset ℤ)
    (h : Nonempty (X ≅ TwoLayer.homologySum X s)) (j : ℤ) : delta X j = 0 := by
  rw [delta_zero_iff_cutoff]
  exact cutoff_cap_zero_of_cutoff_zero X j (TwoLayer.connecting_zero_of_formal X s h j)

/-- Lower truncation preserves vanishing of every adjacent attachment. -/
theorem lower_delta_zero (X : DerivedCategory (ModuleCat R))
    (h : ∀ j, delta X j = 0) (b j : ℤ) : delta (lower X b) j = 0 := by
  rw [delta_zero_iff_cutoff]
  by_cases hj : j < b
  · let := t.isIso_truncLT_map_truncLTι_app (j + 1) b (by omega) X
    exact connecting_of_iso (asIso ((t.truncLT (j + 1)).map ((t.truncLTι b).app X))) j
      ((delta_zero_iff_cutoff X j).mp (h j))
  · let : (lower X b).IsLE (j - 1) := t.isLE_of_le (lower X b) (b - 1) (j - 1) (by omega)
    exact (t.isZero_truncGE_obj_of_isLE (j - 1) j (by omega) (cap (lower X b) j)).eq_of_src _ _

/-- Lemma 6, without a bound on the number or dimensions of the layers. -/
theorem formal_iff_all_delta : ∀ (s : Finset ℤ) (X : DerivedCategory (ModuleCat R)),
    Supported X s →
      (Nonempty (X ≅ TwoLayer.homologySum X s) ↔ ∀ j : ℤ, delta X j = 0) := by
  intro s
  refine Finset.strongInductionOn s (fun s ih => ?_)
  intro X hX
  constructor
  · exact fun h j => delta_zero_of_formal X s h j
  · intro h
    by_cases hs : s.Nonempty
    · let j := s.max' hs
      have hj : j ∈ s := Finset.max'_mem s hs
      have hle : ∀ i ∈ s, i ≤ j := fun i hi => Finset.le_max' s i hi
      have hlt : ∀ i ∈ s.erase j, i < j := by
        intro i hi
        have hi' := Finset.mem_erase.mp hi
        have := hle i hi'.2
        omega
      let : X.IsLE j := supported_isLE hX j hle
      let : IsIso ((t.truncLTι (j + 1)).app X) :=
        (t.isLE_iff_isIso_truncLTι_app j (j + 1) rfl X).mp inferInstance
      have hδ : TwoLayer.connecting X j = 0 :=
        connecting_of_iso (asIso ((t.truncLTι (j + 1)).app X)).symm j
          ((delta_zero_iff_cutoff X j).mp (h j))
      obtain ⟨eL⟩ := (ih (s.erase j) (Finset.erase_ssubset hj) (lower X j)
        (lower_supported hX j)).mpr (lower_delta_zero X h j)
      let eLower := eL ≪≫ biproduct.mapIso (fun i : s.erase j =>
        (DerivedCategory.singleFunctor (ModuleCat R) i).mapIso
          (lowerHomologyIso X j i (hlt i i.property)))
      obtain ⟨es, _, _⟩ := (Triangles.connecting_eq_zero_iff_compatible_biproduct
        (triangle X j) (t.triangleLTGE_distinguished j X)).mp hδ
      exact ⟨es.symm ≪≫ biprod.mapIso eLower (upperSingleIso X j) ≪≫
        FiniteBiproduct.eraseIso
          (fun i => (DerivedCategory.singleFunctor (ModuleCat R) i).obj (H X i)) s j hj⟩
    · exact TwoLayer.formal_of_card_le_one X s hX (by
        rw [Finset.not_nonempty_iff_eq_empty.mp hs]
        simp)

end
end Decoupling.HighDim.AdjacentGluing
