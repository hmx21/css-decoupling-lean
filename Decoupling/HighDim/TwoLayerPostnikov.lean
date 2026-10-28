import Decoupling.HighDim.PostnikovInduction

/-!
# Canonical gluing and formality for a two-layer derived object

Source: Corollary 2, HD008. The connecting map is from the canonical
t-structure triangle of the actual derived object. Its vanishing is
equivalent to a derived splitting, even when no compatibility data are
given with the splitting isomorphism. Two-layer support identifies the
end terms with the actual homology modules.
-/

namespace Decoupling.HighDim.TwoLayer
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open PostnikovTruncation PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]

/-- The actual Postnikov connecting morphism, retaining all extension data. -/
abbrev connecting (X : DerivedCategory (ModuleCat R)) (j : ℤ) := (triangle X j).mor₃

/-- Splitting criterion for any distinguished triangle separated by the t-structure. -/
theorem triangle_zero_iff_split (T : Triangle (DerivedCategory (ModuleCat R)))
    (hT : T ∈ distTriang _) (j : ℤ) [T.obj₁.IsLE (j - 1)] [T.obj₃.IsGE j] :
    T.mor₃ = 0 ↔ Nonempty (T.obj₂ ≅ T.obj₁ ⊞ T.obj₃) := by
  constructor
  · intro h
    obtain ⟨e, _, _⟩ := (Triangles.connecting_eq_zero_iff_compatible_biproduct T hT).mp h
    exact ⟨e.symm⟩
  · rintro ⟨e⟩
    obtain ⟨f, _⟩ := t.triangle_iso_exists hT
      (binaryBiproductTriangle_distinguished T.obj₁ T.obj₃)
      e (j - 1) j (by infer_instance) (by infer_instance)
      (by change t.IsLE T.obj₁ (j - 1); infer_instance)
      (by change t.IsGE T.obj₃ j; infer_instance) (by omega)
    have hf : IsIso f.hom.hom₁ := by
      change IsIso ((Triangle.π₁).map f.hom)
      infer_instance
    have hh := f.hom.comm₃
    change T.mor₃ ≫ f.hom.hom₁⟦(1 : ℤ)⟧' = f.hom.hom₃ ≫ 0 at hh
    apply (cancel_mono (f.hom.hom₁⟦(1 : ℤ)⟧')).mp
    simpa only [comp_zero, zero_comp] using hh

/-- A mere object isomorphism suffices: t-structure uniqueness supplies
compatibility with the canonical inclusion and projection. -/
theorem connecting_zero_iff_split (X : DerivedCategory (ModuleCat R)) (j : ℤ) :
    connecting X j = 0 ↔ Nonempty (X ≅ lower X j ⊞ upper X j) := by
  constructor
  · intro h
    obtain ⟨e, _, _⟩ := (Triangles.connecting_eq_zero_iff_compatible_biproduct
      (triangle X j) (t.triangleLTGE_distinguished j X)).mp h
    exact ⟨e.symm⟩
  · rintro ⟨e⟩
    obtain ⟨f, _⟩ := t.triangle_iso_exists (t.triangleLTGE_distinguished j X)
      (binaryBiproductTriangle_distinguished (lower X j) (upper X j))
      e (j - 1) j (by infer_instance) (by infer_instance)
      (by change t.IsLE (lower X j) (j - 1); infer_instance)
      (by change t.IsGE (upper X j) j; infer_instance) (by omega)
    have hf : IsIso f.hom.hom₁ := by
      change IsIso ((Triangle.π₁).map f.hom)
      infer_instance
    have hh := f.hom.comm₃
    change connecting X j ≫ f.hom.hom₁⟦(1 : ℤ)⟧' = f.hom.hom₃ ≫ 0 at hh
    apply (cancel_mono (f.hom.hom₁⟦(1 : ℤ)⟧')).mp
    simpa using hh

variable (X : DerivedCategory (ModuleCat R)) (i j : ℤ) (hij : i < j)
  (hX : Supported X {i, j})

include hX in
theorem lower_supported_single : Supported (lower X j) {i} := by
  intro k hk
  by_cases hkj : k < j
  · exact (hX k (by simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢; omega)).of_iso
      (lowerHomologyIso X j k hkj)
  · exact DerivedCategory.isZero_of_isLE (lower X j) (j - 1) k (by omega)

def lowerLayerIso : lower X j ≅ (DerivedCategory.singleFunctor (ModuleCat R) i).obj (H X i) := by
  let : (lower X j).IsLE i := supported_isLE (lower_supported_single X i j hX) i
    (by intro k hk; have := Finset.mem_singleton.mp hk; omega)
  let : (lower X j).IsGE i := supported_isGE (lower_supported_single X i j hX) i
    (by intro k hk; have := Finset.mem_singleton.mp hk; omega)
  exact Profile.singleDegreeIso (lower X j) i ≪≫
    (DerivedCategory.singleFunctor (ModuleCat R) i).mapIso (lowerHomologyIso X j i hij)

def upperLayerIso : upper X j ≅ (DerivedCategory.singleFunctor (ModuleCat R) j).obj (H X j) := by
  let : X.IsLE j := supported_isLE hX j (by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    omega)
  exact upperSingleIso X j

/-- The canonical gluing map with the uniquely determined two layers as endpoints. -/
def layerConnecting :
    (DerivedCategory.singleFunctor (ModuleCat R) j).obj (H X j) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat R) i).obj (H X i))⟦(1 : ℤ)⟧ :=
  (upperLayerIso X i j hij hX).inv ≫ connecting X j ≫
    (lowerLayerIso X i j hij hX).hom⟦(1 : ℤ)⟧'

theorem layerConnecting_eq_zero_iff : layerConnecting X i j hij hX = 0 ↔ connecting X j = 0 := by
  simp only [layerConnecting, ← cancel_epi (upperLayerIso X i j hij hX).inv,
    ← cancel_mono ((lowerLayerIso X i j hij hX).hom⟦(1 : ℤ)⟧'), comp_zero, zero_comp,
    Category.assoc]

/-- Full two-layer formality, expressed with actual homology rather than supplied modules. -/
theorem layerConnecting_zero_iff_split :
    layerConnecting X i j hij hX = 0 ↔
      Nonempty (X ≅ (DerivedCategory.singleFunctor (ModuleCat R) i).obj (H X i) ⊞
        (DerivedCategory.singleFunctor (ModuleCat R) j).obj (H X j)) := by
  rw [layerConnecting_eq_zero_iff, connecting_zero_iff_split]
  constructor
  · rintro ⟨e⟩
    exact ⟨e ≪≫ biprod.mapIso (lowerLayerIso X i j hij hX) (upperLayerIso X i j hij hX)⟩
  · rintro ⟨e⟩
    exact ⟨e ≪≫ (biprod.mapIso (lowerLayerIso X i j hij hX) (upperLayerIso X i j hij hX)).symm⟩

end
end Decoupling.HighDim.TwoLayer
