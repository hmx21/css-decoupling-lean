import Decoupling.HighDim.ProfileBounds

/-!
# The one-layer base case is a derived statement

An object supported in one cohomological degree is isomorphic to that
homology module placed in that degree. We apply this to the genuine CSS
profile and discharge the support condition when the layer count is one.
Translation trivialization and multiplicity coordinates are separate steps.
-/

namespace Decoupling.HighDim.Profile

open CategoryTheory CategoryTheory.Limits
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable

variable {R : Type} [CommRing R]

/-- An actual derived object supported in degree `n` is its homology in that degree. -/
def singleDegreeIso (X : DerivedCategory (ModuleCat R)) (n : ℤ)
    [X.IsGE n] [X.IsLE n] :
    X ≅ (DerivedCategory.singleFunctor (ModuleCat R) n).obj
      ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj X) := by
  let h := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := h.choose
  let e : X ≅ (DerivedCategory.singleFunctor (ModuleCat R) n).obj Y := h.choose_spec.some
  let hY : Y ≅ (DerivedCategory.homologyFunctor (ModuleCat R) n).obj X :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) n).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat R) n).mapIso e.symm
  exact e ≪≫ (DerivedCategory.singleFunctor (ModuleCat R) n).mapIso hY

variable {p D q s r : ℕ} [Fact p.Prime]

theorem homology_isZero_away (c : CSS.Checks (ZMod p) D q s r)
    (hc : c.Topological) (hD : 1 ≤ D) (n : ℕ)
    (hOther : ∀ k : ℕ, 1 ≤ k → k < D → k ≠ n + 1 → Subsingleton (Layers.E_X c k))
    (i : ℤ) (hi : i ≠ (n + 1 : ℕ)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat (Laurent (ZMod p) D)) i).obj (S_X c)) := by
  by_cases hi0 : i < 1
  · exact DerivedCategory.isZero_of_isGE (S_X c) 1 i hi0
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hs : Subsingleton (Layers.E_X c (k + 1)) := by
      by_cases hk : k + 1 < D
      · exact hOther _ (by omega) hk (by omega)
      · exact DegreeBound.ext_subsingleton c hc hD (by omega)
    exact ModuleCat.isZero_iff_subsingleton.mpr (homologyEquivLayer c k).injective.subsingleton

def singleLayerIso (c : CSS.Checks (ZMod p) D q s r)
    (hc : c.Topological) (hD : 1 ≤ D) (n : ℕ)
    (hOther : ∀ k : ℕ, 1 ≤ k → k < D → k ≠ n + 1 → Subsingleton (Layers.E_X c k)) :
    S_X c ≅ (DerivedCategory.singleFunctor (ModuleCat (Laurent (ZMod p) D)) (n + 1 : ℕ)).obj
      (Layers.layer c (n + 1)) := by
  letI : (S_X c).IsGE (n + 1 : ℕ) := (DerivedCategory.isGE_iff _ _).mpr
    (fun i hi => homology_isZero_away c hc hD n hOther i (by omega))
  letI : (S_X c).IsLE (n + 1 : ℕ) := (DerivedCategory.isLE_iff _ _).mpr
    (fun i hi => homology_isZero_away c hc hD n hOther i (by omega))
  exact singleDegreeIso (S_X c) (n + 1 : ℕ) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat (Laurent (ZMod p) D)) (n + 1 : ℕ)).mapIso
      (homologyEquivLayer c n).toModuleIso

/-- No splitting assumption is needed when exactly one genuine layer is nonzero. -/
theorem exists_singleLayerIso_of_count_one (c : CSS.Checks (ZMod p) D q s r)
    (hc : c.Topological) (hD : 1 ≤ D) (hm : Layers.nonzeroLayerCount c = 1) :
    ∃ n : ℕ, n + 1 < D ∧ Nontrivial (Layers.E_X c (n + 1)) ∧
      Nonempty (S_X c ≅
        (DerivedCategory.singleFunctor (ModuleCat (Laurent (ZMod p) D)) (n + 1 : ℕ)).obj
          (Layers.layer c (n + 1))) := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hm
  have hjmem : j ∈ (Finset.range D).filter (fun j => 1 ≤ j ∧ Nontrivial (Layers.E_X c j)) := by
    rw [hj]
    exact Finset.mem_singleton_self j
  obtain ⟨hjD, hjpos, hjnz⟩ := Finset.mem_filter.mp hjmem
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  refine ⟨n, Finset.mem_range.mp hjD, hjnz, ⟨singleLayerIso c hc hD n ?_⟩⟩
  intro k hk hkD hkne
  apply not_nontrivial_iff_subsingleton.mp
  intro hn
  have hkmem : k ∈ (Finset.range D).filter (fun j => 1 ≤ j ∧ Nontrivial (Layers.E_X c j)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkD, hk, hn⟩
  rw [hj, Finset.mem_singleton] at hkmem
  exact hkne hkmem

end
end Decoupling.HighDim.Profile
