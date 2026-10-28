import Decoupling.HighDim.StableFreeDerived
import Decoupling.HighDim.GluedNativeHomology

/-!
# Prescribing cocycle values by an actual cochain homotopy

HD012 Appendix C1. These are the elementary correction identities
used after normalising the map on native homology. The correction is
the actual `d h + h d` cochain map. Its value on a cycle and its
homotopy to the original map are proved, with no characteristic-two
assumption.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparison
open CategoryTheory HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
noncomputable section
variable {R : Type u} [CommRing R]
variable {T C : CochainComplex (ModuleCat.{u} R) ℤ}

def loweringFamily (h : ∀ j, T.X j ⟶ C.X (j - 1)) (a b : ℤ)
    (hab : (ComplexShape.up ℤ).Rel b a) : T.X a ⟶ C.X b :=
  h a ≫ eqToHom (congrArg C.X (by change b + 1 = a at hab; omega))

def correctedMap (f : T ⟶ C) (h : ∀ j, T.X j ⟶ C.X (j - 1)) : T ⟶ C :=
  f + Homotopy.nullHomotopicMap' (loweringFamily h)

def correctedMapHomotopy (f : T ⟶ C) (h : ∀ j, T.X j ⟶ C.X (j - 1)) :
    Homotopy (correctedMap f h) f :=
  ((Homotopy.refl f).add (Homotopy.nullHomotopy' (loweringFamily h))).trans
    (Homotopy.ofEq (add_zero f))

theorem correctedMap_cycle (f : T ⟶ C) (h : ∀ j, T.X j ⟶ C.X (j - 1))
    (j : ℤ) (x : T.X j) (hx : T.d j (j + 1) x = 0) :
    (correctedMap f h).f j x = f.f j x + C.d (j - 1) j (h j x) := by
  rw [correctedMap, HomologicalComplex.add_f_apply,
    Homotopy.nullHomotopicMap'_f (k₂ := j - 1) (k₀ := j + 1)
      (by change j - 1 + 1 = j; omega) (by rfl)]
  change f.f j x +
    (loweringFamily h (j + 1) j (by rfl) (T.d j (j + 1) x) +
      C.d (j - 1) j (h j x)) = _
  rw [hx, map_zero, zero_add]

theorem correctedMap_prescribed (f : T ⟶ C) (h : ∀ j, T.X j ⟶ C.X (j - 1))
    (j : ℤ) (x : T.X j) (hx : T.d j (j + 1) x = 0) (c : C.X j)
    (hc : C.d (j - 1) j (h j x) = c - f.f j x) :
    (correctedMap f h).f j x = c := by
  rw [correctedMap_cycle f h j x hx, hc]
  abel

/-- Native homology classes are unchanged in every degree. -/
theorem correctedMap_homology (f : T ⟶ C) (h : ∀ j, T.X j ⟶ C.X (j - 1)) (j : ℤ) :
    homologyMap (correctedMap f h) j = homologyMap f j :=
  (correctedMapHomotopy f h).homologyMap_eq j

theorem quasiIso_of_homotopy {f g : T ⟶ C} (h : Homotopy g f) [QuasiIso f] :
    QuasiIso g := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap, h.homologyMap_eq]
  infer_instance

/-- When the original map is a homotopy equivalence, the corrected
map is the forward map of an actual homotopy equivalence as well. -/
def correctedEquivalence (e : HomotopyEquiv T C) (h : ∀ j, T.X j ⟶ C.X (j - 1)) :
    HomotopyEquiv T C :=
  e.copy (correctedMapHomotopy e.hom h).symm

theorem correctedEquivalence_hom (e : HomotopyEquiv T C) (h : ∀ j, T.X j ⟶ C.X (j - 1)) :
    (correctedEquivalence e h).hom = correctedMap e.hom h := rfl

end
end Decoupling.HighDim.AlgorithmTwoComparison
