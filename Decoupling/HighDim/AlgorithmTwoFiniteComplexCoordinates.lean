import Decoupling.HighDim.StableFreeCochain
import Decoupling.HighDim.AlgorithmTwoLinearComparisonSystem

/-!
# Finite total coordinates of actual bounded cochain complexes

The degree labels are a finite array. The maps below are ordinary supplied
free coordinates: inclusion and projection of each degree into the total
coordinate module, with explicit inverse and grade-projector identities.
No exactness, splitting, chain map or homotopy is a coordinate field.
-/
namespace Decoupling.HighDim.AlgorithmTwoFiniteComplex
open CategoryTheory HomologicalComplex Matrix
noncomputable section
universe u
variable {R : Type u} [CommRing R]

structure Coordinates (C : CochainComplex (ModuleCat R) ℤ) (n : ℕ) where
  degree : Vector ℤ n
  embed : ∀ j, C.X j →ₗ[R] (Fin n → R)
  project : ∀ j, (Fin n → R) →ₗ[R] C.X j
  project_embed : ∀ j x, project j (embed j x) = x
  embed_project : ∀ j x i, embed j (project j x) i = if degree.get i = j then x i else 0

variable {C T : CochainComplex (ModuleCat R) ℤ} {n m : ℕ}

namespace Coordinates

theorem embed_injective (c : Coordinates C n) (j : ℤ) : Function.Injective (c.embed j) := by
  intro x y h
  simpa only [c.project_embed] using congrArg (c.project j) h

theorem embed_supported (c : Coordinates C n) (j : ℤ) (x : C.X j) (i : Fin n)
    (hi : (c.degree.get i) ≠ j) : c.embed j x i = 0 := by
  have he := c.embed_project j (c.embed j x) i
  simpa only [c.project_embed, ite_eq_right hi] using he

theorem project_supported (c : Coordinates C n) (j : ℤ) (x : Fin n → R)
    (hx : ∀ i, (c.degree.get i) ≠ j → x i = 0) : c.embed j (c.project j x) = x := by
  funext i
  rw [c.embed_project]
  split_ifs with hi
  · rfl
  · exact (hx i hi).symm

theorem project_single_zero (c : Coordinates C n) (j : ℤ) (i : Fin n)
    (hi : (c.degree.get i) ≠ j) : c.project j (Pi.single i 1) = 0 := by
  apply c.embed_injective j
  funext a
  rw [c.embed_project]
  by_cases ha : a = i
  · subst a
    rw [ite_eq_right hi]
    simp
  · simp [ha]

/-- The precise relation between the stored total differential and the
actual native differential in the original supplied coordinates. -/
def RepresentsDifferential (c : Coordinates C n) (d : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ j x, d *ᵥ c.embed j x = c.embed (j+1) ((C.d j (j+1)).hom x)

end Coordinates

/-- Actual grade condition, with arbitrary integer displacement. -/
def Homogeneous (source : Vector ℤ m) (target : Vector ℤ n) (s : ℤ)
    (A : Matrix (Fin n) (Fin m) R) : Prop :=
  ∀ i j, (target.get i) ≠ (source.get j) + s → A i j = 0

theorem homogeneous_mulVec_supported (source : Vector ℤ m) (target : Vector ℤ n)
    (s j : ℤ) (A : Matrix (Fin n) (Fin m) R) (hA : Homogeneous source target s A)
    (x : Fin m → R) (hx : ∀ a, (source.get a) ≠ j → x a = 0) :
    ∀ i, (target.get i) ≠ j+s → (A *ᵥ x) i = 0 := by
  intro i hi
  change ∑ a, A i a * x a = 0
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : (source.get a) = j
  · rw [hA i a (by simpa [ha] using hi), zero_mul]
  · rw [hx a ha, mul_zero]

/-- A homogeneous total matrix induces its actual degreewise maps. -/
def component (cT : Coordinates T m) (cC : Coordinates C n)
    (A : Matrix (Fin n) (Fin m) R) (a b : ℤ) : T.X a →ₗ[R] C.X b :=
  (cC.project b).comp (A.mulVecLin.comp (cT.embed a))

theorem component_embed (cT : Coordinates T m) (cC : Coordinates C n)
    (A : Matrix (Fin n) (Fin m) R) (s a : ℤ) (hA : Homogeneous cT.degree cC.degree s A)
    (x : T.X a) : cC.embed (a+s) (component cT cC A a (a+s) x) = A *ᵥ cT.embed a x := by
  apply cC.project_supported
  exact homogeneous_mulVec_supported _ _ _ _ A hA _ (cT.embed_supported a x)

theorem component_embed_zero (cT : Coordinates T m) (cC : Coordinates C n)
    (A : Matrix (Fin n) (Fin m) R) (a : ℤ) (hA : Homogeneous cT.degree cC.degree 0 A)
    (x : T.X a) : cC.embed a (component cT cC A a a x) = A *ᵥ cT.embed a x := by
  apply cC.project_supported
  intro i hi
  exact homogeneous_mulVec_supported _ _ 0 a A hA _ (cT.embed_supported a x) i
    (by simpa using hi)

/-- Reconstruct an actual cochain map from the solved degree-zero matrix. -/
def cochainMap (cT : Coordinates T m) (cC : Coordinates C n)
    (dT : Matrix (Fin m) (Fin m) R) (dC : Matrix (Fin n) (Fin n) R)
    (hdT : cT.RepresentsDifferential dT) (hdC : cC.RepresentsDifferential dC)
    (A : Matrix (Fin n) (Fin m) R) (hA : Homogeneous cT.degree cC.degree 0 A)
    (hcomm : dC * A = A * dT) : T ⟶ C :=
  CochainComplex.ofHom (fun j => ModuleCat.ofHom (component cT cC A j j)) (by
    intro j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply cC.embed_injective (j+1)
    change cC.embed (j+1) ((C.d j (j+1)).hom (component cT cC A j j x)) =
      cC.embed (j+1) (component cT cC A (j+1) (j+1) ((T.d j (j+1)).hom x))
    rw [← hdC]
    rw [component_embed_zero cT cC A j hA x,
      component_embed_zero cT cC A (j+1) hA ((T.d j (j+1)).hom x),
      ← hdT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm])

end
end Decoupling.HighDim.AlgorithmTwoFiniteComplex
