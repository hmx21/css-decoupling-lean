import Decoupling.HighDim.AlgorithmTwoFiniteComplexMatrix
import Decoupling.HighDim.AlgorithmTwoComparisonCone

/-!
# Actual contraction from the solved finite matrix equation

The matrix equation is `d H + H d = I`, with H of degree minus one.
This module reconstructs a native Homotopy id 0, and conversely encodes
any such homotopy. It does not assume a contraction as a final input.
-/
namespace Decoupling.HighDim.AlgorithmTwoFiniteComplex
open CategoryTheory HomologicalComplex Matrix
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {C : CochainComplex (ModuleCat R) ℤ} {n : ℕ}

theorem component_embed_at (c : Coordinates C n) (H : Matrix (Fin n) (Fin n) R)
    (s a b : ℤ) (hab : b = a+s) (hH : Homogeneous c.degree c.degree s H) (x : C.X a) :
    c.embed b (component c c H a b x) = H *ᵥ c.embed a x := by
  subst b
  exact component_embed c c H s a hH x

theorem represents_at (c : Coordinates C n) (d : Matrix (Fin n) (Fin n) R)
    (hd : c.RepresentsDifferential d) (a b : ℤ) (hab : b = a+1) (x : C.X a) :
    d *ᵥ c.embed a x = c.embed b ((C.d a b).hom x) := by
  subst b
  exact hd a x

def contractingMap (c : Coordinates C n) (H : Matrix (Fin n) (Fin n) R) : C ⟶ C :=
  Homotopy.nullHomotopicMap' (fun a b _ => ModuleCat.ofHom (component c c H a b))

theorem contractingMap_eq_id (c : Coordinates C n) (d H : Matrix (Fin n) (Fin n) R)
    (hd : c.RepresentsDifferential d) (hH : Homogeneous c.degree c.degree (-1) H)
    (he : d*H + H*d = 1) : contractingMap c H = 𝟙 C := by
  apply HomologicalComplex.Hom.ext
  funext j
  rw [contractingMap, Homotopy.nullHomotopicMap'_f (k₂ := j-1) (k₀ := j+1)
    (by change j-1+1=j; omega) (by rfl)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply c.embed_injective j
  change c.embed j (component c c H (j+1) j ((C.d j (j+1)).hom x) +
    (C.d (j-1) j).hom (component c c H j (j-1) x)) = c.embed j x
  rw [map_add, component_embed_at c H (-1) (j+1) j (by omega) hH,
    ← hd, ← represents_at c d hd (j-1) j (by omega),
    component_embed_at c H (-1) j (j-1) (by omega) hH,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, add_comm, he,
    Matrix.one_mulVec]

/-- The actual solved H yields a native contraction. -/
def contraction (c : Coordinates C n) (d H : Matrix (Fin n) (Fin n) R)
    (hd : c.RepresentsDifferential d) (hH : Homogeneous c.degree c.degree (-1) H)
    (he : d*H + H*d = 1) : Homotopy (𝟙 C) 0 :=
  (Homotopy.ofEq (contractingMap_eq_id c d H hd hH he).symm).trans
    (Homotopy.nullHomotopy' (fun a b _ => ModuleCat.ofHom (component c c H a b)))

theorem contraction_hom_at (c : Coordinates C n) (d H : Matrix (Fin n) (Fin n) R)
    (hd : c.RepresentsDifferential d) (hH : Homogeneous c.degree c.degree (-1) H)
    (he : d*H + H*d = 1) (a b : ℤ) (hab : b+1=a) :
    (contraction c d H hd hH he).hom a b = ModuleCat.ofHom (component c c H a b) := by
  simp [contraction, Homotopy.trans, Homotopy.ofEq, Homotopy.nullHomotopy',
    Homotopy.nullHomotopy, ComplexShape.up_Rel, hab]

/-- The actual native homotopy expressed in total coordinates. -/
def homotopyMatrix (c : Coordinates C n) (h : Homotopy (𝟙 C) 0) :
    Matrix (Fin n) (Fin n) R :=
  familyMatrix c c (fun j => j-1) (fun j => (h.hom j (j-1)).hom)

theorem homotopyMatrix_homogeneous (c : Coordinates C n) (h : Homotopy (𝟙 C) 0) :
    Homogeneous c.degree c.degree (-1) (homotopyMatrix c h) :=
  familyMatrix_homogeneous c c (fun j => j-1) _ (-1) (fun _ => by omega)

theorem homotopyMatrix_mulVec (c : Coordinates C n) (h : Homotopy (𝟙 C) 0)
    (a b : ℤ) (hab : b = a-1) (x : C.X a) :
    homotopyMatrix c h *ᵥ c.embed a x = c.embed b ((h.hom a b).hom x) := by
  subst b
  exact familyMatrix_mulVec c c (fun j => j-1) _ a x

theorem homotopyMatrix_equation (c : Coordinates C n) (d : Matrix (Fin n) (Fin n) R)
    (hd : c.RepresentsDifferential d) (h : Homotopy (𝟙 C) 0) :
    d * homotopyMatrix c h + homotopyMatrix c h * d = 1 := by
  apply matrix_ext c
  intro j x
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    homotopyMatrix_mulVec c h j (j-1) rfl, represents_at c d hd (j-1) j (by omega),
    hd, homotopyMatrix_mulVec c h (j+1) j (by omega), Matrix.one_mulVec, ← map_add]
  apply congrArg (c.embed j)
  have heq : C.d j (j+1) ≫ h.hom (j+1) j + h.hom j (j-1) ≫ C.d (j-1) j = 𝟙 (C.X j) := by
    have hh := congrArg (fun f : C ⟶ C => f.f j) h.sub_eq_nullHomotopicMap
    simpa only [sub_zero, HomologicalComplex.id_f,
      Homotopy.nullHomotopicMap_f (C := C) (D := C) (k₁ := j) (k₂ := j-1) (k₀ := j+1)
        (by change j-1+1=j; omega) (by rfl)] using hh.symm
  have he := congrArg (fun f : C.X j ⟶ C.X j => f.hom x) heq
  simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply, add_comm] using he

end
end Decoupling.HighDim.AlgorithmTwoFiniteComplex
