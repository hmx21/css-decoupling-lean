import Decoupling.HighDim.AlgorithmTwoFiniteComplexContraction

/-! # Native homotopies from exact solved matrix identities -/
namespace Decoupling.HighDim.AlgorithmTwoFiniteComplex
open CategoryTheory HomologicalComplex Matrix
noncomputable section
universe u
variable {R : Type u} [CommRing R] {m n : ℕ}
variable {T C : CochainComplex (ModuleCat R) ℤ}

theorem component_embed_between (cT : Coordinates T m) (cC : Coordinates C n)
    (H : Matrix (Fin n) (Fin m) R) (s a b : ℤ) (hab : b=a+s)
    (hH : Homogeneous cT.degree cC.degree s H) (x : T.X a) :
    cC.embed b (component cT cC H a b x) = H *ᵥ cT.embed a x := by
  subst b
  exact component_embed cT cC H s a hH x

def homotopyMap (cT : Coordinates T m) (cC : Coordinates C n)
    (H : Matrix (Fin n) (Fin m) R) : T ⟶ C :=
  Homotopy.nullHomotopicMap' (fun a b _ => ModuleCat.ofHom (component cT cC H a b))

theorem homotopyMap_eq_sub (cT : Coordinates T m) (cC : Coordinates C n)
    (dT : Matrix (Fin m) (Fin m) R) (dC : Matrix (Fin n) (Fin n) R)
    (hdT : cT.RepresentsDifferential dT) (hdC : cC.RepresentsDifferential dC)
    (f g : T ⟶ C) (F G H : Matrix (Fin n) (Fin m) R)
    (hF : ∀ j x, F *ᵥ cT.embed j x = cC.embed j ((f.f j).hom x))
    (hG : ∀ j x, G *ᵥ cT.embed j x = cC.embed j ((g.f j).hom x))
    (hH : Homogeneous cT.degree cC.degree (-1) H)
    (he : dC*H + H*dT = F-G) : homotopyMap cT cC H = f-g := by
  apply HomologicalComplex.Hom.ext
  funext j
  rw [homotopyMap, Homotopy.nullHomotopicMap'_f (k₂ := j-1) (k₀ := j+1)
    (by change j-1+1=j; omega) (by rfl)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply cC.embed_injective j
  change cC.embed j (component cT cC H (j+1) j ((T.d j (j+1)).hom x) +
    (C.d (j-1) j).hom (component cT cC H j (j-1) x)) =
    cC.embed j ((f.f j).hom x - (g.f j).hom x)
  rw [map_add, map_sub, component_embed_between cT cC H (-1) (j+1) j (by omega) hH,
    ← hdT, ← represents_at cC dC hdC (j-1) j (by omega),
    component_embed_between cT cC H (-1) j (j-1) (by omega) hH,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, add_comm, he,
    Matrix.sub_mulVec, hF, hG]

def matrixHomotopy (cT : Coordinates T m) (cC : Coordinates C n)
    (dT : Matrix (Fin m) (Fin m) R) (dC : Matrix (Fin n) (Fin n) R)
    (hdT : cT.RepresentsDifferential dT) (hdC : cC.RepresentsDifferential dC)
    (f g : T ⟶ C) (F G H : Matrix (Fin n) (Fin m) R)
    (hF : ∀ j x, F *ᵥ cT.embed j x = cC.embed j ((f.f j).hom x))
    (hG : ∀ j x, G *ᵥ cT.embed j x = cC.embed j ((g.f j).hom x))
    (hH : Homogeneous cT.degree cC.degree (-1) H)
    (he : dC*H + H*dT = F-G) : Homotopy f g :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (homotopyMap_eq_sub cT cC dT dC hdT hdC f g F G H hF hG hH he).symm).trans
      (Homotopy.nullHomotopy' (fun a b _ => ModuleCat.ofHom (component cT cC H a b))))

theorem matrixHomotopy_hom_at (cT : Coordinates T m) (cC : Coordinates C n)
    (dT : Matrix (Fin m) (Fin m) R) (dC : Matrix (Fin n) (Fin n) R)
    (hdT : cT.RepresentsDifferential dT) (hdC : cC.RepresentsDifferential dC)
    (f g : T ⟶ C) (F G H : Matrix (Fin n) (Fin m) R)
    (hF : ∀ j x, F *ᵥ cT.embed j x = cC.embed j ((f.f j).hom x))
    (hG : ∀ j x, G *ᵥ cT.embed j x = cC.embed j ((g.f j).hom x))
    (hH : Homogeneous cT.degree cC.degree (-1) H)
    (he : dC*H + H*dT = F-G) (a b : ℤ) (hab : b+1=a) :
    (matrixHomotopy cT cC dT dC hdT hdC f g F G H hF hG hH he).hom a b =
      ModuleCat.ofHom (component cT cC H a b) := by
  simp [matrixHomotopy, Homotopy.equivSubZero, Homotopy.trans, Homotopy.ofEq,
    Homotopy.nullHomotopy', Homotopy.nullHomotopy, ComplexShape.up_Rel, hab]

end
end Decoupling.HighDim.AlgorithmTwoFiniteComplex
