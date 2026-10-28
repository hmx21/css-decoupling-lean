import Decoupling.HighDim.AlgorithmTwoToricDataConeCoordinates

/-!
# Extracting the inverse from the supplied cone contraction

All maps here are literal blocks of the given contraction. In
particular the inverse is not selected from a separate existence
theorem. This is the native bridge used after the contraction's
finite coefficient system has actually been solved.
-/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgorithmTwoComparison CochainComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
noncomputable section
variable {R : Type} [CommRing R] {T C : CochainComplex (ModuleCat.{0} R) ℤ}

theorem contraction_equation_at (G : CochainComplex (ModuleCat R) ℤ)
    (h : Homotopy (𝟙 G) 0) (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c) :
    G.d b c ≫ h.hom c b + h.hom b a ≫ G.d a b = 𝟙 (G.X b) := by
  have he := congrArg (fun f : G ⟶ G => f.f b) h.sub_eq_nullHomotopicMap
  rw [sub_zero, HomologicalComplex.id_f,
    Homotopy.nullHomotopicMap_f (c := ComplexShape.up ℤ) (k₂ := a) (k₁ := b) (k₀ := c)
      hab hbc h.hom] at he
  exact he.symm

def inverseComponent (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0) (n : ℤ) :
    C.X n ⟶ T.X n :=
  (mappingCone.inr f).f n ≫ h.hom n (n - 1) ≫
    (mappingCone.fst f).1.v (n - 1) n (by omega)

theorem inverseComponent_at (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0)
    (n m : ℤ) (hm : n - 1 = m) :
    inverseComponent f h n = (mappingCone.inr f).f n ≫ h.hom n m ≫
      (mappingCone.fst f).1.v m n (by omega) := by
  subst m
  rfl

theorem inverseComponent_comm (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0) (n : ℤ) :
    inverseComponent f h n ≫ T.d n (n + 1) =
      C.d n (n + 1) ≫ inverseComponent f h (n + 1) := by
  have he := congrArg (fun z : (mappingCone f).X n ⟶ (mappingCone f).X n =>
    (mappingCone.inr f).f n ≫ z ≫ (mappingCone.fst f).1.v n (n + 1) rfl)
      (contraction_equation_at (mappingCone f) h (n - 1) n (n + 1) (by omega) rfl)
  simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
    Category.id_comp, mappingCone.inr_f_fst_v] at he
  rw [mappingCone.inr_f_d_assoc, mappingCone.d_fst_v f (n - 1) n (n + 1) (by omega) rfl] at he
  simp only [Preadditive.comp_neg] at he
  have he' : C.d n (n + 1) ≫ inverseComponent f h (n + 1) -
      inverseComponent f h n ≫ T.d n (n + 1) = 0 := by
    rw [inverseComponent_at f h (n + 1) n (by omega)]
    simpa only [inverseComponent, sub_eq_add_neg, Category.assoc] using he
  exact (sub_eq_zero.mp he').symm

/-- The lower-left inverse in the paper's `(C,T[1])` convention,
equivalently the upper-right block in native `(T[1],C)` coordinates. -/
def inverseFromContraction (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0) : C ⟶ T where
  f n := inverseComponent f h n
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    exact inverseComponent_comm f h i

def sourceHomotopyBlock (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel j i) : T.X i ⟶ T.X j :=
  (mappingCone.inl f).v i j (by change j + 1 = i at hij; omega) ≫
    h.hom j (j - 1) ≫ (mappingCone.fst f).1.v (j - 1) j (by omega)

def targetHomotopyBlock (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0)
    (i j : ℤ) (_hij : (ComplexShape.up ℤ).Rel j i) : C.X i ⟶ C.X j :=
  -((mappingCone.inr f).f i ≫ h.hom i j ≫ (mappingCone.snd f).v j j (add_zero j))

theorem sourceHomotopyBlock_at (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel j i) (k : ℤ) (hk : j - 1 = k) :
    sourceHomotopyBlock f h i j hij =
      (mappingCone.inl f).v i j (by change j + 1 = i at hij; omega) ≫
        h.hom j k ≫ (mappingCone.fst f).1.v k j (by omega) := by
  subst k
  rfl

theorem sourceBlock_equation (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0) :
    f ≫ inverseFromContraction f h =
      𝟙 T + Homotopy.nullHomotopicMap' (sourceHomotopyBlock f h) := by
  apply HomologicalComplex.Hom.ext
  funext n
  have he := congrArg (fun z : (mappingCone f).X (n - 1) ⟶ (mappingCone f).X (n - 1) =>
    (mappingCone.inl f).v n (n - 1) (by omega) ≫ z ≫
      (mappingCone.fst f).1.v (n - 1) n (by omega))
    (contraction_equation_at (mappingCone f) h (n - 2) (n - 1) n (by omega) (by omega))
  simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
    Category.id_comp, mappingCone.inl_v_fst_v] at he
  rw [mappingCone.inl_v_d_assoc f n (n - 1) (n + 1) (by omega) (by omega),
    mappingCone.d_fst_v f (n - 2) (n - 1) n (by omega) (by omega)] at he
  simp only [Preadditive.sub_comp, Preadditive.comp_neg, Category.assoc] at he
  let A := T.d n (n + 1) ≫ sourceHomotopyBlock f h (n + 1) n (by rfl)
  let B := sourceHomotopyBlock f h n (n - 1) (by change n - 1 + 1 = n; omega) ≫ T.d (n - 1) n
  have he' : f.f n ≫ inverseComponent f h n - A - B = 𝟙 (T.X n) := by
    dsimp only [A, B]
    rw [sourceHomotopyBlock_at f h n (n - 1) _ (n - 2) (by omega)]
    simpa only [sourceHomotopyBlock, inverseComponent, sub_eq_add_neg, Category.assoc] using he
  rw [HomologicalComplex.comp_f, HomologicalComplex.add_f_apply, HomologicalComplex.id_f,
    Homotopy.nullHomotopicMap'_f (k₂ := n - 1) (k₀ := n + 1)
      (by change n - 1 + 1 = n; omega) (by rfl)]
  change f.f n ≫ inverseComponent f h n = 𝟙 (T.X n) + (A + B)
  convert congrArg (fun z => z + A + B) he' using 1 <;> abel

theorem targetBlock_equation (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0) :
    inverseFromContraction f h ≫ f =
      𝟙 C + Homotopy.nullHomotopicMap' (targetHomotopyBlock f h) := by
  apply HomologicalComplex.Hom.ext
  funext n
  have he := congrArg (fun z : (mappingCone f).X n ⟶ (mappingCone f).X n =>
    (mappingCone.inr f).f n ≫ z ≫ (mappingCone.snd f).v n n (add_zero n))
    (contraction_equation_at (mappingCone f) h (n - 1) n (n + 1) (by omega) rfl)
  simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
    Category.id_comp, mappingCone.inr_f_snd_v] at he
  rw [mappingCone.inr_f_d_assoc, mappingCone.d_snd_v f (n - 1) n (by omega)] at he
  simp only [Preadditive.comp_add] at he
  let A := C.d n (n + 1) ≫ (mappingCone.inr f).f (n + 1) ≫ h.hom (n + 1) n ≫
    (mappingCone.snd f).v n n (add_zero n)
  let B := (mappingCone.inr f).f n ≫ h.hom n (n - 1) ≫
    (mappingCone.snd f).v (n - 1) (n - 1) (add_zero _) ≫ C.d (n - 1) n
  have he' : A + (inverseComponent f h n ≫ f.f n + B) = 𝟙 (C.X n) := by
    simpa only [A, B, inverseComponent, Category.assoc] using he
  rw [HomologicalComplex.comp_f, HomologicalComplex.add_f_apply, HomologicalComplex.id_f,
    Homotopy.nullHomotopicMap'_f (k₂ := n - 1) (k₀ := n + 1)
      (by change n - 1 + 1 = n; omega) (by rfl)]
  simp only [targetHomotopyBlock, Preadditive.comp_neg, Preadditive.neg_comp]
  change inverseComponent f h n ≫ f.f n = 𝟙 (C.X n) + (-A + -B)
  convert congrArg (fun z => z - A - B) he' using 1 <;> abel

def sourceBlockHomotopy (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0) :
    Homotopy (f ≫ inverseFromContraction f h) (𝟙 T) :=
  (Homotopy.ofEq (sourceBlock_equation f h)).trans
    (((Homotopy.refl (𝟙 T)).add (Homotopy.nullHomotopy' (sourceHomotopyBlock f h))).trans
      (Homotopy.ofEq (add_zero (𝟙 T))))

def targetBlockHomotopy (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0) :
    Homotopy (inverseFromContraction f h ≫ f) (𝟙 C) :=
  (Homotopy.ofEq (targetBlock_equation f h)).trans
    (((Homotopy.refl (𝟙 C)).add (Homotopy.nullHomotopy' (targetHomotopyBlock f h))).trans
      (Homotopy.ofEq (add_zero (𝟙 C))))

/-- The supplied Γ and the literal blocks of its supplied contraction
form a native homotopy equivalence. No new solution is chosen. -/
def homotopyEquivFromContraction (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0) :
    HomotopyEquiv T C where
  hom := f
  inv := inverseFromContraction f h
  homotopyHomInvId := sourceBlockHomotopy f h
  homotopyInvHomId := targetBlockHomotopy f h

@[simp] theorem homotopyEquivFromContraction_hom (f : T ⟶ C)
    (h : Homotopy (𝟙 (mappingCone f)) 0) :
    (homotopyEquivFromContraction f h).hom = f := rfl

@[simp] theorem homotopyEquivFromContraction_inv_f (f : T ⟶ C)
    (h : Homotopy (𝟙 (mappingCone f)) 0) (n : ℤ) :
    (homotopyEquivFromContraction f h).inv.f n = inverseComponent f h n := rfl

theorem sourceBlockHomotopy_hom (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel j i) :
    (sourceBlockHomotopy f h).hom i j = sourceHomotopyBlock f h i j hij := by
  change j + 1 = i at hij
  simp [sourceBlockHomotopy, hij]

theorem targetBlockHomotopy_hom (f : T ⟶ C) (h : Homotopy (𝟙 (mappingCone f)) 0)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel j i) :
    (targetBlockHomotopy f h).hom i j = targetHomotopyBlock f h i j hij := by
  change j + 1 = i at hij
  simp [targetBlockHomotopy, hij]

end
end Decoupling.HighDim.AlgorithmTwoToricData
