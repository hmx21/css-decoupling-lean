import Decoupling.HighDim.GluedNativeCone

/-!
# The actual cell inclusions in the native cone

These formulae keep the minus sign on the source differential of the
native mapping cone and the actual displayed off-diagonal coupling.
-/

namespace Decoupling.HighDim.Glued
open CategoryTheory CategoryTheory.Limits HomologicalComplex Koszul
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

/-- The degree `2-k` source-cell summand of the actual cone. -/
def coneCellInclusion (k : ℕ) : ModuleCat.of (Laurent K 3) (Term (Laurent K 3) 3 k) ⟶
    (couplingCone K).X (2 - k) :=
  (Toric.termIso K 3 3 k).inv ≫
    homotopyCofiber.inlX (couplingToSingle K) (3 - k) (2 - k) (by change (2 - (k : ℤ)) + 1 = 3 - k; omega)

def coneCellProjection (k : ℕ) : (couplingCone K).X (2 - k) ⟶
    ModuleCat.of (Laurent K 3) (Term (Laurent K 3) 3 k) :=
  homotopyCofiber.fstX (couplingToSingle K) (2 - k) (3 - k) (by change (2 - (k : ℤ)) + 1 = 3 - k; omega) ≫
    (Toric.termIso K 3 3 k).hom

def coneCoefficientInclusion : coefficientModule K 3 ⟶ (couplingCone K).X 1 :=
  (singleObjXSelf (.up ℤ) 1 (coefficientModule K 3)).inv ≫
    (CochainComplex.mappingCone.inr (couplingToSingle K)).f 1

def coneCoefficientProjection : (couplingCone K).X 1 ⟶ coefficientModule K 3 :=
  homotopyCofiber.sndX (couplingToSingle K) 1 ≫
    (singleObjXSelf (.up ℤ) 1 (coefficientModule K 3)).hom

@[reassoc (attr := simp)] theorem coneCell_inclusion_projection (k : ℕ) :
    coneCellInclusion K k ≫ coneCellProjection K k = 𝟙 _ := by
  simp [coneCellInclusion, coneCellProjection]

@[reassoc (attr := simp)] theorem coneCoefficient_inclusion_projection :
    coneCoefficientInclusion K ≫ coneCoefficientProjection K = 𝟙 _ := by
  simp [coneCoefficientInclusion, coneCoefficientProjection, CochainComplex.mappingCone.inr]

@[reassoc (attr := simp)] theorem coneCell_coefficient :
    coneCellInclusion K 1 ≫ coneCoefficientProjection K = 0 := by
  simp [coneCellInclusion, coneCoefficientProjection]

@[reassoc (attr := simp)] theorem coneCoefficient_cell :
    coneCoefficientInclusion K ≫ coneCellProjection K 1 = 0 := by
  simp [coneCellProjection, coneCoefficientInclusion, CochainComplex.mappingCone.inr]

theorem couplingToSingle_f_one : (couplingToSingle K).f 1 =
    (Toric.termIso K 3 3 2).hom ≫ couplingCochain K ≫
      (singleObjXSelf (.up ℤ) 1 (coefficientModule K 3)).inv := by
  rw [couplingToSingle, mkHomToSingle_f]
  rfl

theorem couplingToSingle_f_ne (i : ℤ) (hi : i ≠ 1) : (couplingToSingle K).f i = 0 := by
  exact (isZero_single_obj_X (.up ℤ) 1 (coefficientModule K 3) i hi).eq_of_tgt _ _

@[reassoc] theorem coneCell_two_d :
    coneCellInclusion K 2 ≫ (couplingCone K).d 0 1 =
      (show ModuleCat.of (Laurent K 3) (Term (Laurent K 3) 3 2) ⟶
        (couplingCone K).X 1 from
          -(boundary (Laurent K 3) (difference K) 1 ≫ coneCellInclusion K 1)) +
        couplingCochain K ≫ coneCoefficientInclusion K := by
  change ((Toric.termIso K 3 3 2).inv ≫
    homotopyCofiber.inlX (couplingToSingle K) 1 0 rfl) ≫
      homotopyCofiber.d (couplingToSingle K) 0 1 = _
  rw [Category.assoc, homotopyCofiber.inlX_d _ 0 1 2 rfl rfl]
  rw [show (Toric.model K 3 3).d 1 2 =
    (Toric.termIso K 3 3 2).hom ≫ boundary (Laurent K 3) (difference K) 1 ≫
      (Toric.termIso K 3 3 1).inv from Toric.differential K 3 3 1]
  rw [couplingToSingle_f_one]
  simp [Category.assoc, coneCellInclusion, coneCoefficientInclusion,
    CochainComplex.mappingCone.inr]

@[reassoc] theorem coneCell_one_d :
    coneCellInclusion K 1 ≫ (couplingCone K).d 1 2 =
      -(boundary (Laurent K 3) (difference K) 0 ≫ coneCellInclusion K 0) := by
  change ((Toric.termIso K 3 3 1).inv ≫
    homotopyCofiber.inlX (couplingToSingle K) 2 1 rfl) ≫
      homotopyCofiber.d (couplingToSingle K) 1 2 = _
  rw [Category.assoc, homotopyCofiber.inlX_d _ 1 2 3 rfl rfl]
  rw [show (Toric.model K 3 3).d 2 3 =
    (Toric.termIso K 3 3 1).hom ≫ boundary (Laurent K 3) (difference K) 0 ≫
      (Toric.termIso K 3 3 0).inv from Toric.differential K 3 3 0]
  rw [couplingToSingle_f_ne K 2 (by decide)]
  simp [Category.assoc, coneCellInclusion]

@[reassoc] theorem coneCoefficient_d :
    coneCoefficientInclusion K ≫ (couplingCone K).d 1 2 = 0 := by
  dsimp [coneCoefficientInclusion, couplingCone]
  rw [Category.assoc, CochainComplex.mappingCone.inr_f_d]
  simp

/-- Away from degree 1 the cone has only its Koszul-cell summand. -/
def coneCellIso (k : ℕ) (hk : k ≠ 1) :
    ModuleCat.of (Laurent K 3) (Term (Laurent K 3) 3 k) ≅ (couplingCone K).X (2 - k) where
  hom := coneCellInclusion K k
  inv := coneCellProjection K k
  hom_inv_id := coneCell_inclusion_projection K k
  inv_hom_id := by
    apply homotopyCofiber.ext_from_X (couplingToSingle K) (3 - k) (2 - k)
      (by change (2 - (k : ℤ)) + 1 = 3 - k; omega)
    · simp [coneCellProjection, coneCellInclusion]
      exact (Category.comp_id _).symm
    · exact (isZero_single_obj_X (.up ℤ) 1 (coefficientModule K 3) (2 - k)
        (by omega)).eq_of_src _ _

theorem coneOne_total :
    (show (couplingCone K).X 1 ⟶ (couplingCone K).X 1 from
      coneCellProjection K 1 ≫ coneCellInclusion K 1) +
      coneCoefficientProjection K ≫ coneCoefficientInclusion K = 𝟙 ((couplingCone K).X 1) := by
  apply homotopyCofiber.ext_from_X (couplingToSingle K) 2 1 rfl
  · simp [coneCellProjection, coneCellInclusion,
      coneCoefficientProjection, coneCoefficientInclusion]
    exact (Category.comp_id _).symm
  · simp [coneCellProjection, coneCellInclusion, coneCoefficientProjection,
      coneCoefficientInclusion, CochainComplex.mappingCone.inr]
    exact (Category.comp_id _).symm

theorem coneOne_decomposition (z : (couplingCone K).X 1) :
    (show (couplingCone K).X 1 from coneCellInclusion K 1 (coneCellProjection K 1 z)) +
      coneCoefficientInclusion K (coneCoefficientProjection K z) = z :=
  congrArg (fun f : (couplingCone K).X 1 ⟶ (couplingCone K).X 1 => f z) (coneOne_total K)

theorem cone_X_zero (n : ℤ) (hn : 3 ≤ n) : IsZero ((couplingCone K).X n) := by
  rw [couplingCone, CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨(Toric.model K 3 3).isZero_of_isStrictlyLE 3 (n + 1) (by omega),
    isZero_single_obj_X (.up ℤ) 1 (coefficientModule K 3) n (by omega)⟩

end
end Decoupling.HighDim.Glued
