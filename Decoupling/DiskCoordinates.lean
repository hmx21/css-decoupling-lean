import Decoupling.ContractibleDisk
import Decoupling.Stabilization
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Coordinates of the actual contractible-disk stabilization

The natural coordinate maps below identify the degree-one differential of
`K ⊞ D₁(P)` with `diag(d,id_P)`, and that of `K ⊞ D₂(Q)` with `(d,0)`.
Thus the printed stabilization blocks are coordinates of the actual complexes.
-/

namespace Decoupling.DiskCoordinates

open CategoryTheory CategoryTheory.Limits HomologicalComplex Matrix

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K L : ChainComplex (ModuleCat.{0} R) ℤ)

private instance evalPreservesBinaryBiproducts (i : ℤ) :
    PreservesBinaryBiproducts (eval (ModuleCat.{0} R) (ComplexShape.down ℤ) i) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

/-- Evaluation commutes with the categorical biproduct, followed by the
canonical module biproduct/product identification. -/
def coordinates (i : ℤ) : (K ⊞ L).X i ≃ₗ[R] (K.X i × L.X i) :=
  (((eval (ModuleCat R) (ComplexShape.down ℤ) i).mapBiprod K L) ≪≫
    ModuleCat.biprodIsoProd (K.X i) (L.X i)).toLinearEquiv

private theorem prod_fst (M N : ModuleCat R) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.fst R M N) =
      biprod.fst := by
  rw [← ModuleCat.biprodIsoProd_inv_comp_fst, Iso.hom_inv_id_assoc]

private theorem prod_snd (M N : ModuleCat R) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.snd R M N) =
      biprod.snd := by
  rw [← ModuleCat.biprodIsoProd_inv_comp_snd, Iso.hom_inv_id_assoc]

@[simp] theorem coordinates_fst (i : ℤ) (v : (K ⊞ L).X i) :
    (coordinates K L i v).1 = (biprod.fst : K ⊞ L ⟶ K).f i v := by
  have h : (((eval (ModuleCat R) (ComplexShape.down ℤ) i).mapBiprod K L).hom ≫
      (ModuleCat.biprodIsoProd (K.X i) (L.X i)).hom) ≫
      ModuleCat.ofHom (LinearMap.fst R (K.X i) (L.X i)) =
      (biprod.fst : K ⊞ L ⟶ K).f i := by
    rw [Category.assoc, prod_fst, Functor.mapBiprod_hom]
    exact biprod.lift_fst _ _
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) v

@[simp] theorem coordinates_snd (i : ℤ) (v : (K ⊞ L).X i) :
    (coordinates K L i v).2 = (biprod.snd : K ⊞ L ⟶ L).f i v := by
  have h : (((eval (ModuleCat R) (ComplexShape.down ℤ) i).mapBiprod K L).hom ≫
      (ModuleCat.biprodIsoProd (K.X i) (L.X i)).hom) ≫
      ModuleCat.ofHom (LinearMap.snd R (K.X i) (L.X i)) =
      (biprod.snd : K ⊞ L ⟶ L).f i := by
    rw [Category.assoc, prod_snd, Functor.mapBiprod_hom]
    exact biprod.lift_snd _ _
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) v

/-- Naturality of the actual differential in these coordinates. -/
theorem coordinates_d (i j : ℤ) (v : (K ⊞ L).X i) :
    coordinates K L j ((K ⊞ L).d i j v) =
      (K.d i j (coordinates K L i v).1, L.d i j (coordinates K L i v).2) := by
  apply Prod.ext
  · simp only [coordinates_fst]
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp
      ((biprod.fst : K ⊞ L ⟶ K).comm i j).symm) v
  · simp only [coordinates_snd]
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp
      ((biprod.snd : K ⊞ L ⟶ L).comm i j).symm) v

variable (P : ModuleCat.{0} R)

def disk₁Upper : (K ⊞ ContractibleDisk.disk P 1).X 1 ≃ₗ[R] (K.X 1 × P) :=
  (coordinates K (ContractibleDisk.disk P 1) 1).trans
    ((LinearEquiv.refl R _).prodCongr (ContractibleDisk.upperIso P 1).toLinearEquiv)

def disk₁Lower : (K ⊞ ContractibleDisk.disk P 1).X 0 ≃ₗ[R] (K.X 0 × P) :=
  (coordinates K (ContractibleDisk.disk P 1) 0).trans
    ((LinearEquiv.refl R _).prodCongr (ContractibleDisk.lowerIso P 1).toLinearEquiv)

/-- The first disk adds exactly the identity boundary, with no sign or
summand reversal. -/
theorem disk₁_d (v : (K ⊞ ContractibleDisk.disk P 1).X 1) :
    disk₁Lower K P ((K ⊞ ContractibleDisk.disk P 1).d 1 0 v) =
      (K.d 1 0 (disk₁Upper K P v).1, (disk₁Upper K P v).2) := by
  have hd := coordinates_d K (ContractibleDisk.disk P 1) 1 0 v
  have hid : (ContractibleDisk.disk P 1).d 1 0 ≫ (ContractibleDisk.lowerIso P 1).hom =
      (ContractibleDisk.upperIso P 1).hom := by
    change (double (𝟙 P) _).d 1 0 ≫ (ContractibleDisk.lowerIso P 1).hom = _
    rw [double_d _ _ (by decide : (1 : ℤ) ≠ 0)]
    simp [ContractibleDisk.lowerIso, ContractibleDisk.upperIso, Category.assoc]
  apply Prod.ext
  · simpa only [disk₁Lower, disk₁Upper, LinearEquiv.trans_apply,
      LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply] using congrArg Prod.fst hd
  · exact (congrArg (fun x => (ContractibleDisk.lowerIso P 1).hom x.2) hd).trans
      (DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hid) _)

def disk₂Upper : (K ⊞ ContractibleDisk.disk P 2).X 1 ≃ₗ[R] (K.X 1 × P) :=
  (coordinates K (ContractibleDisk.disk P 2) 1).trans
    ((LinearEquiv.refl R _).prodCongr (ContractibleDisk.lowerIso P 2).toLinearEquiv)

private instance disk₂ZeroSubsingleton : Subsingleton ((ContractibleDisk.disk P 2).X 0) :=
  ModuleCat.subsingleton_of_isZero (isZero_double_X (𝟙 P)
    (show (ComplexShape.down ℤ).Rel 2 (2 - 1) by decide) 0 (by decide) (by decide))

private instance disk₂ZeroUnique : Unique ((ContractibleDisk.disk P 2).X 0) :=
  uniqueOfSubsingleton 0

def disk₂Lower : (K ⊞ ContractibleDisk.disk P 2).X 0 ≃ₗ[R] K.X 0 :=
  (coordinates K (ContractibleDisk.disk P 2) 0).trans LinearEquiv.prodUnique

/-- The second disk contributes no boundary from degree one to degree zero. -/
theorem disk₂_d (v : (K ⊞ ContractibleDisk.disk P 2).X 1) :
    disk₂Lower K P ((K ⊞ ContractibleDisk.disk P 2).d 1 0 v) =
      K.d 1 0 (disk₂Upper K P v).1 :=
  congrArg Prod.fst (coordinates_d K (ContractibleDisk.disk P 2) 1 0 v)

section FreeCoordinates

variable {F₀ F₁ A B : Type} [Fintype F₀] [Fintype F₁] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]
variable (e₀ : K.X 0 ≃ₗ[R] (F₀ → R)) (e₁ : K.X 1 ≃ₗ[R] (F₁ → R))

/-- Natural degree-one free coordinates after the first disk. -/
def first₁ : (K ⊞ ContractibleDisk.disk (ModuleCat.of R (A → R)) 1).X 1 ≃ₗ[R]
    ((F₁ ⊕ A) → R) :=
  (disk₁Upper K (ModuleCat.of R (A → R))).trans
    (e₁.prodCongr (LinearEquiv.refl R (A → R))) |>.trans
      (LinearEquiv.sumArrowLequivProdArrow F₁ A R R).symm

/-- Natural degree-zero free coordinates after the first disk. -/
def first₀ : (K ⊞ ContractibleDisk.disk (ModuleCat.of R (A → R)) 1).X 0 ≃ₗ[R]
    ((F₀ ⊕ A) → R) :=
  (disk₁Lower K (ModuleCat.of R (A → R))).trans
    (e₀.prodCongr (LinearEquiv.refl R (A → R))) |>.trans
      (LinearEquiv.sumArrowLequivProdArrow F₀ A R R).symm

omit [Fintype F₀] in
/-- In these explicit coordinates the actual first-disk differential is
the printed block diagonal, assuming only a representation of the input d. -/
theorem first_d (D : Matrix F₀ F₁ R)
    (hD : ∀ v : K.X 1, e₀ (K.d 1 0 v) = D *ᵥ e₁ v)
    (v : (K ⊞ ContractibleDisk.disk (ModuleCat.of R (A → R)) 1).X 1) :
    first₀ K e₀ ((K ⊞ ContractibleDisk.disk (ModuleCat.of R (A → R)) 1).d 1 0 v) =
      Matrix.fromBlocks D 0 0 (1 : Matrix A A R) *ᵥ first₁ K e₁ v := by
  rw [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.zero_mulVec,
    add_zero, zero_add, Matrix.one_mulVec]
  apply (LinearEquiv.sumArrowLequivProdArrow F₀ A R R).injective
  change (e₀ ((disk₁Lower K _ _).1), (disk₁Lower K _ _).2) =
    (D *ᵥ e₁ (disk₁Upper K _ v).1, (disk₁Upper K _ v).2)
  rw [disk₁_d]
  exact Prod.ext (hD _) rfl

/-- Natural degree-one free coordinates after the second disk. -/
def second₁ : (K ⊞ ContractibleDisk.disk (ModuleCat.of R (B → R)) 2).X 1 ≃ₗ[R]
    ((F₁ ⊕ B) → R) :=
  (disk₂Upper K (ModuleCat.of R (B → R))).trans
    (e₁.prodCongr (LinearEquiv.refl R (B → R))) |>.trans
      (LinearEquiv.sumArrowLequivProdArrow F₁ B R R).symm

/-- The second disk has zero degree-zero module, so these coordinates retain
exactly the existing degree-zero labels. -/
def second₀ : (K ⊞ ContractibleDisk.disk (ModuleCat.of R (B → R)) 2).X 0 ≃ₗ[R]
    (F₀ → R) := (disk₂Lower K (ModuleCat.of R (B → R))).trans e₀

omit [Fintype F₀] [DecidableEq B] in
/-- The actual second-disk differential is the printed added zero-column block. -/
theorem second_d (D : Matrix F₀ F₁ R)
    (hD : ∀ v : K.X 1, e₀ (K.d 1 0 v) = D *ᵥ e₁ v)
    (v : (K ⊞ ContractibleDisk.disk (ModuleCat.of R (B → R)) 2).X 1) :
    second₀ K e₀ ((K ⊞ ContractibleDisk.disk (ModuleCat.of R (B → R)) 2).d 1 0 v) =
      Matrix.fromCols D (0 : Matrix F₀ B R) *ᵥ second₁ K e₁ v := by
  rw [Matrix.fromCols_mulVec, Matrix.zero_mulVec, add_zero]
  change e₀ (disk₂Lower K _ _) = D *ᵥ e₁ (disk₂Upper K _ v).1
  rw [disk₂_d]
  exact hD _

/-- The actual complex after both disk adjunctions. -/
abbrev twice := (K ⊞ ContractibleDisk.disk (ModuleCat.of R (A → R)) 1) ⊞
  ContractibleDisk.disk (ModuleCat.of R (B → R)) 2

def twice₁ : (twice (A := A) (B := B) K).X 1 ≃ₗ[R] (((F₁ ⊕ A) ⊕ B) → R) :=
  second₁ _ (first₁ K e₁)

def twice₀ : (twice (A := A) (B := B) K).X 0 ≃ₗ[R] ((F₀ ⊕ A) → R) :=
  second₀ _ (first₀ K e₀)

omit [Fintype F₀] [DecidableEq B] in
/-- Both disk steps give precisely `(diag(D,I_A),0_B)` in degree one. -/
theorem twice_d (D : Matrix F₀ F₁ R)
    (hD : ∀ v : K.X 1, e₀ (K.d 1 0 v) = D *ᵥ e₁ v)
    (v : (twice (A := A) (B := B) K).X 1) :
    twice₀ K e₀ ((twice (A := A) (B := B) K).d 1 0 v) =
      Matrix.fromCols (Matrix.fromBlocks D 0 0 (1 : Matrix A A R))
        (0 : Matrix (F₀ ⊕ A) B R) *ᵥ twice₁ K e₁ v :=
  second_d _ (first₀ K e₀) (first₁ K e₁) _ (first_d K e₀ e₁ D hD) v

end FreeCoordinates

section StabilizationMatrices

open Stabilization

variable {F₀ F₁ G₀ G₁ : Type} [Fintype F₀] [Fintype F₁] [Fintype G₀] [Fintype G₁]
  [DecidableEq F₀] [DecidableEq F₁] [DecidableEq G₀] [DecidableEq G₁]
variable (d : ComparisonData R F₀ F₁ G₀ G₁)
variable (e₀ : K.X 0 ≃ₗ[R] (F₀ → R)) (e₁ : K.X 1 ≃ₗ[R] (F₁ → R))
variable (hd : ∀ v : K.X 1, e₀ (K.d 1 0 v) = d.d₁ *ᵥ e₁ v)

omit [DecidableEq F₁] [DecidableEq G₁] in
include hd in
/-- The first actual disk gives exactly `ComparisonData.D_F`. -/
theorem D_F_coordinates
    (v : (K ⊞ ContractibleDisk.disk (ModuleCat.of R (G₀ → R)) 1).X 1) :
    first₀ K e₀ ((K ⊞ ContractibleDisk.disk (ModuleCat.of R (G₀ → R)) 1).d 1 0 v) =
      d.D_F *ᵥ first₁ K e₁ v := first_d K e₀ e₁ d.d₁ hd v

omit [DecidableEq F₁] [DecidableEq G₁] in
include hd in
/-- The two actual source disks give exactly the physical input X matrix. -/
theorem H_X_hat_coordinates
    (v : (twice (A := G₀) (B := G₁ ⊕ F₀) K).X 1) :
    twice₀ K e₀ ((twice (A := G₀) (B := G₁ ⊕ F₀) K).d 1 0 v) =
      d.H_X_hat *ᵥ twice₁ K e₁ v := twice_d K e₀ e₁ d.d₁ hd v

variable (g₀ : L.X 0 ≃ₗ[R] (G₀ → R)) (g₁ : L.X 1 ≃ₗ[R] (G₁ → R))
variable (htd : ∀ v : L.X 1, g₀ (L.d 1 0 v) = d.td₁ *ᵥ g₁ v)

omit [DecidableEq F₁] [DecidableEq G₁] in
include htd in
/-- The same coordinates on the target preserve its reversed species order. -/
theorem D_G_coordinates
    (v : (L ⊞ ContractibleDisk.disk (ModuleCat.of R (F₀ → R)) 1).X 1) :
    first₀ L g₀ ((L ⊞ ContractibleDisk.disk (ModuleCat.of R (F₀ → R)) 1).d 1 0 v) =
      d.D_G *ᵥ first₁ L g₁ v := first_d L g₀ g₁ d.td₁ htd v

omit [DecidableEq F₁] [DecidableEq G₁] in
include htd in
/-- The two actual target disks give exactly the physical target X matrix. -/
theorem H_X_tilde_coordinates
    (v : (twice (A := F₀) (B := F₁ ⊕ G₀) L).X 1) :
    twice₀ L g₀ ((twice (A := F₀) (B := F₁ ⊕ G₀) L).d 1 0 v) =
      d.H_X_tilde *ᵥ twice₁ L g₁ v := twice_d L g₀ g₁ d.td₁ htd v

end StabilizationMatrices

end
end Decoupling.DiskCoordinates
