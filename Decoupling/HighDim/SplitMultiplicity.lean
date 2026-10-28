import Decoupling.HighDim.Lambda0Profile
import Decoupling.HighDim.ToricSplitCircuit
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Original multiplicities and individual toric copies

The finite coefficient vectors are expanded into actual biproducts of
one-dimensional augmentation modules. Zero-multiplicity degrees contribute
no copies. The reindexing keeps the original degree and original Ext rank.
-/

namespace Decoupling.HighDim.SplitMultiplicity

open CategoryTheory CategoryTheory.Limits TrivialLayers
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (D : ℕ)

def vectorIso (n : ℕ) : coefficientVector K D n ≅
    ⨁ (fun _ : Fin n => Koszul.coefficientModule K D) :=
  (ModuleCat.biproductIsoPi (fun _ : Fin n => Koszul.coefficientModule K D)).symm

def singleVectorIso (j : ℤ) (n : ℕ) :
    (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj (coefficientVector K D n) ≅
      ⨁ (fun _ : Fin n => (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj
        (Koszul.coefficientModule K D)) :=
  (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).mapIso (vectorIso K D n) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).mapBiproduct _

variable {K D} {p q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r)

def multiplicities : Fin (D - 1) → ℕ := fun j => Layers.multiplicity c (j.val + 1)

abbrev SupportedCopies := Σ i : Profile.support c, Fin (Layers.multiplicity c i.val.toNat)

omit [Fact p.Prime] in
theorem support_bounds (i : Profile.support c) :
    1 ≤ i.val.toNat ∧ i.val.toNat < D ∧ (i.val.toNat : ℤ) = i := by
  obtain ⟨n, hn, hnD, _, he⟩ := (Profile.mem_support_iff c i).mp i.property
  simpa only [← he, Int.toNat_natCast] using And.intro hn (And.intro hnD (Eq.refl (n : ℤ)))

def copyToSupport (x : Toric.Copies D (multiplicities c)) : SupportedCopies c :=
  ⟨⟨(x.1.val + 1 : ℕ), (Profile.mem_support_iff c _).mpr
    ⟨x.1.val + 1, by omega, by have := x.1.isLt; omega,
      Module.nontrivial_of_finrank_pos (R := ZMod p)
        (M := Layers.coefficients (Layers.layer c (x.1.val + 1)))
        (by change 0 < Layers.multiplicity c (x.1.val + 1)
            exact lt_of_le_of_lt (Nat.zero_le _) x.2.isLt), rfl⟩⟩,
    x.2⟩

theorem copyToSupport_injective : Function.Injective (copyToSupport c) := by
  rintro ⟨j, a⟩ ⟨k, b⟩ he
  have hjk : j = k := by
    apply Fin.ext
    have hh := congrArg (fun z : SupportedCopies c => z.1.val) he
    change ((j.val + 1 : ℕ) : ℤ) = ((k.val + 1 : ℕ) : ℤ) at hh
    omega
  subst k
  have hab : a = b := Fin.ext (congrArg (fun z : SupportedCopies c => z.2.val) he)
  subst b
  rfl

theorem copyToSupport_surjective : Function.Surjective (copyToSupport c) := by
  rintro ⟨i, a⟩
  obtain ⟨hpos, hlt, hcast⟩ := support_bounds c i
  let j : Fin (D - 1) := ⟨i.val.toNat - 1, by omega⟩
  have hj : j.val + 1 = i.val.toNat := by dsimp [j]; omega
  let b : Fin (multiplicities c j) := ⟨a.val, by simpa only [multiplicities, hj] using a.isLt⟩
  refine ⟨⟨j, b⟩, ?_⟩
  apply Sigma.ext
  · apply Subtype.ext
    change ((j.val + 1 : ℕ) : ℤ) = i.val
    rw [hj, hcast]
  · apply (Fin.heq_ext_iff ?_).mpr
    · rfl
    · change Layers.multiplicity c (j.val + 1) = Layers.multiplicity c i.val.toNat
      rw [hj]

def copiesEquiv : Toric.Copies D (multiplicities c) ≃ SupportedCopies c :=
  Equiv.ofBijective (copyToSupport c) ⟨copyToSupport_injective c, copyToSupport_surjective c⟩

variable (h : Layers.FiniteXLayers c)

def supportedHomologyIso (i : Profile.support c) :
    PostnikovInduction.H (Lambda0Profile.profile c h) i ≅
      coefficientVector (ZMod p) D (Layers.multiplicity c i.val.toNat) :=
  eqToIso (congrArg (PostnikovInduction.H (Lambda0Profile.profile c h))
    (support_bounds c i).2.2.symm) ≪≫
      Lambda0Profile.homologyCoordinatesIso c h i.val.toNat (support_bounds c i).1
        (support_bounds c i).2.1

/-- Identifies the split genuine homology layers with exactly the paper's
toric multiplicity target, including absent degrees and empty stacks. -/
def homologyToToricIso :
    FiniteBiproduct.sumObj
      (fun i => (DerivedCategory.singleFunctor (ModuleCat (Laurent (ZMod p) D)) i).obj
        (PostnikovInduction.H (Lambda0Profile.profile c h) i)) (Profile.support c) ≅
      Toric.splitTarget (ZMod p) D (Toric.copyForms D (multiplicities c)) := by
  let B := fun i : Profile.support c => (DerivedCategory.singleFunctor
    (ModuleCat (Laurent (ZMod p) D)) i).obj (Koszul.coefficientModule (ZMod p) D)
  let e₁ := biproduct.mapIso (fun i : Profile.support c =>
    (DerivedCategory.singleFunctor (ModuleCat (Laurent (ZMod p) D)) i).mapIso
      (supportedHomologyIso c h i) ≪≫
      singleVectorIso (ZMod p) D i (Layers.multiplicity c i.val.toNat))
  let e₂ := biproductBiproductIso (fun i : Profile.support c =>
    Fin (Layers.multiplicity c i.val.toNat)) (fun i _ => B i)
  let e₃ : Toric.splitTarget (ZMod p) D (Toric.copyForms D (multiplicities c)) ≅
      ⨁ (fun x : SupportedCopies c => B x.1) :=
    biproduct.whiskerEquiv
      (f := fun x : Toric.Copies D (multiplicities c) =>
        (DerivedCategory.singleFunctor (ModuleCat (Laurent (ZMod p) D))
          (Toric.copyForms D (multiplicities c) x + 1)).obj (Koszul.coefficientModule (ZMod p) D))
      (g := fun x : SupportedCopies c => B x.1)
      (copiesEquiv c) (fun _ => Iso.refl _)
  exact e₁ ≪≫ e₂ ≪≫ e₃.symm

/-- Theorem 1's genuine splitting after Lambda0 and exactly m-1 p-steps,
now in the exact multiplicity notation needed by the physical theorem. -/
theorem exists_multiplicity_split (hc : c.Topological) (hD : 1 ≤ D) :
    Nonempty ((ExactIteration.derived (ScalingSplitting.restriction p)
      (Layers.nonzeroLayerCount c - 1)).obj (Lambda0Profile.profile c h) ≅
      Toric.splitTarget (ZMod p) D (Toric.copyForms D (multiplicities c))) := by
  obtain ⟨e⟩ := Lambda0Profile.exists_split c h hc hD
  exact ⟨e ≪≫ homologyToToricIso c h⟩

end
end Decoupling.HighDim.SplitMultiplicity
