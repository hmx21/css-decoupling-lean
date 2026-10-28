import Decoupling.HighDim.CorollaryOneZDual
import Decoupling.HighDim.CorollaryOneZOrientation
import Decoupling.HighDim.ToricDualLatticeStackSites

/-! # The final Z result with explicit dual-cell geometry and orientation semantics -/

namespace Decoupling.HighDim.Toric

open Matrix Koszul
noncomputable section
variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι]
  (forms complements : ι → ℕ) (h : ∀ i, forms i + complements i + 2 = D)

/-- Literal geometric evidence for the map in the final stabilizer
transport: dagger inverse, actual translation-covariant site bijection,
unit displacement bound, and exact signed single-site Laurent action. -/
def DualGeometry : Prop :=
  dagger (stackDualMatrix K D forms complements h) * stackDualMatrix K D forms complements h = 1 ∧
  stackDualMatrix K D forms complements h * dagger (stackDualMatrix K D forms complements h) = 1 ∧
  (∀ x : Σ i, Cell D (forms i + 1) × Translation D,
    (stackDualSiteEquiv D forms complements h x).1 = x.1) ∧
  (∀ (i : ι) (I : Cell D (forms i + 1)) (n a : Translation D),
    stackDualSiteEquiv D forms complements h ⟨i, I, n + a⟩ =
      ⟨i, (dualSiteEquiv (by have := h i; omega : (forms i + 1) + (complements i + 1) = D) (I, n)).1,
        (dualSiteEquiv (by have := h i; omega : (forms i + 1) + (complements i + 1) = D) (I, n)).2 + a⟩) ∧
  (∀ (i : ι) (I : Cell D (forms i + 1)) (n : Translation D) (x : Fin D),
    (((stackDualSiteEquiv D forms complements h ⟨i, I, n⟩).2.2 - n) x).natAbs ≤ 1) ∧
  (∀ (i : ι) (I : Cell D (forms i + 1)) (n : Translation D),
    stackDualMatrix K D forms complements h *ᵥ
      Pi.single ((Fintype.equivFin (Σ i, Fin (cellCount D (forms i + 1))))
        ⟨i, (Fintype.equivFin _) I⟩) (monomial K n) =
      Pi.single ((Fintype.equivFin (Σ i, Fin (cellCount D (complements i + 1))))
        ⟨i, (Fintype.equivFin _) (dualSiteEquiv
          (by have := h i; omega : (forms i + 1) + (complements i + 1) = D) (I, n)).1⟩)
        ((-1 : Laurent K D) ^ ((∑ x ∈ Hodge.directions I, x.val) + (forms i + 1)) *
          monomial K (dualSiteEquiv
            (by have := h i; omega : (forms i + 1) + (complements i + 1) = D) (I, n)).2))

theorem dualGeometry : DualGeometry K D forms complements h :=
  ⟨stackDualMatrix_dagger_mul K D forms complements h,
    stackDualMatrix_mul_dagger K D forms complements h,
    stackDualSiteEquiv_copy D forms complements h,
    stackDualSiteEquiv_translation D forms complements h,
    stackDualSiteEquiv_range D forms complements h,
    stackDualMatrix_site D forms complements h K⟩

end
end Decoupling.HighDim.Toric

namespace Decoupling.HighDim.CorollaryOneZ

open Matrix Koszul PauliUnitary Toric
noncomputable section
variable {p D q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r) (h : Layers.FiniteZLayers c)

/-- The final code theorem and all actual dual-cell geometric properties
hold together, with no supplied geometric or circuit certificate. -/
theorem decouples_Z_with_geometry (hc : c.Topological) (hD : 2 ≤ D) :
    Toric.DecouplesToComplementaryStack (ZMod p) D
      (Toric.copyForms D (multiplicities c)) (complementaryForms c)
      (complementary_degree c) (coarseChecks c h) ∧
    Toric.DualGeometry (ZMod p) D
      (Toric.copyForms D (multiplicities c)) (complementaryForms c)
      (complementary_degree c) :=
  ⟨decouples_Z_with_duality c h hc hD,
    Toric.dualGeometry (ZMod p) D _ _ (complementary_degree c)⟩

/-- The exact orientation factor of every dual cell is implemented by a
genuine single-qudit complex unitary, with no characteristic-two simplification. -/
def dualOrientationUnitary (copy : Toric.Copies D (multiplicities c))
    (I : Cell D (Toric.copyForms D (multiplicities c) copy + 1)) :
    Matrix.unitaryGroup (Config p Unit) ℂ :=
  orientationUnitary ((∑ x ∈ Hodge.directions I, x.val) +
    (Toric.copyForms D (multiplicities c) copy + 1))

theorem dualOrientation_X (copy : Toric.Copies D (multiplicities c))
    (I : Cell D (Toric.copyForms D (multiplicities c) copy + 1)) (a : Config p Unit) :
    permutation (orientationGate ((∑ x ∈ Hodge.directions I, x.val) +
      (Toric.copyForms D (multiplicities c) copy + 1))).toEquiv * X a *
      (permutation (orientationGate ((∑ x ∈ Hodge.directions I, x.val) +
        (Toric.copyForms D (multiplicities c) copy + 1))).toEquiv)ᴴ =
      X (fun i => (-1 : ZMod p) ^ ((∑ x ∈ Hodge.directions I, x.val) +
        (Toric.copyForms D (multiplicities c) copy + 1)) * a i) :=
  orientation_conjugate_X _ a

theorem dualOrientation_Z (copy : Toric.Copies D (multiplicities c))
    (I : Cell D (Toric.copyForms D (multiplicities c) copy + 1)) (b : Config p Unit) :
    permutation (orientationGate ((∑ x ∈ Hodge.directions I, x.val) +
      (Toric.copyForms D (multiplicities c) copy + 1))).toEquiv * Z b *
      (permutation (orientationGate ((∑ x ∈ Hodge.directions I, x.val) +
        (Toric.copyForms D (multiplicities c) copy + 1))).toEquiv)ᴴ =
      Z (fun i => (-1 : ZMod p) ^ ((∑ x ∈ Hodge.directions I, x.val) +
        (Toric.copyForms D (multiplicities c) copy + 1)) * b i) :=
  orientation_conjugate_Z _ b

end
end Decoupling.HighDim.CorollaryOneZ
