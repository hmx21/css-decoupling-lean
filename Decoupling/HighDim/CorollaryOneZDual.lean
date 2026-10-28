import Decoupling.HighDim.CorollaryOneZDualSupport
import Decoupling.HighDim.ToricDualLatticeStack

/-!
# Z-sector decoupling to the actual complementary toric stack

The constructed SUM/SWAP word is followed only by the explicitly proved
complementary dual-cell identification. Both ancillary blocks are fixed
by that identification. Its signed monomial matrix is kept separate from
the local circuit, and both final stabilizer-module image equalities are
proved for the literal composite action.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory PhysicalIsomorphism
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι]
  (forms complements : ι → ℕ) (hd : ∀ i, forms i + complements i + 2 = D)
  {q s r : ℕ}

/-- Both actual composite support actions, with all identity-check and
product-state ancillary blocks shown. The circuit acts on the retained
lattice and `stackDualMatrix` only identifies complementary dual cells. -/
def DecouplesToComplementaryStack (c : CSS.Checks K D q s r) : Prop :=
  ∃ a b : ℕ, ∃ gates : List (Circuit.Layer K D
      ((Fin (stackCount D forms 1) ⊕ (Fin r ⊕ Fin a)) ⊕
        (Fin q ⊕ (Fin (stackCount D forms 0) ⊕ Fin b)))),
    TransportsAfter gates (Equiv.sumComm _ _)
      (ancillaryExtension (A := Fin r ⊕ Fin a)
        (B := Fin q ⊕ (Fin (stackCount D forms 0) ⊕ Fin b))
        (stackDualMatrix K D forms complements hd))
      (dagger (StableCSS.H_Z_dagger (A := Fin (stackCount D forms 0) ⊕ Fin b)
        (B := Fin (stackCount D forms 1) ⊕ (Fin r ⊕ Fin a)) (dagger c.H_X)))
      (dagger (StableCSS.H_Z_dagger (A := Fin r ⊕ Fin a)
        (B := Fin q ⊕ (Fin (stackCount D forms 0) ⊕ Fin b))
        (dagger (stackChecks K D complements).H_X)))
      (dagger (StableCSS.H_X (A := Fin (stackCount D forms 0) ⊕ Fin b)
        (B := Fin (stackCount D forms 1) ⊕ (Fin r ⊕ Fin a))
        (StableCSS.identityChecks (A := Fin a) c.H_Z)))
      (dagger (StableCSS.H_X (A := Fin r ⊕ Fin a)
        (B := Fin q ⊕ (Fin (stackCount D forms 0) ⊕ Fin b))
        (StableCSS.identityChecks (A := Fin b) (stackChecks K D complements).H_Z))) ∧
    LocalCircuit gates

/-- Compose the actual Fourier-dual word with the actual complementary
dual-cell map, using its already proved stabilizer images. -/
theorem decouples_complementary_of_dual (c : CSS.Checks K D q s r)
    (h : DecouplesToDualStack K D forms c) :
    DecouplesToComplementaryStack K D forms complements hd c := by
  obtain ⟨a, b, gates, htrans, hlocal⟩ := h
  refine ⟨a, b, gates, ?_, hlocal⟩
  apply transportsAfter_of_images gates (Equiv.sumComm _ _) _ _ _ _ _ _ _ htrans
  · exact ancillaryExtension_X_image _ _ _
      (stackDual_z_stabilizers K D forms complements hd)
  · simpa only [dagger_dagger] using
      ancillaryExtension_Z_image (A := Fin r ⊕ Fin a)
        (B := Fin q ⊕ (Fin (stackCount D forms 0) ⊕ Fin b))
        (stackDualMatrix K D forms complements hd)
        (dagger (stackChecks K D forms).H_Z)
        (dagger (stackChecks K D complements).H_X)
        (stackDual_x_stabilizers K D forms complements hd)

end
end Decoupling.HighDim.Toric

namespace Decoupling.HighDim.CorollaryOneZ

noncomputable section
variable {p D q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r) (h : Layers.FiniteZLayers c)

/-- Corollary 1 with the literal composite stabilizer action to TC_(D-j).
The only assumptions are the original Z-layer finiteness, both topological
equalities, and D ≥ 2. The circuit itself is a same-lattice finite SUM/SWAP
word; the separately proved signed dual-cell identification is explicit. -/
theorem decouples_Z_with_duality (hc : c.Topological) (hD : 2 ≤ D) :
    Toric.DecouplesToComplementaryStack (ZMod p) D
      (Toric.copyForms D (multiplicities c)) (complementaryForms c)
      (complementary_degree c) (coarseChecks c h) :=
  Toric.decouples_complementary_of_dual (ZMod p) D
    (Toric.copyForms D (multiplicities c)) (complementaryForms c)
    (complementary_degree c) (coarseChecks c h) (decouples_Z c h hc hD)

end
end Decoupling.HighDim.CorollaryOneZ
