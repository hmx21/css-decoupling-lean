import Decoupling.HighDim.CorollaryOne
import Decoupling.HighDim.ToricDualLatticeSites

/-!
# Corollary 1, Z sector, on the exact retained lattice

Only the original two-sided topological condition and finite positive Z
layers are inputs. The X result is applied to the exchanged checks, and
each gate is conjugated by the proved complex Fourier transform. For SUM
this reverses its actual sites and negates its weight. Product-state
ancillas exchange their roles. Complementary dual-cell identification is
kept distinct from the same-lattice SUM/SWAP circuit.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory PhysicalIsomorphism
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι] (forms : ι → ℕ)
  {q s r : ℕ}

/-- The actual stable circuit conclusion before the geometric dual-cell
identification. Its target is the sector exchange of the displayed toric
stack; the explicit ancillary blocks are the Fourier exchanges of |0⟩/|+⟩. -/
def DecouplesToDualStack (c : CSS.Checks K D q s r) : Prop :=
  ∃ a b : ℕ, ∃ gates : List (Circuit.Layer K D
      ((Fin (stackCount D forms 1) ⊕ (Fin r ⊕ Fin a)) ⊕
        (Fin q ⊕ (Fin (stackCount D forms 0) ⊕ Fin b)))),
    Transports gates (Equiv.sumComm _ _)
      (dagger (StableCSS.H_Z_dagger (A := Fin (stackCount D forms 0) ⊕ Fin b)
        (B := Fin (stackCount D forms 1) ⊕ (Fin r ⊕ Fin a)) (dagger c.H_X)))
      (dagger (StableCSS.H_Z_dagger (A := Fin r ⊕ Fin a)
        (B := Fin q ⊕ (Fin (stackCount D forms 0) ⊕ Fin b))
        (dagger (stackChecks K D forms).H_Z)))
      (dagger (StableCSS.H_X (A := Fin (stackCount D forms 0) ⊕ Fin b)
        (B := Fin (stackCount D forms 1) ⊕ (Fin r ⊕ Fin a))
        (StableCSS.identityChecks (A := Fin a) c.H_Z)))
      (dagger (StableCSS.H_X (A := Fin r ⊕ Fin a)
        (B := Fin q ⊕ (Fin (stackCount D forms 0) ⊕ Fin b))
        (StableCSS.identityChecks (A := Fin b) (stackChecks K D forms).H_X))) ∧
    LocalCircuit gates

/-- Fourier-conjugating the constructed gate word stays in SUM/SWAP,
preserves locality, and exchanges both actual stabilizer module equalities. -/
theorem decouples_dual_of_swap (c : CSS.Checks K D q s r)
    (h : DecouplesToStack K D forms c.swap) : DecouplesToDualStack K D forms c := by
  obtain ⟨a, b, gates, htrans, _⟩ := h
  exact ⟨a, b, gates.map Circuit.fourierDual,
    transports_fourierDual gates _ _ _ _ _ htrans, localCircuit _⟩

/-- Theorem 2 in the Z sector. Its only non-topological premise is exactly
the advertised genuine split Z profile, expressed as S_X of exchanged checks. -/
theorem decouples_dual_of_split (c : CSS.Checks K D q s r) (hc : c.Topological)
    (e : Profile.S_X c.swap ≅ splitTarget K D forms) :
    DecouplesToDualStack K D forms c :=
  decouples_dual_of_swap K D forms c
    (decouples_of_split K D forms c.swap (c.topological_swap hc) e)

end
end Decoupling.HighDim.Toric

namespace Decoupling.HighDim.CorollaryOneZ

open CategoryTheory ScalingLattice
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {p D q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r) (h : Layers.FiniteZLayers c)

/-- Precisely the common-kernel-and-p-scaling lattice for the original Z layers. -/
def lattice : AddSubgroup (Translation D) := TheoremOne.lattice c.swap

include h in
theorem lattice_finiteIndex : (lattice c).FiniteIndex :=
  TheoremOne.lattice_finiteIndex c.swap h

/-- Actual coarse-grained original checks; sector exchange is undone after
using the same physical restriction of c.swap. -/
def coarseChecks : CSS.Checks (ZMod p) D
    (CorollaryOne.coarseCount c.swap h q)
    (CorollaryOne.coarseCount c.swap h s)
    (CorollaryOne.coarseCount c.swap h r) :=
  (CorollaryOne.coarseChecks c.swap h).swap

/-- The preceding definition is literally the physical coset expansion
of the original checks on the selected Z lattice. -/
theorem coarseChecks_eq : coarseChecks c h =
    (by
      letI : (lattice c).FiniteIndex := lattice_finiteIndex c h
      exact physicalChecks (ZMod p) (lattice c) (TheoremOne.coordinates c.swap h) c) := rfl

theorem coarseChecks_topological (hc : c.Topological) : (coarseChecks c h).Topological :=
  (CorollaryOne.coarseChecks c.swap h).topological_swap
    (CorollaryOne.coarseChecks_topological c.swap h (c.topological_swap hc))

/-- The original Z-sector multiplicity in each degree, without changing its
coefficient field dimension during restriction. -/
def multiplicities : Fin (D - 1) → ℕ := SplitMultiplicity.multiplicities c.swap

/-- Corollary 1, Z branch: all intermediate split-profile, comparison-map,
stable-cokernel and circuit-certificate hypotheses have been discharged. -/
theorem decouples_Z (hc : c.Topological) (hD : 2 ≤ D) :
    Toric.DecouplesToDualStack (ZMod p) D (Toric.copyForms D (multiplicities c))
      (coarseChecks c h) := by
  apply Toric.decouples_dual_of_swap
  change Toric.DecouplesToStack (ZMod p) D
    (Toric.copyForms D (SplitMultiplicity.multiplicities c.swap))
    (CorollaryOne.coarseChecks c.swap h)
  exact CorollaryOne.decouples_X c.swap h (c.topological_swap hc) hD

/-- An offset j-1 indexes the actual j-form toric code. Sector exchange
therefore has complementary offset D-j-1, including both endpoint forms. -/
def complementaryForms : Toric.Copies D (multiplicities c) → ℕ :=
  fun copy => D - Toric.copyForms D (multiplicities c) copy - 2

theorem complementary_degree (copy : Toric.Copies D (multiplicities c)) :
    Toric.copyForms D (multiplicities c) copy + complementaryForms c copy + 2 = D := by
  have hi := copy.1.isLt
  dsimp [Toric.copyForms, complementaryForms]
  omega

/-- In the manuscript's form-degree notation the target is TC_(D-j),
with exactly the original Z-layer multiplicity t_j. -/
theorem complementary_form (copy : Toric.Copies D (multiplicities c)) :
    complementaryForms c copy + 1 = D - (copy.1.val + 1) := by
  have hi := copy.1.isLt
  dsimp [complementaryForms, Toric.copyForms]
  omega

end
end Decoupling.HighDim.CorollaryOneZ
