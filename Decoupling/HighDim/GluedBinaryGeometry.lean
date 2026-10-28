import Decoupling.HighDim.GluedBinaryCircuit

/-! The single CNOT layer on actual original-lattice sites, not just labels. -/

namespace Decoupling.HighDim.GluedDirectional

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime]

/-- Species, residue, and retained-cell coordinates give an actual
bijection with the original fine-lattice physical sites. -/
def physicalSiteEquiv : ((Fin 6 × Fin p) × Translation 3) ≃ (Fin 6 × Translation 3) :=
  (Equiv.prodAssoc (Fin 6) (Fin p) (Translation 3)).trans
    (Equiv.prodCongr (Equiv.refl _) (exponentEquiv p).symm)

@[simp] theorem physicalSiteEquiv_apply (i : Fin 6) (r : Fin p) (a : Translation 3) :
    physicalSiteEquiv p ((i, r), a) = (i, inclusion p a + row p r) := rfl

theorem physicalSite_translate (i : Fin 6) (r : Fin p) (a b : Translation 3) :
    physicalSiteEquiv p ((i, r), a + b) =
      (i, (physicalSiteEquiv p ((i, r), a)).2 + inclusion p b) := by
  simp only [physicalSiteEquiv_apply, map_add]
  congr 1
  abel

/-- The binary gates connect adjacent fine rows along the second axis. -/
theorem binary_fine_displacement (g : Fin 2) (a : Translation 3) :
    (physicalSiteEquiv 2 ((binaryGate g).destination a)).2 -
      (physicalSiteEquiv 2 ((binaryGate g).source a)).2 = translationBasis 1 := by
  simp [Circuit.SUM.source, Circuit.SUM.destination, binaryGate, row]

/-- Distinct gate instances have no common physical endpoint in the
original lattice. Relabeling alone cannot conceal a shared site. -/
theorem binary_fine_parallel (a b : Fin 2) (n m : Translation 3)
    (h : (a, n) ≠ (b, m)) :
    physicalSiteEquiv 2 ((binaryGate a).source n) ≠
        physicalSiteEquiv 2 ((binaryGate b).source m) ∧
    physicalSiteEquiv 2 ((binaryGate a).source n) ≠
        physicalSiteEquiv 2 ((binaryGate b).destination m) ∧
    physicalSiteEquiv 2 ((binaryGate a).destination n) ≠
        physicalSiteEquiv 2 ((binaryGate b).source m) ∧
    physicalSiteEquiv 2 ((binaryGate a).destination n) ≠
        physicalSiteEquiv 2 ((binaryGate b).destination m) := by
  simpa only [ne_eq, Equiv.apply_eq_iff_eq] using binary_parallel a b n m h

/-- Every retained translation permutes the gate pairs themselves. -/
theorem binary_fine_translation (g : Fin 2) (a b : Translation 3) :
    physicalSiteEquiv 2 ((binaryGate g).source (a + b)) =
      ((binaryGate g).control.1,
        (physicalSiteEquiv 2 ((binaryGate g).source a)).2 + inclusion 2 b) ∧
    physicalSiteEquiv 2 ((binaryGate g).destination (a + b)) =
      ((binaryGate g).target.1,
        (physicalSiteEquiv 2 ((binaryGate g).destination a)).2 + inclusion 2 b) := by
  constructor <;>
    simpa only [Circuit.SUM.source, Circuit.SUM.destination, binaryGate, add_zero] using
      (physicalSite_translate 2 _ _ a b)

end
end Decoupling.HighDim.GluedDirectional
