import Decoupling.HighDim.GluedShearMatrices
import Decoupling.HighDim.PhysicalIsomorphism

/-!
# A finite, ancilla-free SUM circuit for the actual glued example

The physical species are exactly the six original species in each of the
p residue rows. Both stabilizer images are transported to the retained
first-plus-second Koszul CSS windows. The shear and check equivalence are
constructed from the Laurent derivative, not assumed as certificates.
-/

namespace Decoupling.HighDim.GluedDirectional

open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime]

private theorem relabel_zMatrix {K : Type*} [CommRing K] {D : ℕ}
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (g : Circuit.SUM K D ι) (e : ι ≃ κ) :
    (g.relabel e).zMatrix = g.zMatrix.submatrix e.symm e.symm := by
  simp [Circuit.SUM.zMatrix_formula, Circuit.SUM.relabel, Matrix.submatrix_sub]

private theorem zAction_relabel {K : Type*} [CommRing K] {D : ℕ}
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (c : List (Circuit.SUM K D ι)) (e : ι ≃ κ) :
    Circuit.zAction (c.map (fun g => g.relabel e)) =
      (Circuit.zAction c).submatrix e.symm e.symm := by
  induction c with
  | nil => simp
  | cons g c ih =>
    simp only [List.map_cons, Circuit.zAction_cons, relabel_zMatrix, ih,
      Matrix.submatrix_mul_equiv]

theorem exists_sum_action :
    ∃ c : List (Circuit.SUM (ZMod p) 3 (Fin 6 × Fin p)),
      Circuit.zAction c = quditMatrix p := by
  obtain ⟨c, hc⟩ := Circuit.two_shear_z_compilation
    (0 : Matrix (Fin 3 × Fin p) (Fin 3 × Fin p) (Laurent (ZMod p) 3)) (shearBlock p)
  refine ⟨c.map (fun g => g.relabel (blockSpecies p)), ?_⟩
  rw [zAction_relabel, hc, quditMatrix_upper]
  simp [Circuit.lower, Matrix.fromBlocks_one]

/-- Both physical stabilizer sectors are transformed by a finite SUM word
on exactly 6p species, without ancillary qudits. -/
theorem exists_noAncilla_sumCircuit :
    ∃ c : List (Circuit.SUM (ZMod p) 3 (Fin 6 × Fin p)),
      PhysicalIsomorphism.Transports (c.map Circuit.Layer.sum) (Equiv.refl _)
        (expandMatrix p (Glued.xChecks (ZMod p)))
        (expandMatrix p (Glued.splitX (ZMod p)))
        (expandMatrix p (Glued.zGenerators (ZMod p)))
        (expandMatrix p (Glued.splitZ (ZMod p))) ∧
      Circuit.zAction c = quditMatrix p ∧
      Circuit.wordX (c.map Circuit.Layer.sum) = dagger (quditInverse p) ∧
      ∃ depth range : ℕ, depth = c.length ∧
        ∀ g ∈ c, ∀ i : Fin 3, (g.displacement i).natAbs ≤ range := by
  obtain ⟨c, hc⟩ := exists_sum_action p
  have hz : Circuit.wordZ (c.map Circuit.Layer.sum) = quditMatrix p := by
    rw [Circuit.wordZ_sum, hc]
  have hx := Circuit.wordX_eq_dagger_inverse (c.map Circuit.Layer.sum)
    (quditMatrix p) (quditInverse p) hz (qudit_inverse p)
  refine ⟨c, ?_, hc, hx, Circuit.finite_depth_range c⟩
  apply PhysicalIsomorphism.transports_of_actions _ (Equiv.refl _)
    _ _ _ _ (quditMatrix p) (quditInverse p) (syndromeMatrix p) (syndromeInverse p)
    (qudit_inverse p) (syndrome_inverse p) (matrix_square p)
  · intro v
    exact expandMatrix_exact p _ _ (Glued.exact_X (ZMod p)) v
  · intro v
    exact expandMatrix_exact p _ _ (Glued.split_exact (ZMod p)) v
  · simpa using hz
  · simpa using hx

end
end Decoupling.HighDim.GluedDirectional
