import ElevenSquare.Tasks.T07.Ext.CompactWitness

/-! Small kernel-evaluated checks of reconstruction, including bad-data rejection.
These exercise the original implication and tree checkers; they do not certify
any generated family. -/
namespace ElevenSquare.Tasks.T07.Ext.CompactWitnessAudit
open ElevenSquare.Pending
open CompactWitness

private def axisP : Polygon := [⟨2, 0, 3⟩, ⟨0, -3, 6⟩]
private def obliqueP : Polygon := [⟨2, 1, 7⟩, ⟨1, 3, 11⟩]

example : Support.weights axisP ⟨5, 0, 8⟩ (.one 0) = [5/2, 0] := by decide +kernel
example : impliesB axisP (Support.weights axisP ⟨5, 0, 8⟩ (.one 0)) ⟨5, 0, 8⟩ = true := by decide +kernel
example : Support.weights axisP ⟨0, -6, 12⟩ (.one 1) = [0, 2] := by decide +kernel
example : Support.weights obliqueP ⟨7, 11, 47⟩ (.two 0 1) = [2, 3] := by decide +kernel
example : impliesB obliqueP (Support.weights obliqueP ⟨7, 11, 47⟩ (.two 0 1)) ⟨7, 11, 47⟩ = true := by decide +kernel
example : Support.weights [⟨-1/2, 1/3, 2/5⟩, ⟨2/7, 3/5, 9/11⟩]
    ⟨-1/12, 19/10, 138/55⟩ (.two 0 1) = [3/2, 7/3] := by decide +kernel
example : Support.weights axisP ⟨0, 0, 1⟩ .zero = [0, 0] := by decide +kernel
example : Support.weights axisP ⟨0, 0, 1⟩ (.literal [1/3, 2/7, 0]) = [1/3, 2/7, 0] := by decide +kernel
example : impliesB axisP (Support.weights axisP ⟨1, 0, 1⟩ (.one 99)) ⟨1, 0, 1⟩ = false := by decide +kernel
example : impliesB [⟨1, 0, 2⟩, ⟨2, 0, 4⟩]
    (Support.weights [⟨1, 0, 2⟩, ⟨2, 0, 4⟩] ⟨1, 0, 2⟩ (.two 0 1))
    ⟨1, 0, 2⟩ = false := by decide +kernel

private def emptyState : PoseState := ⟨fun _ => [], fun _ => []⟩
private def splitContext : Ctx :=
  ⟨emptyState, 0, [⟨0, 1, [⟨1, 0, 0⟩]⟩, ⟨0, 1, [⟨-1, 0, 0⟩]⟩], [], 0, 1, []⟩

example : CTree.check splitContext []
    (chain [.left ⟨1, 0, 0⟩ (keep 1 [.one 0])] (keep 0 [.one 0]) splitContext []) = true := by
  decide +kernel
example : CTree.check splitContext []
    (chain [.right ⟨1, 0, 0⟩ (keep 0 [.one 0])] (keep 1 [.one 0]) splitContext []) = true := by
  decide +kernel
example : CTree.check splitContext []
    (chain [.left ⟨1, 0, 0⟩ (keep 0 [.one 0])] (keep 0 [.one 0]) splitContext []) = false := by
  decide +kernel

end ElevenSquare.Tasks.T07.Ext.CompactWitnessAudit
