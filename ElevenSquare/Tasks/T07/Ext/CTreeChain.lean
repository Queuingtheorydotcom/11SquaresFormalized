import ElevenSquare.Tasks.T07.Ext.Promote

/-! A pruning certificate often follows a sequence of cuts, with one terminal
certificate beside the continuing branch at each cut. Store that sequence once
as a list instead of repeating the binary-tree plumbing at every node.

This is only a constructor for the existing `CTree`. It does not replace or
weaken `CTree.check`; all original rational witnesses and both sides of every
closed half-plane split remain in the reconstructed tree. -/
namespace ElevenSquare.Tasks.T07.Ext.CTreeChain
open ElevenSquare.Pending

/-- The constructor name identifies the branch that continues down the spine. -/
inductive Cut where
  | left (plane : Halfplane) (side : CTree)
  | right (plane : Halfplane) (side : CTree)

/-- Reconstruct the ordinary pruning tree consumed by the unchanged checker. -/
def build : List Cut → CTree → CTree
  | [], last => last
  | .left plane side :: cuts, last => .split plane (build cuts last) side
  | .right plane side :: cuts, last => .split plane side (build cuts last)

theorem build_nil (last : CTree) : build [] last = last := rfl

theorem build_left (plane : Halfplane) (side : CTree) (cuts : List Cut)
    (last : CTree) :
    build (.left plane side :: cuts) last = .split plane (build cuts last) side := rfl

theorem build_right (plane : Halfplane) (side : CTree) (cuts : List Cut)
    (last : CTree) :
    build (.right plane side :: cuts) last = .split plane side (build cuts last) := rfl

end ElevenSquare.Tasks.T07.Ext.CTreeChain
