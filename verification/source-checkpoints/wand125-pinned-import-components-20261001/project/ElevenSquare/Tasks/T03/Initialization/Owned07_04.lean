import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned07_04Part000

namespace ElevenSquare.Pending.T03.Initialization.Owned07_04
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 7 point 0 (1/8) = true :=
  OwnershipTree.leaf_checked leaf000 7 point 0 (1/8) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 7 point (1/8) (3/16) = true :=
  OwnershipTree.leaf_checked leaf001 7 point (1/8) (3/16) rfl rfl leaf001_checked

def node002 : OwnershipTree := .leaf leaf002

theorem node002_checked : node002.check 7 point (3/16) (7/32) = true :=
  OwnershipTree.leaf_checked leaf002 7 point (3/16) (7/32) rfl rfl leaf002_checked

def node003 : OwnershipTree := .split (3/16) node001 node002

theorem node003_checked : node003.check 7 point (1/8) (7/32) = true :=
  OwnershipTree.split_checked node001 node002 7 point (1/8) (3/16) (7/32) node001_checked node002_checked

def node004 : OwnershipTree := .split (1/8) node000 node003

theorem node004_checked : node004.check 7 point 0 (7/32) = true :=
  OwnershipTree.split_checked node000 node003 7 point 0 (1/8) (7/32) node000_checked node003_checked

def node005 : OwnershipTree := .leaf leaf003

theorem node005_checked : node005.check 7 point (7/32) (1/4) = true :=
  OwnershipTree.leaf_checked leaf003 7 point (7/32) (1/4) rfl rfl leaf003_checked

def node006 : OwnershipTree := .leaf leaf004

theorem node006_checked : node006.check 7 point (1/4) (1/2) = true :=
  OwnershipTree.leaf_checked leaf004 7 point (1/4) (1/2) rfl rfl leaf004_checked

def node007 : OwnershipTree := .leaf leaf005

theorem node007_checked : node007.check 7 point (1/2) 1 = true :=
  OwnershipTree.leaf_checked leaf005 7 point (1/2) 1 rfl rfl leaf005_checked

def node008 : OwnershipTree := .split (1/2) node006 node007

theorem node008_checked : node008.check 7 point (1/4) 1 = true :=
  OwnershipTree.split_checked node006 node007 7 point (1/4) (1/2) 1 node006_checked node007_checked

def node009 : OwnershipTree := .split (1/4) node005 node008

theorem node009_checked : node009.check 7 point (7/32) 1 = true :=
  OwnershipTree.split_checked node005 node008 7 point (7/32) (1/4) 1 node005_checked node008_checked

def node010 : OwnershipTree := .split (7/32) node004 node009

theorem node010_checked : node010.check 7 point 0 1 = true :=
  OwnershipTree.split_checked node004 node009 7 point 0 (7/32) 1 node004_checked node009_checked

def certificate : OwnershipTree := node010

theorem checked : certificate.check 7 point 0 1 = true := node010_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 7 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned07_04
