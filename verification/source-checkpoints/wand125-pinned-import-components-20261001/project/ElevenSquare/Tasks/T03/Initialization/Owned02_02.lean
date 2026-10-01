import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned02_02Part000

namespace ElevenSquare.Pending.T03.Initialization.Owned02_02
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 2 point 0 (1/16) = true :=
  OwnershipTree.leaf_checked leaf000 2 point 0 (1/16) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 2 point (1/16) (1/8) = true :=
  OwnershipTree.leaf_checked leaf001 2 point (1/16) (1/8) rfl rfl leaf001_checked

def node002 : OwnershipTree := .split (1/16) node000 node001

theorem node002_checked : node002.check 2 point 0 (1/8) = true :=
  OwnershipTree.split_checked node000 node001 2 point 0 (1/16) (1/8) node000_checked node001_checked

def node003 : OwnershipTree := .leaf leaf002

theorem node003_checked : node003.check 2 point (1/8) (1/4) = true :=
  OwnershipTree.leaf_checked leaf002 2 point (1/8) (1/4) rfl rfl leaf002_checked

def node004 : OwnershipTree := .leaf leaf003

theorem node004_checked : node004.check 2 point (1/4) (3/8) = true :=
  OwnershipTree.leaf_checked leaf003 2 point (1/4) (3/8) rfl rfl leaf003_checked

def node005 : OwnershipTree := .split (1/4) node003 node004

theorem node005_checked : node005.check 2 point (1/8) (3/8) = true :=
  OwnershipTree.split_checked node003 node004 2 point (1/8) (1/4) (3/8) node003_checked node004_checked

def node006 : OwnershipTree := .split (1/8) node002 node005

theorem node006_checked : node006.check 2 point 0 (3/8) = true :=
  OwnershipTree.split_checked node002 node005 2 point 0 (1/8) (3/8) node002_checked node005_checked

def node007 : OwnershipTree := .leaf leaf004

theorem node007_checked : node007.check 2 point (3/8) (7/16) = true :=
  OwnershipTree.leaf_checked leaf004 2 point (3/8) (7/16) rfl rfl leaf004_checked

def node008 : OwnershipTree := .leaf leaf005

theorem node008_checked : node008.check 2 point (7/16) (1/2) = true :=
  OwnershipTree.leaf_checked leaf005 2 point (7/16) (1/2) rfl rfl leaf005_checked

def node009 : OwnershipTree := .split (7/16) node007 node008

theorem node009_checked : node009.check 2 point (3/8) (1/2) = true :=
  OwnershipTree.split_checked node007 node008 2 point (3/8) (7/16) (1/2) node007_checked node008_checked

def node010 : OwnershipTree := .leaf leaf006

theorem node010_checked : node010.check 2 point (1/2) (3/4) = true :=
  OwnershipTree.leaf_checked leaf006 2 point (1/2) (3/4) rfl rfl leaf006_checked

def node011 : OwnershipTree := .leaf leaf007

theorem node011_checked : node011.check 2 point (3/4) 1 = true :=
  OwnershipTree.leaf_checked leaf007 2 point (3/4) 1 rfl rfl leaf007_checked

def node012 : OwnershipTree := .split (3/4) node010 node011

theorem node012_checked : node012.check 2 point (1/2) 1 = true :=
  OwnershipTree.split_checked node010 node011 2 point (1/2) (3/4) 1 node010_checked node011_checked

def node013 : OwnershipTree := .split (1/2) node009 node012

theorem node013_checked : node013.check 2 point (3/8) 1 = true :=
  OwnershipTree.split_checked node009 node012 2 point (3/8) (1/2) 1 node009_checked node012_checked

def node014 : OwnershipTree := .split (3/8) node006 node013

theorem node014_checked : node014.check 2 point 0 1 = true :=
  OwnershipTree.split_checked node006 node013 2 point 0 (3/8) 1 node006_checked node013_checked

def certificate : OwnershipTree := node014

theorem checked : certificate.check 2 point 0 1 = true := node014_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 2 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 2 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned02_02
