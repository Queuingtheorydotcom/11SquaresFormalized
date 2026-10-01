import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned09_04Part000
import ElevenSquare.Tasks.T03.Initialization.Owned09_04Part001

namespace ElevenSquare.Pending.T03.Initialization.Owned09_04
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 9 point 0 (1/4) = true :=
  OwnershipTree.leaf_checked leaf000 9 point 0 (1/4) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 9 point (1/4) (5/16) = true :=
  OwnershipTree.leaf_checked leaf001 9 point (1/4) (5/16) rfl rfl leaf001_checked

def node002 : OwnershipTree := .split (1/4) node000 node001

theorem node002_checked : node002.check 9 point 0 (5/16) = true :=
  OwnershipTree.split_checked node000 node001 9 point 0 (1/4) (5/16) node000_checked node001_checked

def node003 : OwnershipTree := .leaf leaf002

theorem node003_checked : node003.check 9 point (5/16) (11/32) = true :=
  OwnershipTree.leaf_checked leaf002 9 point (5/16) (11/32) rfl rfl leaf002_checked

def node004 : OwnershipTree := .leaf leaf003

theorem node004_checked : node004.check 9 point (11/32) (3/8) = true :=
  OwnershipTree.leaf_checked leaf003 9 point (11/32) (3/8) rfl rfl leaf003_checked

def node005 : OwnershipTree := .split (11/32) node003 node004

theorem node005_checked : node005.check 9 point (5/16) (3/8) = true :=
  OwnershipTree.split_checked node003 node004 9 point (5/16) (11/32) (3/8) node003_checked node004_checked

def node006 : OwnershipTree := .split (5/16) node002 node005

theorem node006_checked : node006.check 9 point 0 (3/8) = true :=
  OwnershipTree.split_checked node002 node005 9 point 0 (5/16) (3/8) node002_checked node005_checked

def node007 : OwnershipTree := .leaf leaf004

theorem node007_checked : node007.check 9 point (3/8) (1/2) = true :=
  OwnershipTree.leaf_checked leaf004 9 point (3/8) (1/2) rfl rfl leaf004_checked

def node008 : OwnershipTree := .leaf leaf005

theorem node008_checked : node008.check 9 point (1/2) (3/4) = true :=
  OwnershipTree.leaf_checked leaf005 9 point (1/2) (3/4) rfl rfl leaf005_checked

def node009 : OwnershipTree := .split (1/2) node007 node008

theorem node009_checked : node009.check 9 point (3/8) (3/4) = true :=
  OwnershipTree.split_checked node007 node008 9 point (3/8) (1/2) (3/4) node007_checked node008_checked

def node010 : OwnershipTree := .leaf leaf006

theorem node010_checked : node010.check 9 point (3/4) (13/16) = true :=
  OwnershipTree.leaf_checked leaf006 9 point (3/4) (13/16) rfl rfl leaf006_checked

def node011 : OwnershipTree := .leaf leaf007

theorem node011_checked : node011.check 9 point (13/16) (7/8) = true :=
  OwnershipTree.leaf_checked leaf007 9 point (13/16) (7/8) rfl rfl leaf007_checked

def node012 : OwnershipTree := .leaf leaf008

theorem node012_checked : node012.check 9 point (7/8) 1 = true :=
  OwnershipTree.leaf_checked leaf008 9 point (7/8) 1 rfl rfl leaf008_checked

def node013 : OwnershipTree := .split (7/8) node011 node012

theorem node013_checked : node013.check 9 point (13/16) 1 = true :=
  OwnershipTree.split_checked node011 node012 9 point (13/16) (7/8) 1 node011_checked node012_checked

def node014 : OwnershipTree := .split (13/16) node010 node013

theorem node014_checked : node014.check 9 point (3/4) 1 = true :=
  OwnershipTree.split_checked node010 node013 9 point (3/4) (13/16) 1 node010_checked node013_checked

def node015 : OwnershipTree := .split (3/4) node009 node014

theorem node015_checked : node015.check 9 point (3/8) 1 = true :=
  OwnershipTree.split_checked node009 node014 9 point (3/8) (3/4) 1 node009_checked node014_checked

def node016 : OwnershipTree := .split (3/8) node006 node015

theorem node016_checked : node016.check 9 point 0 1 = true :=
  OwnershipTree.split_checked node006 node015 9 point 0 (3/8) 1 node006_checked node015_checked

def certificate : OwnershipTree := node016

theorem checked : certificate.check 9 point 0 1 = true := node016_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 9 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 9 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned09_04
