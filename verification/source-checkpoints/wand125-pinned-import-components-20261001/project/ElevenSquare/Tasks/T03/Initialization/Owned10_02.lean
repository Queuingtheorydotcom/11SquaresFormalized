import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned10_02Part000
import ElevenSquare.Tasks.T03.Initialization.Owned10_02Part001

namespace ElevenSquare.Pending.T03.Initialization.Owned10_02
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 10 point 0 (1/8) = true :=
  OwnershipTree.leaf_checked leaf000 10 point 0 (1/8) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 10 point (1/8) (1/4) = true :=
  OwnershipTree.leaf_checked leaf001 10 point (1/8) (1/4) rfl rfl leaf001_checked

def node002 : OwnershipTree := .leaf leaf002

theorem node002_checked : node002.check 10 point (1/4) (5/16) = true :=
  OwnershipTree.leaf_checked leaf002 10 point (1/4) (5/16) rfl rfl leaf002_checked

def node003 : OwnershipTree := .split (1/4) node001 node002

theorem node003_checked : node003.check 10 point (1/8) (5/16) = true :=
  OwnershipTree.split_checked node001 node002 10 point (1/8) (1/4) (5/16) node001_checked node002_checked

def node004 : OwnershipTree := .split (1/8) node000 node003

theorem node004_checked : node004.check 10 point 0 (5/16) = true :=
  OwnershipTree.split_checked node000 node003 10 point 0 (1/8) (5/16) node000_checked node003_checked

def node005 : OwnershipTree := .leaf leaf003

theorem node005_checked : node005.check 10 point (5/16) (11/32) = true :=
  OwnershipTree.leaf_checked leaf003 10 point (5/16) (11/32) rfl rfl leaf003_checked

def node006 : OwnershipTree := .leaf leaf004

theorem node006_checked : node006.check 10 point (11/32) (3/8) = true :=
  OwnershipTree.leaf_checked leaf004 10 point (11/32) (3/8) rfl rfl leaf004_checked

def node007 : OwnershipTree := .leaf leaf005

theorem node007_checked : node007.check 10 point (3/8) (1/2) = true :=
  OwnershipTree.leaf_checked leaf005 10 point (3/8) (1/2) rfl rfl leaf005_checked

def node008 : OwnershipTree := .split (3/8) node006 node007

theorem node008_checked : node008.check 10 point (11/32) (1/2) = true :=
  OwnershipTree.split_checked node006 node007 10 point (11/32) (3/8) (1/2) node006_checked node007_checked

def node009 : OwnershipTree := .split (11/32) node005 node008

theorem node009_checked : node009.check 10 point (5/16) (1/2) = true :=
  OwnershipTree.split_checked node005 node008 10 point (5/16) (11/32) (1/2) node005_checked node008_checked

def node010 : OwnershipTree := .split (5/16) node004 node009

theorem node010_checked : node010.check 10 point 0 (1/2) = true :=
  OwnershipTree.split_checked node004 node009 10 point 0 (5/16) (1/2) node004_checked node009_checked

def node011 : OwnershipTree := .leaf leaf006

theorem node011_checked : node011.check 10 point (1/2) (17/32) = true :=
  OwnershipTree.leaf_checked leaf006 10 point (1/2) (17/32) rfl rfl leaf006_checked

def node012 : OwnershipTree := .leaf leaf007

theorem node012_checked : node012.check 10 point (17/32) (9/16) = true :=
  OwnershipTree.leaf_checked leaf007 10 point (17/32) (9/16) rfl rfl leaf007_checked

def node013 : OwnershipTree := .leaf leaf008

theorem node013_checked : node013.check 10 point (9/16) (5/8) = true :=
  OwnershipTree.leaf_checked leaf008 10 point (9/16) (5/8) rfl rfl leaf008_checked

def node014 : OwnershipTree := .split (9/16) node012 node013

theorem node014_checked : node014.check 10 point (17/32) (5/8) = true :=
  OwnershipTree.split_checked node012 node013 10 point (17/32) (9/16) (5/8) node012_checked node013_checked

def node015 : OwnershipTree := .split (17/32) node011 node014

theorem node015_checked : node015.check 10 point (1/2) (5/8) = true :=
  OwnershipTree.split_checked node011 node014 10 point (1/2) (17/32) (5/8) node011_checked node014_checked

def node016 : OwnershipTree := .leaf leaf009

theorem node016_checked : node016.check 10 point (5/8) (3/4) = true :=
  OwnershipTree.leaf_checked leaf009 10 point (5/8) (3/4) rfl rfl leaf009_checked

def node017 : OwnershipTree := .leaf leaf010

theorem node017_checked : node017.check 10 point (3/4) (7/8) = true :=
  OwnershipTree.leaf_checked leaf010 10 point (3/4) (7/8) rfl rfl leaf010_checked

def node018 : OwnershipTree := .leaf leaf011

theorem node018_checked : node018.check 10 point (7/8) 1 = true :=
  OwnershipTree.leaf_checked leaf011 10 point (7/8) 1 rfl rfl leaf011_checked

def node019 : OwnershipTree := .split (7/8) node017 node018

theorem node019_checked : node019.check 10 point (3/4) 1 = true :=
  OwnershipTree.split_checked node017 node018 10 point (3/4) (7/8) 1 node017_checked node018_checked

def node020 : OwnershipTree := .split (3/4) node016 node019

theorem node020_checked : node020.check 10 point (5/8) 1 = true :=
  OwnershipTree.split_checked node016 node019 10 point (5/8) (3/4) 1 node016_checked node019_checked

def node021 : OwnershipTree := .split (5/8) node015 node020

theorem node021_checked : node021.check 10 point (1/2) 1 = true :=
  OwnershipTree.split_checked node015 node020 10 point (1/2) (5/8) 1 node015_checked node020_checked

def node022 : OwnershipTree := .split (1/2) node010 node021

theorem node022_checked : node022.check 10 point 0 1 = true :=
  OwnershipTree.split_checked node010 node021 10 point 0 (1/2) 1 node010_checked node021_checked

def certificate : OwnershipTree := node022

theorem checked : certificate.check 10 point 0 1 = true := node022_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 10 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 10 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned10_02
