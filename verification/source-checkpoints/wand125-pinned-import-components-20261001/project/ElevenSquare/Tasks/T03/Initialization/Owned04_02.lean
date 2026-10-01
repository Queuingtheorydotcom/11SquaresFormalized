import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned04_02Part000
import ElevenSquare.Tasks.T03.Initialization.Owned04_02Part001
import ElevenSquare.Tasks.T03.Initialization.Owned04_02Part002

namespace ElevenSquare.Pending.T03.Initialization.Owned04_02
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 4 point 0 (1/16) = true :=
  OwnershipTree.leaf_checked leaf000 4 point 0 (1/16) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 4 point (1/16) (3/32) = true :=
  OwnershipTree.leaf_checked leaf001 4 point (1/16) (3/32) rfl rfl leaf001_checked

def node002 : OwnershipTree := .split (1/16) node000 node001

theorem node002_checked : node002.check 4 point 0 (3/32) = true :=
  OwnershipTree.split_checked node000 node001 4 point 0 (1/16) (3/32) node000_checked node001_checked

def node003 : OwnershipTree := .leaf leaf002

theorem node003_checked : node003.check 4 point (3/32) (7/64) = true :=
  OwnershipTree.leaf_checked leaf002 4 point (3/32) (7/64) rfl rfl leaf002_checked

def node004 : OwnershipTree := .leaf leaf003

theorem node004_checked : node004.check 4 point (7/64) (15/128) = true :=
  OwnershipTree.leaf_checked leaf003 4 point (7/64) (15/128) rfl rfl leaf003_checked

def node005 : OwnershipTree := .split (7/64) node003 node004

theorem node005_checked : node005.check 4 point (3/32) (15/128) = true :=
  OwnershipTree.split_checked node003 node004 4 point (3/32) (7/64) (15/128) node003_checked node004_checked

def node006 : OwnershipTree := .split (3/32) node002 node005

theorem node006_checked : node006.check 4 point 0 (15/128) = true :=
  OwnershipTree.split_checked node002 node005 4 point 0 (3/32) (15/128) node002_checked node005_checked

def node007 : OwnershipTree := .leaf leaf004

theorem node007_checked : node007.check 4 point (15/128) (1/8) = true :=
  OwnershipTree.leaf_checked leaf004 4 point (15/128) (1/8) rfl rfl leaf004_checked

def node008 : OwnershipTree := .leaf leaf005

theorem node008_checked : node008.check 4 point (1/8) (17/128) = true :=
  OwnershipTree.leaf_checked leaf005 4 point (1/8) (17/128) rfl rfl leaf005_checked

def node009 : OwnershipTree := .split (1/8) node007 node008

theorem node009_checked : node009.check 4 point (15/128) (17/128) = true :=
  OwnershipTree.split_checked node007 node008 4 point (15/128) (1/8) (17/128) node007_checked node008_checked

def node010 : OwnershipTree := .leaf leaf006

theorem node010_checked : node010.check 4 point (17/128) (9/64) = true :=
  OwnershipTree.leaf_checked leaf006 4 point (17/128) (9/64) rfl rfl leaf006_checked

def node011 : OwnershipTree := .leaf leaf007

theorem node011_checked : node011.check 4 point (9/64) (19/128) = true :=
  OwnershipTree.leaf_checked leaf007 4 point (9/64) (19/128) rfl rfl leaf007_checked

def node012 : OwnershipTree := .leaf leaf008

theorem node012_checked : node012.check 4 point (19/128) (5/32) = true :=
  OwnershipTree.leaf_checked leaf008 4 point (19/128) (5/32) rfl rfl leaf008_checked

def node013 : OwnershipTree := .split (19/128) node011 node012

theorem node013_checked : node013.check 4 point (9/64) (5/32) = true :=
  OwnershipTree.split_checked node011 node012 4 point (9/64) (19/128) (5/32) node011_checked node012_checked

def node014 : OwnershipTree := .split (9/64) node010 node013

theorem node014_checked : node014.check 4 point (17/128) (5/32) = true :=
  OwnershipTree.split_checked node010 node013 4 point (17/128) (9/64) (5/32) node010_checked node013_checked

def node015 : OwnershipTree := .split (17/128) node009 node014

theorem node015_checked : node015.check 4 point (15/128) (5/32) = true :=
  OwnershipTree.split_checked node009 node014 4 point (15/128) (17/128) (5/32) node009_checked node014_checked

def node016 : OwnershipTree := .split (15/128) node006 node015

theorem node016_checked : node016.check 4 point 0 (5/32) = true :=
  OwnershipTree.split_checked node006 node015 4 point 0 (15/128) (5/32) node006_checked node015_checked

def node017 : OwnershipTree := .leaf leaf009

theorem node017_checked : node017.check 4 point (5/32) (21/128) = true :=
  OwnershipTree.leaf_checked leaf009 4 point (5/32) (21/128) rfl rfl leaf009_checked

def node018 : OwnershipTree := .leaf leaf010

theorem node018_checked : node018.check 4 point (21/128) (11/64) = true :=
  OwnershipTree.leaf_checked leaf010 4 point (21/128) (11/64) rfl rfl leaf010_checked

def node019 : OwnershipTree := .split (21/128) node017 node018

theorem node019_checked : node019.check 4 point (5/32) (11/64) = true :=
  OwnershipTree.split_checked node017 node018 4 point (5/32) (21/128) (11/64) node017_checked node018_checked

def node020 : OwnershipTree := .leaf leaf011

theorem node020_checked : node020.check 4 point (11/64) (3/16) = true :=
  OwnershipTree.leaf_checked leaf011 4 point (11/64) (3/16) rfl rfl leaf011_checked

def node021 : OwnershipTree := .leaf leaf012

theorem node021_checked : node021.check 4 point (3/16) (1/4) = true :=
  OwnershipTree.leaf_checked leaf012 4 point (3/16) (1/4) rfl rfl leaf012_checked

def node022 : OwnershipTree := .split (3/16) node020 node021

theorem node022_checked : node022.check 4 point (11/64) (1/4) = true :=
  OwnershipTree.split_checked node020 node021 4 point (11/64) (3/16) (1/4) node020_checked node021_checked

def node023 : OwnershipTree := .split (11/64) node019 node022

theorem node023_checked : node023.check 4 point (5/32) (1/4) = true :=
  OwnershipTree.split_checked node019 node022 4 point (5/32) (11/64) (1/4) node019_checked node022_checked

def node024 : OwnershipTree := .leaf leaf013

theorem node024_checked : node024.check 4 point (1/4) (1/2) = true :=
  OwnershipTree.leaf_checked leaf013 4 point (1/4) (1/2) rfl rfl leaf013_checked

def node025 : OwnershipTree := .leaf leaf014

theorem node025_checked : node025.check 4 point (1/2) (9/16) = true :=
  OwnershipTree.leaf_checked leaf014 4 point (1/2) (9/16) rfl rfl leaf014_checked

def node026 : OwnershipTree := .split (1/2) node024 node025

theorem node026_checked : node026.check 4 point (1/4) (9/16) = true :=
  OwnershipTree.split_checked node024 node025 4 point (1/4) (1/2) (9/16) node024_checked node025_checked

def node027 : OwnershipTree := .leaf leaf015

theorem node027_checked : node027.check 4 point (9/16) (5/8) = true :=
  OwnershipTree.leaf_checked leaf015 4 point (9/16) (5/8) rfl rfl leaf015_checked

def node028 : OwnershipTree := .leaf leaf016

theorem node028_checked : node028.check 4 point (5/8) (3/4) = true :=
  OwnershipTree.leaf_checked leaf016 4 point (5/8) (3/4) rfl rfl leaf016_checked

def node029 : OwnershipTree := .leaf leaf017

theorem node029_checked : node029.check 4 point (3/4) 1 = true :=
  OwnershipTree.leaf_checked leaf017 4 point (3/4) 1 rfl rfl leaf017_checked

def node030 : OwnershipTree := .split (3/4) node028 node029

theorem node030_checked : node030.check 4 point (5/8) 1 = true :=
  OwnershipTree.split_checked node028 node029 4 point (5/8) (3/4) 1 node028_checked node029_checked

def node031 : OwnershipTree := .split (5/8) node027 node030

theorem node031_checked : node031.check 4 point (9/16) 1 = true :=
  OwnershipTree.split_checked node027 node030 4 point (9/16) (5/8) 1 node027_checked node030_checked

def node032 : OwnershipTree := .split (9/16) node026 node031

theorem node032_checked : node032.check 4 point (1/4) 1 = true :=
  OwnershipTree.split_checked node026 node031 4 point (1/4) (9/16) 1 node026_checked node031_checked

def node033 : OwnershipTree := .split (1/4) node023 node032

theorem node033_checked : node033.check 4 point (5/32) 1 = true :=
  OwnershipTree.split_checked node023 node032 4 point (5/32) (1/4) 1 node023_checked node032_checked

def node034 : OwnershipTree := .split (5/32) node016 node033

theorem node034_checked : node034.check 4 point 0 1 = true :=
  OwnershipTree.split_checked node016 node033 4 point 0 (5/32) 1 node016_checked node033_checked

def certificate : OwnershipTree := node034

theorem checked : certificate.check 4 point 0 1 = true := node034_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 4 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned04_02
