import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned04_06Part000
import ElevenSquare.Tasks.T03.Initialization.Owned04_06Part001
import ElevenSquare.Tasks.T03.Initialization.Owned04_06Part002

namespace ElevenSquare.Pending.T03.Initialization.Owned04_06
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 4 point 0 (1/16) = true :=
  OwnershipTree.leaf_checked leaf000 4 point 0 (1/16) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 4 point (1/16) (1/8) = true :=
  OwnershipTree.leaf_checked leaf001 4 point (1/16) (1/8) rfl rfl leaf001_checked

def node002 : OwnershipTree := .split (1/16) node000 node001

theorem node002_checked : node002.check 4 point 0 (1/8) = true :=
  OwnershipTree.split_checked node000 node001 4 point 0 (1/16) (1/8) node000_checked node001_checked

def node003 : OwnershipTree := .leaf leaf002

theorem node003_checked : node003.check 4 point (1/8) (1/4) = true :=
  OwnershipTree.leaf_checked leaf002 4 point (1/8) (1/4) rfl rfl leaf002_checked

def node004 : OwnershipTree := .leaf leaf003

theorem node004_checked : node004.check 4 point (1/4) (1/2) = true :=
  OwnershipTree.leaf_checked leaf003 4 point (1/4) (1/2) rfl rfl leaf003_checked

def node005 : OwnershipTree := .leaf leaf004

theorem node005_checked : node005.check 4 point (1/2) (9/16) = true :=
  OwnershipTree.leaf_checked leaf004 4 point (1/2) (9/16) rfl rfl leaf004_checked

def node006 : OwnershipTree := .split (1/2) node004 node005

theorem node006_checked : node006.check 4 point (1/4) (9/16) = true :=
  OwnershipTree.split_checked node004 node005 4 point (1/4) (1/2) (9/16) node004_checked node005_checked

def node007 : OwnershipTree := .split (1/4) node003 node006

theorem node007_checked : node007.check 4 point (1/8) (9/16) = true :=
  OwnershipTree.split_checked node003 node006 4 point (1/8) (1/4) (9/16) node003_checked node006_checked

def node008 : OwnershipTree := .split (1/8) node002 node007

theorem node008_checked : node008.check 4 point 0 (9/16) = true :=
  OwnershipTree.split_checked node002 node007 4 point 0 (1/8) (9/16) node002_checked node007_checked

def node009 : OwnershipTree := .leaf leaf005

theorem node009_checked : node009.check 4 point (9/16) (19/32) = true :=
  OwnershipTree.leaf_checked leaf005 4 point (9/16) (19/32) rfl rfl leaf005_checked

def node010 : OwnershipTree := .leaf leaf006

theorem node010_checked : node010.check 4 point (19/32) (5/8) = true :=
  OwnershipTree.leaf_checked leaf006 4 point (19/32) (5/8) rfl rfl leaf006_checked

def node011 : OwnershipTree := .leaf leaf007

theorem node011_checked : node011.check 4 point (5/8) (41/64) = true :=
  OwnershipTree.leaf_checked leaf007 4 point (5/8) (41/64) rfl rfl leaf007_checked

def node012 : OwnershipTree := .split (5/8) node010 node011

theorem node012_checked : node012.check 4 point (19/32) (41/64) = true :=
  OwnershipTree.split_checked node010 node011 4 point (19/32) (5/8) (41/64) node010_checked node011_checked

def node013 : OwnershipTree := .split (19/32) node009 node012

theorem node013_checked : node013.check 4 point (9/16) (41/64) = true :=
  OwnershipTree.split_checked node009 node012 4 point (9/16) (19/32) (41/64) node009_checked node012_checked

def node014 : OwnershipTree := .leaf leaf008

theorem node014_checked : node014.check 4 point (41/64) (21/32) = true :=
  OwnershipTree.leaf_checked leaf008 4 point (41/64) (21/32) rfl rfl leaf008_checked

def node015 : OwnershipTree := .leaf leaf009

theorem node015_checked : node015.check 4 point (21/32) (85/128) = true :=
  OwnershipTree.leaf_checked leaf009 4 point (21/32) (85/128) rfl rfl leaf009_checked

def node016 : OwnershipTree := .leaf leaf010

theorem node016_checked : node016.check 4 point (85/128) (43/64) = true :=
  OwnershipTree.leaf_checked leaf010 4 point (85/128) (43/64) rfl rfl leaf010_checked

def node017 : OwnershipTree := .split (85/128) node015 node016

theorem node017_checked : node017.check 4 point (21/32) (43/64) = true :=
  OwnershipTree.split_checked node015 node016 4 point (21/32) (85/128) (43/64) node015_checked node016_checked

def node018 : OwnershipTree := .split (21/32) node014 node017

theorem node018_checked : node018.check 4 point (41/64) (43/64) = true :=
  OwnershipTree.split_checked node014 node017 4 point (41/64) (21/32) (43/64) node014_checked node017_checked

def node019 : OwnershipTree := .split (41/64) node013 node018

theorem node019_checked : node019.check 4 point (9/16) (43/64) = true :=
  OwnershipTree.split_checked node013 node018 4 point (9/16) (41/64) (43/64) node013_checked node018_checked

def node020 : OwnershipTree := .split (9/16) node008 node019

theorem node020_checked : node020.check 4 point 0 (43/64) = true :=
  OwnershipTree.split_checked node008 node019 4 point 0 (9/16) (43/64) node008_checked node019_checked

def node021 : OwnershipTree := .leaf leaf011

theorem node021_checked : node021.check 4 point (43/64) (87/128) = true :=
  OwnershipTree.leaf_checked leaf011 4 point (43/64) (87/128) rfl rfl leaf011_checked

def node022 : OwnershipTree := .leaf leaf012

theorem node022_checked : node022.check 4 point (87/128) (11/16) = true :=
  OwnershipTree.leaf_checked leaf012 4 point (87/128) (11/16) rfl rfl leaf012_checked

def node023 : OwnershipTree := .split (87/128) node021 node022

theorem node023_checked : node023.check 4 point (43/64) (11/16) = true :=
  OwnershipTree.split_checked node021 node022 4 point (43/64) (87/128) (11/16) node021_checked node022_checked

def node024 : OwnershipTree := .leaf leaf013

theorem node024_checked : node024.check 4 point (11/16) (89/128) = true :=
  OwnershipTree.leaf_checked leaf013 4 point (11/16) (89/128) rfl rfl leaf013_checked

def node025 : OwnershipTree := .leaf leaf014

theorem node025_checked : node025.check 4 point (89/128) (45/64) = true :=
  OwnershipTree.leaf_checked leaf014 4 point (89/128) (45/64) rfl rfl leaf014_checked

def node026 : OwnershipTree := .leaf leaf015

theorem node026_checked : node026.check 4 point (45/64) (23/32) = true :=
  OwnershipTree.leaf_checked leaf015 4 point (45/64) (23/32) rfl rfl leaf015_checked

def node027 : OwnershipTree := .split (45/64) node025 node026

theorem node027_checked : node027.check 4 point (89/128) (23/32) = true :=
  OwnershipTree.split_checked node025 node026 4 point (89/128) (45/64) (23/32) node025_checked node026_checked

def node028 : OwnershipTree := .split (89/128) node024 node027

theorem node028_checked : node028.check 4 point (11/16) (23/32) = true :=
  OwnershipTree.split_checked node024 node027 4 point (11/16) (89/128) (23/32) node024_checked node027_checked

def node029 : OwnershipTree := .split (11/16) node023 node028

theorem node029_checked : node029.check 4 point (43/64) (23/32) = true :=
  OwnershipTree.split_checked node023 node028 4 point (43/64) (11/16) (23/32) node023_checked node028_checked

def node030 : OwnershipTree := .leaf leaf016

theorem node030_checked : node030.check 4 point (23/32) (47/64) = true :=
  OwnershipTree.leaf_checked leaf016 4 point (23/32) (47/64) rfl rfl leaf016_checked

def node031 : OwnershipTree := .leaf leaf017

theorem node031_checked : node031.check 4 point (47/64) (3/4) = true :=
  OwnershipTree.leaf_checked leaf017 4 point (47/64) (3/4) rfl rfl leaf017_checked

def node032 : OwnershipTree := .leaf leaf018

theorem node032_checked : node032.check 4 point (3/4) (25/32) = true :=
  OwnershipTree.leaf_checked leaf018 4 point (3/4) (25/32) rfl rfl leaf018_checked

def node033 : OwnershipTree := .split (3/4) node031 node032

theorem node033_checked : node033.check 4 point (47/64) (25/32) = true :=
  OwnershipTree.split_checked node031 node032 4 point (47/64) (3/4) (25/32) node031_checked node032_checked

def node034 : OwnershipTree := .split (47/64) node030 node033

theorem node034_checked : node034.check 4 point (23/32) (25/32) = true :=
  OwnershipTree.split_checked node030 node033 4 point (23/32) (47/64) (25/32) node030_checked node033_checked

def node035 : OwnershipTree := .leaf leaf019

theorem node035_checked : node035.check 4 point (25/32) (13/16) = true :=
  OwnershipTree.leaf_checked leaf019 4 point (25/32) (13/16) rfl rfl leaf019_checked

def node036 : OwnershipTree := .leaf leaf020

theorem node036_checked : node036.check 4 point (13/16) (7/8) = true :=
  OwnershipTree.leaf_checked leaf020 4 point (13/16) (7/8) rfl rfl leaf020_checked

def node037 : OwnershipTree := .leaf leaf021

theorem node037_checked : node037.check 4 point (7/8) 1 = true :=
  OwnershipTree.leaf_checked leaf021 4 point (7/8) 1 rfl rfl leaf021_checked

def node038 : OwnershipTree := .split (7/8) node036 node037

theorem node038_checked : node038.check 4 point (13/16) 1 = true :=
  OwnershipTree.split_checked node036 node037 4 point (13/16) (7/8) 1 node036_checked node037_checked

def node039 : OwnershipTree := .split (13/16) node035 node038

theorem node039_checked : node039.check 4 point (25/32) 1 = true :=
  OwnershipTree.split_checked node035 node038 4 point (25/32) (13/16) 1 node035_checked node038_checked

def node040 : OwnershipTree := .split (25/32) node034 node039

theorem node040_checked : node040.check 4 point (23/32) 1 = true :=
  OwnershipTree.split_checked node034 node039 4 point (23/32) (25/32) 1 node034_checked node039_checked

def node041 : OwnershipTree := .split (23/32) node029 node040

theorem node041_checked : node041.check 4 point (43/64) 1 = true :=
  OwnershipTree.split_checked node029 node040 4 point (43/64) (23/32) 1 node029_checked node040_checked

def node042 : OwnershipTree := .split (43/64) node020 node041

theorem node042_checked : node042.check 4 point 0 1 = true :=
  OwnershipTree.split_checked node020 node041 4 point 0 (43/64) 1 node020_checked node041_checked

def certificate : OwnershipTree := node042

theorem checked : certificate.check 4 point 0 1 = true := node042_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 4 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned04_06
