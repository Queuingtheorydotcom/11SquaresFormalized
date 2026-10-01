import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned03_03Part000
import ElevenSquare.Tasks.T03.Initialization.Owned03_03Part001
import ElevenSquare.Tasks.T03.Initialization.Owned03_03Part002
import ElevenSquare.Tasks.T03.Initialization.Owned03_03Part003

namespace ElevenSquare.Pending.T03.Initialization.Owned03_03
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 3 point 0 (1/32) = true :=
  OwnershipTree.leaf_checked leaf000 3 point 0 (1/32) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 3 point (1/32) (3/64) = true :=
  OwnershipTree.leaf_checked leaf001 3 point (1/32) (3/64) rfl rfl leaf001_checked

def node002 : OwnershipTree := .leaf leaf002

theorem node002_checked : node002.check 3 point (3/64) (1/16) = true :=
  OwnershipTree.leaf_checked leaf002 3 point (3/64) (1/16) rfl rfl leaf002_checked

def node003 : OwnershipTree := .split (3/64) node001 node002

theorem node003_checked : node003.check 3 point (1/32) (1/16) = true :=
  OwnershipTree.split_checked node001 node002 3 point (1/32) (3/64) (1/16) node001_checked node002_checked

def node004 : OwnershipTree := .split (1/32) node000 node003

theorem node004_checked : node004.check 3 point 0 (1/16) = true :=
  OwnershipTree.split_checked node000 node003 3 point 0 (1/32) (1/16) node000_checked node003_checked

def node005 : OwnershipTree := .leaf leaf003

theorem node005_checked : node005.check 3 point (1/16) (9/128) = true :=
  OwnershipTree.leaf_checked leaf003 3 point (1/16) (9/128) rfl rfl leaf003_checked

def node006 : OwnershipTree := .leaf leaf004

theorem node006_checked : node006.check 3 point (9/128) (5/64) = true :=
  OwnershipTree.leaf_checked leaf004 3 point (9/128) (5/64) rfl rfl leaf004_checked

def node007 : OwnershipTree := .leaf leaf005

theorem node007_checked : node007.check 3 point (5/64) (11/128) = true :=
  OwnershipTree.leaf_checked leaf005 3 point (5/64) (11/128) rfl rfl leaf005_checked

def node008 : OwnershipTree := .split (5/64) node006 node007

theorem node008_checked : node008.check 3 point (9/128) (11/128) = true :=
  OwnershipTree.split_checked node006 node007 3 point (9/128) (5/64) (11/128) node006_checked node007_checked

def node009 : OwnershipTree := .split (9/128) node005 node008

theorem node009_checked : node009.check 3 point (1/16) (11/128) = true :=
  OwnershipTree.split_checked node005 node008 3 point (1/16) (9/128) (11/128) node005_checked node008_checked

def node010 : OwnershipTree := .split (1/16) node004 node009

theorem node010_checked : node010.check 3 point 0 (11/128) = true :=
  OwnershipTree.split_checked node004 node009 3 point 0 (1/16) (11/128) node004_checked node009_checked

def node011 : OwnershipTree := .leaf leaf006

theorem node011_checked : node011.check 3 point (11/128) (23/256) = true :=
  OwnershipTree.leaf_checked leaf006 3 point (11/128) (23/256) rfl rfl leaf006_checked

def node012 : OwnershipTree := .leaf leaf007

theorem node012_checked : node012.check 3 point (23/256) (3/32) = true :=
  OwnershipTree.leaf_checked leaf007 3 point (23/256) (3/32) rfl rfl leaf007_checked

def node013 : OwnershipTree := .leaf leaf008

theorem node013_checked : node013.check 3 point (3/32) (25/256) = true :=
  OwnershipTree.leaf_checked leaf008 3 point (3/32) (25/256) rfl rfl leaf008_checked

def node014 : OwnershipTree := .split (3/32) node012 node013

theorem node014_checked : node014.check 3 point (23/256) (25/256) = true :=
  OwnershipTree.split_checked node012 node013 3 point (23/256) (3/32) (25/256) node012_checked node013_checked

def node015 : OwnershipTree := .split (23/256) node011 node014

theorem node015_checked : node015.check 3 point (11/128) (25/256) = true :=
  OwnershipTree.split_checked node011 node014 3 point (11/128) (23/256) (25/256) node011_checked node014_checked

def node016 : OwnershipTree := .leaf leaf009

theorem node016_checked : node016.check 3 point (25/256) (13/128) = true :=
  OwnershipTree.leaf_checked leaf009 3 point (25/256) (13/128) rfl rfl leaf009_checked

def node017 : OwnershipTree := .leaf leaf010

theorem node017_checked : node017.check 3 point (13/128) (27/256) = true :=
  OwnershipTree.leaf_checked leaf010 3 point (13/128) (27/256) rfl rfl leaf010_checked

def node018 : OwnershipTree := .leaf leaf011

theorem node018_checked : node018.check 3 point (27/256) (7/64) = true :=
  OwnershipTree.leaf_checked leaf011 3 point (27/256) (7/64) rfl rfl leaf011_checked

def node019 : OwnershipTree := .split (27/256) node017 node018

theorem node019_checked : node019.check 3 point (13/128) (7/64) = true :=
  OwnershipTree.split_checked node017 node018 3 point (13/128) (27/256) (7/64) node017_checked node018_checked

def node020 : OwnershipTree := .split (13/128) node016 node019

theorem node020_checked : node020.check 3 point (25/256) (7/64) = true :=
  OwnershipTree.split_checked node016 node019 3 point (25/256) (13/128) (7/64) node016_checked node019_checked

def node021 : OwnershipTree := .split (25/256) node015 node020

theorem node021_checked : node021.check 3 point (11/128) (7/64) = true :=
  OwnershipTree.split_checked node015 node020 3 point (11/128) (25/256) (7/64) node015_checked node020_checked

def node022 : OwnershipTree := .split (11/128) node010 node021

theorem node022_checked : node022.check 3 point 0 (7/64) = true :=
  OwnershipTree.split_checked node010 node021 3 point 0 (11/128) (7/64) node010_checked node021_checked

def node023 : OwnershipTree := .leaf leaf012

theorem node023_checked : node023.check 3 point (7/64) (29/256) = true :=
  OwnershipTree.leaf_checked leaf012 3 point (7/64) (29/256) rfl rfl leaf012_checked

def node024 : OwnershipTree := .leaf leaf013

theorem node024_checked : node024.check 3 point (29/256) (15/128) = true :=
  OwnershipTree.leaf_checked leaf013 3 point (29/256) (15/128) rfl rfl leaf013_checked

def node025 : OwnershipTree := .leaf leaf014

theorem node025_checked : node025.check 3 point (15/128) (1/8) = true :=
  OwnershipTree.leaf_checked leaf014 3 point (15/128) (1/8) rfl rfl leaf014_checked

def node026 : OwnershipTree := .split (15/128) node024 node025

theorem node026_checked : node026.check 3 point (29/256) (1/8) = true :=
  OwnershipTree.split_checked node024 node025 3 point (29/256) (15/128) (1/8) node024_checked node025_checked

def node027 : OwnershipTree := .split (29/256) node023 node026

theorem node027_checked : node027.check 3 point (7/64) (1/8) = true :=
  OwnershipTree.split_checked node023 node026 3 point (7/64) (29/256) (1/8) node023_checked node026_checked

def node028 : OwnershipTree := .leaf leaf015

theorem node028_checked : node028.check 3 point (1/8) (17/128) = true :=
  OwnershipTree.leaf_checked leaf015 3 point (1/8) (17/128) rfl rfl leaf015_checked

def node029 : OwnershipTree := .leaf leaf016

theorem node029_checked : node029.check 3 point (17/128) (9/64) = true :=
  OwnershipTree.leaf_checked leaf016 3 point (17/128) (9/64) rfl rfl leaf016_checked

def node030 : OwnershipTree := .leaf leaf017

theorem node030_checked : node030.check 3 point (9/64) (5/32) = true :=
  OwnershipTree.leaf_checked leaf017 3 point (9/64) (5/32) rfl rfl leaf017_checked

def node031 : OwnershipTree := .split (9/64) node029 node030

theorem node031_checked : node031.check 3 point (17/128) (5/32) = true :=
  OwnershipTree.split_checked node029 node030 3 point (17/128) (9/64) (5/32) node029_checked node030_checked

def node032 : OwnershipTree := .split (17/128) node028 node031

theorem node032_checked : node032.check 3 point (1/8) (5/32) = true :=
  OwnershipTree.split_checked node028 node031 3 point (1/8) (17/128) (5/32) node028_checked node031_checked

def node033 : OwnershipTree := .split (1/8) node027 node032

theorem node033_checked : node033.check 3 point (7/64) (5/32) = true :=
  OwnershipTree.split_checked node027 node032 3 point (7/64) (1/8) (5/32) node027_checked node032_checked

def node034 : OwnershipTree := .leaf leaf018

theorem node034_checked : node034.check 3 point (5/32) (3/16) = true :=
  OwnershipTree.leaf_checked leaf018 3 point (5/32) (3/16) rfl rfl leaf018_checked

def node035 : OwnershipTree := .leaf leaf019

theorem node035_checked : node035.check 3 point (3/16) (1/4) = true :=
  OwnershipTree.leaf_checked leaf019 3 point (3/16) (1/4) rfl rfl leaf019_checked

def node036 : OwnershipTree := .leaf leaf020

theorem node036_checked : node036.check 3 point (1/4) (3/8) = true :=
  OwnershipTree.leaf_checked leaf020 3 point (1/4) (3/8) rfl rfl leaf020_checked

def node037 : OwnershipTree := .split (1/4) node035 node036

theorem node037_checked : node037.check 3 point (3/16) (3/8) = true :=
  OwnershipTree.split_checked node035 node036 3 point (3/16) (1/4) (3/8) node035_checked node036_checked

def node038 : OwnershipTree := .split (3/16) node034 node037

theorem node038_checked : node038.check 3 point (5/32) (3/8) = true :=
  OwnershipTree.split_checked node034 node037 3 point (5/32) (3/16) (3/8) node034_checked node037_checked

def node039 : OwnershipTree := .leaf leaf021

theorem node039_checked : node039.check 3 point (3/8) (7/16) = true :=
  OwnershipTree.leaf_checked leaf021 3 point (3/8) (7/16) rfl rfl leaf021_checked

def node040 : OwnershipTree := .leaf leaf022

theorem node040_checked : node040.check 3 point (7/16) (1/2) = true :=
  OwnershipTree.leaf_checked leaf022 3 point (7/16) (1/2) rfl rfl leaf022_checked

def node041 : OwnershipTree := .split (7/16) node039 node040

theorem node041_checked : node041.check 3 point (3/8) (1/2) = true :=
  OwnershipTree.split_checked node039 node040 3 point (3/8) (7/16) (1/2) node039_checked node040_checked

def node042 : OwnershipTree := .leaf leaf023

theorem node042_checked : node042.check 3 point (1/2) (3/4) = true :=
  OwnershipTree.leaf_checked leaf023 3 point (1/2) (3/4) rfl rfl leaf023_checked

def node043 : OwnershipTree := .leaf leaf024

theorem node043_checked : node043.check 3 point (3/4) 1 = true :=
  OwnershipTree.leaf_checked leaf024 3 point (3/4) 1 rfl rfl leaf024_checked

def node044 : OwnershipTree := .split (3/4) node042 node043

theorem node044_checked : node044.check 3 point (1/2) 1 = true :=
  OwnershipTree.split_checked node042 node043 3 point (1/2) (3/4) 1 node042_checked node043_checked

def node045 : OwnershipTree := .split (1/2) node041 node044

theorem node045_checked : node045.check 3 point (3/8) 1 = true :=
  OwnershipTree.split_checked node041 node044 3 point (3/8) (1/2) 1 node041_checked node044_checked

def node046 : OwnershipTree := .split (3/8) node038 node045

theorem node046_checked : node046.check 3 point (5/32) 1 = true :=
  OwnershipTree.split_checked node038 node045 3 point (5/32) (3/8) 1 node038_checked node045_checked

def node047 : OwnershipTree := .split (5/32) node033 node046

theorem node047_checked : node047.check 3 point (7/64) 1 = true :=
  OwnershipTree.split_checked node033 node046 3 point (7/64) (5/32) 1 node033_checked node046_checked

def node048 : OwnershipTree := .split (7/64) node022 node047

theorem node048_checked : node048.check 3 point 0 1 = true :=
  OwnershipTree.split_checked node022 node047 3 point 0 (7/64) 1 node022_checked node047_checked

def certificate : OwnershipTree := node048

theorem checked : certificate.check 3 point 0 1 = true := node048_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 3 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 3 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned03_03
