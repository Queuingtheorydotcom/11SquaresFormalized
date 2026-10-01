import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned08_04Part000
import ElevenSquare.Tasks.T03.Initialization.Owned08_04Part001
import ElevenSquare.Tasks.T03.Initialization.Owned08_04Part002
import ElevenSquare.Tasks.T03.Initialization.Owned08_04Part003

namespace ElevenSquare.Pending.T03.Initialization.Owned08_04
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 8 point 0 (1/16) = true :=
  OwnershipTree.leaf_checked leaf000 8 point 0 (1/16) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 8 point (1/16) (3/32) = true :=
  OwnershipTree.leaf_checked leaf001 8 point (1/16) (3/32) rfl rfl leaf001_checked

def node002 : OwnershipTree := .leaf leaf002

theorem node002_checked : node002.check 8 point (3/32) (1/8) = true :=
  OwnershipTree.leaf_checked leaf002 8 point (3/32) (1/8) rfl rfl leaf002_checked

def node003 : OwnershipTree := .split (3/32) node001 node002

theorem node003_checked : node003.check 8 point (1/16) (1/8) = true :=
  OwnershipTree.split_checked node001 node002 8 point (1/16) (3/32) (1/8) node001_checked node002_checked

def node004 : OwnershipTree := .split (1/16) node000 node003

theorem node004_checked : node004.check 8 point 0 (1/8) = true :=
  OwnershipTree.split_checked node000 node003 8 point 0 (1/16) (1/8) node000_checked node003_checked

def node005 : OwnershipTree := .leaf leaf003

theorem node005_checked : node005.check 8 point (1/8) (9/64) = true :=
  OwnershipTree.leaf_checked leaf003 8 point (1/8) (9/64) rfl rfl leaf003_checked

def node006 : OwnershipTree := .leaf leaf004

theorem node006_checked : node006.check 8 point (9/64) (5/32) = true :=
  OwnershipTree.leaf_checked leaf004 8 point (9/64) (5/32) rfl rfl leaf004_checked

def node007 : OwnershipTree := .leaf leaf005

theorem node007_checked : node007.check 8 point (5/32) (21/128) = true :=
  OwnershipTree.leaf_checked leaf005 8 point (5/32) (21/128) rfl rfl leaf005_checked

def node008 : OwnershipTree := .split (5/32) node006 node007

theorem node008_checked : node008.check 8 point (9/64) (21/128) = true :=
  OwnershipTree.split_checked node006 node007 8 point (9/64) (5/32) (21/128) node006_checked node007_checked

def node009 : OwnershipTree := .split (9/64) node005 node008

theorem node009_checked : node009.check 8 point (1/8) (21/128) = true :=
  OwnershipTree.split_checked node005 node008 8 point (1/8) (9/64) (21/128) node005_checked node008_checked

def node010 : OwnershipTree := .split (1/8) node004 node009

theorem node010_checked : node010.check 8 point 0 (21/128) = true :=
  OwnershipTree.split_checked node004 node009 8 point 0 (1/8) (21/128) node004_checked node009_checked

def node011 : OwnershipTree := .leaf leaf006

theorem node011_checked : node011.check 8 point (21/128) (11/64) = true :=
  OwnershipTree.leaf_checked leaf006 8 point (21/128) (11/64) rfl rfl leaf006_checked

def node012 : OwnershipTree := .leaf leaf007

theorem node012_checked : node012.check 8 point (11/64) (23/128) = true :=
  OwnershipTree.leaf_checked leaf007 8 point (11/64) (23/128) rfl rfl leaf007_checked

def node013 : OwnershipTree := .leaf leaf008

theorem node013_checked : node013.check 8 point (23/128) (3/16) = true :=
  OwnershipTree.leaf_checked leaf008 8 point (23/128) (3/16) rfl rfl leaf008_checked

def node014 : OwnershipTree := .split (23/128) node012 node013

theorem node014_checked : node014.check 8 point (11/64) (3/16) = true :=
  OwnershipTree.split_checked node012 node013 8 point (11/64) (23/128) (3/16) node012_checked node013_checked

def node015 : OwnershipTree := .split (11/64) node011 node014

theorem node015_checked : node015.check 8 point (21/128) (3/16) = true :=
  OwnershipTree.split_checked node011 node014 8 point (21/128) (11/64) (3/16) node011_checked node014_checked

def node016 : OwnershipTree := .leaf leaf009

theorem node016_checked : node016.check 8 point (3/16) (25/128) = true :=
  OwnershipTree.leaf_checked leaf009 8 point (3/16) (25/128) rfl rfl leaf009_checked

def node017 : OwnershipTree := .leaf leaf010

theorem node017_checked : node017.check 8 point (25/128) (13/64) = true :=
  OwnershipTree.leaf_checked leaf010 8 point (25/128) (13/64) rfl rfl leaf010_checked

def node018 : OwnershipTree := .leaf leaf011

theorem node018_checked : node018.check 8 point (13/64) (27/128) = true :=
  OwnershipTree.leaf_checked leaf011 8 point (13/64) (27/128) rfl rfl leaf011_checked

def node019 : OwnershipTree := .split (13/64) node017 node018

theorem node019_checked : node019.check 8 point (25/128) (27/128) = true :=
  OwnershipTree.split_checked node017 node018 8 point (25/128) (13/64) (27/128) node017_checked node018_checked

def node020 : OwnershipTree := .split (25/128) node016 node019

theorem node020_checked : node020.check 8 point (3/16) (27/128) = true :=
  OwnershipTree.split_checked node016 node019 8 point (3/16) (25/128) (27/128) node016_checked node019_checked

def node021 : OwnershipTree := .split (3/16) node015 node020

theorem node021_checked : node021.check 8 point (21/128) (27/128) = true :=
  OwnershipTree.split_checked node015 node020 8 point (21/128) (3/16) (27/128) node015_checked node020_checked

def node022 : OwnershipTree := .split (21/128) node010 node021

theorem node022_checked : node022.check 8 point 0 (27/128) = true :=
  OwnershipTree.split_checked node010 node021 8 point 0 (21/128) (27/128) node010_checked node021_checked

def node023 : OwnershipTree := .leaf leaf012

theorem node023_checked : node023.check 8 point (27/128) (7/32) = true :=
  OwnershipTree.leaf_checked leaf012 8 point (27/128) (7/32) rfl rfl leaf012_checked

def node024 : OwnershipTree := .leaf leaf013

theorem node024_checked : node024.check 8 point (7/32) (29/128) = true :=
  OwnershipTree.leaf_checked leaf013 8 point (7/32) (29/128) rfl rfl leaf013_checked

def node025 : OwnershipTree := .leaf leaf014

theorem node025_checked : node025.check 8 point (29/128) (15/64) = true :=
  OwnershipTree.leaf_checked leaf014 8 point (29/128) (15/64) rfl rfl leaf014_checked

def node026 : OwnershipTree := .split (29/128) node024 node025

theorem node026_checked : node026.check 8 point (7/32) (15/64) = true :=
  OwnershipTree.split_checked node024 node025 8 point (7/32) (29/128) (15/64) node024_checked node025_checked

def node027 : OwnershipTree := .split (7/32) node023 node026

theorem node027_checked : node027.check 8 point (27/128) (15/64) = true :=
  OwnershipTree.split_checked node023 node026 8 point (27/128) (7/32) (15/64) node023_checked node026_checked

def node028 : OwnershipTree := .leaf leaf015

theorem node028_checked : node028.check 8 point (15/64) (1/4) = true :=
  OwnershipTree.leaf_checked leaf015 8 point (15/64) (1/4) rfl rfl leaf015_checked

def node029 : OwnershipTree := .leaf leaf016

theorem node029_checked : node029.check 8 point (1/4) (5/16) = true :=
  OwnershipTree.leaf_checked leaf016 8 point (1/4) (5/16) rfl rfl leaf016_checked

def node030 : OwnershipTree := .leaf leaf017

theorem node030_checked : node030.check 8 point (5/16) (3/8) = true :=
  OwnershipTree.leaf_checked leaf017 8 point (5/16) (3/8) rfl rfl leaf017_checked

def node031 : OwnershipTree := .split (5/16) node029 node030

theorem node031_checked : node031.check 8 point (1/4) (3/8) = true :=
  OwnershipTree.split_checked node029 node030 8 point (1/4) (5/16) (3/8) node029_checked node030_checked

def node032 : OwnershipTree := .split (1/4) node028 node031

theorem node032_checked : node032.check 8 point (15/64) (3/8) = true :=
  OwnershipTree.split_checked node028 node031 8 point (15/64) (1/4) (3/8) node028_checked node031_checked

def node033 : OwnershipTree := .split (15/64) node027 node032

theorem node033_checked : node033.check 8 point (27/128) (3/8) = true :=
  OwnershipTree.split_checked node027 node032 8 point (27/128) (15/64) (3/8) node027_checked node032_checked

def node034 : OwnershipTree := .leaf leaf018

theorem node034_checked : node034.check 8 point (3/8) (1/2) = true :=
  OwnershipTree.leaf_checked leaf018 8 point (3/8) (1/2) rfl rfl leaf018_checked

def node035 : OwnershipTree := .leaf leaf019

theorem node035_checked : node035.check 8 point (1/2) (5/8) = true :=
  OwnershipTree.leaf_checked leaf019 8 point (1/2) (5/8) rfl rfl leaf019_checked

def node036 : OwnershipTree := .leaf leaf020

theorem node036_checked : node036.check 8 point (5/8) (3/4) = true :=
  OwnershipTree.leaf_checked leaf020 8 point (5/8) (3/4) rfl rfl leaf020_checked

def node037 : OwnershipTree := .split (5/8) node035 node036

theorem node037_checked : node037.check 8 point (1/2) (3/4) = true :=
  OwnershipTree.split_checked node035 node036 8 point (1/2) (5/8) (3/4) node035_checked node036_checked

def node038 : OwnershipTree := .split (1/2) node034 node037

theorem node038_checked : node038.check 8 point (3/8) (3/4) = true :=
  OwnershipTree.split_checked node034 node037 8 point (3/8) (1/2) (3/4) node034_checked node037_checked

def node039 : OwnershipTree := .leaf leaf021

theorem node039_checked : node039.check 8 point (3/4) (13/16) = true :=
  OwnershipTree.leaf_checked leaf021 8 point (3/4) (13/16) rfl rfl leaf021_checked

def node040 : OwnershipTree := .leaf leaf022

theorem node040_checked : node040.check 8 point (13/16) (7/8) = true :=
  OwnershipTree.leaf_checked leaf022 8 point (13/16) (7/8) rfl rfl leaf022_checked

def node041 : OwnershipTree := .split (13/16) node039 node040

theorem node041_checked : node041.check 8 point (3/4) (7/8) = true :=
  OwnershipTree.split_checked node039 node040 8 point (3/4) (13/16) (7/8) node039_checked node040_checked

def node042 : OwnershipTree := .leaf leaf023

theorem node042_checked : node042.check 8 point (7/8) (15/16) = true :=
  OwnershipTree.leaf_checked leaf023 8 point (7/8) (15/16) rfl rfl leaf023_checked

def node043 : OwnershipTree := .leaf leaf024

theorem node043_checked : node043.check 8 point (15/16) 1 = true :=
  OwnershipTree.leaf_checked leaf024 8 point (15/16) 1 rfl rfl leaf024_checked

def node044 : OwnershipTree := .split (15/16) node042 node043

theorem node044_checked : node044.check 8 point (7/8) 1 = true :=
  OwnershipTree.split_checked node042 node043 8 point (7/8) (15/16) 1 node042_checked node043_checked

def node045 : OwnershipTree := .split (7/8) node041 node044

theorem node045_checked : node045.check 8 point (3/4) 1 = true :=
  OwnershipTree.split_checked node041 node044 8 point (3/4) (7/8) 1 node041_checked node044_checked

def node046 : OwnershipTree := .split (3/4) node038 node045

theorem node046_checked : node046.check 8 point (3/8) 1 = true :=
  OwnershipTree.split_checked node038 node045 8 point (3/8) (3/4) 1 node038_checked node045_checked

def node047 : OwnershipTree := .split (3/8) node033 node046

theorem node047_checked : node047.check 8 point (27/128) 1 = true :=
  OwnershipTree.split_checked node033 node046 8 point (27/128) (3/8) 1 node033_checked node046_checked

def node048 : OwnershipTree := .split (27/128) node022 node047

theorem node048_checked : node048.check 8 point 0 1 = true :=
  OwnershipTree.split_checked node022 node047 8 point 0 (27/128) 1 node022_checked node047_checked

def certificate : OwnershipTree := node048

theorem checked : certificate.check 8 point 0 1 = true := node048_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 8 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 8 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned08_04
