import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned03_04Part000
import ElevenSquare.Tasks.T03.Initialization.Owned03_04Part001
import ElevenSquare.Tasks.T03.Initialization.Owned03_04Part002
import ElevenSquare.Tasks.T03.Initialization.Owned03_04Part003

namespace ElevenSquare.Pending.T03.Initialization.Owned03_04
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 3 point 0 (1/32) = true :=
  OwnershipTree.leaf_checked leaf000 3 point 0 (1/32) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 3 point (1/32) (1/16) = true :=
  OwnershipTree.leaf_checked leaf001 3 point (1/32) (1/16) rfl rfl leaf001_checked

def node002 : OwnershipTree := .leaf leaf002

theorem node002_checked : node002.check 3 point (1/16) (3/32) = true :=
  OwnershipTree.leaf_checked leaf002 3 point (1/16) (3/32) rfl rfl leaf002_checked

def node003 : OwnershipTree := .split (1/16) node001 node002

theorem node003_checked : node003.check 3 point (1/32) (3/32) = true :=
  OwnershipTree.split_checked node001 node002 3 point (1/32) (1/16) (3/32) node001_checked node002_checked

def node004 : OwnershipTree := .split (1/32) node000 node003

theorem node004_checked : node004.check 3 point 0 (3/32) = true :=
  OwnershipTree.split_checked node000 node003 3 point 0 (1/32) (3/32) node000_checked node003_checked

def node005 : OwnershipTree := .leaf leaf003

theorem node005_checked : node005.check 3 point (3/32) (7/64) = true :=
  OwnershipTree.leaf_checked leaf003 3 point (3/32) (7/64) rfl rfl leaf003_checked

def node006 : OwnershipTree := .leaf leaf004

theorem node006_checked : node006.check 3 point (7/64) (1/8) = true :=
  OwnershipTree.leaf_checked leaf004 3 point (7/64) (1/8) rfl rfl leaf004_checked

def node007 : OwnershipTree := .split (7/64) node005 node006

theorem node007_checked : node007.check 3 point (3/32) (1/8) = true :=
  OwnershipTree.split_checked node005 node006 3 point (3/32) (7/64) (1/8) node005_checked node006_checked

def node008 : OwnershipTree := .leaf leaf005

theorem node008_checked : node008.check 3 point (1/8) (9/64) = true :=
  OwnershipTree.leaf_checked leaf005 3 point (1/8) (9/64) rfl rfl leaf005_checked

def node009 : OwnershipTree := .leaf leaf006

theorem node009_checked : node009.check 3 point (9/64) (19/128) = true :=
  OwnershipTree.leaf_checked leaf006 3 point (9/64) (19/128) rfl rfl leaf006_checked

def node010 : OwnershipTree := .split (9/64) node008 node009

theorem node010_checked : node010.check 3 point (1/8) (19/128) = true :=
  OwnershipTree.split_checked node008 node009 3 point (1/8) (9/64) (19/128) node008_checked node009_checked

def node011 : OwnershipTree := .split (1/8) node007 node010

theorem node011_checked : node011.check 3 point (3/32) (19/128) = true :=
  OwnershipTree.split_checked node007 node010 3 point (3/32) (1/8) (19/128) node007_checked node010_checked

def node012 : OwnershipTree := .split (3/32) node004 node011

theorem node012_checked : node012.check 3 point 0 (19/128) = true :=
  OwnershipTree.split_checked node004 node011 3 point 0 (3/32) (19/128) node004_checked node011_checked

def node013 : OwnershipTree := .leaf leaf007

theorem node013_checked : node013.check 3 point (19/128) (5/32) = true :=
  OwnershipTree.leaf_checked leaf007 3 point (19/128) (5/32) rfl rfl leaf007_checked

def node014 : OwnershipTree := .leaf leaf008

theorem node014_checked : node014.check 3 point (5/32) (21/128) = true :=
  OwnershipTree.leaf_checked leaf008 3 point (5/32) (21/128) rfl rfl leaf008_checked

def node015 : OwnershipTree := .leaf leaf009

theorem node015_checked : node015.check 3 point (21/128) (11/64) = true :=
  OwnershipTree.leaf_checked leaf009 3 point (21/128) (11/64) rfl rfl leaf009_checked

def node016 : OwnershipTree := .split (21/128) node014 node015

theorem node016_checked : node016.check 3 point (5/32) (11/64) = true :=
  OwnershipTree.split_checked node014 node015 3 point (5/32) (21/128) (11/64) node014_checked node015_checked

def node017 : OwnershipTree := .split (5/32) node013 node016

theorem node017_checked : node017.check 3 point (19/128) (11/64) = true :=
  OwnershipTree.split_checked node013 node016 3 point (19/128) (5/32) (11/64) node013_checked node016_checked

def node018 : OwnershipTree := .leaf leaf010

theorem node018_checked : node018.check 3 point (11/64) (23/128) = true :=
  OwnershipTree.leaf_checked leaf010 3 point (11/64) (23/128) rfl rfl leaf010_checked

def node019 : OwnershipTree := .leaf leaf011

theorem node019_checked : node019.check 3 point (23/128) (3/16) = true :=
  OwnershipTree.leaf_checked leaf011 3 point (23/128) (3/16) rfl rfl leaf011_checked

def node020 : OwnershipTree := .split (23/128) node018 node019

theorem node020_checked : node020.check 3 point (11/64) (3/16) = true :=
  OwnershipTree.split_checked node018 node019 3 point (11/64) (23/128) (3/16) node018_checked node019_checked

def node021 : OwnershipTree := .leaf leaf012

theorem node021_checked : node021.check 3 point (3/16) (49/256) = true :=
  OwnershipTree.leaf_checked leaf012 3 point (3/16) (49/256) rfl rfl leaf012_checked

def node022 : OwnershipTree := .leaf leaf013

theorem node022_checked : node022.check 3 point (49/256) (25/128) = true :=
  OwnershipTree.leaf_checked leaf013 3 point (49/256) (25/128) rfl rfl leaf013_checked

def node023 : OwnershipTree := .split (49/256) node021 node022

theorem node023_checked : node023.check 3 point (3/16) (25/128) = true :=
  OwnershipTree.split_checked node021 node022 3 point (3/16) (49/256) (25/128) node021_checked node022_checked

def node024 : OwnershipTree := .split (3/16) node020 node023

theorem node024_checked : node024.check 3 point (11/64) (25/128) = true :=
  OwnershipTree.split_checked node020 node023 3 point (11/64) (3/16) (25/128) node020_checked node023_checked

def node025 : OwnershipTree := .split (11/64) node017 node024

theorem node025_checked : node025.check 3 point (19/128) (25/128) = true :=
  OwnershipTree.split_checked node017 node024 3 point (19/128) (11/64) (25/128) node017_checked node024_checked

def node026 : OwnershipTree := .split (19/128) node012 node025

theorem node026_checked : node026.check 3 point 0 (25/128) = true :=
  OwnershipTree.split_checked node012 node025 3 point 0 (19/128) (25/128) node012_checked node025_checked

def node027 : OwnershipTree := .leaf leaf014

theorem node027_checked : node027.check 3 point (25/128) (13/64) = true :=
  OwnershipTree.leaf_checked leaf014 3 point (25/128) (13/64) rfl rfl leaf014_checked

def node028 : OwnershipTree := .leaf leaf015

theorem node028_checked : node028.check 3 point (13/64) (27/128) = true :=
  OwnershipTree.leaf_checked leaf015 3 point (13/64) (27/128) rfl rfl leaf015_checked

def node029 : OwnershipTree := .leaf leaf016

theorem node029_checked : node029.check 3 point (27/128) (7/32) = true :=
  OwnershipTree.leaf_checked leaf016 3 point (27/128) (7/32) rfl rfl leaf016_checked

def node030 : OwnershipTree := .split (27/128) node028 node029

theorem node030_checked : node030.check 3 point (13/64) (7/32) = true :=
  OwnershipTree.split_checked node028 node029 3 point (13/64) (27/128) (7/32) node028_checked node029_checked

def node031 : OwnershipTree := .split (13/64) node027 node030

theorem node031_checked : node031.check 3 point (25/128) (7/32) = true :=
  OwnershipTree.split_checked node027 node030 3 point (25/128) (13/64) (7/32) node027_checked node030_checked

def node032 : OwnershipTree := .leaf leaf017

theorem node032_checked : node032.check 3 point (7/32) (29/128) = true :=
  OwnershipTree.leaf_checked leaf017 3 point (7/32) (29/128) rfl rfl leaf017_checked

def node033 : OwnershipTree := .leaf leaf018

theorem node033_checked : node033.check 3 point (29/128) (15/64) = true :=
  OwnershipTree.leaf_checked leaf018 3 point (29/128) (15/64) rfl rfl leaf018_checked

def node034 : OwnershipTree := .split (29/128) node032 node033

theorem node034_checked : node034.check 3 point (7/32) (15/64) = true :=
  OwnershipTree.split_checked node032 node033 3 point (7/32) (29/128) (15/64) node032_checked node033_checked

def node035 : OwnershipTree := .leaf leaf019

theorem node035_checked : node035.check 3 point (15/64) (1/4) = true :=
  OwnershipTree.leaf_checked leaf019 3 point (15/64) (1/4) rfl rfl leaf019_checked

def node036 : OwnershipTree := .leaf leaf020

theorem node036_checked : node036.check 3 point (1/4) (5/16) = true :=
  OwnershipTree.leaf_checked leaf020 3 point (1/4) (5/16) rfl rfl leaf020_checked

def node037 : OwnershipTree := .split (1/4) node035 node036

theorem node037_checked : node037.check 3 point (15/64) (5/16) = true :=
  OwnershipTree.split_checked node035 node036 3 point (15/64) (1/4) (5/16) node035_checked node036_checked

def node038 : OwnershipTree := .split (15/64) node034 node037

theorem node038_checked : node038.check 3 point (7/32) (5/16) = true :=
  OwnershipTree.split_checked node034 node037 3 point (7/32) (15/64) (5/16) node034_checked node037_checked

def node039 : OwnershipTree := .split (7/32) node031 node038

theorem node039_checked : node039.check 3 point (25/128) (5/16) = true :=
  OwnershipTree.split_checked node031 node038 3 point (25/128) (7/32) (5/16) node031_checked node038_checked

def node040 : OwnershipTree := .leaf leaf021

theorem node040_checked : node040.check 3 point (5/16) (3/8) = true :=
  OwnershipTree.leaf_checked leaf021 3 point (5/16) (3/8) rfl rfl leaf021_checked

def node041 : OwnershipTree := .leaf leaf022

theorem node041_checked : node041.check 3 point (3/8) (1/2) = true :=
  OwnershipTree.leaf_checked leaf022 3 point (3/8) (1/2) rfl rfl leaf022_checked

def node042 : OwnershipTree := .split (3/8) node040 node041

theorem node042_checked : node042.check 3 point (5/16) (1/2) = true :=
  OwnershipTree.split_checked node040 node041 3 point (5/16) (3/8) (1/2) node040_checked node041_checked

def node043 : OwnershipTree := .leaf leaf023

theorem node043_checked : node043.check 3 point (1/2) (5/8) = true :=
  OwnershipTree.leaf_checked leaf023 3 point (1/2) (5/8) rfl rfl leaf023_checked

def node044 : OwnershipTree := .leaf leaf024

theorem node044_checked : node044.check 3 point (5/8) (3/4) = true :=
  OwnershipTree.leaf_checked leaf024 3 point (5/8) (3/4) rfl rfl leaf024_checked

def node045 : OwnershipTree := .split (5/8) node043 node044

theorem node045_checked : node045.check 3 point (1/2) (3/4) = true :=
  OwnershipTree.split_checked node043 node044 3 point (1/2) (5/8) (3/4) node043_checked node044_checked

def node046 : OwnershipTree := .split (1/2) node042 node045

theorem node046_checked : node046.check 3 point (5/16) (3/4) = true :=
  OwnershipTree.split_checked node042 node045 3 point (5/16) (1/2) (3/4) node042_checked node045_checked

def node047 : OwnershipTree := .leaf leaf025

theorem node047_checked : node047.check 3 point (3/4) (13/16) = true :=
  OwnershipTree.leaf_checked leaf025 3 point (3/4) (13/16) rfl rfl leaf025_checked

def node048 : OwnershipTree := .leaf leaf026

theorem node048_checked : node048.check 3 point (13/16) (7/8) = true :=
  OwnershipTree.leaf_checked leaf026 3 point (13/16) (7/8) rfl rfl leaf026_checked

def node049 : OwnershipTree := .split (13/16) node047 node048

theorem node049_checked : node049.check 3 point (3/4) (7/8) = true :=
  OwnershipTree.split_checked node047 node048 3 point (3/4) (13/16) (7/8) node047_checked node048_checked

def node050 : OwnershipTree := .leaf leaf027

theorem node050_checked : node050.check 3 point (7/8) (15/16) = true :=
  OwnershipTree.leaf_checked leaf027 3 point (7/8) (15/16) rfl rfl leaf027_checked

def node051 : OwnershipTree := .leaf leaf028

theorem node051_checked : node051.check 3 point (15/16) 1 = true :=
  OwnershipTree.leaf_checked leaf028 3 point (15/16) 1 rfl rfl leaf028_checked

def node052 : OwnershipTree := .split (15/16) node050 node051

theorem node052_checked : node052.check 3 point (7/8) 1 = true :=
  OwnershipTree.split_checked node050 node051 3 point (7/8) (15/16) 1 node050_checked node051_checked

def node053 : OwnershipTree := .split (7/8) node049 node052

theorem node053_checked : node053.check 3 point (3/4) 1 = true :=
  OwnershipTree.split_checked node049 node052 3 point (3/4) (7/8) 1 node049_checked node052_checked

def node054 : OwnershipTree := .split (3/4) node046 node053

theorem node054_checked : node054.check 3 point (5/16) 1 = true :=
  OwnershipTree.split_checked node046 node053 3 point (5/16) (3/4) 1 node046_checked node053_checked

def node055 : OwnershipTree := .split (5/16) node039 node054

theorem node055_checked : node055.check 3 point (25/128) 1 = true :=
  OwnershipTree.split_checked node039 node054 3 point (25/128) (5/16) 1 node039_checked node054_checked

def node056 : OwnershipTree := .split (25/128) node026 node055

theorem node056_checked : node056.check 3 point 0 1 = true :=
  OwnershipTree.split_checked node026 node055 3 point 0 (25/128) 1 node026_checked node055_checked

def certificate : OwnershipTree := node056

theorem checked : certificate.check 3 point 0 1 = true := node056_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 3 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 3 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned03_04
