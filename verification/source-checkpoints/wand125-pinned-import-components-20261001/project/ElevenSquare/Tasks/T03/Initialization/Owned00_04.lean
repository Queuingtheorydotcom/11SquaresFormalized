import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned00_04Part000
import ElevenSquare.Tasks.T03.Initialization.Owned00_04Part001
import ElevenSquare.Tasks.T03.Initialization.Owned00_04Part002
import ElevenSquare.Tasks.T03.Initialization.Owned00_04Part003
import ElevenSquare.Tasks.T03.Initialization.Owned00_04Part004

namespace ElevenSquare.Pending.T03.Initialization.Owned00_04
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 0 point 0 (1/256) = true :=
  OwnershipTree.leaf_checked leaf000 0 point 0 (1/256) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 0 point (1/256) (1/128) = true :=
  OwnershipTree.leaf_checked leaf001 0 point (1/256) (1/128) rfl rfl leaf001_checked

def node002 : OwnershipTree := .split (1/256) node000 node001

theorem node002_checked : node002.check 0 point 0 (1/128) = true :=
  OwnershipTree.split_checked node000 node001 0 point 0 (1/256) (1/128) node000_checked node001_checked

def node003 : OwnershipTree := .leaf leaf002

theorem node003_checked : node003.check 0 point (1/128) (1/64) = true :=
  OwnershipTree.leaf_checked leaf002 0 point (1/128) (1/64) rfl rfl leaf002_checked

def node004 : OwnershipTree := .leaf leaf003

theorem node004_checked : node004.check 0 point (1/64) (3/128) = true :=
  OwnershipTree.leaf_checked leaf003 0 point (1/64) (3/128) rfl rfl leaf003_checked

def node005 : OwnershipTree := .split (1/64) node003 node004

theorem node005_checked : node005.check 0 point (1/128) (3/128) = true :=
  OwnershipTree.split_checked node003 node004 0 point (1/128) (1/64) (3/128) node003_checked node004_checked

def node006 : OwnershipTree := .split (1/128) node002 node005

theorem node006_checked : node006.check 0 point 0 (3/128) = true :=
  OwnershipTree.split_checked node002 node005 0 point 0 (1/128) (3/128) node002_checked node005_checked

def node007 : OwnershipTree := .leaf leaf004

theorem node007_checked : node007.check 0 point (3/128) (1/32) = true :=
  OwnershipTree.leaf_checked leaf004 0 point (3/128) (1/32) rfl rfl leaf004_checked

def node008 : OwnershipTree := .leaf leaf005

theorem node008_checked : node008.check 0 point (1/32) (3/64) = true :=
  OwnershipTree.leaf_checked leaf005 0 point (1/32) (3/64) rfl rfl leaf005_checked

def node009 : OwnershipTree := .split (1/32) node007 node008

theorem node009_checked : node009.check 0 point (3/128) (3/64) = true :=
  OwnershipTree.split_checked node007 node008 0 point (3/128) (1/32) (3/64) node007_checked node008_checked

def node010 : OwnershipTree := .leaf leaf006

theorem node010_checked : node010.check 0 point (3/64) (1/16) = true :=
  OwnershipTree.leaf_checked leaf006 0 point (3/64) (1/16) rfl rfl leaf006_checked

def node011 : OwnershipTree := .leaf leaf007

theorem node011_checked : node011.check 0 point (1/16) (3/32) = true :=
  OwnershipTree.leaf_checked leaf007 0 point (1/16) (3/32) rfl rfl leaf007_checked

def node012 : OwnershipTree := .leaf leaf008

theorem node012_checked : node012.check 0 point (3/32) (1/8) = true :=
  OwnershipTree.leaf_checked leaf008 0 point (3/32) (1/8) rfl rfl leaf008_checked

def node013 : OwnershipTree := .split (3/32) node011 node012

theorem node013_checked : node013.check 0 point (1/16) (1/8) = true :=
  OwnershipTree.split_checked node011 node012 0 point (1/16) (3/32) (1/8) node011_checked node012_checked

def node014 : OwnershipTree := .split (1/16) node010 node013

theorem node014_checked : node014.check 0 point (3/64) (1/8) = true :=
  OwnershipTree.split_checked node010 node013 0 point (3/64) (1/16) (1/8) node010_checked node013_checked

def node015 : OwnershipTree := .split (3/64) node009 node014

theorem node015_checked : node015.check 0 point (3/128) (1/8) = true :=
  OwnershipTree.split_checked node009 node014 0 point (3/128) (3/64) (1/8) node009_checked node014_checked

def node016 : OwnershipTree := .split (3/128) node006 node015

theorem node016_checked : node016.check 0 point 0 (1/8) = true :=
  OwnershipTree.split_checked node006 node015 0 point 0 (3/128) (1/8) node006_checked node015_checked

def node017 : OwnershipTree := .leaf leaf009

theorem node017_checked : node017.check 0 point (1/8) (5/32) = true :=
  OwnershipTree.leaf_checked leaf009 0 point (1/8) (5/32) rfl rfl leaf009_checked

def node018 : OwnershipTree := .leaf leaf010

theorem node018_checked : node018.check 0 point (5/32) (3/16) = true :=
  OwnershipTree.leaf_checked leaf010 0 point (5/32) (3/16) rfl rfl leaf010_checked

def node019 : OwnershipTree := .split (5/32) node017 node018

theorem node019_checked : node019.check 0 point (1/8) (3/16) = true :=
  OwnershipTree.split_checked node017 node018 0 point (1/8) (5/32) (3/16) node017_checked node018_checked

def node020 : OwnershipTree := .leaf leaf011

theorem node020_checked : node020.check 0 point (3/16) (13/64) = true :=
  OwnershipTree.leaf_checked leaf011 0 point (3/16) (13/64) rfl rfl leaf011_checked

def node021 : OwnershipTree := .leaf leaf012

theorem node021_checked : node021.check 0 point (13/64) (7/32) = true :=
  OwnershipTree.leaf_checked leaf012 0 point (13/64) (7/32) rfl rfl leaf012_checked

def node022 : OwnershipTree := .leaf leaf013

theorem node022_checked : node022.check 0 point (7/32) (29/128) = true :=
  OwnershipTree.leaf_checked leaf013 0 point (7/32) (29/128) rfl rfl leaf013_checked

def node023 : OwnershipTree := .split (7/32) node021 node022

theorem node023_checked : node023.check 0 point (13/64) (29/128) = true :=
  OwnershipTree.split_checked node021 node022 0 point (13/64) (7/32) (29/128) node021_checked node022_checked

def node024 : OwnershipTree := .split (13/64) node020 node023

theorem node024_checked : node024.check 0 point (3/16) (29/128) = true :=
  OwnershipTree.split_checked node020 node023 0 point (3/16) (13/64) (29/128) node020_checked node023_checked

def node025 : OwnershipTree := .split (3/16) node019 node024

theorem node025_checked : node025.check 0 point (1/8) (29/128) = true :=
  OwnershipTree.split_checked node019 node024 0 point (1/8) (3/16) (29/128) node019_checked node024_checked

def node026 : OwnershipTree := .leaf leaf014

theorem node026_checked : node026.check 0 point (29/128) (15/64) = true :=
  OwnershipTree.leaf_checked leaf014 0 point (29/128) (15/64) rfl rfl leaf014_checked

def node027 : OwnershipTree := .leaf leaf015

theorem node027_checked : node027.check 0 point (15/64) (31/128) = true :=
  OwnershipTree.leaf_checked leaf015 0 point (15/64) (31/128) rfl rfl leaf015_checked

def node028 : OwnershipTree := .split (15/64) node026 node027

theorem node028_checked : node028.check 0 point (29/128) (31/128) = true :=
  OwnershipTree.split_checked node026 node027 0 point (29/128) (15/64) (31/128) node026_checked node027_checked

def node029 : OwnershipTree := .leaf leaf016

theorem node029_checked : node029.check 0 point (31/128) (1/4) = true :=
  OwnershipTree.leaf_checked leaf016 0 point (31/128) (1/4) rfl rfl leaf016_checked

def node030 : OwnershipTree := .leaf leaf017

theorem node030_checked : node030.check 0 point (1/4) (33/128) = true :=
  OwnershipTree.leaf_checked leaf017 0 point (1/4) (33/128) rfl rfl leaf017_checked

def node031 : OwnershipTree := .leaf leaf018

theorem node031_checked : node031.check 0 point (33/128) (17/64) = true :=
  OwnershipTree.leaf_checked leaf018 0 point (33/128) (17/64) rfl rfl leaf018_checked

def node032 : OwnershipTree := .split (33/128) node030 node031

theorem node032_checked : node032.check 0 point (1/4) (17/64) = true :=
  OwnershipTree.split_checked node030 node031 0 point (1/4) (33/128) (17/64) node030_checked node031_checked

def node033 : OwnershipTree := .split (1/4) node029 node032

theorem node033_checked : node033.check 0 point (31/128) (17/64) = true :=
  OwnershipTree.split_checked node029 node032 0 point (31/128) (1/4) (17/64) node029_checked node032_checked

def node034 : OwnershipTree := .split (31/128) node028 node033

theorem node034_checked : node034.check 0 point (29/128) (17/64) = true :=
  OwnershipTree.split_checked node028 node033 0 point (29/128) (31/128) (17/64) node028_checked node033_checked

def node035 : OwnershipTree := .split (29/128) node025 node034

theorem node035_checked : node035.check 0 point (1/8) (17/64) = true :=
  OwnershipTree.split_checked node025 node034 0 point (1/8) (29/128) (17/64) node025_checked node034_checked

def node036 : OwnershipTree := .split (1/8) node016 node035

theorem node036_checked : node036.check 0 point 0 (17/64) = true :=
  OwnershipTree.split_checked node016 node035 0 point 0 (1/8) (17/64) node016_checked node035_checked

def node037 : OwnershipTree := .leaf leaf019

theorem node037_checked : node037.check 0 point (17/64) (9/32) = true :=
  OwnershipTree.leaf_checked leaf019 0 point (17/64) (9/32) rfl rfl leaf019_checked

def node038 : OwnershipTree := .leaf leaf020

theorem node038_checked : node038.check 0 point (9/32) (5/16) = true :=
  OwnershipTree.leaf_checked leaf020 0 point (9/32) (5/16) rfl rfl leaf020_checked

def node039 : OwnershipTree := .split (9/32) node037 node038

theorem node039_checked : node039.check 0 point (17/64) (5/16) = true :=
  OwnershipTree.split_checked node037 node038 0 point (17/64) (9/32) (5/16) node037_checked node038_checked

def node040 : OwnershipTree := .leaf leaf021

theorem node040_checked : node040.check 0 point (5/16) (3/8) = true :=
  OwnershipTree.leaf_checked leaf021 0 point (5/16) (3/8) rfl rfl leaf021_checked

def node041 : OwnershipTree := .leaf leaf022

theorem node041_checked : node041.check 0 point (3/8) (1/2) = true :=
  OwnershipTree.leaf_checked leaf022 0 point (3/8) (1/2) rfl rfl leaf022_checked

def node042 : OwnershipTree := .split (3/8) node040 node041

theorem node042_checked : node042.check 0 point (5/16) (1/2) = true :=
  OwnershipTree.split_checked node040 node041 0 point (5/16) (3/8) (1/2) node040_checked node041_checked

def node043 : OwnershipTree := .split (5/16) node039 node042

theorem node043_checked : node043.check 0 point (17/64) (1/2) = true :=
  OwnershipTree.split_checked node039 node042 0 point (17/64) (5/16) (1/2) node039_checked node042_checked

def node044 : OwnershipTree := .leaf leaf023

theorem node044_checked : node044.check 0 point (1/2) (5/8) = true :=
  OwnershipTree.leaf_checked leaf023 0 point (1/2) (5/8) rfl rfl leaf023_checked

def node045 : OwnershipTree := .leaf leaf024

theorem node045_checked : node045.check 0 point (5/8) (11/16) = true :=
  OwnershipTree.leaf_checked leaf024 0 point (5/8) (11/16) rfl rfl leaf024_checked

def node046 : OwnershipTree := .split (5/8) node044 node045

theorem node046_checked : node046.check 0 point (1/2) (11/16) = true :=
  OwnershipTree.split_checked node044 node045 0 point (1/2) (5/8) (11/16) node044_checked node045_checked

def node047 : OwnershipTree := .leaf leaf025

theorem node047_checked : node047.check 0 point (11/16) (3/4) = true :=
  OwnershipTree.leaf_checked leaf025 0 point (11/16) (3/4) rfl rfl leaf025_checked

def node048 : OwnershipTree := .leaf leaf026

theorem node048_checked : node048.check 0 point (3/4) (13/16) = true :=
  OwnershipTree.leaf_checked leaf026 0 point (3/4) (13/16) rfl rfl leaf026_checked

def node049 : OwnershipTree := .leaf leaf027

theorem node049_checked : node049.check 0 point (13/16) (27/32) = true :=
  OwnershipTree.leaf_checked leaf027 0 point (13/16) (27/32) rfl rfl leaf027_checked

def node050 : OwnershipTree := .split (13/16) node048 node049

theorem node050_checked : node050.check 0 point (3/4) (27/32) = true :=
  OwnershipTree.split_checked node048 node049 0 point (3/4) (13/16) (27/32) node048_checked node049_checked

def node051 : OwnershipTree := .split (3/4) node047 node050

theorem node051_checked : node051.check 0 point (11/16) (27/32) = true :=
  OwnershipTree.split_checked node047 node050 0 point (11/16) (3/4) (27/32) node047_checked node050_checked

def node052 : OwnershipTree := .split (11/16) node046 node051

theorem node052_checked : node052.check 0 point (1/2) (27/32) = true :=
  OwnershipTree.split_checked node046 node051 0 point (1/2) (11/16) (27/32) node046_checked node051_checked

def node053 : OwnershipTree := .split (1/2) node043 node052

theorem node053_checked : node053.check 0 point (17/64) (27/32) = true :=
  OwnershipTree.split_checked node043 node052 0 point (17/64) (1/2) (27/32) node043_checked node052_checked

def node054 : OwnershipTree := .leaf leaf028

theorem node054_checked : node054.check 0 point (27/32) (7/8) = true :=
  OwnershipTree.leaf_checked leaf028 0 point (27/32) (7/8) rfl rfl leaf028_checked

def node055 : OwnershipTree := .leaf leaf029

theorem node055_checked : node055.check 0 point (7/8) (29/32) = true :=
  OwnershipTree.leaf_checked leaf029 0 point (7/8) (29/32) rfl rfl leaf029_checked

def node056 : OwnershipTree := .split (7/8) node054 node055

theorem node056_checked : node056.check 0 point (27/32) (29/32) = true :=
  OwnershipTree.split_checked node054 node055 0 point (27/32) (7/8) (29/32) node054_checked node055_checked

def node057 : OwnershipTree := .leaf leaf030

theorem node057_checked : node057.check 0 point (29/32) (59/64) = true :=
  OwnershipTree.leaf_checked leaf030 0 point (29/32) (59/64) rfl rfl leaf030_checked

def node058 : OwnershipTree := .leaf leaf031

theorem node058_checked : node058.check 0 point (59/64) (15/16) = true :=
  OwnershipTree.leaf_checked leaf031 0 point (59/64) (15/16) rfl rfl leaf031_checked

def node059 : OwnershipTree := .leaf leaf032

theorem node059_checked : node059.check 0 point (15/16) (61/64) = true :=
  OwnershipTree.leaf_checked leaf032 0 point (15/16) (61/64) rfl rfl leaf032_checked

def node060 : OwnershipTree := .split (15/16) node058 node059

theorem node060_checked : node060.check 0 point (59/64) (61/64) = true :=
  OwnershipTree.split_checked node058 node059 0 point (59/64) (15/16) (61/64) node058_checked node059_checked

def node061 : OwnershipTree := .split (59/64) node057 node060

theorem node061_checked : node061.check 0 point (29/32) (61/64) = true :=
  OwnershipTree.split_checked node057 node060 0 point (29/32) (59/64) (61/64) node057_checked node060_checked

def node062 : OwnershipTree := .split (29/32) node056 node061

theorem node062_checked : node062.check 0 point (27/32) (61/64) = true :=
  OwnershipTree.split_checked node056 node061 0 point (27/32) (29/32) (61/64) node056_checked node061_checked

def node063 : OwnershipTree := .leaf leaf033

theorem node063_checked : node063.check 0 point (61/64) (31/32) = true :=
  OwnershipTree.leaf_checked leaf033 0 point (61/64) (31/32) rfl rfl leaf033_checked

def node064 : OwnershipTree := .leaf leaf034

theorem node064_checked : node064.check 0 point (31/32) (125/128) = true :=
  OwnershipTree.leaf_checked leaf034 0 point (31/32) (125/128) rfl rfl leaf034_checked

def node065 : OwnershipTree := .split (31/32) node063 node064

theorem node065_checked : node065.check 0 point (61/64) (125/128) = true :=
  OwnershipTree.split_checked node063 node064 0 point (61/64) (31/32) (125/128) node063_checked node064_checked

def node066 : OwnershipTree := .leaf leaf035

theorem node066_checked : node066.check 0 point (125/128) (63/64) = true :=
  OwnershipTree.leaf_checked leaf035 0 point (125/128) (63/64) rfl rfl leaf035_checked

def node067 : OwnershipTree := .leaf leaf036

theorem node067_checked : node067.check 0 point (63/64) (127/128) = true :=
  OwnershipTree.leaf_checked leaf036 0 point (63/64) (127/128) rfl rfl leaf036_checked

def node068 : OwnershipTree := .leaf leaf037

theorem node068_checked : node068.check 0 point (127/128) 1 = true :=
  OwnershipTree.leaf_checked leaf037 0 point (127/128) 1 rfl rfl leaf037_checked

def node069 : OwnershipTree := .split (127/128) node067 node068

theorem node069_checked : node069.check 0 point (63/64) 1 = true :=
  OwnershipTree.split_checked node067 node068 0 point (63/64) (127/128) 1 node067_checked node068_checked

def node070 : OwnershipTree := .split (63/64) node066 node069

theorem node070_checked : node070.check 0 point (125/128) 1 = true :=
  OwnershipTree.split_checked node066 node069 0 point (125/128) (63/64) 1 node066_checked node069_checked

def node071 : OwnershipTree := .split (125/128) node065 node070

theorem node071_checked : node071.check 0 point (61/64) 1 = true :=
  OwnershipTree.split_checked node065 node070 0 point (61/64) (125/128) 1 node065_checked node070_checked

def node072 : OwnershipTree := .split (61/64) node062 node071

theorem node072_checked : node072.check 0 point (27/32) 1 = true :=
  OwnershipTree.split_checked node062 node071 0 point (27/32) (61/64) 1 node062_checked node071_checked

def node073 : OwnershipTree := .split (27/32) node053 node072

theorem node073_checked : node073.check 0 point (17/64) 1 = true :=
  OwnershipTree.split_checked node053 node072 0 point (17/64) (27/32) 1 node053_checked node072_checked

def node074 : OwnershipTree := .split (17/64) node036 node073

theorem node074_checked : node074.check 0 point 0 1 = true :=
  OwnershipTree.split_checked node036 node073 0 point 0 (17/64) 1 node036_checked node073_checked

def certificate : OwnershipTree := node074

theorem checked : certificate.check 0 point 0 1 = true := node074_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 0 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 0 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned00_04
