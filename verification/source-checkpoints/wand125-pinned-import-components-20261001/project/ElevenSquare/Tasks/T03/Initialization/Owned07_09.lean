import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned07_09Part000
import ElevenSquare.Tasks.T03.Initialization.Owned07_09Part001
import ElevenSquare.Tasks.T03.Initialization.Owned07_09Part002
import ElevenSquare.Tasks.T03.Initialization.Owned07_09Part003
import ElevenSquare.Tasks.T03.Initialization.Owned07_09Part004
import ElevenSquare.Tasks.T03.Initialization.Owned07_09Part005

namespace ElevenSquare.Pending.T03.Initialization.Owned07_09
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 7 point 0 (1/256) = true :=
  OwnershipTree.leaf_checked leaf000 7 point 0 (1/256) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 7 point (1/256) (1/128) = true :=
  OwnershipTree.leaf_checked leaf001 7 point (1/256) (1/128) rfl rfl leaf001_checked

def node002 : OwnershipTree := .split (1/256) node000 node001

theorem node002_checked : node002.check 7 point 0 (1/128) = true :=
  OwnershipTree.split_checked node000 node001 7 point 0 (1/256) (1/128) node000_checked node001_checked

def node003 : OwnershipTree := .leaf leaf002

theorem node003_checked : node003.check 7 point (1/128) (1/64) = true :=
  OwnershipTree.leaf_checked leaf002 7 point (1/128) (1/64) rfl rfl leaf002_checked

def node004 : OwnershipTree := .leaf leaf003

theorem node004_checked : node004.check 7 point (1/64) (3/128) = true :=
  OwnershipTree.leaf_checked leaf003 7 point (1/64) (3/128) rfl rfl leaf003_checked

def node005 : OwnershipTree := .leaf leaf004

theorem node005_checked : node005.check 7 point (3/128) (1/32) = true :=
  OwnershipTree.leaf_checked leaf004 7 point (3/128) (1/32) rfl rfl leaf004_checked

def node006 : OwnershipTree := .split (3/128) node004 node005

theorem node006_checked : node006.check 7 point (1/64) (1/32) = true :=
  OwnershipTree.split_checked node004 node005 7 point (1/64) (3/128) (1/32) node004_checked node005_checked

def node007 : OwnershipTree := .split (1/64) node003 node006

theorem node007_checked : node007.check 7 point (1/128) (1/32) = true :=
  OwnershipTree.split_checked node003 node006 7 point (1/128) (1/64) (1/32) node003_checked node006_checked

def node008 : OwnershipTree := .split (1/128) node002 node007

theorem node008_checked : node008.check 7 point 0 (1/32) = true :=
  OwnershipTree.split_checked node002 node007 7 point 0 (1/128) (1/32) node002_checked node007_checked

def node009 : OwnershipTree := .leaf leaf005

theorem node009_checked : node009.check 7 point (1/32) (3/64) = true :=
  OwnershipTree.leaf_checked leaf005 7 point (1/32) (3/64) rfl rfl leaf005_checked

def node010 : OwnershipTree := .leaf leaf006

theorem node010_checked : node010.check 7 point (3/64) (1/16) = true :=
  OwnershipTree.leaf_checked leaf006 7 point (3/64) (1/16) rfl rfl leaf006_checked

def node011 : OwnershipTree := .split (3/64) node009 node010

theorem node011_checked : node011.check 7 point (1/32) (1/16) = true :=
  OwnershipTree.split_checked node009 node010 7 point (1/32) (3/64) (1/16) node009_checked node010_checked

def node012 : OwnershipTree := .leaf leaf007

theorem node012_checked : node012.check 7 point (1/16) (3/32) = true :=
  OwnershipTree.leaf_checked leaf007 7 point (1/16) (3/32) rfl rfl leaf007_checked

def node013 : OwnershipTree := .leaf leaf008

theorem node013_checked : node013.check 7 point (3/32) (1/8) = true :=
  OwnershipTree.leaf_checked leaf008 7 point (3/32) (1/8) rfl rfl leaf008_checked

def node014 : OwnershipTree := .leaf leaf009

theorem node014_checked : node014.check 7 point (1/8) (5/32) = true :=
  OwnershipTree.leaf_checked leaf009 7 point (1/8) (5/32) rfl rfl leaf009_checked

def node015 : OwnershipTree := .split (1/8) node013 node014

theorem node015_checked : node015.check 7 point (3/32) (5/32) = true :=
  OwnershipTree.split_checked node013 node014 7 point (3/32) (1/8) (5/32) node013_checked node014_checked

def node016 : OwnershipTree := .split (3/32) node012 node015

theorem node016_checked : node016.check 7 point (1/16) (5/32) = true :=
  OwnershipTree.split_checked node012 node015 7 point (1/16) (3/32) (5/32) node012_checked node015_checked

def node017 : OwnershipTree := .split (1/16) node011 node016

theorem node017_checked : node017.check 7 point (1/32) (5/32) = true :=
  OwnershipTree.split_checked node011 node016 7 point (1/32) (1/16) (5/32) node011_checked node016_checked

def node018 : OwnershipTree := .split (1/32) node008 node017

theorem node018_checked : node018.check 7 point 0 (5/32) = true :=
  OwnershipTree.split_checked node008 node017 7 point 0 (1/32) (5/32) node008_checked node017_checked

def node019 : OwnershipTree := .leaf leaf010

theorem node019_checked : node019.check 7 point (5/32) (11/64) = true :=
  OwnershipTree.leaf_checked leaf010 7 point (5/32) (11/64) rfl rfl leaf010_checked

def node020 : OwnershipTree := .leaf leaf011

theorem node020_checked : node020.check 7 point (11/64) (3/16) = true :=
  OwnershipTree.leaf_checked leaf011 7 point (11/64) (3/16) rfl rfl leaf011_checked

def node021 : OwnershipTree := .split (11/64) node019 node020

theorem node021_checked : node021.check 7 point (5/32) (3/16) = true :=
  OwnershipTree.split_checked node019 node020 7 point (5/32) (11/64) (3/16) node019_checked node020_checked

def node022 : OwnershipTree := .leaf leaf012

theorem node022_checked : node022.check 7 point (3/16) (25/128) = true :=
  OwnershipTree.leaf_checked leaf012 7 point (3/16) (25/128) rfl rfl leaf012_checked

def node023 : OwnershipTree := .leaf leaf013

theorem node023_checked : node023.check 7 point (25/128) (13/64) = true :=
  OwnershipTree.leaf_checked leaf013 7 point (25/128) (13/64) rfl rfl leaf013_checked

def node024 : OwnershipTree := .leaf leaf014

theorem node024_checked : node024.check 7 point (13/64) (27/128) = true :=
  OwnershipTree.leaf_checked leaf014 7 point (13/64) (27/128) rfl rfl leaf014_checked

def node025 : OwnershipTree := .split (13/64) node023 node024

theorem node025_checked : node025.check 7 point (25/128) (27/128) = true :=
  OwnershipTree.split_checked node023 node024 7 point (25/128) (13/64) (27/128) node023_checked node024_checked

def node026 : OwnershipTree := .split (25/128) node022 node025

theorem node026_checked : node026.check 7 point (3/16) (27/128) = true :=
  OwnershipTree.split_checked node022 node025 7 point (3/16) (25/128) (27/128) node022_checked node025_checked

def node027 : OwnershipTree := .split (3/16) node021 node026

theorem node027_checked : node027.check 7 point (5/32) (27/128) = true :=
  OwnershipTree.split_checked node021 node026 7 point (5/32) (3/16) (27/128) node021_checked node026_checked

def node028 : OwnershipTree := .leaf leaf015

theorem node028_checked : node028.check 7 point (27/128) (7/32) = true :=
  OwnershipTree.leaf_checked leaf015 7 point (27/128) (7/32) rfl rfl leaf015_checked

def node029 : OwnershipTree := .leaf leaf016

theorem node029_checked : node029.check 7 point (7/32) (29/128) = true :=
  OwnershipTree.leaf_checked leaf016 7 point (7/32) (29/128) rfl rfl leaf016_checked

def node030 : OwnershipTree := .split (7/32) node028 node029

theorem node030_checked : node030.check 7 point (27/128) (29/128) = true :=
  OwnershipTree.split_checked node028 node029 7 point (27/128) (7/32) (29/128) node028_checked node029_checked

def node031 : OwnershipTree := .leaf leaf017

theorem node031_checked : node031.check 7 point (29/128) (15/64) = true :=
  OwnershipTree.leaf_checked leaf017 7 point (29/128) (15/64) rfl rfl leaf017_checked

def node032 : OwnershipTree := .leaf leaf018

theorem node032_checked : node032.check 7 point (15/64) (31/128) = true :=
  OwnershipTree.leaf_checked leaf018 7 point (15/64) (31/128) rfl rfl leaf018_checked

def node033 : OwnershipTree := .leaf leaf019

theorem node033_checked : node033.check 7 point (31/128) (1/4) = true :=
  OwnershipTree.leaf_checked leaf019 7 point (31/128) (1/4) rfl rfl leaf019_checked

def node034 : OwnershipTree := .split (31/128) node032 node033

theorem node034_checked : node034.check 7 point (15/64) (1/4) = true :=
  OwnershipTree.split_checked node032 node033 7 point (15/64) (31/128) (1/4) node032_checked node033_checked

def node035 : OwnershipTree := .split (15/64) node031 node034

theorem node035_checked : node035.check 7 point (29/128) (1/4) = true :=
  OwnershipTree.split_checked node031 node034 7 point (29/128) (15/64) (1/4) node031_checked node034_checked

def node036 : OwnershipTree := .split (29/128) node030 node035

theorem node036_checked : node036.check 7 point (27/128) (1/4) = true :=
  OwnershipTree.split_checked node030 node035 7 point (27/128) (29/128) (1/4) node030_checked node035_checked

def node037 : OwnershipTree := .split (27/128) node027 node036

theorem node037_checked : node037.check 7 point (5/32) (1/4) = true :=
  OwnershipTree.split_checked node027 node036 7 point (5/32) (27/128) (1/4) node027_checked node036_checked

def node038 : OwnershipTree := .split (5/32) node018 node037

theorem node038_checked : node038.check 7 point 0 (1/4) = true :=
  OwnershipTree.split_checked node018 node037 7 point 0 (5/32) (1/4) node018_checked node037_checked

def node039 : OwnershipTree := .leaf leaf020

theorem node039_checked : node039.check 7 point (1/4) (17/64) = true :=
  OwnershipTree.leaf_checked leaf020 7 point (1/4) (17/64) rfl rfl leaf020_checked

def node040 : OwnershipTree := .leaf leaf021

theorem node040_checked : node040.check 7 point (17/64) (9/32) = true :=
  OwnershipTree.leaf_checked leaf021 7 point (17/64) (9/32) rfl rfl leaf021_checked

def node041 : OwnershipTree := .split (17/64) node039 node040

theorem node041_checked : node041.check 7 point (1/4) (9/32) = true :=
  OwnershipTree.split_checked node039 node040 7 point (1/4) (17/64) (9/32) node039_checked node040_checked

def node042 : OwnershipTree := .leaf leaf022

theorem node042_checked : node042.check 7 point (9/32) (5/16) = true :=
  OwnershipTree.leaf_checked leaf022 7 point (9/32) (5/16) rfl rfl leaf022_checked

def node043 : OwnershipTree := .leaf leaf023

theorem node043_checked : node043.check 7 point (5/16) (3/8) = true :=
  OwnershipTree.leaf_checked leaf023 7 point (5/16) (3/8) rfl rfl leaf023_checked

def node044 : OwnershipTree := .leaf leaf024

theorem node044_checked : node044.check 7 point (3/8) (1/2) = true :=
  OwnershipTree.leaf_checked leaf024 7 point (3/8) (1/2) rfl rfl leaf024_checked

def node045 : OwnershipTree := .split (3/8) node043 node044

theorem node045_checked : node045.check 7 point (5/16) (1/2) = true :=
  OwnershipTree.split_checked node043 node044 7 point (5/16) (3/8) (1/2) node043_checked node044_checked

def node046 : OwnershipTree := .split (5/16) node042 node045

theorem node046_checked : node046.check 7 point (9/32) (1/2) = true :=
  OwnershipTree.split_checked node042 node045 7 point (9/32) (5/16) (1/2) node042_checked node045_checked

def node047 : OwnershipTree := .split (9/32) node041 node046

theorem node047_checked : node047.check 7 point (1/4) (1/2) = true :=
  OwnershipTree.split_checked node041 node046 7 point (1/4) (9/32) (1/2) node041_checked node046_checked

def node048 : OwnershipTree := .leaf leaf025

theorem node048_checked : node048.check 7 point (1/2) (5/8) = true :=
  OwnershipTree.leaf_checked leaf025 7 point (1/2) (5/8) rfl rfl leaf025_checked

def node049 : OwnershipTree := .leaf leaf026

theorem node049_checked : node049.check 7 point (5/8) (11/16) = true :=
  OwnershipTree.leaf_checked leaf026 7 point (5/8) (11/16) rfl rfl leaf026_checked

def node050 : OwnershipTree := .split (5/8) node048 node049

theorem node050_checked : node050.check 7 point (1/2) (11/16) = true :=
  OwnershipTree.split_checked node048 node049 7 point (1/2) (5/8) (11/16) node048_checked node049_checked

def node051 : OwnershipTree := .leaf leaf027

theorem node051_checked : node051.check 7 point (11/16) (3/4) = true :=
  OwnershipTree.leaf_checked leaf027 7 point (11/16) (3/4) rfl rfl leaf027_checked

def node052 : OwnershipTree := .leaf leaf028

theorem node052_checked : node052.check 7 point (3/4) (25/32) = true :=
  OwnershipTree.leaf_checked leaf028 7 point (3/4) (25/32) rfl rfl leaf028_checked

def node053 : OwnershipTree := .leaf leaf029

theorem node053_checked : node053.check 7 point (25/32) (13/16) = true :=
  OwnershipTree.leaf_checked leaf029 7 point (25/32) (13/16) rfl rfl leaf029_checked

def node054 : OwnershipTree := .split (25/32) node052 node053

theorem node054_checked : node054.check 7 point (3/4) (13/16) = true :=
  OwnershipTree.split_checked node052 node053 7 point (3/4) (25/32) (13/16) node052_checked node053_checked

def node055 : OwnershipTree := .split (3/4) node051 node054

theorem node055_checked : node055.check 7 point (11/16) (13/16) = true :=
  OwnershipTree.split_checked node051 node054 7 point (11/16) (3/4) (13/16) node051_checked node054_checked

def node056 : OwnershipTree := .split (11/16) node050 node055

theorem node056_checked : node056.check 7 point (1/2) (13/16) = true :=
  OwnershipTree.split_checked node050 node055 7 point (1/2) (11/16) (13/16) node050_checked node055_checked

def node057 : OwnershipTree := .split (1/2) node047 node056

theorem node057_checked : node057.check 7 point (1/4) (13/16) = true :=
  OwnershipTree.split_checked node047 node056 7 point (1/4) (1/2) (13/16) node047_checked node056_checked

def node058 : OwnershipTree := .leaf leaf030

theorem node058_checked : node058.check 7 point (13/16) (27/32) = true :=
  OwnershipTree.leaf_checked leaf030 7 point (13/16) (27/32) rfl rfl leaf030_checked

def node059 : OwnershipTree := .leaf leaf031

theorem node059_checked : node059.check 7 point (27/32) (7/8) = true :=
  OwnershipTree.leaf_checked leaf031 7 point (27/32) (7/8) rfl rfl leaf031_checked

def node060 : OwnershipTree := .split (27/32) node058 node059

theorem node060_checked : node060.check 7 point (13/16) (7/8) = true :=
  OwnershipTree.split_checked node058 node059 7 point (13/16) (27/32) (7/8) node058_checked node059_checked

def node061 : OwnershipTree := .leaf leaf032

theorem node061_checked : node061.check 7 point (7/8) (29/32) = true :=
  OwnershipTree.leaf_checked leaf032 7 point (7/8) (29/32) rfl rfl leaf032_checked

def node062 : OwnershipTree := .leaf leaf033

theorem node062_checked : node062.check 7 point (29/32) (59/64) = true :=
  OwnershipTree.leaf_checked leaf033 7 point (29/32) (59/64) rfl rfl leaf033_checked

def node063 : OwnershipTree := .leaf leaf034

theorem node063_checked : node063.check 7 point (59/64) (15/16) = true :=
  OwnershipTree.leaf_checked leaf034 7 point (59/64) (15/16) rfl rfl leaf034_checked

def node064 : OwnershipTree := .split (59/64) node062 node063

theorem node064_checked : node064.check 7 point (29/32) (15/16) = true :=
  OwnershipTree.split_checked node062 node063 7 point (29/32) (59/64) (15/16) node062_checked node063_checked

def node065 : OwnershipTree := .split (29/32) node061 node064

theorem node065_checked : node065.check 7 point (7/8) (15/16) = true :=
  OwnershipTree.split_checked node061 node064 7 point (7/8) (29/32) (15/16) node061_checked node064_checked

def node066 : OwnershipTree := .split (7/8) node060 node065

theorem node066_checked : node066.check 7 point (13/16) (15/16) = true :=
  OwnershipTree.split_checked node060 node065 7 point (13/16) (7/8) (15/16) node060_checked node065_checked

def node067 : OwnershipTree := .leaf leaf035

theorem node067_checked : node067.check 7 point (15/16) (61/64) = true :=
  OwnershipTree.leaf_checked leaf035 7 point (15/16) (61/64) rfl rfl leaf035_checked

def node068 : OwnershipTree := .leaf leaf036

theorem node068_checked : node068.check 7 point (61/64) (31/32) = true :=
  OwnershipTree.leaf_checked leaf036 7 point (61/64) (31/32) rfl rfl leaf036_checked

def node069 : OwnershipTree := .leaf leaf037

theorem node069_checked : node069.check 7 point (31/32) (125/128) = true :=
  OwnershipTree.leaf_checked leaf037 7 point (31/32) (125/128) rfl rfl leaf037_checked

def node070 : OwnershipTree := .split (31/32) node068 node069

theorem node070_checked : node070.check 7 point (61/64) (125/128) = true :=
  OwnershipTree.split_checked node068 node069 7 point (61/64) (31/32) (125/128) node068_checked node069_checked

def node071 : OwnershipTree := .split (61/64) node067 node070

theorem node071_checked : node071.check 7 point (15/16) (125/128) = true :=
  OwnershipTree.split_checked node067 node070 7 point (15/16) (61/64) (125/128) node067_checked node070_checked

def node072 : OwnershipTree := .leaf leaf038

theorem node072_checked : node072.check 7 point (125/128) (63/64) = true :=
  OwnershipTree.leaf_checked leaf038 7 point (125/128) (63/64) rfl rfl leaf038_checked

def node073 : OwnershipTree := .leaf leaf039

theorem node073_checked : node073.check 7 point (63/64) (127/128) = true :=
  OwnershipTree.leaf_checked leaf039 7 point (63/64) (127/128) rfl rfl leaf039_checked

def node074 : OwnershipTree := .leaf leaf040

theorem node074_checked : node074.check 7 point (127/128) 1 = true :=
  OwnershipTree.leaf_checked leaf040 7 point (127/128) 1 rfl rfl leaf040_checked

def node075 : OwnershipTree := .split (127/128) node073 node074

theorem node075_checked : node075.check 7 point (63/64) 1 = true :=
  OwnershipTree.split_checked node073 node074 7 point (63/64) (127/128) 1 node073_checked node074_checked

def node076 : OwnershipTree := .split (63/64) node072 node075

theorem node076_checked : node076.check 7 point (125/128) 1 = true :=
  OwnershipTree.split_checked node072 node075 7 point (125/128) (63/64) 1 node072_checked node075_checked

def node077 : OwnershipTree := .split (125/128) node071 node076

theorem node077_checked : node077.check 7 point (15/16) 1 = true :=
  OwnershipTree.split_checked node071 node076 7 point (15/16) (125/128) 1 node071_checked node076_checked

def node078 : OwnershipTree := .split (15/16) node066 node077

theorem node078_checked : node078.check 7 point (13/16) 1 = true :=
  OwnershipTree.split_checked node066 node077 7 point (13/16) (15/16) 1 node066_checked node077_checked

def node079 : OwnershipTree := .split (13/16) node057 node078

theorem node079_checked : node079.check 7 point (1/4) 1 = true :=
  OwnershipTree.split_checked node057 node078 7 point (1/4) (13/16) 1 node057_checked node078_checked

def node080 : OwnershipTree := .split (1/4) node038 node079

theorem node080_checked : node080.check 7 point 0 1 = true :=
  OwnershipTree.split_checked node038 node079 7 point 0 (1/4) 1 node038_checked node079_checked

def certificate : OwnershipTree := node080

theorem checked : certificate.check 7 point 0 1 = true := node080_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 7 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned07_09
