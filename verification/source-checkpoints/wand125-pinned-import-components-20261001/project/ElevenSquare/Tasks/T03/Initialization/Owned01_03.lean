import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned01_03Part000
import ElevenSquare.Tasks.T03.Initialization.Owned01_03Part001
import ElevenSquare.Tasks.T03.Initialization.Owned01_03Part002
import ElevenSquare.Tasks.T03.Initialization.Owned01_03Part003
import ElevenSquare.Tasks.T03.Initialization.Owned01_03Part004
import ElevenSquare.Tasks.T03.Initialization.Owned01_03Part005
import ElevenSquare.Tasks.T03.Initialization.Owned01_03Part006
import ElevenSquare.Tasks.T03.Initialization.Owned01_03Part007
import ElevenSquare.Tasks.T03.Initialization.Owned01_03Part008

namespace ElevenSquare.Pending.T03.Initialization.Owned01_03
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 1 point 0 (1/32) = true :=
  OwnershipTree.leaf_checked leaf000 1 point 0 (1/32) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 1 point (1/32) (3/64) = true :=
  OwnershipTree.leaf_checked leaf001 1 point (1/32) (3/64) rfl rfl leaf001_checked

def node002 : OwnershipTree := .split (1/32) node000 node001

theorem node002_checked : node002.check 1 point 0 (3/64) = true :=
  OwnershipTree.split_checked node000 node001 1 point 0 (1/32) (3/64) node000_checked node001_checked

def node003 : OwnershipTree := .leaf leaf002

theorem node003_checked : node003.check 1 point (3/64) (1/16) = true :=
  OwnershipTree.leaf_checked leaf002 1 point (3/64) (1/16) rfl rfl leaf002_checked

def node004 : OwnershipTree := .leaf leaf003

theorem node004_checked : node004.check 1 point (1/16) (9/128) = true :=
  OwnershipTree.leaf_checked leaf003 1 point (1/16) (9/128) rfl rfl leaf003_checked

def node005 : OwnershipTree := .split (1/16) node003 node004

theorem node005_checked : node005.check 1 point (3/64) (9/128) = true :=
  OwnershipTree.split_checked node003 node004 1 point (3/64) (1/16) (9/128) node003_checked node004_checked

def node006 : OwnershipTree := .split (3/64) node002 node005

theorem node006_checked : node006.check 1 point 0 (9/128) = true :=
  OwnershipTree.split_checked node002 node005 1 point 0 (3/64) (9/128) node002_checked node005_checked

def node007 : OwnershipTree := .leaf leaf004

theorem node007_checked : node007.check 1 point (9/128) (5/64) = true :=
  OwnershipTree.leaf_checked leaf004 1 point (9/128) (5/64) rfl rfl leaf004_checked

def node008 : OwnershipTree := .leaf leaf005

theorem node008_checked : node008.check 1 point (5/64) (11/128) = true :=
  OwnershipTree.leaf_checked leaf005 1 point (5/64) (11/128) rfl rfl leaf005_checked

def node009 : OwnershipTree := .split (5/64) node007 node008

theorem node009_checked : node009.check 1 point (9/128) (11/128) = true :=
  OwnershipTree.split_checked node007 node008 1 point (9/128) (5/64) (11/128) node007_checked node008_checked

def node010 : OwnershipTree := .leaf leaf006

theorem node010_checked : node010.check 1 point (11/128) (3/32) = true :=
  OwnershipTree.leaf_checked leaf006 1 point (11/128) (3/32) rfl rfl leaf006_checked

def node011 : OwnershipTree := .leaf leaf007

theorem node011_checked : node011.check 1 point (3/32) (25/256) = true :=
  OwnershipTree.leaf_checked leaf007 1 point (3/32) (25/256) rfl rfl leaf007_checked

def node012 : OwnershipTree := .split (3/32) node010 node011

theorem node012_checked : node012.check 1 point (11/128) (25/256) = true :=
  OwnershipTree.split_checked node010 node011 1 point (11/128) (3/32) (25/256) node010_checked node011_checked

def node013 : OwnershipTree := .split (11/128) node009 node012

theorem node013_checked : node013.check 1 point (9/128) (25/256) = true :=
  OwnershipTree.split_checked node009 node012 1 point (9/128) (11/128) (25/256) node009_checked node012_checked

def node014 : OwnershipTree := .split (9/128) node006 node013

theorem node014_checked : node014.check 1 point 0 (25/256) = true :=
  OwnershipTree.split_checked node006 node013 1 point 0 (9/128) (25/256) node006_checked node013_checked

def node015 : OwnershipTree := .leaf leaf008

theorem node015_checked : node015.check 1 point (25/256) (13/128) = true :=
  OwnershipTree.leaf_checked leaf008 1 point (25/256) (13/128) rfl rfl leaf008_checked

def node016 : OwnershipTree := .leaf leaf009

theorem node016_checked : node016.check 1 point (13/128) (27/256) = true :=
  OwnershipTree.leaf_checked leaf009 1 point (13/128) (27/256) rfl rfl leaf009_checked

def node017 : OwnershipTree := .split (13/128) node015 node016

theorem node017_checked : node017.check 1 point (25/256) (27/256) = true :=
  OwnershipTree.split_checked node015 node016 1 point (25/256) (13/128) (27/256) node015_checked node016_checked

def node018 : OwnershipTree := .leaf leaf010

theorem node018_checked : node018.check 1 point (27/256) (7/64) = true :=
  OwnershipTree.leaf_checked leaf010 1 point (27/256) (7/64) rfl rfl leaf010_checked

def node019 : OwnershipTree := .leaf leaf011

theorem node019_checked : node019.check 1 point (7/64) (29/256) = true :=
  OwnershipTree.leaf_checked leaf011 1 point (7/64) (29/256) rfl rfl leaf011_checked

def node020 : OwnershipTree := .split (7/64) node018 node019

theorem node020_checked : node020.check 1 point (27/256) (29/256) = true :=
  OwnershipTree.split_checked node018 node019 1 point (27/256) (7/64) (29/256) node018_checked node019_checked

def node021 : OwnershipTree := .split (27/256) node017 node020

theorem node021_checked : node021.check 1 point (25/256) (29/256) = true :=
  OwnershipTree.split_checked node017 node020 1 point (25/256) (27/256) (29/256) node017_checked node020_checked

def node022 : OwnershipTree := .leaf leaf012

theorem node022_checked : node022.check 1 point (29/256) (15/128) = true :=
  OwnershipTree.leaf_checked leaf012 1 point (29/256) (15/128) rfl rfl leaf012_checked

def node023 : OwnershipTree := .leaf leaf013

theorem node023_checked : node023.check 1 point (15/128) (61/512) = true :=
  OwnershipTree.leaf_checked leaf013 1 point (15/128) (61/512) rfl rfl leaf013_checked

def node024 : OwnershipTree := .split (15/128) node022 node023

theorem node024_checked : node024.check 1 point (29/256) (61/512) = true :=
  OwnershipTree.split_checked node022 node023 1 point (29/256) (15/128) (61/512) node022_checked node023_checked

def node025 : OwnershipTree := .leaf leaf014

theorem node025_checked : node025.check 1 point (61/512) (31/256) = true :=
  OwnershipTree.leaf_checked leaf014 1 point (61/512) (31/256) rfl rfl leaf014_checked

def node026 : OwnershipTree := .leaf leaf015

theorem node026_checked : node026.check 1 point (31/256) (63/512) = true :=
  OwnershipTree.leaf_checked leaf015 1 point (31/256) (63/512) rfl rfl leaf015_checked

def node027 : OwnershipTree := .leaf leaf016

theorem node027_checked : node027.check 1 point (63/512) (1/8) = true :=
  OwnershipTree.leaf_checked leaf016 1 point (63/512) (1/8) rfl rfl leaf016_checked

def node028 : OwnershipTree := .split (63/512) node026 node027

theorem node028_checked : node028.check 1 point (31/256) (1/8) = true :=
  OwnershipTree.split_checked node026 node027 1 point (31/256) (63/512) (1/8) node026_checked node027_checked

def node029 : OwnershipTree := .split (31/256) node025 node028

theorem node029_checked : node029.check 1 point (61/512) (1/8) = true :=
  OwnershipTree.split_checked node025 node028 1 point (61/512) (31/256) (1/8) node025_checked node028_checked

def node030 : OwnershipTree := .split (61/512) node024 node029

theorem node030_checked : node030.check 1 point (29/256) (1/8) = true :=
  OwnershipTree.split_checked node024 node029 1 point (29/256) (61/512) (1/8) node024_checked node029_checked

def node031 : OwnershipTree := .split (29/256) node021 node030

theorem node031_checked : node031.check 1 point (25/256) (1/8) = true :=
  OwnershipTree.split_checked node021 node030 1 point (25/256) (29/256) (1/8) node021_checked node030_checked

def node032 : OwnershipTree := .split (25/256) node014 node031

theorem node032_checked : node032.check 1 point 0 (1/8) = true :=
  OwnershipTree.split_checked node014 node031 1 point 0 (25/256) (1/8) node014_checked node031_checked

def node033 : OwnershipTree := .leaf leaf017

theorem node033_checked : node033.check 1 point (1/8) (65/512) = true :=
  OwnershipTree.leaf_checked leaf017 1 point (1/8) (65/512) rfl rfl leaf017_checked

def node034 : OwnershipTree := .leaf leaf018

theorem node034_checked : node034.check 1 point (65/512) (33/256) = true :=
  OwnershipTree.leaf_checked leaf018 1 point (65/512) (33/256) rfl rfl leaf018_checked

def node035 : OwnershipTree := .split (65/512) node033 node034

theorem node035_checked : node035.check 1 point (1/8) (33/256) = true :=
  OwnershipTree.split_checked node033 node034 1 point (1/8) (65/512) (33/256) node033_checked node034_checked

def node036 : OwnershipTree := .leaf leaf019

theorem node036_checked : node036.check 1 point (33/256) (67/512) = true :=
  OwnershipTree.leaf_checked leaf019 1 point (33/256) (67/512) rfl rfl leaf019_checked

def node037 : OwnershipTree := .leaf leaf020

theorem node037_checked : node037.check 1 point (67/512) (17/128) = true :=
  OwnershipTree.leaf_checked leaf020 1 point (67/512) (17/128) rfl rfl leaf020_checked

def node038 : OwnershipTree := .split (67/512) node036 node037

theorem node038_checked : node038.check 1 point (33/256) (17/128) = true :=
  OwnershipTree.split_checked node036 node037 1 point (33/256) (67/512) (17/128) node036_checked node037_checked

def node039 : OwnershipTree := .split (33/256) node035 node038

theorem node039_checked : node039.check 1 point (1/8) (17/128) = true :=
  OwnershipTree.split_checked node035 node038 1 point (1/8) (33/256) (17/128) node035_checked node038_checked

def node040 : OwnershipTree := .leaf leaf021

theorem node040_checked : node040.check 1 point (17/128) (35/256) = true :=
  OwnershipTree.leaf_checked leaf021 1 point (17/128) (35/256) rfl rfl leaf021_checked

def node041 : OwnershipTree := .leaf leaf022

theorem node041_checked : node041.check 1 point (35/256) (9/64) = true :=
  OwnershipTree.leaf_checked leaf022 1 point (35/256) (9/64) rfl rfl leaf022_checked

def node042 : OwnershipTree := .split (35/256) node040 node041

theorem node042_checked : node042.check 1 point (17/128) (9/64) = true :=
  OwnershipTree.split_checked node040 node041 1 point (17/128) (35/256) (9/64) node040_checked node041_checked

def node043 : OwnershipTree := .leaf leaf023

theorem node043_checked : node043.check 1 point (9/64) (37/256) = true :=
  OwnershipTree.leaf_checked leaf023 1 point (9/64) (37/256) rfl rfl leaf023_checked

def node044 : OwnershipTree := .leaf leaf024

theorem node044_checked : node044.check 1 point (37/256) (19/128) = true :=
  OwnershipTree.leaf_checked leaf024 1 point (37/256) (19/128) rfl rfl leaf024_checked

def node045 : OwnershipTree := .split (37/256) node043 node044

theorem node045_checked : node045.check 1 point (9/64) (19/128) = true :=
  OwnershipTree.split_checked node043 node044 1 point (9/64) (37/256) (19/128) node043_checked node044_checked

def node046 : OwnershipTree := .split (9/64) node042 node045

theorem node046_checked : node046.check 1 point (17/128) (19/128) = true :=
  OwnershipTree.split_checked node042 node045 1 point (17/128) (9/64) (19/128) node042_checked node045_checked

def node047 : OwnershipTree := .split (17/128) node039 node046

theorem node047_checked : node047.check 1 point (1/8) (19/128) = true :=
  OwnershipTree.split_checked node039 node046 1 point (1/8) (17/128) (19/128) node039_checked node046_checked

def node048 : OwnershipTree := .leaf leaf025

theorem node048_checked : node048.check 1 point (19/128) (39/256) = true :=
  OwnershipTree.leaf_checked leaf025 1 point (19/128) (39/256) rfl rfl leaf025_checked

def node049 : OwnershipTree := .leaf leaf026

theorem node049_checked : node049.check 1 point (39/256) (5/32) = true :=
  OwnershipTree.leaf_checked leaf026 1 point (39/256) (5/32) rfl rfl leaf026_checked

def node050 : OwnershipTree := .split (39/256) node048 node049

theorem node050_checked : node050.check 1 point (19/128) (5/32) = true :=
  OwnershipTree.split_checked node048 node049 1 point (19/128) (39/256) (5/32) node048_checked node049_checked

def node051 : OwnershipTree := .leaf leaf027

theorem node051_checked : node051.check 1 point (5/32) (21/128) = true :=
  OwnershipTree.leaf_checked leaf027 1 point (5/32) (21/128) rfl rfl leaf027_checked

def node052 : OwnershipTree := .leaf leaf028

theorem node052_checked : node052.check 1 point (21/128) (11/64) = true :=
  OwnershipTree.leaf_checked leaf028 1 point (21/128) (11/64) rfl rfl leaf028_checked

def node053 : OwnershipTree := .split (21/128) node051 node052

theorem node053_checked : node053.check 1 point (5/32) (11/64) = true :=
  OwnershipTree.split_checked node051 node052 1 point (5/32) (21/128) (11/64) node051_checked node052_checked

def node054 : OwnershipTree := .split (5/32) node050 node053

theorem node054_checked : node054.check 1 point (19/128) (11/64) = true :=
  OwnershipTree.split_checked node050 node053 1 point (19/128) (5/32) (11/64) node050_checked node053_checked

def node055 : OwnershipTree := .leaf leaf029

theorem node055_checked : node055.check 1 point (11/64) (3/16) = true :=
  OwnershipTree.leaf_checked leaf029 1 point (11/64) (3/16) rfl rfl leaf029_checked

def node056 : OwnershipTree := .leaf leaf030

theorem node056_checked : node056.check 1 point (3/16) (7/32) = true :=
  OwnershipTree.leaf_checked leaf030 1 point (3/16) (7/32) rfl rfl leaf030_checked

def node057 : OwnershipTree := .split (3/16) node055 node056

theorem node057_checked : node057.check 1 point (11/64) (7/32) = true :=
  OwnershipTree.split_checked node055 node056 1 point (11/64) (3/16) (7/32) node055_checked node056_checked

def node058 : OwnershipTree := .leaf leaf031

theorem node058_checked : node058.check 1 point (7/32) (1/4) = true :=
  OwnershipTree.leaf_checked leaf031 1 point (7/32) (1/4) rfl rfl leaf031_checked

def node059 : OwnershipTree := .leaf leaf032

theorem node059_checked : node059.check 1 point (1/4) (1/2) = true :=
  OwnershipTree.leaf_checked leaf032 1 point (1/4) (1/2) rfl rfl leaf032_checked

def node060 : OwnershipTree := .leaf leaf033

theorem node060_checked : node060.check 1 point (1/2) (5/8) = true :=
  OwnershipTree.leaf_checked leaf033 1 point (1/2) (5/8) rfl rfl leaf033_checked

def node061 : OwnershipTree := .split (1/2) node059 node060

theorem node061_checked : node061.check 1 point (1/4) (5/8) = true :=
  OwnershipTree.split_checked node059 node060 1 point (1/4) (1/2) (5/8) node059_checked node060_checked

def node062 : OwnershipTree := .split (1/4) node058 node061

theorem node062_checked : node062.check 1 point (7/32) (5/8) = true :=
  OwnershipTree.split_checked node058 node061 1 point (7/32) (1/4) (5/8) node058_checked node061_checked

def node063 : OwnershipTree := .split (7/32) node057 node062

theorem node063_checked : node063.check 1 point (11/64) (5/8) = true :=
  OwnershipTree.split_checked node057 node062 1 point (11/64) (7/32) (5/8) node057_checked node062_checked

def node064 : OwnershipTree := .split (11/64) node054 node063

theorem node064_checked : node064.check 1 point (19/128) (5/8) = true :=
  OwnershipTree.split_checked node054 node063 1 point (19/128) (11/64) (5/8) node054_checked node063_checked

def node065 : OwnershipTree := .split (19/128) node047 node064

theorem node065_checked : node065.check 1 point (1/8) (5/8) = true :=
  OwnershipTree.split_checked node047 node064 1 point (1/8) (19/128) (5/8) node047_checked node064_checked

def node066 : OwnershipTree := .split (1/8) node032 node065

theorem node066_checked : node066.check 1 point 0 (5/8) = true :=
  OwnershipTree.split_checked node032 node065 1 point 0 (1/8) (5/8) node032_checked node065_checked

def node067 : OwnershipTree := .leaf leaf034

theorem node067_checked : node067.check 1 point (5/8) (21/32) = true :=
  OwnershipTree.leaf_checked leaf034 1 point (5/8) (21/32) rfl rfl leaf034_checked

def node068 : OwnershipTree := .leaf leaf035

theorem node068_checked : node068.check 1 point (21/32) (11/16) = true :=
  OwnershipTree.leaf_checked leaf035 1 point (21/32) (11/16) rfl rfl leaf035_checked

def node069 : OwnershipTree := .split (21/32) node067 node068

theorem node069_checked : node069.check 1 point (5/8) (11/16) = true :=
  OwnershipTree.split_checked node067 node068 1 point (5/8) (21/32) (11/16) node067_checked node068_checked

def node070 : OwnershipTree := .leaf leaf036

theorem node070_checked : node070.check 1 point (11/16) (45/64) = true :=
  OwnershipTree.leaf_checked leaf036 1 point (11/16) (45/64) rfl rfl leaf036_checked

def node071 : OwnershipTree := .leaf leaf037

theorem node071_checked : node071.check 1 point (45/64) (23/32) = true :=
  OwnershipTree.leaf_checked leaf037 1 point (45/64) (23/32) rfl rfl leaf037_checked

def node072 : OwnershipTree := .split (45/64) node070 node071

theorem node072_checked : node072.check 1 point (11/16) (23/32) = true :=
  OwnershipTree.split_checked node070 node071 1 point (11/16) (45/64) (23/32) node070_checked node071_checked

def node073 : OwnershipTree := .split (11/16) node069 node072

theorem node073_checked : node073.check 1 point (5/8) (23/32) = true :=
  OwnershipTree.split_checked node069 node072 1 point (5/8) (11/16) (23/32) node069_checked node072_checked

def node074 : OwnershipTree := .leaf leaf038

theorem node074_checked : node074.check 1 point (23/32) (93/128) = true :=
  OwnershipTree.leaf_checked leaf038 1 point (23/32) (93/128) rfl rfl leaf038_checked

def node075 : OwnershipTree := .leaf leaf039

theorem node075_checked : node075.check 1 point (93/128) (47/64) = true :=
  OwnershipTree.leaf_checked leaf039 1 point (93/128) (47/64) rfl rfl leaf039_checked

def node076 : OwnershipTree := .split (93/128) node074 node075

theorem node076_checked : node076.check 1 point (23/32) (47/64) = true :=
  OwnershipTree.split_checked node074 node075 1 point (23/32) (93/128) (47/64) node074_checked node075_checked

def node077 : OwnershipTree := .leaf leaf040

theorem node077_checked : node077.check 1 point (47/64) (95/128) = true :=
  OwnershipTree.leaf_checked leaf040 1 point (47/64) (95/128) rfl rfl leaf040_checked

def node078 : OwnershipTree := .leaf leaf041

theorem node078_checked : node078.check 1 point (95/128) (3/4) = true :=
  OwnershipTree.leaf_checked leaf041 1 point (95/128) (3/4) rfl rfl leaf041_checked

def node079 : OwnershipTree := .split (95/128) node077 node078

theorem node079_checked : node079.check 1 point (47/64) (3/4) = true :=
  OwnershipTree.split_checked node077 node078 1 point (47/64) (95/128) (3/4) node077_checked node078_checked

def node080 : OwnershipTree := .split (47/64) node076 node079

theorem node080_checked : node080.check 1 point (23/32) (3/4) = true :=
  OwnershipTree.split_checked node076 node079 1 point (23/32) (47/64) (3/4) node076_checked node079_checked

def node081 : OwnershipTree := .split (23/32) node073 node080

theorem node081_checked : node081.check 1 point (5/8) (3/4) = true :=
  OwnershipTree.split_checked node073 node080 1 point (5/8) (23/32) (3/4) node073_checked node080_checked

def node082 : OwnershipTree := .leaf leaf042

theorem node082_checked : node082.check 1 point (3/4) (97/128) = true :=
  OwnershipTree.leaf_checked leaf042 1 point (3/4) (97/128) rfl rfl leaf042_checked

def node083 : OwnershipTree := .leaf leaf043

theorem node083_checked : node083.check 1 point (97/128) (195/256) = true :=
  OwnershipTree.leaf_checked leaf043 1 point (97/128) (195/256) rfl rfl leaf043_checked

def node084 : OwnershipTree := .split (97/128) node082 node083

theorem node084_checked : node084.check 1 point (3/4) (195/256) = true :=
  OwnershipTree.split_checked node082 node083 1 point (3/4) (97/128) (195/256) node082_checked node083_checked

def node085 : OwnershipTree := .leaf leaf044

theorem node085_checked : node085.check 1 point (195/256) (49/64) = true :=
  OwnershipTree.leaf_checked leaf044 1 point (195/256) (49/64) rfl rfl leaf044_checked

def node086 : OwnershipTree := .leaf leaf045

theorem node086_checked : node086.check 1 point (49/64) (197/256) = true :=
  OwnershipTree.leaf_checked leaf045 1 point (49/64) (197/256) rfl rfl leaf045_checked

def node087 : OwnershipTree := .split (49/64) node085 node086

theorem node087_checked : node087.check 1 point (195/256) (197/256) = true :=
  OwnershipTree.split_checked node085 node086 1 point (195/256) (49/64) (197/256) node085_checked node086_checked

def node088 : OwnershipTree := .split (195/256) node084 node087

theorem node088_checked : node088.check 1 point (3/4) (197/256) = true :=
  OwnershipTree.split_checked node084 node087 1 point (3/4) (195/256) (197/256) node084_checked node087_checked

def node089 : OwnershipTree := .leaf leaf046

theorem node089_checked : node089.check 1 point (197/256) (99/128) = true :=
  OwnershipTree.leaf_checked leaf046 1 point (197/256) (99/128) rfl rfl leaf046_checked

def node090 : OwnershipTree := .leaf leaf047

theorem node090_checked : node090.check 1 point (99/128) (199/256) = true :=
  OwnershipTree.leaf_checked leaf047 1 point (99/128) (199/256) rfl rfl leaf047_checked

def node091 : OwnershipTree := .split (99/128) node089 node090

theorem node091_checked : node091.check 1 point (197/256) (199/256) = true :=
  OwnershipTree.split_checked node089 node090 1 point (197/256) (99/128) (199/256) node089_checked node090_checked

def node092 : OwnershipTree := .leaf leaf048

theorem node092_checked : node092.check 1 point (199/256) (25/32) = true :=
  OwnershipTree.leaf_checked leaf048 1 point (199/256) (25/32) rfl rfl leaf048_checked

def node093 : OwnershipTree := .leaf leaf049

theorem node093_checked : node093.check 1 point (25/32) (201/256) = true :=
  OwnershipTree.leaf_checked leaf049 1 point (25/32) (201/256) rfl rfl leaf049_checked

def node094 : OwnershipTree := .leaf leaf050

theorem node094_checked : node094.check 1 point (201/256) (101/128) = true :=
  OwnershipTree.leaf_checked leaf050 1 point (201/256) (101/128) rfl rfl leaf050_checked

def node095 : OwnershipTree := .split (201/256) node093 node094

theorem node095_checked : node095.check 1 point (25/32) (101/128) = true :=
  OwnershipTree.split_checked node093 node094 1 point (25/32) (201/256) (101/128) node093_checked node094_checked

def node096 : OwnershipTree := .split (25/32) node092 node095

theorem node096_checked : node096.check 1 point (199/256) (101/128) = true :=
  OwnershipTree.split_checked node092 node095 1 point (199/256) (25/32) (101/128) node092_checked node095_checked

def node097 : OwnershipTree := .split (199/256) node091 node096

theorem node097_checked : node097.check 1 point (197/256) (101/128) = true :=
  OwnershipTree.split_checked node091 node096 1 point (197/256) (199/256) (101/128) node091_checked node096_checked

def node098 : OwnershipTree := .split (197/256) node088 node097

theorem node098_checked : node098.check 1 point (3/4) (101/128) = true :=
  OwnershipTree.split_checked node088 node097 1 point (3/4) (197/256) (101/128) node088_checked node097_checked

def node099 : OwnershipTree := .split (3/4) node081 node098

theorem node099_checked : node099.check 1 point (5/8) (101/128) = true :=
  OwnershipTree.split_checked node081 node098 1 point (5/8) (3/4) (101/128) node081_checked node098_checked

def node100 : OwnershipTree := .leaf leaf051

theorem node100_checked : node100.check 1 point (101/128) (203/256) = true :=
  OwnershipTree.leaf_checked leaf051 1 point (101/128) (203/256) rfl rfl leaf051_checked

def node101 : OwnershipTree := .leaf leaf052

theorem node101_checked : node101.check 1 point (203/256) (51/64) = true :=
  OwnershipTree.leaf_checked leaf052 1 point (203/256) (51/64) rfl rfl leaf052_checked

def node102 : OwnershipTree := .split (203/256) node100 node101

theorem node102_checked : node102.check 1 point (101/128) (51/64) = true :=
  OwnershipTree.split_checked node100 node101 1 point (101/128) (203/256) (51/64) node100_checked node101_checked

def node103 : OwnershipTree := .leaf leaf053

theorem node103_checked : node103.check 1 point (51/64) (205/256) = true :=
  OwnershipTree.leaf_checked leaf053 1 point (51/64) (205/256) rfl rfl leaf053_checked

def node104 : OwnershipTree := .leaf leaf054

theorem node104_checked : node104.check 1 point (205/256) (103/128) = true :=
  OwnershipTree.leaf_checked leaf054 1 point (205/256) (103/128) rfl rfl leaf054_checked

def node105 : OwnershipTree := .split (205/256) node103 node104

theorem node105_checked : node105.check 1 point (51/64) (103/128) = true :=
  OwnershipTree.split_checked node103 node104 1 point (51/64) (205/256) (103/128) node103_checked node104_checked

def node106 : OwnershipTree := .split (51/64) node102 node105

theorem node106_checked : node106.check 1 point (101/128) (103/128) = true :=
  OwnershipTree.split_checked node102 node105 1 point (101/128) (51/64) (103/128) node102_checked node105_checked

def node107 : OwnershipTree := .leaf leaf055

theorem node107_checked : node107.check 1 point (103/128) (207/256) = true :=
  OwnershipTree.leaf_checked leaf055 1 point (103/128) (207/256) rfl rfl leaf055_checked

def node108 : OwnershipTree := .leaf leaf056

theorem node108_checked : node108.check 1 point (207/256) (13/16) = true :=
  OwnershipTree.leaf_checked leaf056 1 point (207/256) (13/16) rfl rfl leaf056_checked

def node109 : OwnershipTree := .split (207/256) node107 node108

theorem node109_checked : node109.check 1 point (103/128) (13/16) = true :=
  OwnershipTree.split_checked node107 node108 1 point (103/128) (207/256) (13/16) node107_checked node108_checked

def node110 : OwnershipTree := .leaf leaf057

theorem node110_checked : node110.check 1 point (13/16) (209/256) = true :=
  OwnershipTree.leaf_checked leaf057 1 point (13/16) (209/256) rfl rfl leaf057_checked

def node111 : OwnershipTree := .leaf leaf058

theorem node111_checked : node111.check 1 point (209/256) (105/128) = true :=
  OwnershipTree.leaf_checked leaf058 1 point (209/256) (105/128) rfl rfl leaf058_checked

def node112 : OwnershipTree := .leaf leaf059

theorem node112_checked : node112.check 1 point (105/128) (53/64) = true :=
  OwnershipTree.leaf_checked leaf059 1 point (105/128) (53/64) rfl rfl leaf059_checked

def node113 : OwnershipTree := .split (105/128) node111 node112

theorem node113_checked : node113.check 1 point (209/256) (53/64) = true :=
  OwnershipTree.split_checked node111 node112 1 point (209/256) (105/128) (53/64) node111_checked node112_checked

def node114 : OwnershipTree := .split (209/256) node110 node113

theorem node114_checked : node114.check 1 point (13/16) (53/64) = true :=
  OwnershipTree.split_checked node110 node113 1 point (13/16) (209/256) (53/64) node110_checked node113_checked

def node115 : OwnershipTree := .split (13/16) node109 node114

theorem node115_checked : node115.check 1 point (103/128) (53/64) = true :=
  OwnershipTree.split_checked node109 node114 1 point (103/128) (13/16) (53/64) node109_checked node114_checked

def node116 : OwnershipTree := .split (103/128) node106 node115

theorem node116_checked : node116.check 1 point (101/128) (53/64) = true :=
  OwnershipTree.split_checked node106 node115 1 point (101/128) (103/128) (53/64) node106_checked node115_checked

def node117 : OwnershipTree := .leaf leaf060

theorem node117_checked : node117.check 1 point (53/64) (107/128) = true :=
  OwnershipTree.leaf_checked leaf060 1 point (53/64) (107/128) rfl rfl leaf060_checked

def node118 : OwnershipTree := .leaf leaf061

theorem node118_checked : node118.check 1 point (107/128) (27/32) = true :=
  OwnershipTree.leaf_checked leaf061 1 point (107/128) (27/32) rfl rfl leaf061_checked

def node119 : OwnershipTree := .split (107/128) node117 node118

theorem node119_checked : node119.check 1 point (53/64) (27/32) = true :=
  OwnershipTree.split_checked node117 node118 1 point (53/64) (107/128) (27/32) node117_checked node118_checked

def node120 : OwnershipTree := .leaf leaf062

theorem node120_checked : node120.check 1 point (27/32) (109/128) = true :=
  OwnershipTree.leaf_checked leaf062 1 point (27/32) (109/128) rfl rfl leaf062_checked

def node121 : OwnershipTree := .leaf leaf063

theorem node121_checked : node121.check 1 point (109/128) (55/64) = true :=
  OwnershipTree.leaf_checked leaf063 1 point (109/128) (55/64) rfl rfl leaf063_checked

def node122 : OwnershipTree := .split (109/128) node120 node121

theorem node122_checked : node122.check 1 point (27/32) (55/64) = true :=
  OwnershipTree.split_checked node120 node121 1 point (27/32) (109/128) (55/64) node120_checked node121_checked

def node123 : OwnershipTree := .split (27/32) node119 node122

theorem node123_checked : node123.check 1 point (53/64) (55/64) = true :=
  OwnershipTree.split_checked node119 node122 1 point (53/64) (27/32) (55/64) node119_checked node122_checked

def node124 : OwnershipTree := .leaf leaf064

theorem node124_checked : node124.check 1 point (55/64) (7/8) = true :=
  OwnershipTree.leaf_checked leaf064 1 point (55/64) (7/8) rfl rfl leaf064_checked

def node125 : OwnershipTree := .leaf leaf065

theorem node125_checked : node125.check 1 point (7/8) (57/64) = true :=
  OwnershipTree.leaf_checked leaf065 1 point (7/8) (57/64) rfl rfl leaf065_checked

def node126 : OwnershipTree := .split (7/8) node124 node125

theorem node126_checked : node126.check 1 point (55/64) (57/64) = true :=
  OwnershipTree.split_checked node124 node125 1 point (55/64) (7/8) (57/64) node124_checked node125_checked

def node127 : OwnershipTree := .leaf leaf066

theorem node127_checked : node127.check 1 point (57/64) (29/32) = true :=
  OwnershipTree.leaf_checked leaf066 1 point (57/64) (29/32) rfl rfl leaf066_checked

def node128 : OwnershipTree := .leaf leaf067

theorem node128_checked : node128.check 1 point (29/32) (15/16) = true :=
  OwnershipTree.leaf_checked leaf067 1 point (29/32) (15/16) rfl rfl leaf067_checked

def node129 : OwnershipTree := .leaf leaf068

theorem node129_checked : node129.check 1 point (15/16) 1 = true :=
  OwnershipTree.leaf_checked leaf068 1 point (15/16) 1 rfl rfl leaf068_checked

def node130 : OwnershipTree := .split (15/16) node128 node129

theorem node130_checked : node130.check 1 point (29/32) 1 = true :=
  OwnershipTree.split_checked node128 node129 1 point (29/32) (15/16) 1 node128_checked node129_checked

def node131 : OwnershipTree := .split (29/32) node127 node130

theorem node131_checked : node131.check 1 point (57/64) 1 = true :=
  OwnershipTree.split_checked node127 node130 1 point (57/64) (29/32) 1 node127_checked node130_checked

def node132 : OwnershipTree := .split (57/64) node126 node131

theorem node132_checked : node132.check 1 point (55/64) 1 = true :=
  OwnershipTree.split_checked node126 node131 1 point (55/64) (57/64) 1 node126_checked node131_checked

def node133 : OwnershipTree := .split (55/64) node123 node132

theorem node133_checked : node133.check 1 point (53/64) 1 = true :=
  OwnershipTree.split_checked node123 node132 1 point (53/64) (55/64) 1 node123_checked node132_checked

def node134 : OwnershipTree := .split (53/64) node116 node133

theorem node134_checked : node134.check 1 point (101/128) 1 = true :=
  OwnershipTree.split_checked node116 node133 1 point (101/128) (53/64) 1 node116_checked node133_checked

def node135 : OwnershipTree := .split (101/128) node099 node134

theorem node135_checked : node135.check 1 point (5/8) 1 = true :=
  OwnershipTree.split_checked node099 node134 1 point (5/8) (101/128) 1 node099_checked node134_checked

def node136 : OwnershipTree := .split (5/8) node066 node135

theorem node136_checked : node136.check 1 point 0 1 = true :=
  OwnershipTree.split_checked node066 node135 1 point 0 (5/8) 1 node066_checked node135_checked

def certificate : OwnershipTree := node136

theorem checked : certificate.check 1 point 0 1 = true := node136_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 1 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 1 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned01_03
