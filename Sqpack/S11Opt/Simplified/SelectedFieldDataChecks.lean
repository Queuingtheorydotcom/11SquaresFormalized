import Sqpack.S11Opt.Simplified.SelectedFieldDataCore

namespace SquarePacking.S11Opt.Simplified.SelectedFields
open SquarePacking.S11Opt.Split
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CheckedBlocks

/-- Bounded computations keep the trusted kernel evaluation within memory. -/
theorem fieldBlock00 : ∀ j : Fin 32, (outsideField (j.val + 0) ||
    app (maskAt (j.val + 0)) || app (hmask (maskAt (j.val + 0)))) = true := by
  decide +kernel

theorem fieldBlock01 : ∀ j : Fin 32, (outsideField (j.val + 32) ||
    app (maskAt (j.val + 32)) || app (hmask (maskAt (j.val + 32)))) = true := by
  decide +kernel

theorem fieldBlock02 : ∀ j : Fin 32, (outsideField (j.val + 64) ||
    app (maskAt (j.val + 64)) || app (hmask (maskAt (j.val + 64)))) = true := by
  decide +kernel

theorem fieldBlock03 : ∀ j : Fin 32, (outsideField (j.val + 96) ||
    app (maskAt (j.val + 96)) || app (hmask (maskAt (j.val + 96)))) = true := by
  decide +kernel

theorem fieldBlock04 : ∀ j : Fin 32, (outsideField (j.val + 128) ||
    app (maskAt (j.val + 128)) || app (hmask (maskAt (j.val + 128)))) = true := by
  decide +kernel

theorem fieldBlock05 : ∀ j : Fin 32, (outsideField (j.val + 160) ||
    app (maskAt (j.val + 160)) || app (hmask (maskAt (j.val + 160)))) = true := by
  decide +kernel

theorem fieldBlock06 : ∀ j : Fin 32, (outsideField (j.val + 192) ||
    app (maskAt (j.val + 192)) || app (hmask (maskAt (j.val + 192)))) = true := by
  decide +kernel

theorem fieldBlock07 : ∀ j : Fin 32, (outsideField (j.val + 224) ||
    app (maskAt (j.val + 224)) || app (hmask (maskAt (j.val + 224)))) = true := by
  decide +kernel

theorem fieldBlock08 : ∀ j : Fin 32, (outsideField (j.val + 256) ||
    app (maskAt (j.val + 256)) || app (hmask (maskAt (j.val + 256)))) = true := by
  decide +kernel

theorem fieldBlock09 : ∀ j : Fin 32, (outsideField (j.val + 288) ||
    app (maskAt (j.val + 288)) || app (hmask (maskAt (j.val + 288)))) = true := by
  decide +kernel

theorem fieldBlock10 : ∀ j : Fin 32, (outsideField (j.val + 320) ||
    app (maskAt (j.val + 320)) || app (hmask (maskAt (j.val + 320)))) = true := by
  decide +kernel

theorem fieldBlock11 : ∀ j : Fin 32, (outsideField (j.val + 352) ||
    app (maskAt (j.val + 352)) || app (hmask (maskAt (j.val + 352)))) = true := by
  decide +kernel

theorem fieldBlock12 : ∀ j : Fin 32, (outsideField (j.val + 384) ||
    app (maskAt (j.val + 384)) || app (hmask (maskAt (j.val + 384)))) = true := by
  decide +kernel

theorem fieldBlock13 : ∀ j : Fin 32, (outsideField (j.val + 416) ||
    app (maskAt (j.val + 416)) || app (hmask (maskAt (j.val + 416)))) = true := by
  decide +kernel

theorem fieldBlock14 : ∀ j : Fin 32, (outsideField (j.val + 448) ||
    app (maskAt (j.val + 448)) || app (hmask (maskAt (j.val + 448)))) = true := by
  decide +kernel

theorem fieldBlock15 : ∀ j : Fin 32, (outsideField (j.val + 480) ||
    app (maskAt (j.val + 480)) || app (hmask (maskAt (j.val + 480)))) = true := by
  decide +kernel

theorem fieldBlock16 : ∀ j : Fin 32, (outsideField (j.val + 512) ||
    app (maskAt (j.val + 512)) || app (hmask (maskAt (j.val + 512)))) = true := by
  decide +kernel

theorem fieldBlock17 : ∀ j : Fin 32, (outsideField (j.val + 544) ||
    app (maskAt (j.val + 544)) || app (hmask (maskAt (j.val + 544)))) = true := by
  decide +kernel

theorem fieldBlock18 : ∀ j : Fin 32, (outsideField (j.val + 576) ||
    app (maskAt (j.val + 576)) || app (hmask (maskAt (j.val + 576)))) = true := by
  decide +kernel

theorem fieldBlock19 : ∀ j : Fin 32, (outsideField (j.val + 608) ||
    app (maskAt (j.val + 608)) || app (hmask (maskAt (j.val + 608)))) = true := by
  decide +kernel

theorem fieldBlock20 : ∀ j : Fin 32, (outsideField (j.val + 640) ||
    app (maskAt (j.val + 640)) || app (hmask (maskAt (j.val + 640)))) = true := by
  decide +kernel

theorem fieldBlock21 : ∀ j : Fin 32, (outsideField (j.val + 672) ||
    app (maskAt (j.val + 672)) || app (hmask (maskAt (j.val + 672)))) = true := by
  decide +kernel

theorem fieldBlock22 : ∀ j : Fin 32, (outsideField (j.val + 704) ||
    app (maskAt (j.val + 704)) || app (hmask (maskAt (j.val + 704)))) = true := by
  decide +kernel

theorem fieldBlock23 : ∀ j : Fin 32, (outsideField (j.val + 736) ||
    app (maskAt (j.val + 736)) || app (hmask (maskAt (j.val + 736)))) = true := by
  decide +kernel

theorem fieldBlock24 : ∀ j : Fin 32, (outsideField (j.val + 768) ||
    app (maskAt (j.val + 768)) || app (hmask (maskAt (j.val + 768)))) = true := by
  decide +kernel

theorem fieldBlock25 : ∀ j : Fin 32, (outsideField (j.val + 800) ||
    app (maskAt (j.val + 800)) || app (hmask (maskAt (j.val + 800)))) = true := by
  decide +kernel

theorem fieldBlock26 : ∀ j : Fin 32, (outsideField (j.val + 832) ||
    app (maskAt (j.val + 832)) || app (hmask (maskAt (j.val + 832)))) = true := by
  decide +kernel

theorem fieldBlock27 : ∀ j : Fin 32, (outsideField (j.val + 864) ||
    app (maskAt (j.val + 864)) || app (hmask (maskAt (j.val + 864)))) = true := by
  decide +kernel

theorem fieldBlock28 : ∀ j : Fin 32, (outsideField (j.val + 896) ||
    app (maskAt (j.val + 896)) || app (hmask (maskAt (j.val + 896)))) = true := by
  decide +kernel

theorem fieldBlock29 : ∀ j : Fin 32, (outsideField (j.val + 928) ||
    app (maskAt (j.val + 928)) || app (hmask (maskAt (j.val + 928)))) = true := by
  decide +kernel

theorem fieldBlock30 : ∀ j : Fin 32, (outsideField (j.val + 960) ||
    app (maskAt (j.val + 960)) || app (hmask (maskAt (j.val + 960)))) = true := by
  decide +kernel

theorem fieldBlock31 : ∀ j : Fin 32, (outsideField (j.val + 992) ||
    app (maskAt (j.val + 992)) || app (hmask (maskAt (j.val + 992)))) = true := by
  decide +kernel

theorem fieldBlock32 : ∀ j : Fin 32, (outsideField (j.val + 1024) ||
    app (maskAt (j.val + 1024)) || app (hmask (maskAt (j.val + 1024)))) = true := by
  decide +kernel

theorem fieldBlock33 : ∀ j : Fin 32, (outsideField (j.val + 1056) ||
    app (maskAt (j.val + 1056)) || app (hmask (maskAt (j.val + 1056)))) = true := by
  decide +kernel

theorem fieldBlock34 : ∀ j : Fin 32, (outsideField (j.val + 1088) ||
    app (maskAt (j.val + 1088)) || app (hmask (maskAt (j.val + 1088)))) = true := by
  decide +kernel

theorem fieldBlock35 : ∀ j : Fin 32, (outsideField (j.val + 1120) ||
    app (maskAt (j.val + 1120)) || app (hmask (maskAt (j.val + 1120)))) = true := by
  decide +kernel

theorem fieldBlock36 : ∀ j : Fin 32, (outsideField (j.val + 1152) ||
    app (maskAt (j.val + 1152)) || app (hmask (maskAt (j.val + 1152)))) = true := by
  decide +kernel

theorem fieldBlock37 : ∀ j : Fin 32, (outsideField (j.val + 1184) ||
    app (maskAt (j.val + 1184)) || app (hmask (maskAt (j.val + 1184)))) = true := by
  decide +kernel

theorem fieldBlock38 : ∀ j : Fin 32, (outsideField (j.val + 1216) ||
    app (maskAt (j.val + 1216)) || app (hmask (maskAt (j.val + 1216)))) = true := by
  decide +kernel

theorem fieldBlock39 : ∀ j : Fin 32, (outsideField (j.val + 1248) ||
    app (maskAt (j.val + 1248)) || app (hmask (maskAt (j.val + 1248)))) = true := by
  decide +kernel

theorem fieldBlock40 : ∀ j : Fin 32, (outsideField (j.val + 1280) ||
    app (maskAt (j.val + 1280)) || app (hmask (maskAt (j.val + 1280)))) = true := by
  decide +kernel

theorem fieldBlock41 : ∀ j : Fin 32, (outsideField (j.val + 1312) ||
    app (maskAt (j.val + 1312)) || app (hmask (maskAt (j.val + 1312)))) = true := by
  decide +kernel

theorem fieldBlock42 : ∀ j : Fin 32, (outsideField (j.val + 1344) ||
    app (maskAt (j.val + 1344)) || app (hmask (maskAt (j.val + 1344)))) = true := by
  decide +kernel

theorem fieldBlock43 : ∀ j : Fin 32, (outsideField (j.val + 1376) ||
    app (maskAt (j.val + 1376)) || app (hmask (maskAt (j.val + 1376)))) = true := by
  decide +kernel

theorem fieldBlock44 : ∀ j : Fin 32, (outsideField (j.val + 1408) ||
    app (maskAt (j.val + 1408)) || app (hmask (maskAt (j.val + 1408)))) = true := by
  decide +kernel

theorem fieldBlock45 : ∀ j : Fin 32, (outsideField (j.val + 1440) ||
    app (maskAt (j.val + 1440)) || app (hmask (maskAt (j.val + 1440)))) = true := by
  decide +kernel

theorem fieldBlock46 : ∀ j : Fin 32, (outsideField (j.val + 1472) ||
    app (maskAt (j.val + 1472)) || app (hmask (maskAt (j.val + 1472)))) = true := by
  decide +kernel

theorem fieldBlock47 : ∀ j : Fin 32, (outsideField (j.val + 1504) ||
    app (maskAt (j.val + 1504)) || app (hmask (maskAt (j.val + 1504)))) = true := by
  decide +kernel

theorem fieldBlock48 : ∀ j : Fin 32, (outsideField (j.val + 1536) ||
    app (maskAt (j.val + 1536)) || app (hmask (maskAt (j.val + 1536)))) = true := by
  decide +kernel

theorem fieldBlock49 : ∀ j : Fin 32, (outsideField (j.val + 1568) ||
    app (maskAt (j.val + 1568)) || app (hmask (maskAt (j.val + 1568)))) = true := by
  decide +kernel

theorem fieldBlock50 : ∀ j : Fin 32, (outsideField (j.val + 1600) ||
    app (maskAt (j.val + 1600)) || app (hmask (maskAt (j.val + 1600)))) = true := by
  decide +kernel

theorem fieldBlock51 : ∀ j : Fin 32, (outsideField (j.val + 1632) ||
    app (maskAt (j.val + 1632)) || app (hmask (maskAt (j.val + 1632)))) = true := by
  decide +kernel

theorem fieldBlock52 : ∀ j : Fin 32, (outsideField (j.val + 1664) ||
    app (maskAt (j.val + 1664)) || app (hmask (maskAt (j.val + 1664)))) = true := by
  decide +kernel

theorem fieldBlock53 : ∀ j : Fin 32, (outsideField (j.val + 1696) ||
    app (maskAt (j.val + 1696)) || app (hmask (maskAt (j.val + 1696)))) = true := by
  decide +kernel

theorem fieldBlock54 : ∀ j : Fin 32, (outsideField (j.val + 1728) ||
    app (maskAt (j.val + 1728)) || app (hmask (maskAt (j.val + 1728)))) = true := by
  decide +kernel

theorem fieldBlock55 : ∀ j : Fin 32, (outsideField (j.val + 1760) ||
    app (maskAt (j.val + 1760)) || app (hmask (maskAt (j.val + 1760)))) = true := by
  decide +kernel

theorem fieldBlock56 : ∀ j : Fin 32, (outsideField (j.val + 1792) ||
    app (maskAt (j.val + 1792)) || app (hmask (maskAt (j.val + 1792)))) = true := by
  decide +kernel

theorem fieldBlock57 : ∀ j : Fin 32, (outsideField (j.val + 1824) ||
    app (maskAt (j.val + 1824)) || app (hmask (maskAt (j.val + 1824)))) = true := by
  decide +kernel

theorem fieldBlock58 : ∀ j : Fin 32, (outsideField (j.val + 1856) ||
    app (maskAt (j.val + 1856)) || app (hmask (maskAt (j.val + 1856)))) = true := by
  decide +kernel

theorem fieldBlock59 : ∀ j : Fin 32, (outsideField (j.val + 1888) ||
    app (maskAt (j.val + 1888)) || app (hmask (maskAt (j.val + 1888)))) = true := by
  decide +kernel

theorem fieldBlock60 : ∀ j : Fin 32, (outsideField (j.val + 1920) ||
    app (maskAt (j.val + 1920)) || app (hmask (maskAt (j.val + 1920)))) = true := by
  decide +kernel

theorem fieldBlock61 : ∀ j : Fin 32, (outsideField (j.val + 1952) ||
    app (maskAt (j.val + 1952)) || app (hmask (maskAt (j.val + 1952)))) = true := by
  decide +kernel

theorem fieldBlock62 : ∀ j : Fin 32, (outsideField (j.val + 1984) ||
    app (maskAt (j.val + 1984)) || app (hmask (maskAt (j.val + 1984)))) = true := by
  decide +kernel

theorem fieldBlock63 : ∀ j : Fin 32, (outsideField (j.val + 2016) ||
    app (maskAt (j.val + 2016)) || app (hmask (maskAt (j.val + 2016)))) = true := by
  decide +kernel

theorem fieldBlock64 : ∀ j : Fin 32, (outsideField (j.val + 2048) ||
    app (maskAt (j.val + 2048)) || app (hmask (maskAt (j.val + 2048)))) = true := by
  decide +kernel

theorem fieldBlock65 : ∀ j : Fin 32, (outsideField (j.val + 2080) ||
    app (maskAt (j.val + 2080)) || app (hmask (maskAt (j.val + 2080)))) = true := by
  decide +kernel

theorem fieldBlock66 : ∀ j : Fin 32, (outsideField (j.val + 2112) ||
    app (maskAt (j.val + 2112)) || app (hmask (maskAt (j.val + 2112)))) = true := by
  decide +kernel

theorem fieldBlock67 : ∀ j : Fin 32, (outsideField (j.val + 2144) ||
    app (maskAt (j.val + 2144)) || app (hmask (maskAt (j.val + 2144)))) = true := by
  decide +kernel

theorem fieldBlock68 : ∀ j : Fin 8, (outsideField (j.val + 2176) ||
    app (maskAt (j.val + 2176)) || app (hmask (maskAt (j.val + 2176)))) = true := by
  decide +kernel

#print axioms fieldBlock68
end CheckedBlocks
end SquarePacking.S11Opt.Simplified.SelectedFields
